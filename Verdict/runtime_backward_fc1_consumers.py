"""Original FFN backward continuation, using fullrefs rather than adjacency.

The communication readers retain the original autograd context. This composes
source expressions in the same final Store, not SM/PM gradient equivalence.
"""
from Verdict import runtime_backward_ffn_consumers as previous
from Verdict import runtime_backward_linear_reads as linear
from Verdict import runtime_backward_layernorm_reads as layernorm
from Verdict.runtime_lineage import _same_typed


def _consumer(cells, producer, port, op):
    ref = producer.outputs[port]
    rows = [(i, c) for i, c in enumerate(cells) if c.rank == producer.rank
            and any(_same_typed(tuple(r), tuple(ref)) for r in c.inputs)]
    if len(rows) != 1 or rows[0][1].opname.name != op:
        raise ValueError('bw-fc1 unique original ' + op + ' consumer required')
    return rows[0]


def discover(worlds):
    _, prior = previous.render(worlds)
    rows = []
    for p in prior['reads']:
        view, cells, snapshot, order, label = next(w for w in worlds if w[-1] == p['world'])
        g = cells[p['gelu']['source_index']]
        before_i, before = _consumer(cells, g, 0, 'AllGatherPrim') if label == 'pm' else (None, g)
        li, lc = _consumer(cells, before, 0, 'BW_linear')
        lr = previous._read(linear, view, cells, snapshot, li, order, label)
        after_i, after = _consumer(cells, lc, 0, 'AllToAllPrim') if label == 'pm' else (None, lc)
        ni, nc = _consumer(cells, after, 0, 'BW_layernorm')
        nr = previous._read(layernorm, view, cells, snapshot, ni, order, label)
        if (not _same_typed(lr['input_refs'][0], list(before.outputs[0]))
                or not _same_typed(nr['input_refs'][0], list(after.outputs[0]))):
            raise ValueError('bw-fc1 original cotangent port mismatch')
        indices = [p['gelu']['source_index'], li, ni] if label == 'sm' else [p['gelu']['source_index'], before_i, li, after_i, ni]
        positions = [order['execution_to_source'].index(i) for i in indices]
        if positions != sorted(set(positions)):
            raise ValueError('bw-fc1 original reverse execution order mismatch')
        rows.append(dict(world=label, prior=p, linear=lr, layernorm=nr,
                         before_index=before_i, after_index=after_i,
                         before_op=before.opname.name, after_op=after.opname.name,
                         grad_ref=list(before.outputs[0]), dx_ref=list(after.outputs[0])))
    return rows


def _gelu_expression(prior):
    # The preceding stage authenticates these three edges and proves this RHS.
    ar, lr, gr = prior['add'], prior['linear'], prior['gelu']
    a = '(bw_add2 ' + ' '.join(f'(t {i})' for i in ar['input_tids']) + ').2'
    l = f'(bw_linear {a} (t {lr["input_tids"][1]}) (t {lr["input_tids"][2]})).1'
    return f'bw_gelu ({l}) (t {gr["input_tids"][1]})'


def _equation(name, label, tid, expression, rewrites):
    return [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
            f'    t {tid} = {expression} := by',
            '  rw [' + ', '.join(n + ' s t h' for n in rewrites) + ']',
            f'#print axioms {name}']


def render(worlds, capture, rank_code):
    from Verdict import graph_to_lean as compiler
    from Verdict import runtime_backward_collective_reads as collective
    from Verdict import runtime_backward_gelu_reads as gelu
    rows = discover(worlds)
    view, cells, _, order, label = next(w for w in worlds if w[-1] == 'pm')
    snapshot = compiler._load_chunk_source(capture, rank_code)
    compiler.attach_collective_scopes(view, snapshot)
    proofs, source_proofs, collective_rows = [], [], []
    gelus = {(r['world'], r['prior']['gelu']['source_index']): r for r in rows}
    linears = {(r['world'], r['linear']['source_index']): r for r in rows}
    gradients, dxs, dx_names, exchanges = {}, {}, {}, {}

    def communication(r, field, reader, expected, port):
        text, c = collective.render_read(view, cells, snapshot, r[field], order, 'pm', reader, port)
        # Re-bind the primitive's lowered endpoints, independently of its DTO.
        node = cells[r[field]].node
        scope = view.collective_scopes[node]
        if (not _same_typed(c['source_index'], r[field])
                or not _same_typed(c['input_tids'], [t.tid for t in view.node_inputs(node)])
                or not _same_typed(c['input_refs'], [list(view.source_tensor(t)) for t in view.node_inputs(node)])
                or not _same_typed(c['output_ref'], list(cells[r[field]].outputs[0]))
                or not _same_typed(c['output_tid'], view.node_outputs(node)[0].tid)
                or not _same_typed(c['params'], list(scope.params))
                or not _same_typed(c['ranks'], list(scope.ranks))
                or not _same_typed([p['output_refs'][port] for p in c['predecessors']], c['input_refs'])):
            raise ValueError('bw-fc1 original collective binding mismatch')
        source_proofs.append(text); collective_rows.append(c)
        args, names = [], []
        for p in c['predecessors']:
            key = ('pm', p['source_index'])
            if key not in expected:
                raise ValueError('bw-fc1 selected-stage peer missing')
            peer = expected[key]
            original = peer['prior']['gelu'] if field == 'before_index' else peer['linear']
            if not _same_typed(original, p):
                raise ValueError('bw-fc1 authenticated peer differs from original source read')
            if field == 'before_index':
                args.append('(' + _gelu_expression(peer['prior']) + ')')
                names.append(peer['prior']['theorems'][1])
            else:
                args.append('(' + dxs[key] + ')'); names.append(dx_names[key])
        rank = cells[r[field]].rank
        local = c['ranks'].index(rank)
        if field == 'before_index':
            if c['opname'] != 'AllGatherPrim' or len(c['params']) != 1:
                raise ValueError('bw-fc1 original gather required')
            value = f'allGatherPrimDimN {c["params"][0]} {len(c["ranks"])} {local}'
        else:
            if c['opname'] != 'AllToAllPrim' or len(c['params']) != 2:
                raise ValueError('bw-fc1 original reverse exchange required')
            value = f'AllToAllSourceFaithful.tensor {len(c["ranks"])} {local} {c["params"][0]} {c["params"][1]}'
        expression = value + ' [' + ', '.join(args) + ']'
        name = c['theorems'][0] + '_contributions'
        proofs.extend([f'theorem {name} (s t : Store) (h : pmDenoteWithInputs s = some t) :',
                       f'    t {c["output_tid"]} = {expression} := by',
                       f'  rw [{c["theorems"][0]} s t h]',
                       '  simp only [List.map_cons, List.map_nil]',
                       '  rw [' + ', '.join(n + ' s t h' for n in names) + ']',
                       f'#print axioms {name}'])
        return expression, name

    for r in rows:
        key = (r['world'], r['linear']['source_index'])
        gradients[key] = communication(r, 'before_index', gelu.render_read, gelus, 0) if r['world'] == 'pm' else (_gelu_expression(r['prior']), r['prior']['theorems'][1])
    for r in rows:
        lr = r['linear']; label = r['world']; key = (label, lr['source_index'])
        expression, grad_name = gradients[key]
        linear_expression = f'(bw_linear ({expression}) (t {lr["input_tids"][1]}) (t {lr["input_tids"][2]}))'
        names = []
        for port, role in enumerate(('dx', 'dw')):
            name = f'backwardFC1_{label}_{lr["source_index"]}_{role}'
            rhs = linear_expression + f'.{port+1}'
            proofs += _equation(name, label, lr['output_tids'][port], rhs, [lr['theorems'][port], grad_name])
            names.append(name)
            if port == 0: dxs[key], dx_names[key] = rhs, name
        r['linear_consumers'] = names
    # Each exchange needs both peer FC1 reads; emit after the entire linear wave.
    for r in rows:
        key = (r['world'], r['linear']['source_index'])
        exchanges[key] = communication(r, 'after_index', linear.render_read, linears, 0) if r['world'] == 'pm' else (dxs[key], dx_names[key])
    for r in rows:
        nr = r['layernorm']; label = r['world']
        expr, name = exchanges[(label, r['linear']['source_index'])]
        base = f'(bw_layernorm ({expr}) ' + ' '.join(f'(t {i})' for i in nr['input_tids'][1:]) + ')'
        r['layernorm_consumers'] = []
        for port, (role, proj) in enumerate(zip(('dx','dgamma','dbeta'), ('1','2.1','2.2'), strict=True)):
            target = f'backwardFC1Layernorm_{label}_{nr["source_index"]}_{role}'
            proofs += _equation(target, label, nr['output_tids'][port], base+'.'+proj, [nr['theorems'][port], name])
            r['layernorm_consumers'].append(target)
    return '\n'.join(proofs) + '\n', dict(reads=rows, collective_reads=collective_rows,
        collective_source=''.join(source_proofs), proof_admissible=False, kernel_value_proved=False,
        public_complete=False, torch_refinement=False)
