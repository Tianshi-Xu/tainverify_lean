"""Original mixed post-transpose frontier. Emitted source Lean is UNCOMPILED.

No Torch refinement, matmul, attention, downstream closure or kernel claim.
The caller supplies exactly the predecessor's bound and complete run schedule.
"""
from dataclasses import asdict

from Verdict import graph_to_lean as c
from Verdict import runtime_transpose_values as transpose
from Verdict import runtime_projection_values as projection
from Verdict import runtime_view_values as view
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict import runtime_embedding_route_values as primitive
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_world import _ordinary


def _swap(xs):
    a, b, c_, d = xs
    return a, b, d, c_


def _transpose(index, cell, producer):
    node = projection._node(index, cell)
    params, status = _ordinary(index.view, node, c._get_node_params)
    kwargs = dict(cell.kwargs)
    consts = kwargs.pop('__consts', [])
    if (op(cell) != 'FW_transpose' or status is not None
            or not _same_typed(params, [2, 3]) or not _same_typed(consts, [])
            or set(kwargs) != {'dim0', 'dim1'}
            or len(cell.inputs) != 1 or len(cell.outputs) != 1):
        raise ValueError('post-transpose original axes/kwargs/arity mismatch')
    x, = (post._port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    rank = len(x.endpoint.shape)
    axes = [kwargs['dim0'], kwargs['dim1']]
    if (any(type(axis) is not int or not -rank <= axis < rank for axis in axes)
            or [axis + rank if axis < 0 else axis for axis in axes] != [2, 3]):
        raise ValueError('post-transpose original axes/kwargs/arity mismatch')
    y, = (post._port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    if (not _same_typed(x, producer) or len(x.parent_shape) != 4
            or any(p.endpoint.ref[:3] != tuple(node)[:3] for p in (x, y))
            or y.endpoint.writer != tuple(node)):
        raise ValueError('post-transpose original fullref/owner/writer mismatch')
    if (y.parent_shape != _swap(x.parent_shape) or y.bounds != _swap(x.bounds)
            or y.endpoint.shape != _swap(x.endpoint.shape)
            or not _same_typed(y.value_part, x.value_part)):
        raise ValueError('post-transpose original swapped parent/bounds/value mismatch')
    return routes.Step(tuple(node), op(cell), (x,), (y,))


def _boundary(index, cell, ports, ranks, j):
    """Derive output from the independently authenticated ordered input cover."""
    node = projection._node(index, cell)
    kind = op(cell)
    if kind not in ('AllToAllPrim', 'AllGatherPrim'):
        raise ValueError('post-transpose unsupported collective')
    a, b = (3, 1) if kind == 'AllToAllPrim' else (2, None)
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
        'post-transpose source scope missing/ambiguous')
    from trainverify.runtime_source_authority import writer_export_id
    writer = _one((w for w in index.view._collective_source['writers']
        if _same_typed((w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
                       w['ref']['source_cid'], w['source_irname']), tuple(node))
        and w['ref']['op'] == kind), 'post-transpose source writer missing/ambiguous')
    if (scope.source_writer != writer_export_id(writer['ref'])
            or scope.source_writer != writer['export_id']):
        raise ValueError('post-transpose source writer/export/call identity mismatch')
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    for key, refs in [('inputs', cell.inputs), ('outputs', cell.outputs)]:
        if not _same_typed(writer[key], [dict(zip(fields, ref)) for ref in refs]):
            raise ValueError('post-transpose source writer ordered fullrefs mismatch')
    if (scope.op != kind or not _same_typed(scope.params, (a, b) if b else (a,))
            or not _same_typed(scope.ranks, tuple(ranks))
            or not _same_typed(scope.local_index, j)
            or not _same_typed(node.rank, ranks[j])
            or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape, ports[j].endpoint.shape)
            or not _same_typed([tuple(r) for r in cell.inputs], [p.endpoint.ref for p in ports])
            or len(cell.outputs) != 1):
        raise ValueError('post-transpose ordered source peers/owner/scope mismatch')
    kwargs = dict(cell.kwargs); consts = kwargs.pop('__consts', [])
    expected = dict(idim=a, odim=b) if b else dict(dim=a)
    rawranks = kwargs.pop('ranks', None)
    if (type(rawranks) not in (list, tuple) or not _same_typed(tuple(rawranks), tuple(ranks))
            or not _same_typed(kwargs, expected) or not _same_typed(consts, [])):
        raise ValueError('post-transpose raw kwargs mismatch')
    if (len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or not _same_typed([p.endpoint.ref[1] for p in ports], list(ranks))):
        raise ValueError('post-transpose peer rank identity mismatch')
    first = ports[0]
    if len(first.parent_shape) != 4:
        raise ValueError('post-transpose rank-four input required')
    end = 0
    for p in ports:
        if (p.parent_shape != first.parent_shape or p.parent_name != first.parent_name
                or p.value_part != first.value_part or p.bounds[a][0] != end
                or p.endpoint.shape != first.endpoint.shape
                or any(p.bounds[d] != (0, first.parent_shape[d]) for d in range(4) if d != a)):
            raise ValueError('post-transpose input contiguous gather/full split partition mismatch')
        end = p.bounds[a][1]
    if end != first.parent_shape[a]:
        raise ValueError('post-transpose input gather incomplete cover')
    bounds = [(0, d) for d in first.parent_shape]
    if b is not None:
        width, rem = divmod(first.parent_shape[b], len(ranks))
        if rem or width <= 0:
            raise ValueError('post-transpose nondivisible actual split axis')
        bounds[b] = (j*width, (j+1)*width)
    out = index.endpoint(cell.outputs[0])
    if (out.ref[:3] != tuple(node)[:3] or out.writer != tuple(node)
            or not _same_typed(out.tid, scope.output_tid)
            or out.shape != tuple(hi-lo for lo, hi in bounds)):
        raise ValueError('post-transpose output original identity/shape mismatch')
    derived = routes.Port(out, first.parent_name, first.parent_shape, tuple(bounds), first.value_part)
    coverage = {}
    for field, expected_ports in [('_input_irs', ports), ('_output_irs', (derived,))]:
        irs = getattr(cell, field, None)
        key = 'input_metadata' if field == '_input_irs' else 'output_metadata'
        coverage[key] = 'absent'
        if irs is None:
            continue
        if field == '_input_irs' and len(irs) == 1 and len(ports) > 1:
            expected_ports = (ports[j],); coverage[key] = 'local-only'
        else:
            coverage[key] = 'all-peers' if field == '_input_irs' else 'present'
        if len(irs) != len(expected_ports):
            raise ValueError('post-transpose partial original metadata')
        for p, ir in zip(expected_ports, irs, strict=True):
            if not _same_typed(post._port(index, p.endpoint.ref, ir), p):
                raise ValueError('post-transpose original paired metadata mismatch')
    return routes.Step(tuple(node), kind, tuple(ports), (derived,), scope.source_writer,
        tuple(ranks), j, gather_axis=a, split_axis=b,
        peers=tuple(zip(ranks, scope.input_tids))), coverage


def _read(source, label, step, order):
    if step.op == 'AllToAllPrim':
        proof, row = primitive._read(source, label, step, order)
        name = f'postTransposeRead_{label}_{step.outputs[0].endpoint.tid}'
        proof = [line.replace(row['theorem'], name) for line in proof]
        row['theorem'] = name
    else:
        nodes = source.nodes()
        i, node = _one(((i, n) for i, n in enumerate(nodes) if tuple(n) == step.node),
            'post-transpose original read writer missing/ambiguous')
        for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
            if not _same_typed([(tuple(source.source_tensor(t)), t.tid) for t in getattr(source, method)(node)],
                    [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
                raise ValueError('post-transpose read original ordered fullrefs mismatch')
        if str(source.node_opname(node)).split('.')[-1] != step.op:
            raise ValueError('post-transpose read original opcode mismatch')
        k = order['execution_to_source'].index(i)
        ins = [p.endpoint.tid for p in step.inputs]; out = step.outputs[0].endpoint.tid
        for source_index in order['execution_to_source'][k:]:
            if set(ins) & {t.tid for t in source.node_outputs(nodes[source_index])}:
                raise ValueError('post-transpose operand is written by selected node or suffix')
        name, req = f'postTransposeRead_{label}_{out}', f'{label}InputRequests'
        common = [f'{label}Graph {label}Scope {label}Peers {label}Graph.nodes',
            f'    {req} ({req}.take {k}) ({req}.drop {k+1}) {label}Node_{i}']
        if step.op == 'FW_transpose':
            params, status = _ordinary(source, node, c._get_node_params)
            if status is not None or not _same_typed(params, [2, 3]) or len(ins) != 1:
                raise ValueError('post-transpose read original axes mismatch')
            value = f'transposeAxes 2 3 (t {ins[0]})'
            application = 'SourceLayoutRead.transposeAxes_value_of_split'
            args = f'{node.rank} {ins[0]} {out} 2 3'
            obligation = f'∀ row ∈ {req}.drop {k}, {ins[0]} ∉ row.1.outs'
        elif step.op == 'AllGatherPrim':
            if step.peers != tuple(zip(step.ranks, ins)) or step.gather_axis != 2:
                raise ValueError('post-transpose AllGather original peers/axis mismatch')
            value = f'allGatherPrimDimN 2 {len(step.ranks)} {step.local_index} (({ins} : List Tid).map t)'
            application = 'SourceAllGatherRead.allGather_value_of_split'
            args = f'{node.rank} {list(step.ranks)} {ins} {out} 2'
            obligation = f'∀ tid ∈ ({ins} : List Tid), ∀ row ∈ {req}.drop {k}, tid ∉ row.1.outs'
        else:
            raise ValueError('post-transpose unsupported read')
        proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
            f'    t {out} = {value} := by', f'  apply {application} {common[0]}', common[1],
            f'    {args} s t rfl ?_ rfl ?_ h', '  · calc',
            f'      {req} = {req}.take {k} ++ {req}.drop {k} := (List.take_append_drop {k} {req}).symm',
            '      _ = _ := rfl', f'  · change {obligation}', '    decide', f'#print axioms {name}']
        row = dict(theorem=name, world=label, op=step.op, node=list(step.node),
            source_index=i, execution_index=k, input_tids=ins, output_tid=out,
            input_refs=[list(p.endpoint.ref) for p in step.inputs], source_step=asdict(step))
    row.update(output_refs=[list(p.endpoint.ref) for p in step.outputs],
        params=[2, 3] if step.op == 'FW_transpose' else ([3, 1] if step.op == 'AllToAllPrim' else [2]),
        request='global' if step.op == 'FW_transpose' else 'group',
        ranks=list(step.ranks), local_index=step.local_index, source_writer=step.source_writer,
        source_kwargs=dict(source.node_kwargs(next(n for n in source.nodes() if tuple(n) == step.node))),
        input_shapes=[list(p.endpoint.shape) for p in step.inputs],
        output_shape=list(step.outputs[0].endpoint.shape),
        operand_nonwrite_source_indices=order['execution_to_source'][row['execution_index']:])
    return proof, row


def _unit(prior, global_, global_step, ports, steps, names):
    transpose._contract(prior, global_, ports)
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    u = prior['unit']; kind = steps[0].op
    _, S, H, C = ports[0].endpoint.shape
    gy = global_step.outputs[0] if global_step else global_
    gshape = list(gy.endpoint.shape)
    lshape = list(steps[0].outputs[0].endpoint.shape)
    axis = {'AllToAllPrim': 1, 'FW_transpose': 2, 'AllGatherPrim': None}[kind]
    if prior['gather_axis'] != (2 if kind == 'AllGatherPrim' else 3):
        raise ValueError('post-transpose unsupported predecessor gather family')
    if kind == 'AllToAllPrim':
        S, rem = divmod(S, T)
        if rem or S <= 0:
            raise ValueError('post-transpose nondivisible actual input axis1')
    name = f'postTransposeUnitFacts_{gy.endpoint.tid}_{u}_slot{prior["slot"]}'
    row = dict(theorem=name, facts_theorem=name, predecessor=prior['facts_theorem'],
        unit=u, slot=prior['slot'], ranks=prior['ranks'], positions=prior['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C),
        family=kind, layout='replicated_within_dp' if axis is None else 'sharded',
        input_gather_axis=prior['gather_axis'], gather_axis=axis,
        global_shape=gshape, local_shape=lshape, input_shape=list(ports[0].endpoint.shape),
        sm_output_tid=gy.endpoint.tid, sm_output_ref=list(gy.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        input_refs=[list(p.endpoint.ref) for p in ports],
        source_step=asdict(global_step) if global_step else prior['source_step'],
        local_steps=[asdict(s) for s in steps])
    if axis is not None:
        transpose._contract(row, gy, [s.outputs[0] for s in steps])
    else:
        full = (B, *gshape[1:])
        for s in steps:
            y = s.outputs[0]
            if (y.parent_name != gy.parent_name or y.parent_shape != full
                    or y.bounds != tuple((0, d) for d in full)
                    or y.endpoint.shape != full or y.value_part != gy.value_part):
                raise ValueError('post-transpose replicated output full DP contract mismatch')
    xs = _list(f'q {p.endpoint.tid}' for p in ports)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in steps)
    g = gy.endpoint.tid
    chunk = f'chunkPrimDimN 0 {D} {u} (t {g})'
    conclusion = (f'{chunk} = allGatherPrimDimN {axis} {T} 0 {ys}' if axis is not None
        else f'∀ y ∈ {ys}, y = {chunk}')
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {g}).shape = {gshape} ∧', f'    (∀ y ∈ {ys}, y.shape = {lshape}) ∧',
        f'    {conclusion} := by', f'  have predecessor := {prior["facts_theorem"]} s p t q hs hp hvalues']
    if kind == 'AllToAllPrim':
        terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 3 1 {xs}' for j in range(T))
        proof += [f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 3 1 {xs}) := by',
            f'    change {ys} = {terms}', '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in steps]),
            f'  exact SourceRank4ReverseExchange.axis3_output_facts {D} {u} {T} {B} {S} {H} {C} (t {g}) {xs} {ys}',
            '    (by decide) (by decide) (by decide) (by decide) (by decide) rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs']
    elif kind == 'FW_transpose':
        pairs = 'List.Forall₂.nil'
        for s in reversed(steps): pairs = f'List.Forall₂.cons ({names[s.node]} p q hp) ({pairs})'
        proof += [f'  have localReads : List.Forall₂ (fun x y => y = transposeAxes 2 3 x) {xs} {ys} :=',
            f'    {pairs}',
            f'  exact TrainVerify.Denote.source_transpose23_inner_unit_output_reconstruct {D} {T} {B} {S} {H} {C} {u}',
            f'    (t {global_.endpoint.tid}) (t {g}) {xs} {ys}',
            '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
            f'    predecessor.1 rfl predecessor.2.1 predecessor.2.2 ({names[global_step.node]} s t hs) localReads']
    else:
        proof += [f'  have outputs : ∀ y ∈ {ys}, y = {chunk} := by', '    intro y hy',
            '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy',
            '    rcases hy with '+' | '.join(['rfl']*T)]
        proof += [f'    · exact ({names[s.node]} p q hp).trans predecessor.2.2.symm' for s in steps]
        proof += ['  refine ⟨predecessor.1, ?_, outputs⟩', '  intro y hy', '  rw [outputs y hy]',
            f'  rw [chunkPrimDimN_shape 0 {D} {u} (t {g}) {gshape} predecessor.1 (by decide)]', '  rfl']
    proof.append(f'#print axioms {name}')
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Replay fresh original transpose authority under the exact caller objects."""
    _, prior = transpose.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed post-transpose original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, seen, names = [], [], [], {}, {}

    def emit(source, label, step, unit, coverage):
        if step.node in seen:
            if label != 'sm' or not _same_typed(seen[step.node], step):
                raise ValueError('post-transpose duplicate/cross-unit source identity')
            return
        proof, row = _read(source, label, step, order[label])
        row.update(unit=unit['unit'], slot=unit['slot'], **coverage)
        proofs.extend(proof); reads.append(row); seen[step.node] = step; names[step.node] = row['theorem']

    for prior_unit in prior['units']:
        first_new_read = len(reads)
        global_ = transpose._output(si, prior_unit['source_step'])
        ports = [transpose._output(pi, d) for d in prior_unit['local_steps']]
        transpose._contract(prior_unit, global_, ports)
        cells = [view._consumer(pi, p) for p in ports]
        kinds = {op(cell) for cell in cells}
        if len(kinds) != 1 or not kinds <= {'AllToAllPrim', 'FW_transpose', 'AllGatherPrim'}:
            raise ValueError('post-transpose unknown/mixed first forward frontier')
        kind = next(iter(kinds)); global_step = None; steps = []
        if kind == 'FW_transpose':
            global_step = _transpose(si, view._consumer(si, global_), global_)
            emit(sm, 'sm', global_step, prior_unit, dict(input_metadata='present', output_metadata='present'))
        for j, cell in enumerate(cells):
            if kind == 'FW_transpose':
                step = _transpose(pi, cell, ports[j]); coverage = dict(input_metadata='present', output_metadata='present')
            else:
                step, coverage = _boundary(pi, cell, ports, prior_unit['ranks'], j)
            emit(pm, 'pm', step, prior_unit, coverage); steps.append(step)
        proof, unit = _unit(prior_unit, global_, global_step, ports, steps, names)
        for read in reads[first_new_read:]:
            if tuple(read['node']) in {s.node for s in steps} or (global_step and tuple(read['node']) == global_step.node):
                read.update(dimensions=unit['dimensions'], layout=unit['layout'], gather_axis=unit['gather_axis'])
        proofs.extend(proof); units.append(unit)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, full assembly, canonical costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-post-transpose-values-emitted-uncompiled', reads=reads, units=units,
        lean_bytes=len(text.encode()), deferred_stage='after-post-transpose: attention/downstream unproved',
        cost_scope='mixed frontier fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
