"""Original residual Add.right -> original AG -> attention output BW_linear.

Only same-final-Store source equations are composed. Add.left is retained and
local dX is handed off at the first BW_view, without rendering that consumer.
Private helpers take accepted upstream RHSs; only render obtains those RHSs
from their actual renderer. Caller DTOs are not public proof authority.
"""
from Verdict import graph_to_lean as compiler, runtime_schedule
from Verdict import runtime_backward_residual_join_consumers as residual_join_consumers
from Verdict import runtime_backward_fc1_consumers as fc1
from Verdict import runtime_backward_collective_reads as collective
from Verdict import runtime_backward_linear_reads as linear
from Verdict import runtime_backward_add_reads as add
from Verdict.runtime_lineage import _same_typed

_FLAGS = ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')


def _require(ok, reason):
    if not ok:
        raise ValueError('bw-attention-projection ' + reason)


def _one(rows, reason):
    rows = list(rows)
    _require(len(rows) == 1, reason)
    return rows[0]


def _branch(read, port, expression, theorem, kind):
    return residual_join_consumers._branch(read, port, expression, theorem, kind)


def _gather(world, index, prior):
    """Fresh original AG and all ordered Add.right peers, never copied GELU dims."""
    view, cells, snapshot, order, label = world
    source, read = collective.render_read(view, cells, snapshot, index, order, label,
                                          add.render_read, output_port=1)
    scope = view.collective_scopes[cells[index].node]
    _require(label == 'pm' and read['opname'] == 'AllGatherPrim'
             and _same_typed(read['source_index'], index)
             and _same_typed(read['params'], list(scope.params)) and len(read['params']) == 1
             and _same_typed(read['ranks'], list(scope.ranks))
             and _same_typed(read['local_index'], scope.local_index)
             and _same_typed(read['output_port'], 1)
             and _same_typed(read['input_refs'], [list(view.source_tensor(t)) for t in view.node_inputs(cells[index].node)])
             and _same_typed(read['input_tids'], [t.tid for t in view.node_inputs(cells[index].node)])
             and _same_typed(read['output_ref'], list(cells[index].outputs[0]))
             and _same_typed(read['output_tid'], view.node_outputs(cells[index].node)[0].tid)
             and _same_typed([p['output_refs'][1] for p in read['predecessors']], read['input_refs']),
             'original gather binding mismatch')
    contributions = []
    for peer in read['predecessors']:
        original = _one((p for p in prior if p['world'] == label
                         and _same_typed(p['add_read']['source_index'], peer['source_index'])),
                        'complete selected-stage Add peer required')
        _require(_same_typed(original['add_read'], peer), 'fresh original Add peer mismatch')
        _require(cells[peer['source_index']].mb == cells[index].mb
                 and peer['execution_index'] < read['execution_index'], 'original peer order/microbatch mismatch')
        contributions.append(_branch(peer, 1, original['add_expressions'][1],
                                     original['add_theorems'][1], 'add'))
    expression = (f'allGatherPrimDimN {read["params"][0]} {len(read["ranks"])} {read["local_index"]}'
                  + ' [' + ', '.join('(' + b['expression'] + ')' for b in contributions) + ']')
    name = read['theorems'][0] + '_contributions'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
             f'    t {read["output_tid"]} = {expression} := by',
             f'  rw [{read["theorems"][0]} s t h]',
             '  simp only [List.map_cons, List.map_nil]',
             '  rw [' + ', '.join(b['theorem'] + ' s t h' for b in contributions) + ']',
             f'#print axioms {name}']
    branch = _branch(read, 0, expression, name, 'collective')
    branch['contributions'] = contributions
    return '\n'.join(proof) + '\n', source, branch


def _linear(world, index, gradient, prior):
    """Bind both original linear outputs and retain the accepted left branch."""
    view, cells, snapshot, order, label = world
    source, read = linear.render_read(view, cells, snapshot, index, order, label)
    validated = runtime_schedule.validate(view, order['execution_to_source'])
    _require(_same_typed(order['source_to_execution'], validated['source_to_execution']),
             'source/execution inverse mismatch')
    ai = prior['add_read']['source_index']
    _, ar = add.render_read(view, cells, snapshot, ai, order, label)
    _require(prior['world'] == label and _same_typed(prior['add_read'], ar), 'fresh local Add mismatch')
    j, port = gradient['source_index'], gradient['port']
    _require(type(j) is int and 0 <= j < len(cells) and type(port) is int
             and 0 <= port < len(cells[j].outputs), 'typed original gradient port required')
    scalar = 'output_ref' in gradient['read']
    _require(_same_typed(j, gradient['read']['source_index'])
             and _same_typed(gradient['output_ref'], list(cells[j].outputs[port]))
             and _same_typed(gradient['output_ref'], list(view.source_tensor(view.node_outputs(cells[j].node)[port])))
             and _same_typed(gradient['output_ref'], read['input_refs'][0])
             and _same_typed(gradient['output_tid'], view.node_outputs(cells[j].node)[port].tid)
             and _same_typed(gradient['output_tid'], read['input_tids'][0])
             and _same_typed(gradient['output_ref'], gradient['read']['output_ref'] if scalar else gradient['read']['output_refs'][port])
             and _same_typed(gradient['output_tid'], gradient['read']['output_tid'] if scalar else gradient['read']['output_tids'][port])
             and (not scalar or port == 0)
             and cells[j].rank == cells[index].rank == cells[ai].rank
             and cells[j].mb == cells[index].mb == cells[ai].mb
             and _same_typed(gradient['read']['execution_index'], order['source_to_execution'][j])
             and gradient['read']['execution_index'] < read['execution_index'],
             'original gradient endpoint/order mismatch')
    if label == 'sm':
        expected = _branch(ar, 1, prior['add_expressions'][1], prior['add_theorems'][1], 'add')
        _require(_same_typed(gradient, expected), 'original direct Add.right required')
    else:
        gi, _ = fc1._consumer(cells, cells[ai], 1, 'AllGatherPrim')
        _require(j == gi and port == 0 and gradient['kind'] == 'collective', 'original gathered Add.right required')
        # Recheck this boundary on narrow calls too: an accepted DTO must not
        # hide a changed ctx, ordered group, saved tensor or producer port.
        _, checked = collective.render_read(view, cells, snapshot, gi, order, label,
                                             add.render_read, output_port=1)
        _require(_same_typed(gradient['read'], checked), 'fresh gathered Add.right mismatch')
    li, _ = fc1._consumer(cells, cells[j], port, 'BW_linear')
    _require(_same_typed(li, index), 'unique original projection consumer required')
    proofs, expressions, names = [], [], []
    base = f'(bw_linear ({gradient["expression"]}) (t {read["input_tids"][1]}) (t {read["input_tids"][2]}))'
    for p, role in enumerate(('dx', 'dw')):
        name = f'backwardAttentionProjection_{label}_{index}_{role}'
        rhs = base + f'.{p+1}'
        proofs += fc1._equation(name, label, read['output_tids'][p], rhs, [read['theorems'][p], gradient['theorem']])
        expressions.append(rhs); names.append(name)
    vi, vc = fc1._consumer(cells, cells[index], 0, 'BW_view')
    _require(_same_typed(list(vc.inputs[0]), read['output_refs'][0])
             and _same_typed(list(view.source_tensor(view.node_inputs(vc.node)[0])), read['output_refs'][0])
             and cells[index].mb == vc.mb
             and read['execution_index'] < order['source_to_execution'][vi], 'original first view boundary mismatch')
    frontier = dict(source_index=vi, execution_index=order['source_to_execution'][vi],
                    input_ref=read['output_refs'][0], input_tid=read['output_tids'][0],
                    predecessor=_branch(read, 0, expressions[0], names[0], 'linear'))
    retained = _branch(ar, 0, prior['add_expressions'][0], prior['add_theorems'][0], 'retained_add')
    return '\n'.join(proofs) + '\n', source, dict(world=label, prior=prior, gradient=gradient,
        linear=read, linear_expressions=expressions, linear_theorems=names,
        retained=retained, view_frontier=frontier)


def render(worlds, capture, rank_code):
    # Exactly one actual upstream render. Its original theorem names, not
    # self-certified direct-RHS metadata, are used in every composed proof.
    _, prior = residual_join_consumers.render(worlds, capture, rank_code)
    fresh = compiler._load_chunk_source(capture, rank_code)
    pm = _one((w for w in worlds if w[-1] == 'pm'), 'unique PM world required')
    compiler.attach_collective_scopes(pm[0], fresh)
    bound = [(v, c, fresh if label == 'pm' else s, o, label) for v, c, s, o, label in worlds]
    proofs, sources, linear_sources, collective_reads, pending, rows = [], [], [], [], [], []
    # Complete peer Add wave already exists; emit every AG RHS before linears.
    for previous in prior['reads']:
        world = _one((w for w in bound if w[-1] == previous['world']), 'unique original world required')
        view, cells, snapshot, order, label = world
        ar = previous['add_read']
        if label == 'pm':
            gi, _ = fc1._consumer(cells, cells[ar['source_index']], 1, 'AllGatherPrim')
            text, source, gradient = _gather(world, gi, prior['reads'])
            proofs.append(text); sources.append(source); collective_reads.append(gradient['read'])
        else:
            _, checked = add.render_read(view, cells, snapshot, ar['source_index'], order, label)
            _require(_same_typed(checked, ar), 'fresh selected Add mismatch')
            gradient = _branch(ar, 1, previous['add_expressions'][1], previous['add_theorems'][1], 'add')
        li, _ = fc1._consumer(cells, cells[gradient['source_index']], gradient['port'], 'BW_linear')
        pending.append((world, li, gradient, previous))
    for args in pending:
        text, source, row = _linear(*args)
        proofs.append(text); linear_sources.append(source); rows.append(row)
    return ''.join(proofs), dict(reads=rows, collective_reads=collective_reads,
        collective_source=''.join(sources), linear_source=''.join(linear_sources),
        **{flag: False for flag in _FLAGS})
