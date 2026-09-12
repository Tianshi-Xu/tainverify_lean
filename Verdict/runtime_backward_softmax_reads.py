"""Original BW_softmax read fragment, with caller-owned successful Store/run."""
from trainverify.backward_softmax_authority import bind, _fail
from Verdict.runtime_backward_matmul_reads import _writer
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule


def render_read(view, cells, snapshot, source_index, order, label):
    """Fresh raw source binding; never accepts a caller contract DTO."""
    from Verdict import graph_to_lean
    if label not in ('sm', 'pm'):
        _fail('invalid world label')
    contract = bind(cells, source_index)
    nodes = view.nodes(); cell = cells[source_index]
    if (not _same_typed([tuple(n) for n in nodes], [tuple(c.node) for c in cells])
            or cell.node.wtype != {'sm': 's', 'pm': 'p'}[label]):
        _fail('original source node inventory/owner mismatch')
    runtime_schedule.validate(view, order['execution_to_source'])
    schedule = order['execution_to_source']
    if not _same_typed(order.get('source_to_execution'), [schedule.index(i) for i in range(len(cells))]):
        _fail('inverse execution order mismatch')
    node = nodes[source_index]
    source_params = {}
    for original in (cell, cells[contract['fw_source_index']]):
        original_node = original.node
        if (str(view.node_opname(original_node)).split('.')[-1] != original.opname.name
                or not _same_typed(view.node_kwargs(original_node), original.kwargs)):
            _fail('original forward/backward source opcode/kwargs mismatch')
        if any(original_node in getattr(view, key, {}) for key in ('collective_scopes', 'chunk_scopes', 'wred_scopes')):
            _fail('ordinary global scope required')
        params = graph_to_lean._get_node_params(view, original_node, num_parts=0)
        # Current lowering has no softmax params encoding: do not normalize dim
        # or manufacture shape params. Domain authority lives in the raw kwargs.
        if params is not None and not _same_typed(params, []):
            _fail('original empty lowered params required')
        source_params[original_node] = [] if params is None else params
        for side, irs in (('inputs', original._input_irs), ('outputs', original._output_irs)):
            tensors = getattr(view, 'node_' + side)(original_node)
            if not _same_typed([tuple(view.source_tensor(t)) for t in tensors],
                               [tuple(t) for t in getattr(original, side)]):
                _fail('lowered ordered fullref identity mismatch')
            if not _same_typed([tuple(view.tensor_shape(t)) for t in tensors], [tuple(ir.shape) for ir in irs]):
                _fail('lowered original shape mismatch')
    params = source_params[node]
    ids = [t.tid for t in view.node_inputs(node)]
    dx, = [t.tid for t in view.node_outputs(node)]
    k = schedule.index(source_index)
    for i in schedule[k:]:
        if set(ids) & {t.tid for t in view.node_outputs(nodes[i])}:
            _fail('operand written by selected node or execution suffix')
    for i in schedule[k+1:]:
        if dx in {t.tid for t in view.node_outputs(nodes[i])}:
            _fail('output overwritten in execution suffix')
    requests = f'{label}InputRequests'
    name = f'backwardSoftmaxRead_{label}_{source_index}_dx'
    proofs = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {dx} = bw_softmax (t {ids[0]}) (t {ids[1]}) := by',
        f'  apply SourceBWSoftmaxRead.bw_softmax_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{source_index}',
        f'    {node.rank} {ids[0]} {ids[1]} {dx} {params} s t rfl ?_ (by decide) ?_ ?_ h',
        '  · calc',
        f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
        '      _ = _ := rfl']
    for tid in ids:
        proofs.extend([f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs', '    decide'])
    proofs.append(f'#print axioms {name}')
    return '\n'.join(proofs)+'\n', dict(theorems=[name], world=label,
        source_index=source_index, execution_index=k, node=list(node),
        input_tids=ids, output_tid=dx, input_refs=contract['inputs'], output_ref=contract['outputs'][0],
        output_tids=[dx], output_refs=contract['outputs'],
        source_contract=contract, bw_writer=_writer(snapshot, cells, source_index),
        fw_writer=_writer(snapshot, cells, contract['fw_source_index']), params=params, request='global',
        operand_nonwrite_source_indices=schedule[k:], proof_admissible=False,
        kernel_value_proved=False, public_complete=False, torch_refinement=False)
