"""Original BW_contiguous read in the SAME successful run's final Store."""
from trainverify.backward_contiguous_authority import bind
from Verdict.runtime_backward_linear_reads import _writer
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule, graph_to_lean


def render_read(view, cells, snapshot, source_index, order, label):
    if label not in ('sm', 'pm'):
        raise ValueError('bw-contiguous invalid world')
    contract = bind(cells, source_index)
    cell = cells[source_index]; nodes = view.nodes()
    if (not _same_typed([tuple(n) for n in nodes], [tuple(c.node) for c in cells])
            or cell.node.wtype != {'sm': 's', 'pm': 'p'}[label]):
        raise ValueError('bw-contiguous original node inventory/owner mismatch')
    validated = runtime_schedule.validate(view, order['execution_to_source'])
    if not _same_typed(order.get('source_to_execution'), validated['source_to_execution']):
        raise ValueError('bw-contiguous execution/source inverse order mismatch')
    for original in (cell, cells[contract['fw_source_index']]):
        node = original.node
        if (str(view.node_opname(node)).split('.')[-1] != original.opname.name
                or not _same_typed(view.node_kwargs(node), original.kwargs)):
            raise ValueError('bw-contiguous original FW/BW opcode/kwargs mismatch')
        if any(node in getattr(view, key, {}) for key in ('collective_scopes', 'chunk_scopes', 'wred_scopes')):
            raise ValueError('bw-contiguous ordinary global source scope required')
        params = graph_to_lean._get_node_params(view, node, num_parts=0)
        if params is not None and not _same_typed(params, []):
            raise ValueError('bw-contiguous original empty lowered params required')
        for side in ('inputs', 'outputs'):
            ts = getattr(view, 'node_' + side)(node)
            irs = getattr(original, '_' + side[:-1] + '_irs')
            if not _same_typed([tuple(view.source_tensor(t)) for t in ts], [tuple(r) for r in getattr(original, side)]):
                raise ValueError('bw-contiguous lowered ordered fullref mismatch')
            if not _same_typed([tuple(view.tensor_shape(t)) for t in ts], [tuple(ir.shape) for ir in irs]):
                raise ValueError('bw-contiguous lowered original shape mismatch')
    bw_writer = _writer(snapshot, cells, source_index)
    fw_writer = _writer(snapshot, cells, contract['fw_source_index'])
    ids = [t.tid for t in view.node_inputs(cell.node)]
    outs = [t.tid for t in view.node_outputs(cell.node)]
    seq = order['execution_to_source']; k = seq.index(source_index)
    if any(set(ids + outs) & {t.tid for t in view.node_outputs(nodes[j])} for j in seq[k+1:]):
        raise ValueError('bw-contiguous operand/output overwritten in complete execution suffix')
    if set(ids) & set(outs):
        raise ValueError('bw-contiguous selected node overwrites operand')
    requests = f'{label}InputRequests'
    name = f'backwardContiguousRead_{label}_{source_index}_dx'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
             f'    t {outs[0]} = t {ids[0]} := by',
             f'  apply SourceBWContiguousRead.bw_contiguous_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
             f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{source_index}',
             f'    {cell.rank} ' + ' '.join(map(str, [*ids, *outs])) + ' s t rfl ?_ rfl ?_ ?_ h',
             '  · calc', f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
             '      _ = _ := rfl']
    for tid in ids:
        proof += [f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs', '    decide']
    proof += [f'#print axioms {name}']
    return '\n'.join(proof) + '\n', dict(world=label, source_index=source_index, execution_index=k,
        theorems=[name], input_tids=ids, output_tids=outs, params=[], request="global",
        input_refs=contract['inputs'], output_refs=contract['outputs'], source_contract=contract,
        bw_writer=bw_writer, fw_writer=fw_writer, operand_nonwrite_source_indices=seq[k:],
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
