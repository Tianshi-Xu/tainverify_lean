"""Original BW_view read in the SAME successful run's final Store."""
from trainverify.backward_view_authority import bind
from Verdict.runtime_backward_linear_reads import _writer
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule, graph_to_lean


def render_read(view, cells, snapshot, source_index, order, label):
    if label not in ('sm', 'pm'):
        raise ValueError('bw-view invalid world')
    contract = bind(cells, source_index)
    cell = cells[source_index]; nodes = view.nodes()
    if (not _same_typed([tuple(n) for n in nodes], [tuple(c.node) for c in cells])
            or cell.node.wtype != {'sm': 's', 'pm': 'p'}[label]):
        raise ValueError('bw-view original node inventory/owner mismatch')
    validated = runtime_schedule.validate(view, order['execution_to_source'])
    if not _same_typed(order.get('source_to_execution'), validated['source_to_execution']):
        raise ValueError('bw-view execution/source inverse order mismatch')
    for original in (cell, cells[contract['fw_source_index']]):
        node = original.node
        if (str(view.node_opname(node)).split('.')[-1] != original.opname.name
                or not _same_typed(view.node_kwargs(node), original.kwargs)):
            raise ValueError('bw-view original FW/BW opcode/kwargs mismatch')
        if any(node in getattr(view, key, {}) for key in ('collective_scopes', 'chunk_scopes', 'wred_scopes')):
            raise ValueError('bw-view ordinary global source scope required')
        params = graph_to_lean._get_node_params(view, node, num_parts=0)
        expected = contract['target_shape'] if original is cell else contract['forward_shape']
        if not _same_typed(params, expected):
            raise ValueError('bw-view original inverse/FW lowered shape params mismatch')
        for side in ('inputs', 'outputs'):
            ts = getattr(view, 'node_' + side)(node)
            irs = getattr(original, '_' + side[:-1] + '_irs')
            if not _same_typed([tuple(view.source_tensor(t)) for t in ts], [tuple(r) for r in getattr(original, side)]):
                raise ValueError('bw-view lowered ordered fullref mismatch')
            if not _same_typed([tuple(view.tensor_shape(t)) for t in ts], [tuple(ir.shape) for ir in irs]):
                raise ValueError('bw-view lowered original shape mismatch')
    bw_writer = _writer(snapshot, cells, source_index)
    fw_writer = _writer(snapshot, cells, contract['fw_source_index'])
    ids = [t.tid for t in view.node_inputs(cell.node)]
    outs = [t.tid for t in view.node_outputs(cell.node)]
    seq = order['execution_to_source']; k = seq.index(source_index)
    if any(set(ids + outs) & {t.tid for t in view.node_outputs(nodes[j])} for j in seq[k+1:]):
        raise ValueError('bw-view operand/output overwritten in complete execution suffix')
    if set(ids) & set(outs):
        raise ValueError('bw-view selected node overwrites operand')
    target = contract['target_shape']
    requests = f'{label}InputRequests'
    name = f'backwardViewRead_{label}_{source_index}_dx'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
             f'    t {outs[0]} = fw_view {target} (t {ids[0]}) := by',
             f'  apply SourceBWViewRead.bw_view_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
             f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{source_index}',
             f'    {cell.rank} {target[0]} {target[1:]} ' + ' '.join(map(str, [*ids, *outs])) + ' s t rfl ?_ rfl ?_ ?_ h',
             '  · calc', f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
             '      _ = _ := rfl']
    for tid in ids:
        proof += [f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs', '    decide']
    proof += [f'#print axioms {name}']
    return '\n'.join(proof) + '\n', dict(world=label, source_index=source_index, execution_index=k,
        theorems=[name], input_tids=ids, output_tids=outs, params=target, request="global",
        input_refs=contract['inputs'], output_refs=contract['outputs'], source_contract=contract,
        bw_writer=bw_writer, fw_writer=fw_writer, operand_nonwrite_source_indices=seq[k:],
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)


def render_after_linear(worlds, producers):
    """Continue original linear dX proofs through their actual inverse views.

    RHS metadata comes from the producer's generation step; it is not a value
    assumption. The emitted proof must rewrite the corresponding checked theorem.
    """
    from Verdict import runtime_backward_linear_reads as linear
    from Verdict.runtime_backward_fc1_consumers import _consumer
    proof, source, rows = [], [], []
    for p in producers:
        matches = [w for w in worlds if w[-1] == p['world']]
        if len(matches) != 1:
            raise ValueError('bw-view unique original producer world required')
        view, cells, snapshot, order, label = matches[0]
        lr = p['linear']
        _, fresh = linear.render_read(view, cells, snapshot, lr['source_index'], order, label)
        if not _same_typed(lr, fresh):
            raise ValueError('bw-view fresh linear producer mismatch')
        i, _ = _consumer(cells, cells[lr['source_index']], 0, 'BW_view')
        text, vr = render_read(view, cells, snapshot, i, order, label)
        if (not _same_typed(vr['input_refs'][0], lr['output_refs'][0])
                or not _same_typed(vr['input_tids'][0], lr['output_tids'][0])
                or not lr['execution_index'] < vr['execution_index']):
            raise ValueError('bw-view original linear dX edge mismatch')
        source.append(text)
        name = f'backwardViewConsumer_{label}_{i}'
        expression = f'fw_view {vr["params"]} ({p["linear_expressions"][0]})'
        proof += [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                  f'    t {vr["output_tids"][0]} = {expression} := by',
                  f'  rw [{vr["theorems"][0]} s t h, {p["linear_theorems"][0]} s t h]',
                  f'#print axioms {name}']
        rows.append(dict(world=label, producer=p, view_read=vr, expression=expression, theorems=[name]))
    return '\n'.join(proof)+'\n', dict(reads=rows, view_source=''.join(source),
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
