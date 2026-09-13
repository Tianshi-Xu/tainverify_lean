"""SAME-final-Store BW_multiref sum reads from original raw source authority.

Caller owns graph/requests/scope/run definitions. No canonical entry is changed.
Helper ABI (pending parent Lean verification): g scope peer nodes requests
before after sourceNode rank inputs out s t hnode hsplit hscope hinputs hrun.
hinputs: forall tid in inputs, forall row in (sourceNode, none)::after,
         tid not in row.1.outs. Node params=[]; no list-length argument.
"""
from trainverify.backward_multiref_authority import bind, _require
from Verdict.runtime_backward_linear_reads import _writer
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule


def render_read(view, cells, snapshot, source_index, order, label):
    """Bind fresh, authenticate translations, render the complete ordered sum."""
    _require(label in ('sm', 'pm'), 'invalid world label')
    contract = bind(cells, source_index)
    cell = cells[source_index]; nodes = view.nodes()
    _require(_same_typed([tuple(n) for n in nodes], [tuple(c.node) for c in cells]) and
             cell.node.wtype == {'sm': 's', 'pm': 'p'}[label], 'source inventory/owner mismatch')
    validated = runtime_schedule.validate(view, order['execution_to_source'])
    _require(_same_typed(order['source_to_execution'], validated['source_to_execution']),
             'inverse execution order mismatch')
    from Verdict import graph_to_lean
    for index in (source_index, contract['fw_source_index']):
        original = cells[index]; node = original.node
        _require(str(view.node_opname(node)).split('.')[-1] == original.opname.name and
                 _same_typed(view.node_kwargs(node), original.kwargs), 'lowered opcode/kwargs mismatch')
        _require(not any(node in getattr(view, key, {}) for key in
                 ('collective_scopes', 'chunk_scopes', 'wred_scopes')), 'ordinary global scope required')
        params = graph_to_lean._get_node_params(view, node, num_parts=0)
        expected = [] if index == source_index else [contract['times']]
        _require(_same_typed([] if params is None else params, expected), 'lowered original params mismatch')
        for side, irs in (('inputs', original._input_irs), ('outputs', original._output_irs)):
            tensors = getattr(view, 'node_' + side)(node)
            _require(_same_typed([tuple(view.source_tensor(t)) for t in tensors],
                     [tuple(r) for r in getattr(original, side)]), 'lowered ordered fullref mismatch')
            _require(_same_typed([tuple(view.tensor_shape(t)) for t in tensors],
                     [tuple(ir.shape) for ir in irs]), 'lowered original shape mismatch')
    # The shared writer join validates world/rank/mb/cid/call/export and every
    # ordered port. Contribution writers remain obligations, not value proofs.
    bw_writer = _writer(snapshot, cells, source_index)
    fw_writer = _writer(snapshot, cells, contract['fw_source_index'])
    contribution_writers = [_writer(snapshot, cells, c['source_index'])
                            for c in contract['contributions']]
    schedule = validated['execution_to_source']; k = validated['source_to_execution'][source_index]
    inputs = [t.tid for t in view.node_inputs(cell.node)]
    out, = [t.tid for t in view.node_outputs(cell.node)]
    for index in schedule[k:]:
        written = {t.tid for t in view.node_outputs(nodes[index])}
        _require(not set(inputs) & written, 'operand written by selected node or execution suffix')
        if index != source_index:
            _require(out not in written, 'output execution suffix overwrite')
    tids = '[' + ', '.join(map(str, inputs)) + ']'
    requests = f'{label}InputRequests'
    name = f'backwardMultirefRead_{label}_{source_index}'
    text = '\n'.join([
        f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = tensorSum ({tids}.map t) := by',
        f'  apply SourceBWMultirefRead.bw_multiref_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{source_index}',
        f'    {cell.rank} {tids} {out} s t rfl ?_ rfl ?_ h',
        '  · calc',
        f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
        '      _ = _ := rfl',
        f'  · change ∀ tid ∈ ({tids} : List Tid), ∀ row ∈ {requests}.drop {k}, tid ∉ row.1.outs',
        '    decide',
        f'#print axioms {name}', ''])
    return text, dict(theorems=[name], world=label, source_index=source_index, execution_index=k,
        node=list(cell.node), input_tids=inputs, output_tids=[out],
        input_refs=contract['inputs'], output_refs=contract['outputs'], source_contract=contract,
        bw_writer=bw_writer, fw_writer=fw_writer, contribution_writers=contribution_writers,
        params=[], request='global', operand_nonwrite_source_indices=schedule[k:],
        output_nonwrite_source_indices=schedule[k+1:], lean_helper_verified=False,
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
