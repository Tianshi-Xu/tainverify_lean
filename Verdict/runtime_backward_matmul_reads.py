"""Original BW_matmul read fragment for the shared runtime proof DAG.

No canonical entry is changed. Caller owns graph definitions, input requests,
scope and the successful run. The fragment derives dX/dY in that final Store;
it deliberately does not claim cross-model gradients or runtime refinement.
"""
from trainverify.backward_matmul_authority import bind
from trainverify.runtime_source_authority import writer_export_id
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule


def _writer(snapshot, cells, index):
    cell=cells[index]
    rows=[w for w in snapshot['writers'] if _same_typed(
        (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
         w['ref']['source_cid'], w['source_irname']), tuple(cell.node))]
    if len(rows)!=1:
        raise ValueError('bw-matmul original writer missing/ambiguous')
    row,=rows
    key=tuple(cell.node[:4])
    occurrence=sum(tuple(c.node[:4])==key and c.ir is not None for c in cells[:index])
    expected=dict(world=cell.node.wtype,runtime_rank=cell.rank,microbatch=cell.mb,
                  source_cid=cell.node.cid,call_instance=occurrence,op=cell.opname.name,origin='nnscaler')
    if not _same_typed(row['ref'],expected) or row['export_id']!=writer_export_id(expected):
        raise ValueError('bw-matmul original writer/export/call identity mismatch')
    fields=('world','runtime_rank','microbatch','source_tid','version')
    for side in ('inputs','outputs'):
        if not _same_typed(row[side],[dict(zip(fields,r,strict=True)) for r in getattr(cell,side)]):
            raise ValueError('bw-matmul writer ordered fullref identity mismatch')
    return row['export_id']


def render_read(view, cells, snapshot, source_index, order, label):
    """Fresh raw binding + source/export/lowered join; no caller DTO authority."""
    if label not in ('sm','pm'):
        raise ValueError('bw-matmul invalid world label')
    contract=bind(cells,source_index)
    nodes=view.nodes(); cell=cells[source_index]
    if (not _same_typed([tuple(n) for n in nodes],[tuple(c.node) for c in cells])
            or cell.node.wtype != {'sm':'s','pm':'p'}[label]):
        raise ValueError('bw-matmul original source node inventory/owner mismatch')
    runtime_schedule.validate(view,order['execution_to_source'])
    schedule = order['execution_to_source']
    if not _same_typed(order.get('source_to_execution'), [schedule.index(i) for i in range(len(cells))]):
        raise ValueError('bw-matmul inverse execution order mismatch')
    node=nodes[source_index]
    from Verdict import graph_to_lean
    for original in (cell,cells[contract['fw_source_index']]):
        original_node=original.node
        if (str(view.node_opname(original_node)).split('.')[-1]!=original.opname.name
                or not _same_typed(view.node_kwargs(original_node),original.kwargs)):
            raise ValueError('bw-matmul original forward/backward source opcode/kwargs mismatch')
        if any(original_node in getattr(view,key,{}) for key in ('collective_scopes','chunk_scopes','wred_scopes')):
            raise ValueError('bw-matmul ordinary global scope required')
        params=graph_to_lean._get_node_params(view,original_node,num_parts=0)
        if params is not None and not _same_typed(params,[]):
            raise ValueError('bw-matmul original empty params required')
        for side,irs in [('inputs',original._input_irs),('outputs',original._output_irs)]:
            tensors=getattr(view,'node_'+side)(original_node)
            if not _same_typed([tuple(view.source_tensor(t)) for t in tensors],
                               [tuple(t) for t in getattr(original,side)]):
                raise ValueError('bw-matmul lowered ordered fullref identity mismatch')
            if not _same_typed([tuple(view.tensor_shape(t)) for t in tensors],[tuple(ir.shape) for ir in irs]):
                raise ValueError('bw-matmul lowered original shape mismatch')
    inputs=view.node_inputs(node); outputs=view.node_outputs(node)
    bw_writer=_writer(snapshot,cells,source_index)
    fw_writer=_writer(snapshot,cells,contract['fw_source_index'])
    schedule=order['execution_to_source']; k=schedule.index(source_index)
    ids=[t.tid for t in inputs]; dx,dy=[t.tid for t in outputs]
    for i in schedule[k:]:
        if set(ids)&{t.tid for t in view.node_outputs(nodes[i])}:
            raise ValueError('bw-matmul operand written by selected node or execution suffix')
    if dx == dy:
        raise ValueError('bw-matmul distinct lowered output ports required')
    for i in schedule[k+1:]:
        if {dx, dy} & {t.tid for t in view.node_outputs(nodes[i])}:
            raise ValueError('bw-matmul output overwritten in execution suffix')
    requests=f'{label}InputRequests'; proofs=[]; names=[]
    for role,out,projection in [('dx',dx,1),('dy',dy,2)]:
        name=f'backwardMatmulRead_{label}_{source_index}_{role}'; names.append(name)
        proofs.extend([f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
            f'    t {out} = (bw_matmul (t {ids[0]}) (t {ids[1]}) (t {ids[2]})).{projection} := by',
            f'  apply SourceBWMatmulRead.bw_matmul_{role}_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
            f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{source_index}',
            f'    {node.rank} {ids[0]} {ids[1]} {ids[2]} {dx} {dy} s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h',
            '  · calc',
            f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
            '      _ = _ := rfl'])
        for tid in ids:
            proofs.extend([f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs','    decide'])
        proofs.append(f'#print axioms {name}')
    return '\n'.join(proofs)+'\n',dict(theorems=names,world=label,source_index=source_index,execution_index=k,
        node=list(node),input_tids=ids,output_tids=[dx,dy],input_refs=contract['inputs'],output_refs=contract['outputs'],
        source_contract=contract,bw_writer=bw_writer,fw_writer=fw_writer,params=[],request='global',
        operand_nonwrite_source_indices=schedule[k:],
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
