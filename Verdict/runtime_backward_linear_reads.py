"""Original BW_linear read fragment for the shared runtime proof DAG.

No canonical entry is changed. Caller owns graph definitions, input requests,
scope and the successful run. The fragment derives dX/dW in that final Store;
it deliberately does not claim cross-model gradients or runtime refinement.
"""
from trainverify.backward_linear_authority import bind
from trainverify.runtime_source_authority import writer_export_id
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule


def _writer(snapshot, cells, index):
    cell=cells[index]
    rows=[w for w in snapshot['writers'] if _same_typed(
        (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
         w['ref']['source_cid'], w['source_irname']), tuple(cell.node))]
    if len(rows)!=1:
        raise ValueError('bw-linear original writer missing/ambiguous')
    row,=rows
    key=tuple(cell.node[:4])
    occurrence=sum(tuple(c.node[:4])==key and c.ir is not None for c in cells[:index])
    expected=dict(world=cell.node.wtype,runtime_rank=cell.rank,microbatch=cell.mb,
                  source_cid=cell.node.cid,call_instance=occurrence,op=cell.opname.name,origin='nnscaler')
    if not _same_typed(row['ref'],expected) or row['export_id']!=writer_export_id(expected):
        raise ValueError('bw-linear original writer/export/call identity mismatch')
    fields=('world','runtime_rank','microbatch','source_tid','version')
    for side in ('inputs','outputs'):
        if not _same_typed(row[side],[dict(zip(fields,r,strict=True)) for r in getattr(cell,side)]):
            raise ValueError('bw-linear writer ordered fullref identity mismatch')
    return row['export_id']


def render_read(view, cells, snapshot, source_index, order, label):
    """Fresh raw binding + source/export/lowered join; no caller DTO authority."""
    if label not in ('sm','pm'):
        raise ValueError('bw-linear invalid world label')
    contract=bind(cells,source_index)
    nodes=view.nodes(); cell=cells[source_index]
    if (not _same_typed([tuple(n) for n in nodes],[tuple(c.node) for c in cells])
            or cell.node.wtype != {'sm':'s','pm':'p'}[label]):
        raise ValueError('bw-linear original source node inventory/owner mismatch')
    runtime_schedule.validate(view,order['execution_to_source'])
    node=nodes[source_index]
    if str(view.node_opname(node)).split('.')[-1]!='BW_linear' or not _same_typed(view.node_kwargs(node),cell.kwargs):
        raise ValueError('bw-linear original source opcode/kwargs mismatch')
    if any(node in getattr(view,key,{}) for key in ('collective_scopes','chunk_scopes','wred_scopes')):
        raise ValueError('bw-linear ordinary global scope required')
    from Verdict import graph_to_lean
    params=graph_to_lean._get_node_params(view,node,num_parts=0)
    if params is not None and not _same_typed(params,[]):
        raise ValueError('bw-linear original empty params required')
    inputs=view.node_inputs(node); outputs=view.node_outputs(node)
    for side,tensors,irs in [('inputs',inputs,cell._input_irs),('outputs',outputs,cell._output_irs)]:
        if not _same_typed([tuple(view.source_tensor(t)) for t in tensors],
                           [tuple(t) for t in getattr(cell,side)]):
            raise ValueError('bw-linear lowered ordered fullref identity mismatch')
        if not _same_typed([tuple(view.tensor_shape(t)) for t in tensors],[tuple(ir.shape) for ir in irs]):
            raise ValueError('bw-linear lowered original shape mismatch')
    bw_writer=_writer(snapshot,cells,source_index)
    fw_writer=_writer(snapshot,cells,contract['fw_source_index'])
    schedule=order['execution_to_source']; k=schedule.index(source_index)
    ids=[t.tid for t in inputs]; dx,dw=[t.tid for t in outputs]
    for i in schedule[k:]:
        if set(ids)&{t.tid for t in view.node_outputs(nodes[i])}:
            raise ValueError('bw-linear operand written by selected node or execution suffix')
    requests=f'{label}InputRequests'; proofs=[]; names=[]
    for role,out,projection in [('dx',dx,1),('dw',dw,2)]:
        name=f'backwardLinearRead_{label}_{source_index}_{role}'; names.append(name)
        proofs.extend([f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
            f'    t {out} = (bw_linear (t {ids[0]}) (t {ids[1]}) (t {ids[2]})).{projection} := by',
            f'  apply SourceBWLinearRead.bw_linear_{role}_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
            f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{source_index}',
            f'    {node.rank} {ids[0]} {ids[1]} {ids[2]} {dx} {dw} s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h',
            '  · calc',
            f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
            '      _ = _ := rfl'])
        for tid in ids:
            proofs.extend([f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs','    decide'])
        proofs.append(f'#print axioms {name}')
    return '\n'.join(proofs)+'\n',dict(theorems=names,world=label,source_index=source_index,execution_index=k,
        node=list(node),input_tids=ids,output_tids=[dx,dw],input_refs=contract['inputs'],output_refs=contract['outputs'],
        source_contract=contract,bw_writer=bw_writer,fw_writer=fw_writer,params=[],request='global',
        operand_nonwrite_source_indices=schedule[k:],
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
