"""Source-authenticated original BW_layernorm three-output read projections."""
from trainverify.backward_layernorm_authority import bind
from Verdict.runtime_backward_linear_reads import _writer
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule,graph_to_lean


def render_read(view,cells,snapshot,source_index,order,label):
    if label not in ('sm','pm'): raise ValueError('bw-layernorm invalid world')
    contract=bind(cells,source_index); cell=cells[source_index]; nodes=view.nodes()
    if (not _same_typed([tuple(n) for n in nodes],[tuple(c.node) for c in cells])
            or cell.node.wtype!={'sm':'s','pm':'p'}[label]):
        raise ValueError('bw-layernorm original node inventory/owner mismatch')
    runtime_schedule.validate(view,order['execution_to_source'])
    for original in (cell,cells[contract['fw_source_index']]):
        node=original.node
        if (str(view.node_opname(node)).split('.')[-1]!=original.opname.name
                or not _same_typed(view.node_kwargs(node),original.kwargs)):
            raise ValueError('bw-layernorm original FW/BW opcode/kwargs mismatch')
        if any(node in getattr(view,key,{}) for key in ('collective_scopes','chunk_scopes','wred_scopes')):
            raise ValueError('bw-layernorm ordinary global source scope required')
        params=graph_to_lean._get_node_params(view,node,num_parts=0)
        if params is not None and not _same_typed(params,[]):
            raise ValueError('bw-layernorm original empty lowered params required')
        for side in ('inputs','outputs'):
            ts=getattr(view,'node_'+side)(node); irs=getattr(original,'_'+side[:-1]+'_irs')
            if not _same_typed([tuple(view.source_tensor(t)) for t in ts],[tuple(r) for r in getattr(original,side)]):
                raise ValueError('bw-layernorm lowered ordered fullref mismatch')
            if not _same_typed([tuple(view.tensor_shape(t)) for t in ts],[tuple(ir.shape) for ir in irs]):
                raise ValueError('bw-layernorm lowered original shape mismatch')
    bw_writer=_writer(snapshot,cells,source_index); fw_writer=_writer(snapshot,cells,contract['fw_source_index'])
    ids=[t.tid for t in view.node_inputs(cell.node)]; outs=[t.tid for t in view.node_outputs(cell.node)]
    seq=order['execution_to_source']; k=seq.index(source_index)
    if len(set(outs))!=3: raise ValueError('bw-layernorm distinct original gradient outputs required')
    if any(set(ids)&{t.tid for t in view.node_outputs(nodes[j])} for j in seq[k:]):
        raise ValueError('bw-layernorm operand overwritten in selected/full execution suffix')
    requests=f'{label}InputRequests'; names=[]; proof=[]
    for role,out,projection in zip(('dx','dgamma','dbeta'),outs,('1','2.1','2.2'),strict=True):
        name=f'backwardLayernormRead_{label}_{source_index}_{role}'; names.append(name)
        proof += [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                  f'    t {out} = (bw_layernorm '+ ' '.join(f'(t {i})' for i in ids)+f').{projection} := by',
                  f'  apply SourceBWLayernormRead.bw_layernorm_{role}_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
                  f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{source_index}',
                  '    '+' '.join(map(str,[cell.rank,*ids,*outs]))+' s t rfl ?_ rfl (by decide) (by decide) (by decide) ?_ ?_ ?_ ?_ h',
                  '  · calc',f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
                  '      _ = _ := rfl']
        for tid in ids: proof += [f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs','    decide']
        proof += [f'#print axioms {name}']
    return '\n'.join(proof)+'\n',dict(world=label,source_index=source_index,execution_index=k,
        theorems=names,input_tids=ids,output_tids=outs,input_refs=contract['inputs'],output_refs=contract['outputs'],
        source_contract=contract,bw_writer=bw_writer,fw_writer=fw_writer,operand_nonwrite_source_indices=seq[k:],
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
