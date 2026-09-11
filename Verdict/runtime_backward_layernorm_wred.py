"""Original affine LayerNorm gradients into parameter-owned SUM reducers.

A replicated affine parameter can reduce across both TP and DP. Preserve each
original (scale_unit, plan_rank) coordinate once, rather than assuming a DP-only
group or rejecting legitimate same-DP TP contributions. No scaling is invented.
"""
from Verdict import graph_to_lean as compiler,runtime_schedule
from Verdict import runtime_backward_layernorm_reads as layernorm
from Verdict.runtime_backward_wred_reads import _reducer
from Verdict.runtime_lineage import _same_typed
from trainverify.runtime_source_authority import writer_export_id


def _one(rows,reason):
    rows=list(rows)
    if len(rows)!=1: raise ValueError('bw-layernorm-wred '+reason)
    return rows[0]


def _read(view,cells,snapshot,order,index,selected,role):
    port={'dgamma':(2,1,1),'dbeta':(3,2,2)}[role]; ip,op,np=port
    _,local=layernorm.render_read(view,cells,snapshot,index,order,'pm')
    bw=cells[index]; reducer=_reducer(cells,bw.outputs[op]); node=reducer.node
    scope=view.wred_scopes[node]; raw=snapshot.raw_writers[node]
    writer=_one((w for w in snapshot['writers'] if w['export_id']==scope.source_writer),'original reducer writer missing/ambiguous')
    binding=writer['reducer']; placement=raw['placement']
    if (scope.source_writer!=writer_export_id(raw['ref']) or not _same_typed(writer['ref'],raw['ref'])
            or not _same_typed(scope.parameter,tuple(bw.inputs[ip]))):
        raise ValueError('bw-layernorm-wred original affine parameter identity mismatch')
    if not _same_typed([binding['reduce_op'],binding['zero'],binding['nreplicas']],['sum',0,1]):
        raise ValueError('bw-layernorm-wred original SUM/zero0/nreplicas1 required')
    nodes=view.nodes(); i=nodes.index(node); inputs=view.node_inputs(node); output,=view.node_outputs(node)
    if (not _same_typed(scope.ranks,tuple(t.rank for t in inputs))
            or not _same_typed(scope.input_tids,tuple(t.tid for t in inputs))
            or not _same_typed(scope.output_tid,output.tid) or not _same_typed(binding['ranks'],list(scope.ranks))):
        raise ValueError('bw-layernorm-wred ordered source group/input/output mismatch')
    params=compiler._get_node_params(view,node,num_parts=0)
    if params is not None and not _same_typed(params,[]):
        raise ValueError('bw-layernorm-wred empty original params required')
    contributions=[]; coordinates=[]; values=[]
    fields=('world','runtime_rank','microbatch','source_tid','version')
    common=('parent_tid','name','full_shape','indmap','valmap','is_attr','is_grad','is_param')
    for tensor in inputs:
        ref=view.source_tensor(tensor)
        j,producer=_one(((j,c) for j,c in enumerate(cells) if ref in c.outputs),'affine gradient producer missing/ambiguous')
        if j not in selected or producer.opname.name!='BW_layernorm' or not _same_typed(tuple(producer.outputs[op]),tuple(ref)):
            raise ValueError('bw-layernorm-wred complete selected original gradient role required')
        _,read=layernorm.render_read(view,cells,snapshot,j,order,'pm')
        peer=_reducer(cells,ref); ps=view.wred_scopes[peer.node]; pr=snapshot.raw_writers[peer.node]
        if (not _same_typed(ps.parameter,tuple(producer.inputs[ip])) or not _same_typed(ps.ranks,scope.ranks)
                or not _same_typed(pr['grad_input'],dict(zip(fields,ref,strict=True)))
                or not _same_typed(pr['parameter'],dict(zip(fields,producer.inputs[ip],strict=True)))
                or not _same_typed([pr['placement'][k] for k in common],[placement[k] for k in common])):
            raise ValueError('bw-layernorm-wred peer affine parameter/gradient placement mismatch')
        coordinates.append([pr['placement']['scale_unit'],pr['placement']['plan_rank']])
        contributions.append(dict(source_index=j,gradient_ref=list(ref),parameter_ref=list(producer.inputs[ip]),
                                  parameter_placement=pr['placement'],theorem=read['theorems'][op]))
        values.append('(bw_layernorm '+' '.join(f'(t {tid})' for tid in read['input_tids'])+f').2.{np}')
    if any(type(c) is not int or c<0 for pair in coordinates for c in pair) or len({tuple(p) for p in coordinates})!=len(coordinates):
        raise ValueError('bw-layernorm-wred distinct strict original DP/TP coordinates required')
    runtime_schedule.validate(view,order['execution_to_source']); seq=order['execution_to_source']; k=seq.index(i)
    ids=[t.tid for t in inputs]
    if any(set(ids)&{t.tid for t in view.node_outputs(nodes[j])} for j in seq[k:]):
        raise ValueError('bw-layernorm-wred gradient overwritten in selected/full suffix')
    name=f'backwardLayernormWRED_pm_{i}_{role}'; ranks=list(scope.ranks)
    proof=[f'theorem {name}_read (s t : Store) (h : pmDenoteWithInputs s = some t) :',
           f'    t {output.tid} = cross_dp_wred ({ids}.map t) := by',
           '  apply SourceWREDRead.wred_value_of_split pmGraph pmScope pmPeers pmGraph.nodes',
           f'    pmInputRequests (pmInputRequests.take {k}) (pmInputRequests.drop {k+1}) pmNode_{i}',
           f'    {node.rank} {ranks} {ids} {output.tid} s t rfl ?_ rfl ?_ h',
           '  · calc',f'      pmInputRequests = pmInputRequests.take {k} ++ pmInputRequests.drop {k} := (List.take_append_drop {k} pmInputRequests).symm',
           '      _ = _ := rfl',f'  · change ∀ tid ∈ ({ids} : List Tid), ∀ row ∈ pmInputRequests.drop {k}, tid ∉ row.1.outs',
           '    decide',f'#print axioms {name}_read',
           f'theorem {name}_contributions (s t : Store) (h : pmDenoteWithInputs s = some t) :',
           f'    t {output.tid} = cross_dp_wred ['+', '.join(values)+'] := by',
           f'  rw [{name}_read s t h]', '  simp only [List.map_cons, List.map_nil]',
           '  rw ['+', '.join(c['theorem']+' s t h' for c in contributions)+']',f'#print axioms {name}_contributions']
    return '\n'.join(proof)+'\n',dict(role=role,source_index=i,execution_index=k,ranks=ranks,coordinates=coordinates,
        parameter=list(scope.parameter),parameter_placement=placement,contributions=contributions,
        input_tids=ids,output_tid=output.tid,output_ref=list(view.source_tensor(output)),
        theorems=[name+'_read',name+'_contributions'],reduce_op=binding['reduce_op'],zero=binding['zero'],nreplicas=binding['nreplicas'])


def render(worlds,indices,capture_path,rank_code_directory):
    view,cells,_,order,label=worlds[1]
    if label!='pm' or not indices or any(type(i) is not int or not 0<=i<len(cells) for i in indices) or len(indices)!=len(set(indices)):
        raise ValueError('bw-layernorm-wred unique original projections required')
    snapshot=compiler._load_chunk_source(capture_path,rank_code_directory)
    compiler.attach_wred_scopes(view,snapshot,snapshot.raw_writers,snapshot.raw_rank_sources)
    proof=[]; reads=[]
    for i in indices:
        for role in ('dgamma','dbeta'):
            text,row=_read(view,cells,snapshot,order,i,indices,role); proof.append(text); reads.append(row)
    return ''.join(proof),dict(reads=reads,proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
