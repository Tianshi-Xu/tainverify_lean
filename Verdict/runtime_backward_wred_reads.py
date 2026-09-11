"""Source parameter-owned dW contributions into original DP SUM reducers.

The original reducer attachment supplies identity/group/scaling authority.
WredContract is only the checked value evaluator domain, not parameter identity.
Only direct BW_linear dW -> WRED paths are supported in this slice; intervening
accumulation requires its own source certificate and is not skipped.
"""
from Verdict import graph_to_lean as compiler, runtime_backward_linear_reads as linear
from Verdict.runtime_backward_cotangent_reads import _one
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_schedule
from trainverify.runtime_source_authority import writer_export_id


def _reducer(cells,grad):
    cell=_one((c for c in cells if c.rank==grad.rank and grad in c.inputs),
              'dW local consumer missing/ambiguous')
    if cell.opname.name!='CROSS_DP_WRED':
        raise ValueError('bw-wred dW requires an intervening accumulation/consumer certificate')
    return cell


def _read(view,cells,snapshot,order,index,selected):
    _,local=linear.render_read(view,cells,snapshot,index,order,'pm')
    bw=cells[index];reducer=_reducer(cells,bw.outputs[1]);node=reducer.node
    scope=view.wred_scopes[node];raw=snapshot.raw_writers[node]
    writer=_one((w for w in snapshot['writers'] if w['export_id']==scope.source_writer),
                'WRED writer missing/ambiguous')
    binding=writer['reducer'];placement=raw['placement']
    if (scope.source_writer!=writer_export_id(raw['ref']) or not _same_typed(writer['ref'],raw['ref'])
            or not _same_typed(scope.parameter,tuple(bw.inputs[2]))):
        raise ValueError('bw-wred original reducer/linear parameter identity mismatch')
    if (not _same_typed(binding['reduce_op'],'sum') or not _same_typed(binding['zero'],0)
            or not _same_typed(binding['nreplicas'],1)):
        raise ValueError('bw-wred source SUM/zero0/nreplicas1 required')
    nodes=view.nodes();i=nodes.index(node);inputs=view.node_inputs(node);output,=view.node_outputs(node)
    if (not _same_typed(scope.ranks,tuple(t.rank for t in inputs))
            or not _same_typed(scope.input_tids,tuple(t.tid for t in inputs))
            or output.tid!=scope.output_tid or not _same_typed(binding['ranks'],list(scope.ranks))):
        raise ValueError('bw-wred ordered original group/input/output mismatch')
    params=compiler._get_node_params(view,node,num_parts=0)
    if params is not None and not _same_typed(params,[]):
        raise ValueError('bw-wred empty original params required')
    contributions=[];names=[];values=[];units=[]
    fields=('world','runtime_rank','microbatch','source_tid','version')
    identity_fields=('parent_tid','name','full_shape','indmap','valmap','is_attr','is_grad','is_param','plan_rank')
    for t in inputs:
        fullref=view.source_tensor(t)
        pi,producer=_one(((j,c) for j,c in enumerate(cells) if fullref in c.outputs),
                         'WRED contribution writer missing/ambiguous')
        if pi not in selected or producer.opname.name!='BW_linear' or not _same_typed(tuple(producer.outputs[1]),tuple(fullref)):
            raise ValueError('bw-wred complete selected dW contributions required')
        _,proof=linear.render_read(view,cells,snapshot,pi,order,'pm')
        owner=_reducer(cells,fullref);peer_scope=view.wred_scopes[owner.node];peer_raw=snapshot.raw_writers[owner.node]
        if (not _same_typed(peer_scope.parameter,tuple(producer.inputs[2]))
                or not _same_typed(peer_scope.ranks,scope.ranks)
                or not _same_typed(peer_raw['grad_input'],dict(zip(fields,fullref,strict=True)))
                or not _same_typed(peer_raw['parameter'],dict(zip(fields,producer.inputs[2],strict=True)))
                or not _same_typed([peer_raw['placement'][f] for f in identity_fields],[placement[f] for f in identity_fields])):
            raise ValueError('bw-wred independent peer parameter placement/contribution mismatch')
        units.append(peer_raw['placement']['scale_unit'])
        g,x,w=proof['input_tids'];values.append(f'(bw_linear (t {g}) (t {x}) (t {w})).2')
        names.append(proof['theorems'][1])
        contributions.append(dict(source_index=pi,gradient_ref=list(fullref),parameter_ref=list(producer.inputs[2]),
                                  parameter_placement=peer_raw['placement'],theorem=proof['theorems'][1]))
    if any(type(u) is not int or u<0 for u in units):
        raise ValueError('bw-wred strict source DP ownership coordinate required')
    if len(units)!=len(set(units)):
        raise ValueError('bw-wred duplicated source DP contribution ownership')
    runtime_schedule.validate(view,order['execution_to_source'])
    sequence=order['execution_to_source'];k=sequence.index(i);ids=[t.tid for t in inputs]
    for j in sequence[k:]:
        if set(ids)&{t.tid for t in view.node_outputs(nodes[j])}:
            raise ValueError('bw-wred peer gradient overwritten by selected node or full execution suffix')
    name=f'backwardWRED_pm_{i}';rs=list(scope.ranks)
    proof=[f'theorem {name}_read (s t : Store) (h : pmDenoteWithInputs s = some t) :',
        f'    t {output.tid} = cross_dp_wred ({ids}.map t) := by',
        '  apply SourceWREDRead.wred_value_of_split pmGraph pmScope pmPeers pmGraph.nodes',
        f'    pmInputRequests (pmInputRequests.take {k}) (pmInputRequests.drop {k+1}) pmNode_{i}',
        f'    {node.rank} {rs} {ids} {output.tid} s t rfl ?_ rfl ?_ h',
        '  · calc',f'      pmInputRequests = pmInputRequests.take {k} ++ pmInputRequests.drop {k} := (List.take_append_drop {k} pmInputRequests).symm',
        '      _ = _ := rfl',
        f'  · change ∀ tid ∈ ({ids} : List Tid), ∀ row ∈ pmInputRequests.drop {k}, tid ∉ row.1.outs',
        '    decide',f'#print axioms {name}_read',
        f'theorem {name}_dw (s t : Store) (h : pmDenoteWithInputs s = some t) :',
        f'    t {output.tid} = cross_dp_wred ['+', '.join(values)+'] := by',
        f'  rw [{name}_read s t h]',
        '  simp only [List.map_cons, List.map_nil]',
        '  rw ['+', '.join(n+' s t h' for n in names)+']',f'#print axioms {name}_dw']
    return '\n'.join(proof)+'\n',dict(source_index=i,execution_index=k,ranks=rs,
        parameter=list(scope.parameter),parameter_placement=placement,source_writer_ref=raw['ref'],
        contributions=contributions,output_ref=list(view.source_tensor(output)),
        reduce_op=binding['reduce_op'],nreplicas=binding['nreplicas'],zero=binding['zero'],
        theorems=[name+'_read',name+'_dw'],operand_nonwrite_source_indices=sequence[k:])


def render(worlds,indices,capture_path,rank_code_directory):
    view,cells,_,order,label=worlds[1]
    if label!='pm' or not indices or any(type(i) is not int or not 0<=i<len(cells) for i in indices) or len(set(indices))!=len(indices):
        raise ValueError('bw-wred unique complete original linear projection required')
    snapshot=compiler._load_chunk_source(capture_path,rank_code_directory)
    compiler.attach_wred_scopes(view,snapshot,snapshot.raw_writers,snapshot.raw_rank_sources)
    proof=[];rows=[];seen=set()
    for i in indices:
        text,row=_read(view,cells,snapshot,order,i,indices)
        if row['source_index'] in seen:raise ValueError('bw-wred duplicate reducer projection')
        seen.add(row['source_index']);proof.append(text);rows.append(row)
    return ''.join(proof),dict(reads=rows,proof_admissible=False,kernel_value_proved=False,
        public_complete=False,torch_refinement=False)
