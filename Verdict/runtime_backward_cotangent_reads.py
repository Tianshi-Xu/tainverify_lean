"""Backward AllToAll cotangent links over the shared source-read certificates.

Use the source-authenticated autograd context, including reversed dimensions.
The source model value equation is not Torch saved-storage refinement. Existing
seed and linear certificate names are dependencies, never duplicated here.
"""
from pathlib import Path
from Verdict import graph_to_lean as compiler, runtime_backward_seed_reads as seeds
from Verdict import runtime_backward_linear_reads as linear, runtime_schedule
from Verdict.runtime_lineage import _same_typed


def _one(rows,reason):
    rows=list(rows)
    if len(rows)!=1: raise ValueError('bw-cotangent '+reason)
    return rows[0]


def _read(view,cells,snapshot,order,prior,seed_row):
    producer=cells[seed_row['source_index']]
    ref,=producer.outputs
    consumer=_one((c for c in cells if c.rank==producer.rank and ref in c.inputs),
                  'local seed consumer missing/ambiguous')
    if consumer.opname.name!='AllToAllPrim':
        raise ValueError('bw-cotangent first local seed consumer is not AllToAll')
    nodes=view.nodes();i=nodes.index(consumer.node);scope=view.collective_scopes[consumer.node]
    writer=_one((w for w in snapshot['writers'] if w['export_id']==scope.source_writer),
                'collective writer missing/ambiguous')
    ctx=writer['adapter'].get('backward_context',{})
    if (ctx.get('status')!='structurally-bound' or ctx.get('gradient_value_proved') is not False
            or ctx['runtime']['backward']['op']!='AllToAllPrim'
            or not _same_typed(ctx['runtime']['backward']['kwargs'],
                              dict(idim=scope.params[0],odim=scope.params[1],ranks=list(scope.ranks)))):
        raise ValueError('bw-cotangent original backward runtime context required')
    if linear._writer(snapshot,cells,i)!=scope.source_writer:
        raise ValueError('bw-cotangent original collective writer mismatch')
    inputs=view.node_inputs(consumer.node);output,=view.node_outputs(consumer.node)
    if (not _same_typed(tuple(t.tid for t in inputs),scope.input_tids)
            or not _same_typed(tuple(t.rank for t in inputs),scope.ranks)
            or output.tid!=scope.output_tid or scope.local_index!=list(scope.ranks).index(consumer.rank)):
        raise ValueError('bw-cotangent ordered peers/output/local index mismatch')
    preds=[];saved=[]
    for tensor in inputs:
        original=list(view.source_tensor(tensor))
        p=_one((p for p in prior['reads'] if p['output_refs']==[original]),
               'ordered peer gradient producer missing/ambiguous')
        if p['world']!='pm':raise ValueError('bw-cotangent cross-world gradient producer')
        source=cells[p['source_index']]
        primal=view.node_inputs(source.node)[1].tid
        preds.append(p);saved.append(primal)
    fields=('world','runtime_rank','microbatch','source_tid','version')
    local=dict(zip(fields,ref,strict=True));outref=dict(zip(fields,view.source_tensor(output),strict=True))
    if (not _same_typed(ctx['output_gradient'],[local]) or not _same_typed(ctx['input_gradient'],[outref])
            or not _same_typed(ctx['gradient_read_points'],[dict(ref=local,writer=seed_row['bw_writer'])])):
        raise ValueError('bw-cotangent original backward gradient read point mismatch')
    target=_one((c for c in cells if c.rank==consumer.rank and view.source_tensor(output) in c.inputs),
                'local output consumer missing/ambiguous')
    if target.opname.name!='BW_linear' or not _same_typed(tuple(target.inputs[0]),tuple(view.source_tensor(output))):
        raise ValueError('bw-cotangent output is not original linear cotangent')
    li=nodes.index(target.node)
    _,linear_row=linear.render_read(view,cells,snapshot,li,order,'pm')
    runtime_schedule.validate(view,order['execution_to_source'])
    sequence=order['execution_to_source'];k=sequence.index(i);ids=[t.tid for t in inputs]
    for j in sequence[k:]:
        if set(ids)&{t.tid for t in view.node_outputs(nodes[j])}:
            raise ValueError('bw-cotangent peer overwritten in selected/complete execution suffix')
    rs=list(scope.ranks);idim,odim=scope.params;name=f'backwardCotangent_pm_{i}'
    value=f'AllToAllSourceFaithful.tensor {len(rs)} {scope.local_index} {idim} {odim}'
    broadcasts='['+', '.join(f'Tensor.mkShape (t {x}).shape (fun _ => 1)' for x in saved)+']'
    proof=[f'theorem {name}_read (s t : Store) (h : pmDenoteWithInputs s = some t) :',
        f'    t {output.tid} = {value} ({ids}.map t) := by',
        '  apply SourcePrimitiveRead.allToAll_value_of_split pmGraph pmScope pmPeers pmGraph.nodes',
        f'    pmInputRequests (pmInputRequests.take {k}) (pmInputRequests.drop {k+1}) pmNode_{i}',
        f'    {consumer.rank} {rs} {ids} {output.tid} {idim} {odim} s t rfl ?_ rfl ?_ h',
        '  · calc',f'      pmInputRequests = pmInputRequests.take {k} ++ pmInputRequests.drop {k} := (List.take_append_drop {k} pmInputRequests).symm',
        '      _ = _ := rfl',
        f'  · change ∀ tid ∈ ({ids} : List Tid), ∀ row ∈ pmInputRequests.drop {k}, tid ∉ row.1.outs',
        '    decide',f'#print axioms {name}_read',
        f'theorem {name}_seeded (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :',
        f'    t {output.tid} = {value} {broadcasts} := by',
        f'  rw [{name}_read (pmInitialWithSeeds s) t h]',
        '  simp only [List.map_cons, List.map_nil]',
        '  rw ['+', '.join(p['theorems'][2]+' s t h' for p in preds)+']',f'#print axioms {name}_seeded']
    for role,pos in [('dx',0),('dw',1)]:
        out=linear_row['output_tids'][pos];_,x,w=linear_row['input_tids']
        proof += [f'theorem {name}_{role} (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :',
            f'    t {out} = (bw_linear ({value} {broadcasts}) (t {x}) (t {w})).{pos+1} := by',
            f'  rw [{linear_row["theorems"][pos]} (pmInitialWithSeeds s) t h, {name}_seeded s t h]',
            f'#print axioms {name}_{role}']
    return '\n'.join(proof)+'\n',dict(source_index=i,execution_index=k,node=list(consumer.node),
        raw_kwargs=dict(consumer.kwargs),params=list(scope.params),ranks=rs,input_ranks=[t.rank for t in inputs],
        backward_context_status=ctx['status'],predecessors=[p['theorems'][2] for p in preds],
        output_ref=list(view.source_tensor(output)),linear_input_ref=list(target.inputs[0]),
        theorems=[name+s for s in ('_read','_seeded','_dx','_dw')],linear_dependencies=linear_row['theorems'])


def render(worlds,config,handoff_root,rank_code_directory):
    _,prior=seeds.render(worlds,config,handoff_root)
    view,cells,_,order,label=worlds[1]
    if label!='pm':raise ValueError('bw-cotangent expected original PM world')
    snapshot=compiler._load_chunk_source(str(Path(config['pm_capture'])/'capture.pkl'),rank_code_directory)
    compiler.attach_collective_scopes(view,snapshot)
    proofs=[];rows=[]
    for seed_row in prior['reads']:
        if seed_row['world']!='pm':continue
        text,row=_read(view,cells,snapshot,order,prior,seed_row);proofs.append(text);rows.append(row)
    return ''.join(proofs),dict(reads=rows,proof_admissible=False,kernel_value_proved=False,
        public_complete=False,torch_refinement=False)
