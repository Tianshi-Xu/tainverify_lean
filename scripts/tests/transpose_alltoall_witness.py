"""Portable mixed layout authority and optional exact captured-segment replay."""
from dataclasses import replace
from types import SimpleNamespace as NS
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node
T_RULE = "transpose-sharded-k-rank"
A_RULE = "alltoall-k-rank-layout-transport"
A_THEOREM = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
PREFIX = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_"

def renderer_fixture(k=3):
    # SM executes the dependent branch first; PM interleaves the independent branch.
    sm = [Node(0,"BW_transpose",[200,900],[400],[2,3]), Node(0,"BW_transpose",[100,901],[300],[1,2])]
    pm=[]; positions={x:[] for x in "tabc"}
    for r in range(k):
        positions['t'].append(len(pm));pm.append(Node(r,"BW_transpose",[1000+r,910+r],[3000+r],[1,2]))
        positions['a'].append(len(pm));pm.append(Node(r,"AllToAllPrim",list(range(2000,2000+k)),[4000+r],[1,2]))
    for r in range(k):
        positions['b'].append(len(pm));pm.append(Node(r,"AllToAllPrim",list(range(5000,5000+k)),[6000+r],[2,1]))
        positions['c'].append(len(pm));pm.append(Node(r,"BW_transpose",[4000+r,920+r],[7000+r],[2,3]))
    facts=[]
    def fact(name,tid,tids,dim,shape,refs):
        source=rc.RelationFactSpec('sharded',tuple(refs),gather_dim=dim)
        full=list(shape);full[dim]*=k
        f=rc.ClosedRelationFactRecord(name,source,'sharded',tid,tuple(tids),None,None,tuple(full),tuple(shape),gather_dim=dim)
        facts.append(f);return f
    def init(name,tid,base,dim,shape):return fact(name,tid,range(base,base+k),dim,shape,(f'init:{tid}',*(f'init:{base+r}' for r in range(k))))
    p=init('input_t',100,1000,1,(2,3,5*k,7))
    a=init('input_a',200,2000,1,(2,3,5*k,7))
    b=init('input_b',500,5000,2,(2,3*k,5,7))
    q=fact('out_t',300,range(3000,3000+k),2,(2,5*k,3,7),('sm:1:0',*(f'pm:{i}:0' for i in positions['t'])))
    z=fact('out_a',200,range(4000,4000+k),2,(2,3*k,5,7),('init:200',*(f'pm:{i}:0' for i in positions['a'])))
    v=fact('out_c',400,range(7000,7000+k),3,(2,3*k,7,5),('sm:0:0',*(f'pm:{i}:0' for i in positions['c'])))
    w=fact('out_b',500,range(6000,6000+k),1,(2,3,5*k,7),('init:500',*(f'pm:{i}:0' for i in positions['b'])))
    certs=[];ts=[]
    for name,pre,post,si,axes in [('t',p,q,1,(1,2)),('a',a,z,None,None),('c',z,v,0,(2,3)),('b',b,w,None,None)]:
        pis=tuple(positions[name]);steps=tuple(f'pm:{i}:0' for i in pis)
        if axes:
            theorem=PREFIX+f'{axes[0]}_{axes[1]}_dim{pre.gather_dim}_to_dim{post.gather_dim}_rank4'
            c=rc.KRankTransposeRelationCertificate(T_RULE,k,axes,pre.gather_dim,post.gather_dim,pre.full_shape,pre.shard_shape,post.full_shape,post.shard_shape,pre.source,post.source,f'sm:{si}:0',steps,theorem)
        else:c=rc.KRankAllToAllRelationCertificate(A_RULE,k,pre.gather_dim,post.gather_dim,pre.source,post.source,steps,A_THEOREM)
        certs.append(c);ts.append(rc.CertificateTransitionSpec('tr_'+name,c.rule_id,(pre.source,),(post.source,),() if si is None else (si,),pis,c.lean_theorem,certificate_digest=_typed_certificate_digest(c)))
    anchor=rc.ClosedTensorShapeFactRecord('anchor','sm',999,(1,),999)
    before=rc.ClosedRelationStateRecord('before',('anchor',p.fact_id,a.fact_id,b.fact_id))
    after=rc.ClosedRelationStateRecord('after',('anchor',p.fact_id,a.fact_id,b.fact_id,q.fact_id,v.fact_id,w.fact_id))
    seg=rc.ClosedDependentSegmentRecord('segment_000000','component','before','after',tuple(t.transition_id for t in ts),(0,2),(0,4*k))
    chain=NS(complete=True,relation_facts=tuple(facts),authority_facts=(),anchor_fact=anchor,states=(before,after),segments=(seg,))
    return NS(sm_nodes=sm,pm_nodes=pm,sm_num_ranks=1,pm_num_ranks=k,sm_graph_ref='TransposeAllToAll.smGraph',pm_graph_ref='TransposeAllToAll.pmGraph'),NS(certificates=tuple(certs),transition_specs=tuple(ts),dependent_chain_plan=chain)

def witness_source(k=3):
    from trainverify.bridge_emitter.composer import _node_text
    from trainverify.bridge_emitter.transpose_alltoall_renderer import render_closed_transpose_alltoall_segment
    ir,rel=renderer_fixture(k)
    lines=['import denote.RelationCompiler','import denote.KRankTranspose','import denote.KRankTranspose23Extra','open TrainVerify.Denote TrainVerify.Denote.RelationCompiler','namespace TransposeAllToAll','noncomputable section']
    for side,nodes,n in [('sm',ir.sm_nodes,1),('pm',ir.pm_nodes,k)]:
        lines.append(f'def {side}Graph : GraphDecl := {{ numRanks := {n}, nodes := [{", ".join(_node_text(x) for x in nodes)}] }}')
    lines.append('def anchor : RelationFact := .tensorShape .sm 999 [1]')
    for f in rel.dependent_chain_plan.relation_facts:
        lines.append(f'def {f.fact_id} : RelationFact := .sharded {f.sm_tid} {list(f.pm_tids)} {f.gather_dim} {list(f.full_shape)} {list(f.shard_shape)}')
    for s in rel.dependent_chain_plan.states:lines.append(f'def {s.state_id} : RelationState where\n  facts := [{", ".join(s.fact_ids)}]\n  nonempty := by decide')
    lines += [render_closed_transpose_alltoall_segment(ir,rel,'segment_000000'),'#print axioms segment_000000','end','end TransposeAllToAll','']
    return '\n'.join(lines)
