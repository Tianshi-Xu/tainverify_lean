"""Portable independent BW_softmax/transpose atomic authority, plus frozen replay."""
from dataclasses import replace
from types import SimpleNamespace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node

T_RULE = "transpose-sharded-k-rank"
T_THEOREM = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4"
S_RULE = "bw-softmax-sharded-dim1-k-rank"
S_THEOREM = "TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim1_rank4"


def renderer_fixture(k=3,b=2,h=3,q=5,d=7):
    def fact(name,tid,ptids,axis,shard,refs):
        full=tuple(v*k if i==axis else v for i,v in enumerate(shard))
        source=rc.RelationFactSpec("sharded",refs,gather_dim=axis)
        return rc.ClosedRelationFactRecord(name,source,"sharded",tid,ptids,None,None,full,shard,gather_dim=axis)
    def initial(name,tid,axis,shard):
        tids=tuple(tid*10+r for r in range(k))
        return fact(name,tid,tids,axis,shard,(f"init:{tid}",*(f"init:{u}" for u in tids)))
    g=initial("fg",100,1,(b,h,q,d));x=initial("fx",200,1,(b,h,q,d));ti=initial("fti",400,2,(b,h,q,d))
    so=fact("fo",300,tuple(3000+r for r in range(k)),1,(b,h,q,d),("sm:0:0",*(f"pm:{2*r}:0" for r in range(k))))
    to=fact("fto",500,tuple(5000+r for r in range(k)),1,(b,q,h,d),("sm:1:0",*(f"pm:{2*r+1}:0" for r in range(k))))
    sc=rc.KRankBWSoftmaxCertificate(S_RULE,k,1,g.source,x.source,so.source,"sm:0:0",tuple(f"pm:{2*r}:0" for r in range(k)),S_THEOREM,())
    tc=rc.KRankTransposeRelationCertificate(T_RULE,k,(1,2),2,1,ti.full_shape,ti.shard_shape,to.full_shape,to.shard_shape,ti.source,to.source,"sm:1:0",tuple(f"pm:{2*r+1}:0" for r in range(k)),T_THEOREM)
    st=rc.CertificateTransitionSpec("soft",S_RULE,tuple(sorted((g.source,x.source))),(so.source,),(0,),tuple(2*r for r in range(k)),S_THEOREM,certificate_digest=_typed_certificate_digest(sc))
    tt=rc.CertificateTransitionSpec("transpose",T_RULE,(ti.source,),(to.source,),(1,),tuple(2*r+1 for r in range(k)),T_THEOREM,certificate_digest=_typed_certificate_digest(tc))
    sm=[Node(0,"BW_softmax",[100,200],[300],[]),Node(0,"BW_transpose",[400,99],[500],[1,2])]
    pm=[n for r in range(k) for n in (Node(r,"BW_softmax",[1000+r,2000+r],[3000+r],[]),Node(r,"BW_transpose",[4000+r,99],[5000+r],[1,2]))]
    before=rc.ClosedRelationStateRecord("state_000000",("fg","fx","fti"))
    after=rc.ClosedRelationStateRecord("state_000001",("fg","fx","fti","fo","fto"))
    seg=rc.ClosedDependentSegmentRecord("segment_000000","atomic",before.state_id,after.state_id,("soft","transpose"),(0,2),(0,2*k))
    chain=SimpleNamespace(complete=True,relation_facts=(g,x,ti,so,to),authority_facts=(),anchor_fact=None,states=(before,after),segments=(seg,))
    return SimpleNamespace(sm_nodes=sm,pm_nodes=pm,pm_num_ranks=k,sm_graph_ref="BWSoftmaxTranspose.smGraph",pm_graph_ref="BWSoftmaxTranspose.pmGraph"),SimpleNamespace(certificates=(sc,tc),transition_specs=(st,tt),dependent_chain_plan=chain)




def witness_source(k=3):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_softmax_transpose_renderer import render_closed_bw_softmax_transpose_segment
    ir,rel=renderer_fixture(k)
    return fixture_source(ir,rel,render_closed_bw_softmax_transpose_segment,pm_num_ranks=k).replace('SyntheticBWLayernorm','BWSoftmaxTranspose').replace('import denote.KRankBWLayernorm','import denote.KRankBWSoftmaxGeneral\nimport denote.RelationCompiler')
