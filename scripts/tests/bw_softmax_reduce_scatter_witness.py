"""Portable atomic softmax / independent prior reduction witnesses and exact capture replay."""
from dataclasses import replace
from types import SimpleNamespace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node



def fixture(k=2, shard=(2,3,5,7), collision=False):
    """Same independent dependency shape as capture; interleaved rank-last softmax."""
    full=tuple(n*k if i==2 else n for i,n in enumerate(shard))
    output_tid=600 if collision else 30
    sm=[Node(0,"BW_softmax",[10,20],[output_tid],[3])]
    pm=[Node(r,"BW_softmax",[100+r,200+r],[300+r],[3]) for r in range(k-1)]
    pm += [Node(r,"ReduceScatterPrim",list(range(600,600+k)),[700+r],[2]) for r in range(k)]
    pm += [Node(k-1,"BW_softmax",[100+k-1,200+k-1],[300+k-1],[3])]
    si=tuple(i for i,n in enumerate(pm) if n.op=="BW_softmax")
    ri=tuple(i for i,n in enumerate(pm) if n.op=="ReduceScatterPrim")
    def src(kind,st,pts,axis=None):
        return rc.RelationFactSpec(kind,(st,*pts),gather_dim=axis)
    g=src("sharded","init:10",tuple(f"init:{100+r}" for r in range(k)),2)
    x=src("sharded","init:20",tuple(f"init:{200+r}" for r in range(k)),2)
    o=src("sharded","sm:0:0",tuple(f"pm:{i}:0" for i in si),2)
    w=src("reduction","init:50",tuple(f"init:{600+r}" for r in range(k)))
    j=src("sharded","init:50",tuple(f"pm:{i}:0" for i in ri),2)
    def record(name,source,smtid,pmtids,piece=shard):
        return rc.ClosedRelationFactRecord(name,source,source.layout,smtid,pmtids,None,None,full,piece,gather_dim=source.gather_dim)
    facts=(record("fg",g,10,tuple(range(100,100+k))),record("fx",x,20,tuple(range(200,200+k))),
           record("fo",o,output_tid,tuple(range(300,300+k))),record("fw",w,50,tuple(range(600,600+k)),full),
           record("fj",j,50,tuple(range(700,700+k))))
    anchor=rc.ClosedTensorShapeFactRecord("anchor","sm",99,(1,),0)
    active=rc.ClosedTensorEqFactRecord("active", "sm", 98, "pm", 98)
    soft=rc.KRankBWSoftmaxCertificate("bw-softmax-sharded-dim2-k-rank",k,2,g,x,o,"sm:0:0",tuple(f"pm:{i}:0" for i in si),"TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim2_rank4",(3,))
    scatter=rc.KRankReduceScatterReconstructionCertificate("reduce-scatter-reconstruction-k-rank",k,2,full,shard,w,j,tuple(f"pm:{i}:0" for i in ri),"TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn")
    transitions=tuple(replace(rc.CertificateTransitionSpec(name,c.rule_id,pre,(post,),sidx,pidx,c.lean_theorem),certificate_digest=_typed_certificate_digest(c)) for name,c,pre,post,sidx,pidx in (
        ("soft",soft,tuple(sorted((g,x))),o,(0,),si),("scatter",scatter,(w,),j,(),ri)))
    before=rc.ClosedRelationStateRecord("state_000000",("anchor","active","fg","fx","fw"))
    after=rc.ClosedRelationStateRecord("state_000001",("anchor","active","fg","fx","fo","fj"))
    seg=rc.ClosedDependentSegmentRecord("segment_000000","component",before.state_id,after.state_id,("soft","scatter"),(0,1),(0,2*k))
    chain=SimpleNamespace(complete=True,relation_facts=facts,authority_facts=(active,),anchor_fact=anchor,states=(before,after),segments=(seg,))
    ir=SimpleNamespace(sm_nodes=sm,pm_nodes=pm,sm_num_ranks=1,pm_num_ranks=k,sm_graph_ref="SyntheticBWSoftmaxReduceScatter.smGraph",pm_graph_ref="SyntheticBWSoftmaxReduceScatter.pmGraph")
    return ir,SimpleNamespace(certificates=(soft,scatter),transition_specs=transitions,dependent_chain_plan=chain)


def witness_source(k=2, **kwargs):
    from trainverify.bridge_emitter.bw_softmax_reduce_scatter_renderer import render_closed_bw_softmax_reduce_scatter_segment
    from trainverify.bridge_emitter.composer import _node_text,render_closed_relation_declarations
    ir,rel=fixture(k,**kwargs);ns="SyntheticBWSoftmaxReduceScatter"
    decl=render_closed_relation_declarations(rel.dependent_chain_plan,ns)
    decl=decl.replace(f"namespace TrainVerify.Denote.{ns}",f"namespace {ns}")
    graphs=f"def smGraph : GraphDecl := {{ numRanks := 1, nodes := [{', '.join(_node_text(n) for n in ir.sm_nodes)}] }}\ndef pmGraph : GraphDecl := {{ numRanks := {k}, nodes := [{', '.join(_node_text(n) for n in ir.pm_nodes)}] }}\n"
    decl=decl.replace("noncomputable section","noncomputable section\n"+graphs)
    closing=f"\nend\nend TrainVerify.Denote.{ns}\n"
    assert decl.endswith(closing)
    return "import denote.KRankBWSoftmaxGeneral\n" + decl[:-len(closing)] + "\n" + render_closed_bw_softmax_reduce_scatter_segment(ir,rel,"segment_000000") + f"\n#print axioms segment_000000\nend\nend {ns}\n"
