"""General-batch synthetic atomic dX/gather/view/all-to-all regression."""
from dataclasses import replace
from scripts.tests.test_k_rank_bw_linear_dx_column import renderer_fixture
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter.composer import _typed_certificate_digest, render_closed_segment


def fixture(b=2,s=8):
    k=4
    ir,rel=renderer_fixture(k,7,8,b=b,s=s)
    g,x,w,y=rel.dependent_chain_plan.relation_facts
    c=rel.certificates[0]
    yf=replace(c.output_fact,step_triple=("sm:1:0",*c.output_fact.step_triple[1:]))
    c=replace(c,sm_step_id="sm:1:0",output_fact=yf)
    y=replace(y,source=yf)
    t=replace(rel.transition_specs[0],sm_node_indices=(1,),post_facts=(yf,),certificate_digest=_typed_certificate_digest(c))
    source=rc.RelationFactSpec("sharded",("sm:in",*(f"pm:in:{r}" for r in range(k))),gather_dim=2)
    joined=rc.RelationFactSpec("joined",("sm:in",),joined_pm_step="pm:4:0")
    view=rc.RelationFactSpec("joined",("sm:0:0",),joined_pm_step="pm:5:0")
    aout=rc.RelationFactSpec("sharded",("sm:1:0",*(f"pm:{r+6}:0" for r in range(k))),gather_dim=1)
    full=(b,s,32);shard=(b,s,8);a_shard=(b,s//4,32)
    G=rc.KRankAllGatherReconstructionCertificate("allgather-reconstruction-k-rank",k,2,full,shard,source,joined,"pm:4:0","TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather")
    V=rc.JoinedBWViewCertificate("bw-view-joined",full,full,joined,view,"sm:0:0","pm:5:0","TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view")
    A=rc.KRankAllToAllRelationCertificate("alltoall-k-rank-layout-transport",k,2,1,yf,aout,tuple(f"pm:{r+6}:0" for r in range(k)),"TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn")
    records=(g,x,w,y,
        rc.ClosedRelationFactRecord("fact_gin",source,"sharded",600,tuple(6000+r for r in range(k)),None,None,full,shard,gather_dim=2),
        rc.ClosedRelationFactRecord("fact_gout",joined,"joined",600,(),None,None,full,full,joined_pm_tid=6100),
        rc.ClosedRelationFactRecord("fact_view",view,"joined",601,(),None,None,full,full,joined_pm_tid=6101),
        rc.ClosedRelationFactRecord("fact_aout",aout,"sharded",400,tuple(7000+r for r in range(k)),None,None,full,a_shard,gather_dim=1))
    def transition(name,cert,pre,post,sm,pm):
        return rc.CertificateTransitionSpec(name,cert.rule_id,pre,(post,),sm,pm,cert.lean_theorem,certificate_digest=_typed_certificate_digest(cert))
    ts=(t,transition("gather",G,(source,),joined,(),(4,)),transition("view",V,(joined,),view,(0,),(5,)),transition("a2a",A,(yf,),aout,(),tuple(range(6,10))))
    rel.certificates=(c,G,V,A);rel.transition_specs=ts
    chain=rel.dependent_chain_plan;chain.complete=True
    chain.relation_facts=records
    chain.states=(rc.ClosedRelationStateRecord("state_000000",("fact_g","fact_x","fact_w","fact_gin")),rc.ClosedRelationStateRecord("state_000001",("fact_view","fact_aout")))
    chain.segments=(replace(chain.segments[0],sm_range=(0,2),pm_range=(0,10),transition_ids=tuple(t.transition_id for t in ts)),)
    ir.sm_nodes=[Node(0,"BW_view",[600,600],[601],list(full)),*ir.sm_nodes]
    ir.pm_nodes += [Node(0,"AllGatherPrim",[6000+r for r in range(k)],[6100],[2]),Node(0,"BW_view",[6100,6100],[6101],list(full)),*(Node(r,"AllToAllPrim",list(y.pm_tids),[7000+r],[2,1]) for r in range(k))]
    ir.pm_num_ranks=k
    return ir,rel


def test_collective_dx_general_batch_shape_helper():
    ir,rel=fixture()
    source=render_closed_segment(ir,rel,"segment_000000")
    assert "g.shape=[2,8,o]" in source
    assert "x.shape=[2,8,i]" in source


def witness_source():
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    ir,rel=fixture()
    return (fixture_source(ir,rel,render_closed_segment,pm_num_ranks=ir.pm_num_ranks)
        .replace("SyntheticBWLayernorm","SyntheticBWLinearDxColumn")
        .replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDxColumnGeneral\nimport denote.KRankAllToAll"))


def test_collective_general_witness_matches_generator():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedBWColumnCollectiveGeneralWitness.lean"
    assert path.read_text()==witness_source()
