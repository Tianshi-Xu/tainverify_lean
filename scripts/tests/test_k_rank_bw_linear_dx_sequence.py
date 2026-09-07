from dataclasses import replace
from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import LineageGoal, Node
from trainverify.bridge_emitter.composer import _typed_certificate_digest

RULE = "bw-linear-dx-sequence-sharded-k-rank"
THEOREM = "TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3"
CASES = ((2,1,8,64,64),(4,1,4,64,64),(3,2,5,7,11),(1,3,2,1,4),(5,2,1,3,2),(4,1,2,32,32))


def matcher_fixture(k=3,b=2,s=5,o=7,i=11):
    gf,gs,xf,xs,w=(b,s*k,o),(b,s,o),(b,s*k,i),(b,s,i),(o,i)
    sm=SimpleNamespace(step_id="sm:0:0",op="BW_linear",side="sm",rank=0,
        output_projection=".1",parameters=(),input_bindings=("sm:g","sm:x","init:300"),
        input_shapes=(gf,xf,w),output_shape=xf)
    pms=tuple(SimpleNamespace(step_id=f"pm:{r}:0",op="BW_linear",side="pm",rank=r,
        output_projection=".1",parameters=(),input_bindings=(f"pm:g:{r}",f"pm:x:{r}","init:300"),
        input_shapes=(gs,xs,w),output_shape=xs) for r in range(k))
    ir=SimpleNamespace(init_lineages={300:LineageGoal(300,list(w),[(0,300)],[list(w)],gatherDim=0)})
    return SimpleNamespace(steps=(sm,*pms)),ir,(sm.step_id,*(p.step_id for p in pms))


def renderer_fixture(k=3,b=2,s=5,o=7,i=11):
    from scripts.tests.test_k_rank_bw_sum import _bw_linear_dx_renderer_fixture
    ir,rel=_bw_linear_dx_renderer_fixture(k)
    g,x,w,out=rel.dependent_chain_plan.relation_facts
    gf=replace(g.source,gather_dim=1)
    xf=rc.RelationFactSpec("sharded",("sm:x",*(f"pm:x:{r}" for r in range(k))),gather_dim=1)
    wf=rc.RelationFactSpec("sharded",("init:300","init:300"),gather_dim=0)
    of=replace(out.source,layout="sharded",gather_dim=1)
    records=(replace(g,source=gf,gather_dim=1,full_shape=(b,s*k,o),shard_shape=(b,s,o)),
        replace(x,source=xf,kind="sharded",gather_dim=1,pm_tids=tuple(2000+r for r in range(k)),joined_pm_tid=None,full_shape=(b,s*k,i),shard_shape=(b,s,i)),
        replace(w,source=wf,pm_tids=(300,),full_shape=(o,i),shard_shape=(o,i)),
        replace(out,source=of,kind="sharded",gather_dim=1,full_shape=(b,s*k,i),shard_shape=(b,s,i)))
    c=replace(rel.certificates[0],rule_id=RULE,family="sequence-sharded",output_layout="sharded",gather_dim=1,input_facts=(gf,xf,wf),output_fact=of,lean_theorem=THEOREM)
    t=replace(rel.transition_specs[0],rule_id=RULE,pre_facts=tuple(sorted(c.input_facts)),post_facts=(of,),lean_theorem=THEOREM,certificate_digest=_typed_certificate_digest(c))
    rel.certificates=(c,);rel.transition_specs=(t,)
    rel.dependent_chain_plan.relation_facts=records
    rel.dependent_chain_plan.authority_facts=()
    rel.dependent_chain_plan.anchor_fact=None
    rel.dependent_chain_plan.complete=True
    ir.pm_nodes=[Node(r,"BW_linear",[1000+r,2000+r,300],[4000+r,5000+r],[]) for r in range(k)]
    return ir,rel


@pytest.mark.parametrize("args",CASES)
def test_sequence_matcher_generic(args):
    plan,ir,f=matcher_fixture(*args)
    certs,_,_=rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(f,),("sharded",))
    assert (certs[0].rule_id,certs[0].lean_theorem,certs[0].rank_count)==(RULE,THEOREM,args[0])


@pytest.mark.parametrize("mutation",("rank","order","weight-ref","weight-shape","lineage-shape","lineage-rank","activation","gradient","output","zero"))
def test_sequence_matcher_fail_closed(mutation):
    plan,ir,f=matcher_fixture()
    sm,*pms=plan.steps
    if mutation=="rank": pms[1].rank=0
    if mutation=="order": f=(f[0],*reversed(f[1:]))
    if mutation=="weight-ref": pms[1].input_bindings=(*pms[1].input_bindings[:2],"init:301")
    if mutation=="weight-shape": sm.input_shapes=(*sm.input_shapes[:2],(7,12))
    if mutation=="lineage-shape": ir.init_lineages[300].tsShape=[7,12];ir.init_lineages[300].tpShapes=[[7,12]]
    if mutation=="lineage-rank": ir.init_lineages[300].tps=[(1,300)]
    if mutation=="activation": sm.input_shapes=(sm.input_shapes[0],(2,14,11),sm.input_shapes[2])
    if mutation=="gradient": sm.input_shapes=((2,14,7),*sm.input_shapes[1:])
    if mutation=="output": sm.output_shape=(2,15,12)
    if mutation=="zero": plan,ir,f=matcher_fixture(s=0)
    with pytest.raises(rc.RelationCompositionError): rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(f,),("sharded",))


@pytest.mark.parametrize("args",CASES)
def test_sequence_renderer_generic(args):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture(*args)
    text=render_closed_segment(ir,rel,"segment_000000")
    assert THEOREM in text
    assert text.count("private def segment_000000_sm_final") == 1
    assert text.count("private def segment_000000_pm_final") == 1
    assert f"allGatherPrimDimN 1 {args[0]} 0" in text
    assert "g169" not in text and "g143" not in text


@pytest.mark.parametrize("mutation",("rank","pairing","weight","shape","digest","duplicate","frame"))
def test_sequence_renderer_fail_closed(mutation):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture()
    c=rel.certificates[0];t=rel.transition_specs[0]
    if mutation=="rank": ir.pm_nodes[1].rank=0
    if mutation=="pairing": ir.pm_nodes[1].ins[0]=1000
    if mutation=="weight": ir.pm_nodes[1].ins[2]=301
    if mutation=="shape": rel.dependent_chain_plan.relation_facts=tuple(replace(r,full_shape=(2,14,11)) if r.fact_id=="fact_out" else r for r in rel.dependent_chain_plan.relation_facts)
    if mutation=="digest": rel.transition_specs=(replace(t,certificate_digest="0"*64),)
    if mutation=="duplicate": rel.certificates=(c,c)
    if mutation=="frame":
        ir.pm_nodes.append(Node(0,"FW_neg",[4000],[300],[]))
        seg=rel.dependent_chain_plan.segments[0]
        rel.dependent_chain_plan.segments=(replace(seg,pm_range=(0,4)),)
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")


def test_sequence_sparse_frame_is_emitted_once():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture()
    c=rel.certificates[0];t=rel.transition_specs[0]
    ir.pm_nodes.insert(1,Node(0,"FW_neg",[9000],[9001],[]))
    ir.sm_nodes.append(Node(0,"FW_neg",[9010],[9011],[]))
    c=replace(c,pm_step_ids=("pm:0:0","pm:2:0","pm:3:0"))
    rel.certificates=(c,)
    rel.transition_specs=(replace(t,pm_node_indices=(0,2,3),certificate_digest=_typed_certificate_digest(c)),)
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,sm_range=(0,2),pm_range=(0,4)),)
    text=render_closed_segment(ir,rel,"segment_000000")
    assert "9001" in text and "9011" in text
    assert text.count("private def segment_000000_pm_final") == 1
    assert text.count("private def segment_000000_sm_final") == 1


def witness_source(k=3,b=2,s=5,o=7,i=11):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_dx_renderer import render_closed_k_rank_bw_linear_dx_sequence_segment
    ir,rel=renderer_fixture(k,b,s,o,i)
    return fixture_source(ir,rel,render_closed_k_rank_bw_linear_dx_sequence_segment).replace(
        "SyntheticBWLayernorm","SyntheticBWLinearDx").replace(
        "import denote.KRankBWLayernorm","import denote.KRankBWLinearDxSequence")


def test_sequence_leaf_import_and_reproducible_witness():
    spec=rc.get_closed_rule_spec(RULE)
    text=witness_source()
    assert "import denote.KRankBWLinearDxSequence\n" in text
    assert text==witness_source()
    assert THEOREM in text
