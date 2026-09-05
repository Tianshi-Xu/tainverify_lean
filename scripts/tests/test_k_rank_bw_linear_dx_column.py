from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import LineageGoal

RULE="bw-linear-dx-column-sharded-k-rank"
THEOREM="TrainVerify.Denote.bw_linear_dx_weight_allGatherPrimDimN_dim1_rank3"


def matcher_fixture(k=3):
    full=(1,8,32*k); shard=(1,8,32); fw=(32,32*k); sw=(32,32)
    sm=SimpleNamespace(step_id="sm:0:0",op="BW_linear",side="sm",rank=0,
        output_projection=".1",parameters=(),input_bindings=("sm:g:0","sm:x:0","init:700"),
        input_shapes=(shard,full,fw),output_shape=full)
    pms=tuple(SimpleNamespace(step_id=f"pm:{r}:0",op="BW_linear",side="pm",rank=r,
        output_projection=".1",parameters=(),input_bindings=("pm:g:shared",f"pm:x:{r}",f"init:{701+r}"),
        input_shapes=(shard,shard,sw),output_shape=shard) for r in range(k))
    ir=SimpleNamespace(init_lineages={700:LineageGoal(700,list(fw),[(r,701+r) for r in range(k)],
        [list(sw) for _ in range(k)],gatherDim=1)})
    return SimpleNamespace(steps=(sm,*pms)),ir,(sm.step_id,*(p.step_id for p in pms))


@pytest.mark.parametrize("k",(1,2,3,4,5))
def test_column_matcher_dynamic_rank(k):
    plan,ir,frontier=matcher_fixture(k)
    certs,_,_=rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(frontier,),("sharded",))
    assert len(certs)==1
    c=certs[0]
    assert (c.rule_id,c.lean_theorem,c.rank_count)==(RULE,THEOREM,k)
    assert c.input_facts[2].gather_dim==1


def renderer_fixture(k=3):
    from dataclasses import replace
    from scripts.tests.test_k_rank_bw_sum import _bw_linear_dx_renderer_fixture
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import Node
    ir,rel=_bw_linear_dx_renderer_fixture(k)
    g,x,w,out=rel.dependent_chain_plan.relation_facts
    gf=rc.RelationFactSpec("joined",("sm:g",),joined_pm_step="pm:g")
    xf=rc.RelationFactSpec("sharded",("sm:x",*(f"pm:x:{r}" for r in range(k))),gather_dim=2)
    wf=replace(w.source,gather_dim=1)
    of=replace(out.source,layout="sharded",gather_dim=2)
    records=(replace(g,source=gf,kind="joined",pm_tids=(),joined_pm_tid=1000,full_shape=(1,8,32),shard_shape=(1,8,32),gather_dim=None),
        replace(x,source=xf,kind="sharded",pm_tids=tuple(2000+r for r in range(k)),joined_pm_tid=None,
            full_shape=(1,8,32*k),shard_shape=(1,8,32),gather_dim=2),
        replace(w,source=wf,full_shape=(32,32*k),gather_dim=1),
        replace(out,source=of,kind="sharded",gather_dim=2,full_shape=(1,8,32*k)))
    c=replace(rel.certificates[0],rule_id=RULE,family="column-sharded",output_layout="sharded",gather_dim=2,
        input_facts=(gf,xf,wf),output_fact=of,lean_theorem=THEOREM)
    t=replace(rel.transition_specs[0],rule_id=RULE,pre_facts=tuple(sorted(c.input_facts)),post_facts=(of,),
        lean_theorem=THEOREM,certificate_digest=_typed_certificate_digest(c))
    rel.certificates=(c,);rel.transition_specs=(t,);rel.dependent_chain_plan.relation_facts=records
    rel.dependent_chain_plan.states=tuple(replace(st,state_id=f"state_{i:06d}") for i,st in enumerate(rel.dependent_chain_plan.states))
    rel.dependent_chain_plan.segments=(replace(rel.dependent_chain_plan.segments[0],pre_state_id="state_000000",post_state_id="state_000001"),)
    ir.pm_nodes=[Node(r,"BW_linear",[1000,2000+r,3000+r],[4000+r,5000+r],[]) for r in range(k)]
    ir.sm_graph_ref="SyntheticBWLinearDxColumn.smGraph";ir.pm_graph_ref="SyntheticBWLinearDxColumn.pmGraph"
    return ir,rel


@pytest.mark.parametrize("k",(1,3,5))
def test_column_renderer_dynamic_rank(k):
    from trainverify.bridge_emitter.bw_linear_dx_column_renderer import render_closed_k_rank_bw_linear_dx_column_segment
    ir,rel=renderer_fixture(k)
    source=render_closed_k_rank_bw_linear_dx_column_segment(ir,rel,"segment_000000")
    assert THEOREM in source
    assert f"allGatherPrimDimN 2 {k} 0" in source
    assert "bw_linear_dx_wsplit_dim1_4_g213" not in source


def witness_source(k=3):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_dx_column_renderer import render_closed_k_rank_bw_linear_dx_column_segment
    ir,rel=renderer_fixture(k)
    return fixture_source(ir,rel,render_closed_k_rank_bw_linear_dx_column_segment).replace("SyntheticBWLayernorm","SyntheticBWLinearDxColumn").replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDxColumn")


@pytest.mark.parametrize("mutation",("rank","parameters","activation","gradient","weight","lineage-shape","lineage-rank","lineage-axis","input-shape-arity"))
def test_column_matcher_rejects_malformed_authority(mutation):
    plan,ir,f=matcher_fixture()
    sm,*pms=plan.steps
    if mutation=="rank": pms[1].rank=0
    elif mutation=="parameters": pms[1].parameters=(2,)
    elif mutation=="activation": sm.input_shapes=(sm.input_shapes[0],(1,7,96),sm.input_shapes[2])
    elif mutation=="gradient": pms[1].input_bindings=("pm:g:other",*pms[1].input_bindings[1:])
    elif mutation=="weight": pms[1].input_shapes=(*pms[1].input_shapes[:2],(31,32))
    elif mutation=="lineage-shape": ir.init_lineages[700].tsShape=[31,96];ir.init_lineages[700].tpShapes=[[31,32]]*3
    elif mutation=="lineage-rank": ir.init_lineages[700].tps=[(2,701),(1,702),(0,703)]
    elif mutation=="lineage-axis": ir.init_lineages[700].gatherDim=0
    elif mutation=="input-shape-arity": pms[0].input_shapes=((1,8,32),)
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(f,),("sharded",))


def test_column_committed_witness_matches_renderer():
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]
    assert (root/"trainverify/denote/GeneratedKRankBWLinearDxColumnWitness.lean").read_text()==witness_source()


@pytest.mark.parametrize("tail,expected",((('bw-view-joined',),'bw_linear_dx_column_renderer:'),
    (('bw-linear-dw-input-column-sharded-rank4',),'bw_linear_column_dual_renderer:')))
def test_column_compound_routes_dynamic_identity(tail,expected):
    from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer
    selected=select_bw_compound_renderer((RULE,*tail))
    assert selected is not None and selected.startswith(expected)



def dual_fixture(k=4):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=renderer_fixture(k)
    c=rel.certificates[0];g,x,w=c.input_facts
    fact=rc.RelationFactSpec("sharded",("sm:0:1",*(f"pm:{r}:1" for r in range(k))),gather_dim=1)
    dw=rc.KRankBWLinearDwColumnShardedCertificate("bw-linear-dw-input-column-sharded-rank4",k,g,x,w,fact,
        "sm:0:1",tuple(f"pm:{r}:1" for r in range(k)),"TrainVerify.Denote.bw_linear_dw_isplit_dim2_4_1_8_32_g214")
    tr=rc.CertificateTransitionSpec("transition_000001",dw.rule_id,tuple(sorted((g,x,w))),(fact,),
        (0,),tuple(range(k)),dw.lean_theorem,certificate_digest=_typed_certificate_digest(dw))
    record=rc.ClosedRelationFactRecord("fact_dw",fact,"sharded",401,tuple(5000+r for r in range(k)),
        None,None,(32,32*k),(32,32),gather_dim=1)
    rel.dependent_chain_plan.complete=True
    rel.dependent_chain_plan.relation_facts+= (record,)
    before,after=rel.dependent_chain_plan.states
    rel.dependent_chain_plan.states=(before,replace(after,fact_ids=after.fact_ids+("fact_dw",)))
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,transition_ids=seg.transition_ids+(tr.transition_id,)),)
    rel.transition_specs+=(tr,);rel.certificates+=(dw,)
    return ir,rel


def test_column_dual_uses_shared_dynamic_value_backend():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=dual_fixture()
    source=render_closed_segment(ir,rel,"segment_000000")
    assert THEOREM in source
    assert "bw_linear_dw_isplit_dim2_4_1_8_32_g214" in source


def test_column_dual_preserves_dw_rank_boundary():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=dual_fixture(3)
    with pytest.raises(ValueError):
        render_closed_segment(ir,rel,"segment_000000")


def test_column_dual_production_header_imports_theorem():
    from trainverify.bridge_emitter.composer import compose_closed_dependent_bundle
    ir,rel=dual_fixture()
    from dataclasses import replace
    old=rel.dependent_chain_plan
    anchor=rc.ClosedTensorShapeFactRecord("anchor","sm",100,(1,8,32),100)
    states=tuple(replace(s,fact_ids=(*s.fact_ids,"anchor")) for s in old.states)
    rel.dependent_chain_plan=rc.ClosedDependentChainPlan(
        relation_facts=old.relation_facts,authority_facts=(),anchor_fact=anchor,
        states=states,segments=old.segments,initial_state_id=states[0].state_id,terminal_state_id=states[1].state_id,
        terminal_target_fact_id="fact_out",retained_target_fact_ids=("fact_out",),
        expected_sm_node_count=1,expected_pm_node_count=4)
    ir.public_statement_module="denote.GeneratedKRankBWLinearDxColumnWitness"
    bundle=compose_closed_dependent_bundle(ir,rel,"ColumnHeaderAudit","denote.ColumnHeaderAudit",include_public=False,require_full_graph=False)
    segments=[v.decode() for p,v in bundle.items() if p.startswith("Segment")]
    assert segments and any("import denote.KRankBWLinearDxColumn\n" in s and THEOREM in s for s in segments)


def dual_witness_source():
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_column_dual_renderer import render_closed_k_rank_bw_linear_column_dual_segment
    ir,rel=dual_fixture()
    return fixture_source(ir,rel,render_closed_k_rank_bw_linear_column_dual_segment).replace("SyntheticBWLayernorm","SyntheticBWLinearDxColumn").replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDxColumn")


@pytest.mark.parametrize("mutation",("rank","pairing","record-shape","parameters","digest","type"))
def test_column_renderer_rejects_coherent_payload_mutations(mutation):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.bw_linear_dx_column_renderer import render_closed_k_rank_bw_linear_dx_column_segment
    ir,rel=renderer_fixture()
    cert=rel.certificates[0]
    tr=rel.transition_specs[0]
    if mutation=="rank": cert=replace(cert,rank_count=2)
    elif mutation=="pairing": cert=replace(cert,pm_step_ids=tuple(reversed(cert.pm_step_ids)))
    elif mutation=="record-shape":
        rel.dependent_chain_plan.relation_facts=tuple(replace(f,full_shape=(1,7,96)) if f.fact_id=="fact_x" else f for f in rel.dependent_chain_plan.relation_facts)
    elif mutation=="parameters": ir.pm_nodes[1].params=(2,)
    elif mutation=="type": cert=SimpleNamespace(**cert.__dict__)
    rel.certificates=(cert,)
    if mutation=="type": pass
    elif mutation=="digest": tr=replace(tr,certificate_digest="0"*64)
    else: tr=replace(tr,certificate_digest=_typed_certificate_digest(cert))
    rel.transition_specs=(tr,)
    with pytest.raises(ValueError):
        render_closed_k_rank_bw_linear_dx_column_segment(ir,rel,"segment_000000")
