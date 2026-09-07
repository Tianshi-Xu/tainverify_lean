from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import LineageGoal

RULE="bw-linear-dx-column-sharded-k-rank"
THEOREM="TrainVerify.Denote.bw_linear_dx_column_allGather_rank3"


def matcher_fixture(k=3,o=32,d=32,*,b=1,s=8):
    full=(b,s,d*k); shard=(b,s,d); fw=(o,d*k); sw=(o,d); gradient=(b,s,o)
    sm=SimpleNamespace(step_id="sm:0:0",op="BW_linear",side="sm",rank=0,
        output_projection=".1",parameters=(),input_bindings=("sm:g:0","sm:x:0","init:700"),
        input_shapes=(gradient,full,fw),output_shape=full)
    pms=tuple(SimpleNamespace(step_id=f"pm:{r}:0",op="BW_linear",side="pm",rank=r,
        output_projection=".1",parameters=(),input_bindings=("pm:g:shared",f"pm:x:{r}",f"init:{701+r}"),
        input_shapes=(gradient,shard,sw),output_shape=shard) for r in range(k))
    ir=SimpleNamespace(init_lineages={700:LineageGoal(700,list(fw),[(r,701+r) for r in range(k)],
        [list(sw) for _ in range(k)],gatherDim=1)})
    return SimpleNamespace(steps=(sm,*pms)),ir,(sm.step_id,*(p.step_id for p in pms))


@pytest.mark.parametrize("case",((2,1,16,64,32),(4,1,16,64,16),(3,2,5,7,11),(1,3,2,1,4),(5,2,1,3,2)))
def test_column_general_batch_sequence_matcher(case):
    k,b,s,o,d=case
    plan,ir,f=matcher_fixture(k,o,d,b=b,s=s)
    certs,_,_=rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(f,),("sharded",))
    assert certs[0].lean_theorem=="TrainVerify.Denote.bw_linear_dx_column_allGather_rank3"


def test_column_general_batch_sequence_renderer():
    from trainverify.bridge_emitter.bw_linear_dx_column_renderer import render_closed_k_rank_bw_linear_dx_column_segment
    ir,rel=renderer_fixture(3,7,11,b=2,s=5)
    source=render_closed_k_rank_bw_linear_dx_column_segment(ir,rel,"segment_000000")
    assert "bw_linear_dx_column_allGather_rank3 3 2 5 7 11" in source


@pytest.mark.parametrize("k",(1,2,3,4,5))
def test_column_matcher_dynamic_rank(k):
    plan,ir,frontier=matcher_fixture(k)
    certs,_,_=rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(frontier,),("sharded",))
    assert len(certs)==1
    c=certs[0]
    assert (c.rule_id,c.lean_theorem,c.rank_count)==(RULE,THEOREM,k)
    assert c.input_facts[2].gather_dim==1


def renderer_fixture(k=3,o=32,d=32,*,b=1,s=8):
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
    records=(replace(g,source=gf,kind="joined",pm_tids=(),joined_pm_tid=1000,full_shape=(b,s,o),shard_shape=(b,s,o),gather_dim=None),
        replace(x,source=xf,kind="sharded",pm_tids=tuple(2000+r for r in range(k)),joined_pm_tid=None,
            full_shape=(b,s,d*k),shard_shape=(b,s,d),gather_dim=2),
        replace(w,source=wf,full_shape=(o,d*k),shard_shape=(o,d),gather_dim=1),
        replace(out,source=of,kind="sharded",gather_dim=2,full_shape=(b,s,d*k),shard_shape=(b,s,d)))
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


def witness_source(k=3,o=32,d=32,*,b=1,s=8):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_dx_column_renderer import render_closed_k_rank_bw_linear_dx_column_segment
    ir,rel=renderer_fixture(k,o,d,b=b,s=s)
    return fixture_source(ir,rel,render_closed_k_rank_bw_linear_dx_column_segment).replace("SyntheticBWLayernorm","SyntheticBWLinearDxColumn").replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDxColumnGeneral")


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


def general_witness_source():
    cases=((1,3,2,1,4),(2,1,16,64,32),(3,2,5,7,11),(4,1,16,64,16),(5,2,1,3,2))
    sources=[witness_source(k,o,d,b=b,s=s).replace("SyntheticBWLinearDxColumn",f"ColumnCase{n}")
             for n,(k,b,s,o,d) in enumerate(cases)]
    imports=list(dict.fromkeys(line for source in sources for line in source.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in source.splitlines() if not line.startswith("import ")) for source in sources)+"\n"


def test_column_general_witness_matches_generator():
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]
    assert (root/"trainverify/denote/GeneratedBWLinearDxColumnGeneralWitness.lean").read_text()==general_witness_source()


def test_column_committed_witness_matches_renderer():
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]
    assert (root/"trainverify/denote/GeneratedKRankBWLinearDxColumnWitness.lean").read_text()==witness_source()


@pytest.mark.parametrize("tail,expected",((('bw-view-joined',),'bw_linear_dx_column_renderer:'),
    (('bw-linear-dw-input-column-sharded-k-rank',),'bw_linear_column_dual_renderer:')))
def test_column_compound_routes_dynamic_identity(tail,expected):
    from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer
    selected=select_bw_compound_renderer((RULE,*tail))
    assert selected is not None and selected.startswith(expected)



def dual_fixture(k=4,o=32,d=32):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=renderer_fixture(k,o,d)
    c=rel.certificates[0];g,x,w=c.input_facts
    fact=rc.RelationFactSpec("sharded",("sm:0:1",*(f"pm:{r}:1" for r in range(k))),gather_dim=1)
    dw=rc.KRankBWLinearDwColumnShardedCertificate("bw-linear-dw-input-column-sharded-k-rank",k,g,x,w,fact,
        "sm:0:1",tuple(f"pm:{r}:1" for r in range(k)),
        "TrainVerify.Denote.bw_linear_dw_input_allGatherPrimDimN_dim2_rank3")
    tr=rc.CertificateTransitionSpec("transition_000001",dw.rule_id,tuple(sorted((g,x,w))),(fact,),
        (0,),tuple(range(k)),dw.lean_theorem,certificate_digest=_typed_certificate_digest(dw))
    record=rc.ClosedRelationFactRecord("fact_dw",fact,"sharded",401,tuple(5000+r for r in range(k)),
        None,None,(o,d*k),(o,d),gather_dim=1)
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
    assert "bw_linear_dw_input_allGatherPrimDimN_dim2_rank3" in source


@pytest.mark.parametrize("k,o,d",((3,7,5),(1,1,1),(5,3,1)))
def test_column_dual_accepts_dw_dynamic_widths(k,o,d):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=dual_fixture(k,o,d)
    assert "bw_linear_dw_input_allGatherPrimDimN_dim2_rank3" in render_closed_segment(ir,rel,"segment_000000")


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
    assert segments and any("import denote.KRankBWLinearDxColumnGeneral\n" in s and "import denote.KRankBWLinearDwColumn\n" in s and THEOREM in s for s in segments)


def dual_witness_source(o=32,d=32):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_column_dual_renderer import render_closed_k_rank_bw_linear_column_dual_segment
    ir,rel=dual_fixture(4,o,d)
    return fixture_source(ir,rel,render_closed_k_rank_bw_linear_column_dual_segment).replace("SyntheticBWLayernorm","SyntheticBWLinearDxColumn").replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDxColumnGeneral\nimport denote.KRankBWLinearDwColumn")


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


@pytest.mark.parametrize("k,o,d",((2,128,8),(3,7,5),(1,1,1),(5,3,1)))
def test_column_variable_width_matcher(k,o,d):
    plan,ir,f=matcher_fixture(k,o,d)
    certs,_,_=rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(f,),("sharded",))
    assert len(certs)==1
    cert=certs[0]
    assert cert.rule_id==RULE
    assert type(cert) is rc.KRankBWLinearDxCertificate
    assert cert.rank_count==k
    assert cert.output_fact.gather_dim==2
    assert cert.lean_theorem==THEOREM


@pytest.mark.parametrize("k,o,d",((2,128,8),(3,7,5),(1,1,1),(5,3,1)))
def test_column_variable_width_renderer(k,o,d):
    source=witness_source(k,o,d)
    assert THEOREM in source
    assert f"{THEOREM} {k} 1 8 {o} {d}" in source

@pytest.mark.parametrize("o,d",((0,5),(7,0),(-1,5),(7,-1)))
def test_column_rejects_nonpositive_widths(o,d):
    plan,ir,f=matcher_fixture(3,o,d)
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_linear_dx_frontiers(plan,ir,(f,),("sharded",))


@pytest.mark.parametrize("o,d",((32,32),(128,8),(32,8)))
def test_column_dual_binds_dw_theorem_to_widths(o,d):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=dual_fixture(4,o,d)
    assert THEOREM in render_closed_segment(ir,rel,"segment_000000")
    wrong="TrainVerify.Denote.bw_linear_dw_isplit_dim2_4_1_8_8_g154" if d==32 or o==128 else "TrainVerify.Denote.bw_linear_dw_isplit_dim2_4_1_8_32_g214"
    cert=replace(rel.certificates[1],lean_theorem=wrong)
    rel.certificates=(rel.certificates[0],cert)
    rel.transition_specs=(rel.transition_specs[0],replace(rel.transition_specs[1],lean_theorem=wrong,certificate_digest=_typed_certificate_digest(cert)))
    with pytest.raises(ValueError):
        render_closed_segment(ir,rel,"segment_000000")


def test_column_collective_changes_select_focused_gates():
    from scripts import incremental_test_selector as selector
    gates=selector.select_gates(("trainverify/bridge_emitter/bw_linear_gather_view_alltoall_renderer.py", "scripts/tests/test_model_authority.py"),family="k-rank-bw-linear-dx-column")
    assert not gates.full_python
    assert "scripts/tests/test_proof_compiler.py::test_gpt_goal107_mixed_linear_collective_tuple_is_atomic" in gates.pytest_nodes


@pytest.mark.parametrize("case",("family","axis","ordered_operands"))
def test_column_rejects_payload_mutation_with_recomputed_digest(case):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=renderer_fixture(3,7,5)
    rel.dependent_chain_plan.complete=True
    c=rel.certificates[0]
    if case=="family": c=replace(c,family="row-reduction")
    if case=="axis": c=replace(c,gather_dim=1)
    if case=="ordered_operands": c=replace(c,input_facts=(c.input_facts[0],c.input_facts[2],c.input_facts[1]))
    rel.certificates=(c,)
    rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(c)),)
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")


def test_column_dual_rejects_dw_operand_permutation_with_recomputed_digest():
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=dual_fixture()
    c=rel.certificates[1]
    c=replace(c,activation_fact=c.weight_fact,weight_fact=c.activation_fact)
    rel.certificates=(rel.certificates[0],c)
    rel.transition_specs=(rel.transition_specs[0],replace(rel.transition_specs[1],certificate_digest=_typed_certificate_digest(c)))
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")


def with_view_fixture(dual=False):
    from dataclasses import replace
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=dual_fixture() if dual else renderer_fixture(3,7,5)
    g=rel.dependent_chain_plan.relation_facts[0];k=rel.certificates[0].rank_count
    fact=rc.RelationFactSpec("joined",("sm:1:0",),joined_pm_step=f"pm:{k}:0")
    c=rc.JoinedBWViewCertificate("bw-view-joined",g.full_shape,g.full_shape,g.source,fact,
        "sm:1:0",f"pm:{k}:0","TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view")
    tr=rc.CertificateTransitionSpec("transition_view",c.rule_id,(g.source,),(fact,),(1,),(k,),c.lean_theorem,certificate_digest=_typed_certificate_digest(c))
    record=replace(g,fact_id="fact_view",source=fact,sm_tid=110,joined_pm_tid=1100)
    ir.sm_nodes.append(Node(0,"BW_view",[g.sm_tid,g.sm_tid],[110],list(g.full_shape)))
    ir.pm_nodes.append(Node(0,"BW_view",[g.joined_pm_tid,g.joined_pm_tid],[1100],list(g.full_shape)))
    chain=rel.dependent_chain_plan
    chain.complete=True;chain.relation_facts+=(record,)
    before,after=chain.states
    chain.states=(before,replace(after,fact_ids=after.fact_ids+(record.fact_id,)))
    seg=chain.segments[0]
    chain.segments=(replace(seg,sm_range=(0,2),pm_range=(0,k+1),transition_ids=seg.transition_ids+(tr.transition_id,)),)
    rel.certificates+=(c,);rel.transition_specs+=(tr,)
    return ir,rel


@pytest.mark.parametrize("dual",(False,True))
@pytest.mark.parametrize("field",("sm_step_id","pm_step_id"))
def test_column_optional_view_writer_identity(dual,field):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import render_closed_segment,_typed_certificate_digest
    ir,rel=with_view_fixture(dual)
    assert THEOREM in render_closed_segment(ir,rel,"segment_000000")
    c=replace(rel.certificates[-1],**{field:"sm:0:0" if field=="sm_step_id" else "pm:0:0"})
    rel.certificates=rel.certificates[:-1]+(c,)
    rel.transition_specs=rel.transition_specs[:-1]+(replace(rel.transition_specs[-1],certificate_digest=_typed_certificate_digest(c)),)
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")
