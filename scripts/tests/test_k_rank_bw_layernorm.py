from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter.parser import LineageGoal
from trainverify.bridge_emitter import relation_compiler as rc


RULE = "bw-layernorm-dx-dim1-k-rank"
THEOREM = "TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d"


def matcher_fixture(k, b=1, s=2, d=32):
    full, shard = (b, s * k, d), (b, s, d)
    sm = SimpleNamespace(
        step_id="sm:0:0", side="sm", rank=0, op="BW_layernorm",
        output_projection=".1", parameters=(),
        input_bindings=("sm:g", "sm:x", "init:700", "init:701"),
        input_shapes=(full, full, (d,), (d,)), output_shape=full,
    )
    pms = tuple(SimpleNamespace(
        step_id=f"pm:{r}:0", side="pm", rank=r, op="BW_layernorm",
        output_projection=".1", parameters=(),
        input_bindings=(f"pm:g:{r}", f"pm:x:{r}", "init:700", "init:701"),
        input_shapes=(shard, shard, (d,), (d,)), output_shape=shard,
    ) for r in range(k))
    ir = SimpleNamespace(init_lineages={
        tid: LineageGoal(tid, [d], [(0, tid)], [[d]]) for tid in (700, 701)
    })
    return SimpleNamespace(steps=(sm, *pms)), ir, (sm.step_id, *(p.step_id for p in pms))


@pytest.mark.parametrize("k,b,s,d", [(3, 1, 2, 32), (5, 2, 3, 7), (4, 1, 2, 32)])
def test_layernorm_dx_matcher_derives_k_and_symbolic_shape(k, b, s, d):
    plan, ir, frontier = matcher_fixture(k, b, s, d)
    certs, _, _ = rc.advance_k_rank_bw_layernorm_dx_frontiers(plan, ir, (frontier,), ("sharded",))
    assert len(certs) == 1
    cert = certs[0]
    assert (cert.rule_id, cert.lean_theorem, cert.rank_count) == (RULE, THEOREM, k)
    assert cert.full_shape == (b, s * k, d)
    assert cert.shard_shape == (b, s, d)
    assert cert.pm_step_ids == tuple(f"pm:{r}:0" for r in range(k))


def renderer_fixture(k, b=1, s=2, d=32):
    from dataclasses import replace
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    plan, ir, frontier = matcher_fixture(k, b, s, d)
    cert = rc.advance_k_rank_bw_layernorm_dx_frontiers(plan, ir, (frontier,), ("sharded",))[0][0]
    full, shard = (b, s*k, d), (b, s, d)
    def fact(name, src, tid, tids, shape, piece, dim):
        return rc.ClosedRelationFactRecord(name, src, src.layout, tid, tids,
                                          None, None, shape, piece, gather_dim=dim if src.layout == "sharded" else None)
    facts = (
        fact("fg", cert.gradient_fact, 100, tuple(1000+r for r in range(k)), full, shard, 1),
        fact("fx", cert.activation_fact, 200, tuple(2000+r for r in range(k)), full, shard, 1),
        fact("fw", cert.gamma_fact, 700, (700,), (d,), (d,), 0),
        fact("fb", cert.beta_fact, 701, (701,), (d,), (d,), 0),
        fact("fo", cert.output_fact, 300, tuple(3000+r for r in range(k)), full, shard, 1),
    )
    before = rc.ClosedRelationStateRecord("before", tuple(f.fact_id for f in facts[:-1]))
    after = rc.ClosedRelationStateRecord("after", tuple(f.fact_id for f in facts))
    transition = replace(rc.CertificateTransitionSpec(
        "tr", RULE, tuple(sorted((cert.gradient_fact, cert.activation_fact, cert.gamma_fact, cert.beta_fact))),
        (cert.output_fact,), (0,), tuple(range(k)), THEOREM), certificate_digest=_typed_certificate_digest(cert))
    seg = rc.ClosedDependentSegmentRecord("segment_000000", "component", "before", "after", ("tr",), (0,1), (0,k))
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,),
        dependent_chain_plan=SimpleNamespace(relation_facts=facts, states=(before,after), segments=(seg,)))
    ir.sm_nodes = [Node(0, "BW_layernorm", [100,200,700,701], [300,301,302], [])]
    ir.pm_nodes = [Node(r, "BW_layernorm", [1000+r,2000+r,700,701], [3000+r,4000+r,5000+r], []) for r in range(k)]
    ir.sm_graph_ref="SyntheticBWLayernorm.smGraph";ir.pm_graph_ref="SyntheticBWLayernorm.pmGraph"
    return ir, relation


def witness_source(k=3, b=2, s=3, d=7):
    from trainverify.bridge_emitter.composer import _node_text
    from trainverify.bridge_emitter.bw_layernorm_dx_renderer import render_closed_k_rank_bw_layernorm_dx_segment
    ir, rel = renderer_fixture(k,b,s,d)
    return fixture_source(ir, rel, render_closed_k_rank_bw_layernorm_dx_segment)


def fixture_source(ir, rel, render, *, pm_num_ranks=None):
    from trainverify.bridge_emitter.composer import _node_text
    k = len(ir.pm_nodes) if pm_num_ranks is None else pm_num_ranks
    lines = ["import denote.RelationCompiler", "import denote.KRankBWLayernorm",
             "open TrainVerify.Denote TrainVerify.Denote.RelationCompiler",
             "namespace SyntheticBWLayernorm", "noncomputable section"]
    for side, nodes, n in (("sm",ir.sm_nodes,1),("pm",ir.pm_nodes,k)):
        lines.append(f"def {side}Graph : GraphDecl := {{ numRanks := {n}, nodes := [{', '.join(_node_text(x) for x in nodes)}] }}")
    for f in rel.dependent_chain_plan.relation_facts:
        if f.kind == "joined":
            lines.append(f"def {f.fact_id} : RelationFact := .joined {f.sm_tid} {f.joined_pm_tid} {list(f.full_shape)}")
        elif f.kind == "reduction":
            lines.append(f"def {f.fact_id} : RelationFact := .reduction {f.sm_tid} {list(f.pm_tids)} {list(f.full_shape)}")
        else:
            lines.append(f"def {f.fact_id} : RelationFact := .sharded {f.sm_tid} {list(f.pm_tids)} {f.gather_dim} {list(f.full_shape)} {list(f.shard_shape)}")
    for state in rel.dependent_chain_plan.states:
        lines.append(f"def {state.state_id} : RelationState where\n  facts := [{', '.join(state.fact_ids)}]\n  nonempty := by decide")
    lines.append(render(ir,rel,"segment_000000"))
    lines += ["#print axioms segment_000000", "end", "end SyntheticBWLayernorm", ""]
    return "\n".join(lines)


def test_layernorm_dx_renderer_uses_dynamic_lists_and_shape():
    from trainverify.bridge_emitter.bw_layernorm_dx_renderer import render_closed_k_rank_bw_layernorm_dx_segment
    ir, rel = renderer_fixture(3,2,3,7)
    source = render_closed_k_rank_bw_layernorm_dx_segment(ir,rel,"segment_000000")
    assert THEOREM in source
    assert "allGatherPrimDimN 1 3 0" in source
    assert "allGatherPrimDimN 1 4 0" not in source
    assert "[2, 9, 7]" in source and "[2, 3, 7]" in source
    assert source.count("private theorem segment_000000_hPmWriter") == 3


@pytest.mark.parametrize("mutation", ["ranks", "params", "full_extent", "param_shape", "projection"])
def test_layernorm_dx_matcher_rejects_invalid_authority(mutation):
    plan, ir, frontier = matcher_fixture(3)
    if mutation == "ranks":
        plan.steps[2].rank = 0
    elif mutation == "params":
        plan.steps[1].parameters = (1,)
    elif mutation == "full_extent":
        plan.steps[0].output_shape = (1,8,32)
    elif mutation == "param_shape":
        ir.init_lineages[700].tsShape = [31]
    else:
        plan.steps[1].output_projection = ".2.1"
        assert not rc.advance_k_rank_bw_layernorm_dx_frontiers(plan,ir,(frontier,),("sharded",))[0]
        return
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_layernorm_dx_frontiers(plan,ir,(frontier,),("sharded",))


@pytest.mark.parametrize("mutation", ["rank", "pairing", "full_extent", "digest", "shape_certificate", "projection", "params"])
def test_layernorm_dx_renderer_rejects_invalid_authority(mutation):
    from dataclasses import replace
    from trainverify.bridge_emitter.bw_layernorm_dx_renderer import render_closed_k_rank_bw_layernorm_dx_segment as render
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir, rel = renderer_fixture(3,2,3,7)
    if mutation == "rank":
        ir.pm_nodes[1].rank = 0
    elif mutation == "pairing":
        ir.pm_nodes[1].ins[1],ir.pm_nodes[2].ins[1] = ir.pm_nodes[2].ins[1],ir.pm_nodes[1].ins[1]
    elif mutation == "full_extent":
        rel.dependent_chain_plan.relation_facts = tuple(replace(f, full_shape=(2,10,7)) if f.fact_id in {"fg","fx","fo"} else f for f in rel.dependent_chain_plan.relation_facts)
    elif mutation in {"digest", "shape_certificate"}:
        cert = replace(rel.certificates[0], shard_shape=(1,3,7))
        rel.certificates=(cert,)
        if mutation == "shape_certificate":
            rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(cert)),)
    elif mutation == "projection":
        ir.pm_nodes[1].outs[0],ir.pm_nodes[1].outs[1]=ir.pm_nodes[1].outs[1],ir.pm_nodes[1].outs[0]
    else:
        ir.pm_nodes[1].params = [1]
    with pytest.raises(ValueError):
        render(ir,rel,"segment_000000")


def test_layernorm_dx_witness_matches_committed_exact_source():
    from pathlib import Path
    path = Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedKRankBWLayernormWitness.lean"
    assert path.read_text() == witness_source()


def triple_fixture():
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir, rel = renderer_fixture(4)
    dx=rel.certificates[0]; pre=rel.transition_specs[0].pre_facts
    certs=list(rel.certificates); trans=list(rel.transition_specs); facts=list(rel.dependent_chain_plan.relation_facts)
    for i,name,projection in ((1,"dgamma",".2.1"),(2,"dbeta",".2.2")):
        output=rc.RelationFactSpec("reduction",(f"sm:0:{i}",*(f"pm:{r}:{i}" for r in range(4))))
        theorem=f"TrainVerify.Denote.bw_layernorm_{'dw' if i==1 else 'db'}_dp_split_dim1_4_1_2_32"
        cert=rc.KRankBWLayernormParamReductionCertificate(
            rule_id=f"bw-layernorm-{name}-reduction-rank4",projection=projection,rank_count=4,
            gradient_fact=dx.gradient_fact,activation_fact=dx.activation_fact,gamma_fact=dx.gamma_fact,beta_fact=dx.beta_fact,
            output_fact=output,sm_step_id=f"sm:0:{i}",pm_step_ids=tuple(f"pm:{r}:{i}" for r in range(4)),lean_theorem=theorem)
        certs.append(cert)
        trans.append(replace(rel.transition_specs[0],transition_id=name,rule_id=cert.rule_id,post_facts=(output,),lean_theorem=theorem,certificate_digest=_typed_certificate_digest(cert)))
        facts.append(rc.ClosedRelationFactRecord(name,output,"reduction",300+i,tuple(ir.pm_nodes[r].outs[i] for r in range(4)),None,None,(32,),(32,)))
    rel.certificates=tuple(certs);rel.transition_specs=tuple(trans)
    chain=rel.dependent_chain_plan
    chain.relation_facts=tuple(facts)
    chain.states=(chain.states[0],replace(chain.states[1],fact_ids=tuple(f.fact_id for f in facts)))
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in trans)),)
    return ir,rel


def test_layernorm_triple_keeps_rank4_parameter_contract_and_uses_dynamic_dx():
    from trainverify.bridge_emitter.bw_layernorm_triple_renderer import render_closed_k_rank_bw_layernorm_triple_segment as render
    from trainverify.bridge_emitter.compound_rule_dispatch import select_compound_renderer
    from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports
    ir,rel=triple_fixture()
    assert select_compound_renderer(tuple(t.rule_id for t in rel.transition_specs)) == "bw_layernorm_triple_renderer:render_closed_k_rank_bw_layernorm_triple_segment"
    source=render(ir,rel,"segment_000000")
    assert THEOREM in source
    assert "bw_layernorm_dw_dp_split_dim1_4_1_2_32" in source
    assert "bw_layernorm_db_dp_split_dim1_4_1_2_32" in source
    assert "denote.KRankBWLayernorm" in plan_closed_segment_imports(
        tuple(t.rule_id for t in rel.transition_specs), tuple(t.lean_theorem for t in rel.transition_specs), rc.CLOSED_RULE_REGISTRY)


def test_layernorm_dx_width_one_preserves_real_singleton_reduction_authority():
    from trainverify.bridge_emitter.bw_layernorm_dx_renderer import render_closed_k_rank_bw_layernorm_dx_segment as render
    ir,rel=renderer_fixture(3,2,3,1)
    gamma=next(f for f in rel.dependent_chain_plan.relation_facts if f.fact_id=="fw")
    assert gamma.kind == gamma.source.layout == "reduction"
    source=render(ir,rel,"segment_000000")
    assert "ReductionRel" in source
    assert THEOREM in source


def test_layernorm_triple_production_bundle_header_has_dynamic_theorem_import():
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import compose_closed_dependent_bundle
    ir,rel=triple_fixture()
    old=rel.dependent_chain_plan
    anchor=rc.ClosedTensorShapeFactRecord("anchor", "sm", 700, (32,), 700)
    states=tuple(replace(s, state_id=f"state_{i:06d}", fact_ids=(*s.fact_ids,"anchor")) for i,s in enumerate(old.states))
    segments=(replace(old.segments[0],pre_state_id=states[0].state_id,post_state_id=states[1].state_id),)
    rel.dependent_chain_plan=rc.ClosedDependentChainPlan(
        relation_facts=old.relation_facts, authority_facts=(), anchor_fact=anchor,
        states=states, segments=segments, initial_state_id=states[0].state_id,terminal_state_id=states[1].state_id,
        terminal_target_fact_id="fo",retained_target_fact_ids=("fo",),
        expected_sm_node_count=1,expected_pm_node_count=4)
    ir.public_statement_module="denote.GeneratedKRankBWLayernormWitness"
    bundle=compose_closed_dependent_bundle(ir,rel,"TripleHeaderAudit","denote.TripleHeaderAudit",include_public=False,require_full_graph=False)
    segments=[v.decode() for p,v in bundle.items() if p.startswith("Segment")]
    assert segments
    assert any("import denote.KRankBWLayernorm\n" in v and THEOREM in v for v in segments)
