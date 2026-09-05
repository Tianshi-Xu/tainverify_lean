from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import relation_compiler as rc

RULE = "bw-multiref-sum-sharded-k-rank"
THEOREM = "TrainVerify.Denote.tensorSum_allGather_dim_K"


def matcher_fixture(k=3, arity=2, dim=1, shard=(2, 3, 7)):
    full = tuple(x*k if i == dim else x for i, x in enumerate(shard))
    def step(sid, side, rank, shape, refs=(), op="input"):
        return SimpleNamespace(step_id=sid, side=side, rank=rank, op=op,
            parameters=(), output_projection="", output_shape=shape,
            input_shapes=tuple(shape for _ in refs), input_bindings=refs)
    inputs = tuple(step(f"sm:in:{j}", "sm", 0, full) for j in range(arity))
    pieces = tuple(tuple(step(f"pm:in:{j}:{r}", "pm", r, shard)
                         for r in range(k)) for j in range(arity))
    sm = step("sm:0:0", "sm", 0, full, tuple(x.step_id for x in inputs), "BW_multiref")
    pms = tuple(step(f"pm:{r}:0", "pm", r, shard,
                    tuple(xs[r].step_id for xs in pieces), "BW_multiref") for r in range(k))
    plan = SimpleNamespace(steps=(*inputs, *(x for xs in pieces for x in xs), sm, *pms))
    return plan, (sm.step_id, *(x.step_id for x in pms))


@pytest.mark.parametrize("k,arity,dim", [(3, 2, 1), (5, 3, 2), (3, 5, 1)])
def test_multiref_matcher_derives_ordered_k_shape_and_sum_arity(k, arity, dim):
    plan, frontier = matcher_fixture(k, arity, dim)
    certs, _, _ = rc.advance_k_rank_bw_multiref_sum_frontiers(plan, (frontier,), ("sharded",))
    assert len(certs) == 1
    cert = certs[0]
    assert (cert.rule_id, cert.lean_theorem, cert.rank_count) == (RULE, THEOREM, k)
    assert cert.shard_shape == (2, 3, 7)
    assert cert.full_shape == tuple(x*k if i == dim else x for i,x in enumerate((2,3,7)))
    assert cert.pm_step_ids == tuple(f"pm:{r}:0" for r in range(k))
    assert len(cert.input_facts) == arity


def renderer_fixture(k=3, arity=2, dim=1, shard=(2,3,7)):
    from dataclasses import replace
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    plan, frontier = matcher_fixture(k,arity,dim,shard)
    cert = rc.advance_k_rank_bw_multiref_sum_frontiers(plan,(frontier,),("sharded",))[0][0]
    facts = tuple(rc.ClosedRelationFactRecord(
        f"fi{j}", src, "sharded", 100+j, tuple(1000+100*j+r for r in range(k)),
        None, None, cert.full_shape, shard, gather_dim=dim)
        for j,src in enumerate(cert.input_facts))
    out = rc.ClosedRelationFactRecord("fo", cert.output_fact, "sharded", 300,
        tuple(9000+r for r in range(k)),None,None,cert.full_shape,shard,gather_dim=dim)
    before = rc.ClosedRelationStateRecord("state_000000",tuple(f.fact_id for f in facts))
    after = rc.ClosedRelationStateRecord("state_000001",(*before.fact_ids,"fo"))
    tr = replace(rc.CertificateTransitionSpec("tr",RULE,tuple(sorted(cert.input_facts)),
        (cert.output_fact,),(0,),tuple(range(k)),THEOREM),certificate_digest=_typed_certificate_digest(cert))
    seg = rc.ClosedDependentSegmentRecord("segment_000000","component",before.state_id,after.state_id,("tr",),(0,1),(0,k))
    rel = SimpleNamespace(certificates=(cert,),transition_specs=(tr,),dependent_chain_plan=SimpleNamespace(
        relation_facts=(*facts,out),states=(before,after),segments=(seg,)))
    ir = SimpleNamespace(sm_nodes=[Node(0,"BW_multiref",[f.sm_tid for f in facts],[300],[])],
        pm_nodes=[Node(r,"BW_multiref",[f.pm_tids[r] for f in facts],[9000+r],[]) for r in range(k)],
        sm_graph_ref="SyntheticBWMultiref.smGraph",pm_graph_ref="SyntheticBWMultiref.pmGraph")
    return ir,rel


def witness_source(k=3, arity=5, dim=1, shard=(2,3,7)):
    from trainverify.bridge_emitter.bw_multiref_sum_renderer import render_closed_k_rank_bw_multiref_sum_segment as render
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    ir,rel = renderer_fixture(k,arity,dim,shard)
    return fixture_source(ir,rel,render).replace("SyntheticBWLayernorm","SyntheticBWMultiref").replace(
        "import denote.KRankBWLayernorm","import denote.KRankBWMultiref")


@pytest.mark.parametrize("k,arity,dim", [(3,2,1),(5,3,2),(3,5,1)])
def test_multiref_renderer_uses_ordered_generic_sum(k,arity,dim):
    source = witness_source(k,arity,dim)
    assert THEOREM in source
    assert "tensorSumRanks" in source
    assert source.count("private theorem segment_000000_hPmWriter") == k
    assert f"allGatherPrimDimN {dim} {k} 0" in source
    assert "tensorSum_pair_split" not in source


def wred_fixture(k=3, arity=3):
    from dataclasses import replace
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=renderer_fixture(k,arity)
    pre=rc.RelationFactSpec("reduction",("sm:tail",*(f"pm:tail:{r}" for r in range(k))))
    post=rc.RelationFactSpec("joined",("sm:tail",),joined_pm_step=f"pm:{k}:0")
    cert=rc.KRankAllReduceReconstructionCertificate(
        rule_id="cross-dp-wred-reconstruction-k-rank",rank_count=k,full_shape=(7,),input_fact=pre,output_fact=post,
        pm_allreduce_step=f"pm:{k}:0",lean_theorem="TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce")
    pre_rec=rc.ClosedRelationFactRecord("wrpre",pre,"reduction",400,tuple(6000+r for r in range(k)),None,None,(7,),(),gather_dim=None)
    post_rec=rc.ClosedRelationFactRecord("wrpost",post,"joined",400,(),None,None,(7,),(),gather_dim=None,joined_pm_tid=6000)
    tr=replace(rc.CertificateTransitionSpec("wrtr",cert.rule_id,(pre,),(post,),(),(k,),cert.lean_theorem),
        certificate_digest=_typed_certificate_digest(cert))
    chain=rel.dependent_chain_plan
    chain.relation_facts+= (pre_rec,post_rec)
    chain.states=(replace(chain.states[0],fact_ids=(*chain.states[0].fact_ids,"wrpre")),
                  replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,"wrpost")))
    chain.segments=(replace(chain.segments[0],transition_ids=("tr","wrtr"),pm_range=(0,k+1)),)
    rel.certificates+= (cert,);rel.transition_specs+= (tr,)
    ir.pm_nodes.append(Node(0,"CROSS_DP_WRED",list(pre_rec.pm_tids),[6000],[]))
    return ir,rel


def test_multiref_wred_uses_same_generic_value_transport():
    from trainverify.bridge_emitter.bw_multiref_wred_renderer import render_closed_bw_multiref_wred_segment as render
    from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports
    ir,rel=wred_fixture()
    source=render(ir,rel,"segment_000000")
    assert THEOREM in source and "tensorSumRanks" in source
    imports=plan_closed_segment_imports(tuple(t.rule_id for t in rel.transition_specs),tuple(t.lean_theorem for t in rel.transition_specs),rc.CLOSED_RULE_REGISTRY)
    assert "denote.KRankBWMultiref" in imports


@pytest.mark.parametrize("mutation", ["sm_rank","params","projection","input_rank","shape_rank","zero_shape"])
def test_multiref_matcher_rejects_bad_authority(mutation):
    plan,frontier=matcher_fixture()
    by_id={s.step_id:s for s in plan.steps}
    sm=by_id[frontier[0]]
    if mutation=="sm_rank": sm.rank=1
    elif mutation=="params": sm.parameters=(1,)
    elif mutation=="projection": sm.output_projection=".1"
    elif mutation=="input_rank": by_id["pm:in:0:1"].rank=0
    elif mutation=="shape_rank": by_id[frontier[1]].output_shape=(2,3)
    else:
        for step in plan.steps: step.output_shape=(0,*step.output_shape[1:])
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_multiref_sum_frontiers(plan,(frontier,),("sharded",))


@pytest.mark.parametrize("wred", [False,True])
@pytest.mark.parametrize("mutation", ["rank","params","pairing","certificate_shape","digest","full_shape"])
def test_multiref_renderers_reject_tampered_authority(wred,mutation):
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.bw_multiref_sum_renderer import render_closed_k_rank_bw_multiref_sum_segment
    from trainverify.bridge_emitter.bw_multiref_wred_renderer import render_closed_bw_multiref_wred_segment
    ir,rel=wred_fixture() if wred else renderer_fixture()
    if mutation=="rank": ir.pm_nodes[1].rank=0
    elif mutation=="params": ir.pm_nodes[0].params=[1]
    elif mutation=="pairing": ir.pm_nodes[0].ins.reverse()
    elif mutation=="certificate_shape":
        cert=replace(rel.certificates[0],full_shape=(2,99,7))
        rel.certificates=(cert,*rel.certificates[1:])
        rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(cert)),*rel.transition_specs[1:])
    elif mutation=="digest": rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest="0"*64),*rel.transition_specs[1:])
    elif mutation=="full_shape":
        cert=replace(rel.certificates[0],full_shape=(2,10,7))
        rel.certificates=(cert,*rel.certificates[1:])
        rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(cert)),*rel.transition_specs[1:])
        rel.dependent_chain_plan.relation_facts=tuple(replace(f,full_shape=(2,10,7)) if f.kind=="sharded" else f for f in rel.dependent_chain_plan.relation_facts)
    render=render_closed_bw_multiref_wred_segment if wred else render_closed_k_rank_bw_multiref_sum_segment
    with pytest.raises(ValueError): render(ir,rel,"segment_000000")


def test_multiref_committed_source_matches_generator():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedKRankBWMultirefWitness.lean"
    assert path.read_text()==witness_source()


def repeated_operand_fixture():
    from dataclasses import replace
    from trainverify.bridge_emitter.bw_multiref_sum_renderer import render_closed_k_rank_bw_multiref_sum_segment as render
    ir,rel=renderer_fixture()
    cert=rel.certificates[0]
    cert=replace(cert,input_facts=(cert.input_facts[0],cert.input_facts[0]))
    rel.certificates=(cert,)
    tr=rc.build_certificate_transition_specs(None,(cert,))[0]
    rel.transition_specs=(replace(tr,transition_id="tr"),)
    for node in (*ir.sm_nodes,*ir.pm_nodes): node.ins=[node.ins[0],node.ins[0]]
    return ir,rel



def test_multiref_repeated_operand_multiplicity_survives_transition_set():
    from trainverify.bridge_emitter.bw_multiref_sum_renderer import render_closed_k_rank_bw_multiref_sum_segment as render
    ir,rel=repeated_operand_fixture()
    source=render(ir,rel,"segment_000000")
    assert "tensorSum [smFinal 100, smFinal 100]" in source


def test_multiref_wred_production_header_contains_theorem_import():
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import compose_closed_dependent_bundle
    ir,rel=wred_fixture()
    old=rel.dependent_chain_plan
    anchor=rc.ClosedTensorShapeFactRecord("anchor","sm",100,(2,9,7),100)
    states=tuple(replace(s,fact_ids=(*s.fact_ids,"anchor")) for s in old.states)
    rel.dependent_chain_plan=rc.ClosedDependentChainPlan(
        relation_facts=old.relation_facts,authority_facts=(),anchor_fact=anchor,
        states=states,segments=old.segments,initial_state_id=states[0].state_id,terminal_state_id=states[1].state_id,
        terminal_target_fact_id="fo",retained_target_fact_ids=("fo",),
        expected_sm_node_count=1,expected_pm_node_count=4)
    ir.public_statement_module="denote.GeneratedKRankBWMultirefWitness"
    bundle=compose_closed_dependent_bundle(ir,rel,"MultirefHeaderAudit","denote.MultirefHeaderAudit",include_public=False,require_full_graph=False)
    segments=[v.decode() for p,v in bundle.items() if p.startswith("Segment")]
    assert segments and any("import denote.KRankBWMultiref\n" in s and THEOREM in s for s in segments)
