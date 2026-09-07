"""Coherent source-axis mutations must fail at every migrated consumer."""
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter import parser as p, relation_compiler as rc
from trainverify.bridge_emitter.composer import render_closed_segment, _typed_certificate_digest


@pytest.fixture(scope="module")
def real_relation():
    from trainverify.bridge_emitter.proof_compiler import compile_proof_plan,build_default_registry
    names=("DENOTE_DIR","GEN_DIR","GEN_FILE","MOD_PREFIX")
    old={name:getattr(p,name) for name in names}
    try:
        p.DENOTE_DIR=p.GEN_DIR="trainverify/denote/gpt_ly4_regen"
        p.GEN_FILE="GeneratedData.lean";p.MOD_PREFIX="denote.gpt_ly4_regen"
        ir=p.load_goal_ir(107,str(Path(__file__).resolve().parents[2]))
        rel=rc.compile_relation_plan(ir,compile_proof_plan(ir,build_default_registry()))
        return ir,rel
    finally:
        for name,value in old.items():setattr(p,name,value)


def mutate_output_axis(rel,c):
    old=c.output_fact;new=replace(old,gather_dim=2 if old.gather_dim==1 else 1)
    changed=replace(c,output_fact=new)
    rel.certificates=tuple(changed if item is c else item for item in rel.certificates)
    rel.transition_specs=tuple(replace(t,post_facts=(new,),certificate_digest=_typed_certificate_digest(changed)) if t.rule_id==c.rule_id and t.post_facts==(old,) else t for t in rel.transition_specs)
    chain=rel.dependent_chain_plan
    rel.dependent_chain_plan=SimpleNamespace(**(vars(chain)|{"complete":chain.complete,"relation_facts":tuple(replace(r,source=new) if r.source==old else r for r in chain.relation_facts)}))


def add_linear_dw(ir,rel,sid):
    """Add the other projection of the already-present exact BW_linear writers."""
    chain=rel.dependent_chain_plan
    seg=next(s for s in chain.segments if s.segment_id==sid)
    ts={t.transition_id:t for t in rel.transition_specs}
    lt=next(ts[i] for i in seg.transition_ids if ts[i].rule_id=="bw-linear-dx-sequence-sharded-k-rank")
    lc=next(c for c in rel.certificates if type(c) is rc.KRankBWLinearDxCertificate and c.sm_step_id==f"sm:{lt.sm_node_indices[0]}:0" and c.pm_step_ids==tuple(f"pm:{i}:0" for i in lt.pm_node_indices))
    g,x,w=lc.input_facts
    sm=ir.sm_nodes[lt.sm_node_indices[0]];pm=[ir.pm_nodes[i] for i in lt.pm_node_indices]
    refs=(f"sm:{lt.sm_node_indices[0]}:1",*(f"pm:{i}:1" for i in lt.pm_node_indices))
    out=rc.RelationFactSpec("reduction",refs)
    c=rc.KRankBWLinearDwReductionCertificate("bw-linear-dw-sequence-reduction-k-rank",4,1,g,x,w,out,refs[0],refs[1:],"TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3")
    tr=rc.CertificateTransitionSpec("test_dw_projection",c.rule_id,tuple(sorted((g,x,w))),(out,),lt.sm_node_indices,lt.pm_node_indices,c.lean_theorem,certificate_digest=_typed_certificate_digest(c))
    record=rc.ClosedRelationFactRecord("test_dw_fact",out,"reduction",sm.outs[1],tuple(n.outs[1] for n in pm),None,None,(32,32),(32,32))
    rel.certificates+= (c,);rel.transition_specs+=(tr,)
    chain=replace(chain,relation_facts=chain.relation_facts+(record,),
        states=tuple(replace(st,fact_ids=st.fact_ids+(record.fact_id,)) if st.state_id==seg.post_state_id else st for st in chain.states),
        segments=tuple(replace(s,transition_ids=s.transition_ids+(tr.transition_id,)) if s.segment_id==sid else s for s in chain.segments))
    rel.dependent_chain_plan=chain


@pytest.mark.parametrize("case",("linear-head","linear-head-dual","transpose-softmax","reconstruction-softmax"))
def test_mixed_source_axis_agreement(real_relation,case):
    ir,rel=deepcopy(real_relation)
    rel=SimpleNamespace(**vars(rel))
    sid={"linear-head":"segment_000223","linear-head-dual":"segment_000223","transpose-softmax":"segment_000217","reconstruction-softmax":"segment_000348"}[case]
    if case=="linear-head-dual":add_linear_dw(ir,rel,sid)
    assert render_closed_segment(ir,rel,sid)
    seg=next(s for s in rel.dependent_chain_plan.segments if s.segment_id==sid)
    ts={t.transition_id:t for t in rel.transition_specs}
    cls=rc.KRankBWMatmulCertificate if case.startswith("linear") else rc.KRankBWSoftmaxCertificate
    t=next(ts[i] for i in seg.transition_ids if ts[i].rule_id.startswith("bw-matmul-head" if case.startswith("linear") else "bw-softmax"))
    c=next(c for c in rel.certificates if type(c) is cls and c.rule_id==t.rule_id and c.output_fact==t.post_facts[0])
    mutate_output_axis(rel,c)
    with pytest.raises(ValueError):render_closed_segment(ir,rel,sid)


def test_singleton_softmax_source_axis_agreement():
    from scripts.tests.test_k_rank_bw_softmax_general import renderer_fixture
    ir,rel=renderer_fixture()
    assert render_closed_segment(ir,rel,"segment_000000")
    mutate_output_axis(rel,rel.certificates[0])
    with pytest.raises(ValueError):render_closed_segment(ir,rel,"segment_000000")
