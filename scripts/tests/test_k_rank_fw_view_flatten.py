from dataclasses import replace
import pytest
from scripts.tests.test_k_rank_bw_view_flatten import matcher_fixture as bw_matcher_fixture, renderer_fixture as bw_renderer_fixture
from trainverify.bridge_emitter import relation_compiler as rc


def matcher_fixture(k=2,b=1,s=16,n=2,d=16,axis=2):
    plan,f=bw_matcher_fixture(k,b,s,n,d,axis=axis)
    for step in plan.steps:
        step.op="FW_view";step.input_bindings=step.input_bindings[:1];step.input_shapes=step.input_shapes[:1]
    return plan,f


@pytest.mark.parametrize("axis",(1,2))
@pytest.mark.parametrize("case",((2,1,16,2,16),(4,1,16,1,16),(3,2,5,3,7)))
def test_forward_flatten_uses_shared_semantics(case,axis):
    plan,f=matcher_fixture(*case,axis=axis)
    certs,_,_=rc.advance_k_rank_bw_view_flatten_frontiers(plan,(f,),("sharded",))
    assert len(certs)==1
    assert certs[0].rule_id==f"fw-view-flatten-{'sequence' if axis==1 else 'head'}-sharded-k-rank"
    assert certs[0].input_fact.gather_dim==axis


def renderer_fixture(axis=2):
    ir,rel=bw_renderer_fixture(axis=axis)
    for node in (*ir.sm_nodes,*ir.pm_nodes): node.op="FW_view";node.ins=node.ins[:1]
    c=rel.certificates[0]
    c=replace(c,rule_id=c.rule_id.replace("bw-view","fw-view"))
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    rel.certificates=(c,);rel.transition_specs=(replace(rel.transition_specs[0],rule_id=c.rule_id,certificate_digest=_typed_certificate_digest(c)),)
    return ir,rel


@pytest.mark.parametrize("axis",(1,2))
def test_forward_flatten_registered_renderer(axis):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel=renderer_fixture(axis)
    src=render_closed_segment(ir,rel,"segment_000000")
    assert "applyNode_fw_view_out" in src
    assert "applyNode_bw_view_out" not in src


@pytest.mark.parametrize("mutation",("params","shape","rank"))
def test_forward_flatten_rejects_malformed(mutation):
    plan,f=matcher_fixture()
    sm,*pms=plan.steps
    if mutation=="params": pms[0].parameters=(1,16,31)
    elif mutation=="shape": pms[0].output_shape=(1,16,31)
    else: pms[1].rank=0
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_view_flatten_frontiers(plan,(f,),("sharded",))


def witness_source():
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.composer import render_closed_segment
    sources=[]
    for axis in (1,2):
        ir,rel=renderer_fixture(axis)
        src=fixture_source(ir,rel,render_closed_segment).replace("SyntheticBWLayernorm","SyntheticBWSum").replace("import denote.KRankBWLayernorm","import denote.KRankViewFlatten")
        sources.append(src.replace("SyntheticBWSum",f"FWViewFlattenAxis{axis}"))
    imports=list(dict.fromkeys(line for src in sources for line in src.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in src.splitlines() if not line.startswith("import ")) for src in sources)+"\n"


def test_fw_flatten_checked_in_witness():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedFWViewFlattenWitness.lean"
    assert path.read_text()==witness_source()


@pytest.mark.parametrize("backward",(False,True))
def test_flatten_source_record_axis_agreement(backward):
    from trainverify.bridge_emitter.composer import render_closed_segment
    from scripts.tests.test_migrated_source_axis_agreement import mutate_output_axis
    ir,rel=bw_renderer_fixture() if backward else renderer_fixture()
    assert render_closed_segment(ir,rel,"segment_000000")
    mutate_output_axis(rel,rel.certificates[0])
    with pytest.raises(ValueError,match="view source/record axis mismatch"):
        render_closed_segment(ir,rel,"segment_000000")
