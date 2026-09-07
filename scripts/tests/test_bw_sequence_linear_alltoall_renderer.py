from dataclasses import replace
import importlib
import pytest
from scripts.tests.bw_sequence_linear_alltoall_witness import renderer_fixture,witness_source,A_THEOREM


def render(ir,rel):
    try: module=importlib.import_module("trainverify.bridge_emitter.bw_sequence_linear_alltoall_renderer")
    except ModuleNotFoundError: pytest.fail("C02 production family has no atomic renderer")
    return module.render_closed_bw_sequence_linear_alltoall_segment(ir,rel,"segment_000000")


@pytest.mark.parametrize("k",(2,3,4))
def test_valid_production_family(k):
    ir,rel=renderer_fixture(k)
    source=render(ir,rel)
    assert A_THEOREM in source
    assert "bw_linear_dw_sequence_reduction_rank3" in source
    assert "bw_linear_dx_sequence_allGather_rank3" in source
    assert source.count("private def segment_000000_sm_final")==1
    assert source.count("private def segment_000000_pm_final")==1
    assert "fact_a_in.Holds" in source and "fact_a_out.Holds" in source
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,transition_ids=tuple(reversed(seg.transition_ids))),)
    assert render(ir,rel)==source


@pytest.mark.parametrize("mutation",("rank","header","axis","source","roles","protected","anchor","duplicate","latest","shape","projection"))
def test_valid_control_then_reject(mutation):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import Node
    ir,rel=renderer_fixture()
    assert render(ir,rel)
    chain=rel.dependent_chain_plan
    if mutation=="rank":ir.pm_nodes[2].rank=1
    elif mutation=="header":ir.pm_num_ranks=4
    elif mutation=="protected":
        ir.pm_nodes.append(Node(0,"FW_neg",[99],[206],[]))
        chain.segments=(replace(chain.segments[0],pm_range=(0,len(ir.pm_nodes))),)
    elif mutation=="anchor":
        from types import SimpleNamespace
        chain.anchor_fact=SimpleNamespace(fact_id="anchor",kind="tensor_shape",side="pm",tid=8000)
        chain.states=tuple(replace(s,fact_ids=(*s.fact_ids,"anchor")) for s in chain.states)
    elif mutation=="duplicate":rel.certificates=(*rel.certificates,rel.certificates[-1])
    elif mutation=="projection":ir.sm_nodes[0].outs.reverse()
    elif mutation=="shape":chain.relation_facts=tuple(replace(r,shard_shape=(0,5,33)) if r.fact_id=="fact_a_in" else r for r in chain.relation_facts)
    elif mutation=="roles":
        c=rel.certificates[0];c=replace(c,gradient_fact=c.activation_fact,activation_fact=c.gradient_fact)
        rel.certificates=(c,*rel.certificates[1:]);rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
    else:
        c=rel.certificates[-1]
        if mutation=="axis":source=replace(c.input_fact,gather_dim=2)
        elif mutation=="source":source=replace(c.input_fact,step_triple=("init:701",*c.input_fact.step_triple[1:]))
        else:
            ir.sm_nodes.append(Node(0,"FW_neg",[99],[700],[]))
            source=replace(c.input_fact,step_triple=("sm:1:0",*c.input_fact.step_triple[1:]))
        old=c.input_fact;c=replace(c,input_fact=source)
        chain.relation_facts=tuple(replace(r,source=source) if r.source==old else r for r in chain.relation_facts)
        rel.certificates=(*rel.certificates[:-1],c)
        rel.transition_specs=(*rel.transition_specs[:-1],replace(rel.transition_specs[-1],pre_facts=(source,),certificate_digest=_typed_certificate_digest(c)))
    with pytest.raises(ValueError):render(ir,rel)


@pytest.mark.parametrize("k",(2,3,4))
def test_backend_witness(k):
    source=witness_source(k)
    assert source==witness_source(k)
    assert "ClosedDepSegmentCertificate" in source and "sorry" not in source
    assert "import denote.KRankBWLinearDwSequenceGeneral" in source


def test_store_scoped_numeric_overlap():
    ir,rel=renderer_fixture()
    chain=rel.dependent_chain_plan
    ir.sm_nodes[0].outs[0]=8000
    chain.relation_facts=tuple(replace(r,sm_tid=8000) if r.fact_id=="fact_out" else r for r in chain.relation_facts)
    assert render(ir,rel)
