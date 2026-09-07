import importlib.util
import pytest
from scripts.tests.sum_fw_bw_witness import fixture

def render(ir, relation, sid):
    spec=importlib.util.find_spec("trainverify.bridge_emitter.sum_fw_bw_renderer")
    assert spec is not None, "C01 production backend is missing"
    from trainverify.bridge_emitter.sum_fw_bw_renderer import render_closed_sum_fw_bw_segment
    return render_closed_sum_fw_bw_segment(ir,relation,sid)

# Real captured frames are checked by the explicit external kernel harness.
def test_portable_witness_source():
    from scripts.tests import sum_fw_bw_witness as w
    assert callable(getattr(w,"witness_source",None)), "portable witness generator missing"
    for k in (1,2,3,4):
        text=w.witness_source(k)
        assert "import denote.KRankBWSumSequence" in text
        assert "anchor" in text
        assert "ClosedDepSegmentCertificate" in text

def test_duplicate_source_record_rejected():
    ir,rel=fixture(2)
    assert render(ir,rel,"segment_000000")
    rel.dependent_chain_plan.relation_facts += (replace(rel.dependent_chain_plan.relation_facts[1],fact_id="other_x"),)
    with pytest.raises(ValueError): render(ir,rel,"segment_000000")

from dataclasses import replace
from copy import deepcopy
from trainverify.bridge_emitter.composer import _typed_certificate_digest

@pytest.mark.parametrize("k",(1,2,3,4))
def test_portable_interleaved_positive(k):
    ir,rel=fixture(k)
    text=render(ir,rel,"segment_000000")
    assert f"allGatherPrimDimN 1 {k}" in text
    assert text.count("@[irreducible] private def")==2
    assert text.count("smNodes :=")==text.count("pmNodes :=")==1
    assert "fact_x" in text and "fact_g" in text
    assert text==render(ir,rel,"segment_000000")

@pytest.mark.parametrize("mutation",("axis","cert_shape","cert_step","source_tid","stale_source","params","overwrite","duplicate_cert","digest","role","missing_live","rank_order"))
def test_coherent_mutations_rejected(mutation):
    ir,rel=fixture(3)
    assert render(ir,rel,"segment_000000")
    records=list(rel.dependent_chain_plan.relation_facts)
    certs=list(rel.certificates)
    if mutation=="axis":
        old=records[1].source;new=replace(old,gather_dim=2)
        records[1]=replace(records[1],source=new)
        certs[0]=replace(certs[0],input_fact=new)
        certs[1]=replace(certs[1],activation_fact=new)
        rel.transition_specs=tuple(replace(t,pre_facts=tuple(new if f==old else f for f in t.pre_facts)) for t in rel.transition_specs)
    elif mutation=="cert_shape": certs[0]=replace(certs[0],full_shape=(99,99,99))
    elif mutation=="cert_step": certs[0]=replace(certs[0],pm_sum_steps=tuple(reversed(certs[0].pm_sum_steps)))
    elif mutation=="source_tid":
        records[1]=replace(records[1],sm_tid=11)
        ir.sm_nodes[1].ins[0]=11;ir.sm_nodes[2].ins[1]=11
    elif mutation=="stale_source": ir.sm_nodes.insert(1,deepcopy(ir.sm_nodes[0]))
    elif mutation=="params": ir.pm_nodes[3].params=[1]
    elif mutation=="overwrite":
        records[2]=replace(records[2],sm_tid=10);ir.sm_nodes[1].outs[0]=10
    elif mutation=="duplicate_cert": certs.append(certs[0])
    elif mutation=="digest": rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest="bad"),rel.transition_specs[1])
    elif mutation=="role": certs[1]=replace(certs[1],gradient_fact=certs[1].activation_fact,activation_fact=certs[1].gradient_fact)
    elif mutation=="missing_live": rel.dependent_chain_plan.states=(replace(rel.dependent_chain_plan.states[0],fact_ids=("fact_g",)),rel.dependent_chain_plan.states[1])
    elif mutation=="rank_order": ir.pm_nodes[3].rank=1
    rel.dependent_chain_plan.relation_facts=tuple(records)
    rel.certificates=tuple(certs)
    if mutation!="digest": rel.transition_specs=tuple(replace(t,certificate_digest=_typed_certificate_digest(c)) for t,c in zip(rel.transition_specs,certs))
    with pytest.raises(ValueError): render(ir,rel,"segment_000000")

def test_cross_store_overlap_and_reversed_transition_order():
    ir,rel=fixture(3)
    assert render(ir,rel,"segment_000000")
    records=list(rel.dependent_chain_plan.relation_facts)
    records[2]=replace(records[2],sm_tid=records[3].pm_tids[0])
    ir.sm_nodes[1].outs[0]=records[2].sm_tid
    rel.dependent_chain_plan.relation_facts=tuple(records)
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,transition_ids=tuple(reversed(seg.transition_ids))),)
    assert render(ir,rel,"segment_000000")
