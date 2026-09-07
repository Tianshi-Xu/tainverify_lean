import importlib.util
import pytest



from dataclasses import replace
from scripts.tests.bw_layernorm_wred_witness import fixture,witness_source
from trainverify.bridge_emitter.bw_layernorm_wred_renderer import render_closed_bw_layernorm_wred_segment as render
from trainverify.bridge_emitter.composer import _typed_certificate_digest

@pytest.mark.parametrize("k",[2,3,4])
@pytest.mark.parametrize("dims",[(2,3,7),(3,2,1)])
def test_portable_witness(k,dims):
    source=witness_source(k,*dims,collision=True)
    assert source==witness_source(k,*dims,collision=True)
    assert source.count("ClosedDepSegmentCertificate")==1
    assert source.count("apply RelationState.Holds.fold_frame")==1
    assert "four_input_middle_writer" in source
    assert "#print axioms segment_000000" in source
    assert "sorry" not in source and "axiom " not in source
    assert "  have hWredReduce0" in source
    assert "    rw [hWredWriter0]" in source
    assert "import denote.KRankBWLayernormParam" in source

@pytest.mark.parametrize("mutation",["axis","source_tid","stale","ordered","projection","duplicate","cert_shape","retired","anchor","overwrite","rank","internal","authority","fact_only"])
def test_coherent_mutations(mutation):
    ir,rel=fixture(3)
    assert render(ir,rel,"segment_000000")
    chain=rel.dependent_chain_plan
    if mutation in {"axis","source_tid","stale"}:
        f=chain.relation_facts[0]
        src=replace(f.source,gather_dim=0) if mutation=="axis" else replace(f.source,step_triple=("init:999",*f.source.step_triple[1:])) if mutation=="source_tid" else f.source
        if mutation=="stale": ir.sm_nodes[0].outs=[1]
        certs=tuple(replace(c,gradient_fact=src) for c in rel.certificates[:3])
        rel.certificates=(*certs,rel.certificates[-1])
        rel.transition_specs=tuple(replace(t,pre_facts=tuple(sorted((c.gradient_fact,c.activation_fact,c.gamma_fact,c.beta_fact))),certificate_digest=_typed_certificate_digest(c)) for t,c in zip(rel.transition_specs[:3],certs))+(rel.transition_specs[-1],)
        chain.relation_facts=tuple(replace(x,source=src) if x.fact_id==f.fact_id else x for x in chain.relation_facts)
    elif mutation=="ordered": ir.pm_nodes[1].ins[:2]=reversed(ir.pm_nodes[1].ins[:2])
    elif mutation=="duplicate": rel.certificates=(*rel.certificates,rel.certificates[1])
    elif mutation in {"projection","cert_shape"}:
        i=1 if mutation=="projection" else 3
        c=replace(rel.certificates[i],**({"projection":".2.2"} if i==1 else {"full_shape":(99,)}))
        rel.certificates=tuple(c if n==i else x for n,x in enumerate(rel.certificates))
        rel.transition_specs=tuple(replace(t,certificate_digest=_typed_certificate_digest(c)) if n==i else t for n,t in enumerate(rel.transition_specs))
    elif mutation=="retired": chain.states=(chain.states[0],replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,"fact_w")))
    elif mutation=="anchor": chain.anchor_fact=replace(chain.anchor_fact,tid=10)
    elif mutation=="overwrite": ir.pm_nodes[-1].outs=[600]
    elif mutation=="rank": ir.pm_num_ranks=4
    elif mutation=="internal": chain.states=(replace(chain.states[0],fact_ids=tuple(x for x in chain.states[0].fact_ids if x!="fact_w")),chain.states[1])
    elif mutation=="authority": rel.transition_specs=(replace(rel.transition_specs[0],authority_requirements=("phantom",)),*rel.transition_specs[1:])
    else: rel.transition_specs=(replace(rel.transition_specs[0],fact_only=True),*rel.transition_specs[1:])
    with pytest.raises(ValueError): render(ir,rel,"segment_000000")

def test_order_and_unrelated_certificate_neutral():
    ir,rel=fixture(4)
    source=render(ir,rel,"segment_000000")
    chain=rel.dependent_chain_plan
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(reversed(chain.segments[0].transition_ids))),)
    c=replace(rel.certificates[0],output_fact=replace(rel.certificates[0].output_fact,gather_dim=0))
    rel.certificates=(*rel.certificates,c)
    assert render(ir,rel,"segment_000000")==source
