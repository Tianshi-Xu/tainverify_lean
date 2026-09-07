from dataclasses import replace
from pathlib import Path
import pytest
from scripts.tests.alltoall_reduce_scatter_witness import renderer_fixture, witness_source
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.alltoall_reduce_scatter_renderer import render_closed_alltoall_reduce_scatter_segment as render




@pytest.mark.parametrize("k", [2,3,4])
def test_portable_witness(k):
    source=witness_source(k)
    assert source == witness_source(k)
    assert source.count("let pmFinal :=") == source.count("let smFinal :=") == 1
    assert "smNodes : List NodeDecl := []" in source
    assert "#print axioms segment_000000" in source
    assert "allGatherPrimDimN_allToAllPrimWithDims_ofFn" in source
    assert "allGatherPrimDimN_chunks_ofFn" in source
    for line in source.splitlines():
        if line.startswith("import "):
            module=line.split()[1]
            assert (Path(__file__).resolve().parents[2]/'trainverify'/Path(*module.split('.'))).with_suffix('.lean').is_file()


def coherent_cert(rel, index, cert):
    old=rel.certificates[index]
    rel.certificates=tuple(cert if i==index else c for i,c in enumerate(rel.certificates))
    rel.transition_specs=tuple(replace(t,pre_facts=(cert.input_fact,),post_facts=(cert.output_fact,),certificate_digest=_typed_certificate_digest(cert)) if i==index else t for i,t in enumerate(rel.transition_specs))
    rel.dependent_chain_plan.relation_facts=tuple(replace(f,source=cert.input_fact) if f.source==old.input_fact else replace(f,source=cert.output_fact) if f.source==old.output_fact else f for f in rel.dependent_chain_plan.relation_facts)


@pytest.mark.parametrize("mutation", ['digest','duplicate','wrong_type','axis','source','role','rank','order','footprint','live','anchor','publication','state','sm_range'])
def test_coherent_mutations_follow_valid_baseline(mutation):
    ir,rel=renderer_fixture(3); chain=rel.dependent_chain_plan
    assert render(ir,rel,'segment_000000')
    if mutation=='digest':rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest='bad'),rel.transition_specs[1])
    elif mutation=='duplicate':rel.certificates+=rel.certificates[:1]
    elif mutation=='wrong_type':rel.certificates=rel.certificates[1:]
    elif mutation=='axis':coherent_cert(rel,1,replace(rel.certificates[1],scatter_dim=1))
    elif mutation=='source':coherent_cert(rel,0,replace(rel.certificates[0],input_fact=replace(rel.certificates[0].input_fact,step_triple=('init:999',*rel.certificates[0].input_fact.step_triple[1:]))))
    elif mutation=='role':ir.pm_nodes[1].ins.reverse()
    elif mutation=='rank':ir.pm_nodes[1].rank=1
    elif mutation=='order':chain.segments=(replace(chain.segments[0],transition_ids=('r','a')),)
    elif mutation=='footprint':rel.transition_specs=(replace(rel.transition_specs[0],pm_node_indices=(0,2)),rel.transition_specs[1])
    elif mutation in ('live','anchor'):
        f=rc.ClosedTensorShapeFactRecord('guard','pm',300,(1,),300)
        if mutation=='live':chain.authority_facts=(f,)
        else:chain.anchor_fact=f
        chain.states=(replace(chain.states[0],fact_ids=(*chain.states[0].fact_ids,'guard')),chain.states[1])
    elif mutation=='publication':chain.states=(chain.states[0],replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,'unknown')))
    elif mutation=='state':chain.states=(replace(chain.states[0],fact_ids=('a_in',)),chain.states[1])
    elif mutation=='sm_range':chain.segments=(replace(chain.segments[0],sm_range=(-1,-1)),)
    with pytest.raises(ValueError):render(ir,rel,'segment_000000')


def test_retained_inputs_and_cross_store_anchor_and_unrelated_certificate():
    ir,rel=renderer_fixture(3);chain=rel.dependent_chain_plan
    baseline=render(ir,rel,'segment_000000')
    unrelated=replace(rel.certificates[0],input_fact=replace(rel.certificates[0].input_fact,gather_dim=0))
    rel.certificates+= (unrelated,)
    assert render(ir,rel,'segment_000000')==baseline
    guard=rc.ClosedTensorShapeFactRecord('guard','sm',300,(1,),300)
    chain.anchor_fact=guard
    chain.states=(replace(chain.states[0],fact_ids=(*chain.states[0].fact_ids,'guard')),replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,*chain.states[0].fact_ids,'guard')))
    assert render(ir,rel,'segment_000000')
