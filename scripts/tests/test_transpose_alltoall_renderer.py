from dataclasses import replace
import importlib
import pytest
from scripts.tests.transpose_alltoall_witness import renderer_fixture, witness_source
from trainverify.bridge_emitter import composer

def render(ir,rel):
    try:m=importlib.import_module('trainverify.bridge_emitter.transpose_alltoall_renderer')
    except ModuleNotFoundError:return composer.render_closed_segment(ir,rel,'segment_000000')
    return m.render_closed_transpose_alltoall_segment(ir,rel,'segment_000000')

@pytest.mark.parametrize('k',[2,3,4])
def test_mixed_single_fold_dependencies(k):
    ir,rel=renderer_fixture(k)
    source=render(ir,rel)
    assert source.count('@[irreducible] private def')==2
    assert 'fw_transposeAxes_1_2_dim1_to_dim2_rank4' in source
    assert 'fw_transposeAxes_2_3_dim2_to_dim3_rank4' in source
    assert 'allGatherPrimDimN_allToAllPrimWithDims_ofFn' in source
    assert 'out_a.Holds smFinal pmFinal := hframe' not in source
    assert source==render(ir,rel)

@pytest.mark.parametrize('mutation',['rank','axes','input_role','retained','anchor','missing_input','source','cert_axis','duplicate_cert','duplicate_transition','footprint','overwrite','same_store_retained','unknown_fact'])
def test_rejects_coherent_invalid_authority(mutation):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=renderer_fixture(3);assert render(ir,rel);ch=rel.dependent_chain_plan
    if mutation=='rank':ir.pm_nodes[0].rank=1
    elif mutation=='axes':ir.sm_nodes[1].params=[2,3]
    elif mutation=='input_role':ir.pm_nodes[0].ins.reverse()
    elif mutation=='retained':
        ch.states=(ch.states[0],replace(ch.states[1],fact_ids=(*ch.states[1].fact_ids,'not_proved')))
    elif mutation=='anchor':ch.anchor_fact=replace(ch.anchor_fact,tid=400)
    elif mutation=='missing_input':ch.states=(replace(ch.states[0],fact_ids=('anchor','input_t','input_b')),ch.states[1])
    elif mutation=='source':
        c=rel.certificates[0];src=replace(c.input_fact,step_triple=('init:123',*c.input_fact.step_triple[1:]));c=replace(c,input_fact=src)
        rel.certificates=(c,*rel.certificates[1:]);rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=(src,),certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
        ch.relation_facts=tuple(replace(f,source=src) if f.fact_id=='input_t' else f for f in ch.relation_facts)
    elif mutation=='cert_axis':
        c=replace(rel.certificates[0],parameters=(2,3));rel.certificates=(c,*rel.certificates[1:]);rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
    elif mutation=='duplicate_cert':rel.certificates=(*rel.certificates,rel.certificates[0])
    elif mutation=='duplicate_transition':ch.segments=(replace(ch.segments[0],transition_ids=(*ch.segments[0].transition_ids,ch.segments[0].transition_ids[0])),)
    elif mutation=='footprint':rel.transition_specs=(replace(rel.transition_specs[0],pm_node_indices=(0,2,3)),*rel.transition_specs[1:])
    elif mutation=='overwrite':ir.pm_nodes[-1].outs=[3000]
    elif mutation=='same_store_retained':
        ch.anchor_fact=replace(ch.anchor_fact,side='pm',tid=3000)
    else:ch.states=(replace(ch.states[0],fact_ids=(*ch.states[0].fact_ids,'unknown')),ch.states[1])
    with pytest.raises(ValueError):render(ir,rel)

@pytest.mark.parametrize('k',[2,3,4])
def test_portable_witness(k):
    source=witness_source(k)
    assert source==witness_source(k)
    assert 'sorry' not in source and 'axiom ' not in source
    assert 'KRankTranspose23Extra' in source

def test_store_scoped_numeric_overlap():
    ir,rel=renderer_fixture(3)
    # Anchor is an SM read; PM writing the same numeric TID is harmless.
    rel.dependent_chain_plan.anchor_fact=replace(rel.dependent_chain_plan.anchor_fact,tid=3000)
    assert render(ir,rel)

def test_transition_enumeration_is_not_execution_order():
    ir,rel=renderer_fixture(3);ch=rel.dependent_chain_plan
    ch.segments=(replace(ch.segments[0],transition_ids=tuple(reversed(ch.segments[0].transition_ids))),)
    assert render(ir,rel)

def test_unrelated_certificate_does_not_change_bytes():
    ir,rel=renderer_fixture(3);expected=render(ir,rel)
    c=rel.certificates[0];rel.certificates=(*rel.certificates,replace(c,output_fact=replace(c.output_fact,gather_dim=0)))
    assert render(ir,rel)==expected


@pytest.mark.parametrize('mutation',['metadata','source_metadata','missing_anchor'])
def test_rejects_unproved_closed_metadata(mutation):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=renderer_fixture(3);ch=rel.dependent_chain_plan
    if mutation=='metadata':ch.relation_facts=tuple(replace(f,metadata_tid=123) if f.fact_id=='input_t' else f for f in ch.relation_facts)
    elif mutation=='missing_anchor':ch.states=tuple(replace(s,fact_ids=tuple(f for f in s.fact_ids if f!='anchor')) for s in ch.states)
    else:
        c=rel.certificates[0];src=replace(c.input_fact,joined_pm_step='init:1000');c=replace(c,input_fact=src)
        rel.certificates=(c,*rel.certificates[1:]);rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=(src,),certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
        ch.relation_facts=tuple(replace(f,source=src) if f.fact_id=='input_t' else f for f in ch.relation_facts)
    with pytest.raises(ValueError):render(ir,rel)
