from dataclasses import replace
import pytest
from scripts.tests.bw_row_linear_head_matmul_witness import renderer_fixture, witness_source
from trainverify.bridge_emitter.bw_row_linear_head_matmul_renderer import render_closed_bw_row_linear_head_matmul_segment as render
from trainverify.bridge_emitter.composer import _typed_certificate_digest


@pytest.mark.parametrize('k',[2,3,4])
def test_portable_exact_witness(k):
    source=witness_source(k)
    assert source==witness_source(k)
    assert '#print axioms segment_000000' in source
    assert source.count('ClosedDepSegmentCertificate')==1
    assert source.count('private def segment_000000_sm_final ')==1
    assert source.count('private def segment_000000_pm_final ')==1
    for th in ('bw_linear_dx_row_reduction_rank3','bw_linear_dw_row_allGather_rank3','bw_matmul_fst_head_gather_rank4','bw_matmul_snd_head_gather_rank4'):
        assert th in source
    assert 'sorry' not in source and 'axiom ' not in source


def change_certificate(rel,index,cert):
    old=rel.certificates[index]
    rel.certificates=tuple(cert if j==index else c for j,c in enumerate(rel.certificates))
    rel.transition_specs=tuple(replace(t,certificate_digest=_typed_certificate_digest(cert),lean_theorem=cert.lean_theorem,
        pre_facts=tuple(sorted(cert.input_facts)),post_facts=(cert.output_fact,)) if t.certificate_digest==_typed_certificate_digest(old) else t for t in rel.transition_specs)

@pytest.mark.parametrize('mutation',['digest','duplicate','theorem','projection','rank','axis','tid','latest','shape','params','overwrite','footprint'])
def test_coherent_negatives_after_valid_baseline(mutation):
    ir,rel=renderer_fixture(3);assert render(ir,rel,'segment_000000')
    c=rel.certificates[2]
    if mutation=='digest':
        rel.transition_specs=tuple(replace(t,certificate_digest='0'*64) if j==2 else t for j,t in enumerate(rel.transition_specs))
    elif mutation=='duplicate': rel.certificates=(*rel.certificates,c)
    elif mutation=='theorem': change_certificate(rel,2,replace(c,lean_theorem='TrainVerify.Denote.bw_matmul_snd_head_gather_rank4'))
    elif mutation=='projection': change_certificate(rel,2,replace(c,projection='.2'))
    elif mutation=='rank': change_certificate(rel,2,replace(c,rank_count=4))
    elif mutation in ('axis','tid','latest','shape'):
        records=list(rel.dependent_chain_plan.relation_facts);j=next(j for j,r in enumerate(records) if r.fact_id=='mg');r=records[j]
        if mutation=='axis':
            source=replace(r.source,gather_dim=2);records[j]=replace(r,source=source,gather_dim=2)
            for ix in (2,3):
                cc=rel.certificates[ix];change_certificate(rel,ix,replace(cc,input_facts=(source,*cc.input_facts[1:])))
        elif mutation=='tid':
            records[j]=replace(r,sm_tid=601);ir.sm_nodes[0].ins[0]=601
        elif mutation=='latest':
            source=replace(r.source,step_triple=('sm:0:0',*r.source.step_triple[1:]))
            records[j]=replace(r,source=source)
            for ix in (2,3):
                cc=rel.certificates[ix];change_certificate(rel,ix,replace(cc,input_facts=(source,*cc.input_facts[1:])))
        else: records[j]=replace(r,full_shape=(2,99,3,7))
        rel.dependent_chain_plan.relation_facts=tuple(records)
    elif mutation=='params': ir.pm_nodes[3].params=[1]
    elif mutation=='overwrite': ir.pm_nodes[0].outs[0]=9000
    elif mutation=='footprint':
        rel.transition_specs=tuple(replace(t,pm_node_indices=(5,4,3)) if j in (2,3) else t for j,t in enumerate(rel.transition_specs))
    with pytest.raises(ValueError): render(ir,rel,'segment_000000')


def test_family_enumeration_does_not_define_execution_order():
    ir,rel=renderer_fixture();source=render(ir,rel,'segment_000000')
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,transition_ids=tuple(reversed(seg.transition_ids))),)
    assert render(ir,rel,'segment_000000')  # same graph authority; rule tuple order is immaterial
    assert source.count('private def segment_000000_sm_final ')==1


def test_unrelated_certificate_is_not_ambiguous():
    ir,rel=renderer_fixture();source=render(ir,rel,'segment_000000')
    c=rel.certificates[2]
    rel.certificates=(*rel.certificates,replace(c,output_fact=replace(c.output_fact,step_triple=('sm:88:0',*c.output_fact.step_triple[1:]))))
    assert render(ir,rel,'segment_000000')==source


def test_store_scoped_numeric_overlap():
    ir,rel=renderer_fixture();assert render(ir,rel,'segment_000000')
    ir.sm_nodes[0].outs[0]=4000 # PM linear output is a different store.
    rel.dependent_chain_plan.relation_facts=tuple(replace(r,sm_tid=4000) if r.fact_id=='mo0' else r for r in rel.dependent_chain_plan.relation_facts)
    assert render(ir,rel,'segment_000000')
