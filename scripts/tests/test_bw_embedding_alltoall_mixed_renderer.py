import importlib.util
import pytest



@pytest.mark.parametrize('k',[2,3,4])
def test_portable_witness(k):
    from scripts.tests.bw_embedding_alltoall_mixed_witness import witness_source
    src=witness_source(k)
    assert '#print axioms segment_000000_sound' in src
    assert src.count('private def segment_000000_sm_final')==1
    assert src.count('private def segment_000000_pm_final')==1
    assert '/home/' not in src and 'FreshGPT' not in src
    assert 'have hg : hg.Holds smFinal pmFinal := hframe' in src

@pytest.mark.parametrize('mutation',['rank','roles','axis','source','latest','retained','duplicate','world','sm-world'])
def test_mutations_after_valid_control(mutation):
    from dataclasses import replace
    from scripts.tests.bw_embedding_alltoall_mixed_witness import renderer_fixture
    from trainverify.bridge_emitter.bw_embedding_alltoall_mixed_renderer import render_closed_bw_embedding_alltoall_mixed_segment as render
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel,sid=renderer_fixture();assert render(ir,rel,sid)
    c=rel.certificates[0];t=rel.transition_specs[0];chain=rel.dependent_chain_plan
    if mutation=='rank':ir.pm_nodes[t.pm_node_indices[-1]].rank=0
    elif mutation=='roles':ir.sm_nodes[1].ins.reverse()
    elif mutation=='axis':
        f=replace(c.gradient_fact,gather_dim=1);new=replace(c,gradient_fact=f)
        rel.certificates=(new,*rel.certificates[1:]);rel.transition_specs=(replace(t,pre_facts=tuple(sorted((f,c.ids_fact,c.weight_fact))),certificate_digest=_typed_certificate_digest(new)),*rel.transition_specs[1:])
        chain.relation_facts=tuple(replace(r,source=f,gather_dim=1) if r.source==c.gradient_fact else r for r in chain.relation_facts)
    elif mutation=='source':
        f=replace(c.gradient_fact,step_triple=('init:99',*c.gradient_fact.step_triple[1:]));new=replace(c,gradient_fact=f)
        rel.certificates=(new,*rel.certificates[1:]);rel.transition_specs=(replace(t,pre_facts=tuple(sorted((f,c.ids_fact,c.weight_fact))),certificate_digest=_typed_certificate_digest(new)),*rel.transition_specs[1:])
        chain.relation_facts=tuple(replace(r,source=f) if r.source==c.gradient_fact else r for r in chain.relation_facts)
    elif mutation=='latest':ir.pm_nodes[0].outs=[ir.pm_nodes[t.pm_node_indices[0]].ins[0]]
    elif mutation=='retained':chain.states=(chain.states[0],replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,'unknown_public')))
    elif mutation=='duplicate':rel.certificates=(*rel.certificates,c)
    elif mutation=='sm-world':ir.sm_num_ranks=2
    else:ir.pm_num_ranks=4
    with pytest.raises(ValueError):render(ir,rel,sid)


def test_retained_internal_and_cross_store_ids():
    from dataclasses import replace
    from scripts.tests.bw_embedding_alltoall_mixed_witness import renderer_fixture
    from trainverify.bridge_emitter.bw_embedding_alltoall_mixed_renderer import render_closed_bw_embedding_alltoall_mixed_segment as render
    ir,rel,sid=renderer_fixture();assert render(ir,rel,sid)
    ch=rel.dependent_chain_plan
    ch.states=(ch.states[0],replace(ch.states[1],fact_ids=(*ch.states[1].fact_ids,'ao')))
    assert render(ir,rel,sid)
    tid=ir.pm_nodes[rel.transition_specs[0].pm_node_indices[0]].outs[0]
    ir.sm_nodes[1].outs=[tid]
    ch.relation_facts=tuple(replace(r,sm_tid=tid) if r.fact_id=='ho' else r for r in ch.relation_facts)
    assert render(ir,rel,sid)
