import importlib
import pytest
from scripts.tests.bw_flatten_alltoall_div_witness import renderer_fixture, witness_source


def render(ir,rel):
    try:m=importlib.import_module('trainverify.bridge_emitter.bw_flatten_alltoall_div_renderer')
    except ModuleNotFoundError:pytest.fail('production-valid C06 has no atomic backend')
    return m.render_closed_bw_flatten_alltoall_div_segment(ir,rel,rel.dependent_chain_plan.segments[0].segment_id)




@pytest.mark.parametrize('k',(2,3,4))
def test_portable(k):
    ir,rel=renderer_fixture(k)
    source=render(ir,rel)
    assert source.count('private def segment_000000_sm_final')==1
    assert source.count('private def segment_000000_pm_final')==1
    assert 'have hdi := houtA' in source
    assert '#print axioms segment_000000' in witness_source(k)



@pytest.mark.parametrize('mutation',('rank','header','params','order','duplicate','type','axis','source','latest','anchor','retained','digest','dependency'))
def test_valid_control_then_mutation(mutation):
    from dataclasses import replace
    from types import SimpleNamespace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import Node
    ir,rel=renderer_fixture()
    assert render(ir,rel)
    ch=rel.dependent_chain_plan
    if mutation=='rank':ir.pm_nodes[2].rank=1
    elif mutation=='header':ir.pm_num_ranks=4
    elif mutation=='params':ir.pm_nodes[-1].params=[9]
    elif mutation=='order':ir.pm_nodes[2].ins.reverse()
    elif mutation=='duplicate':rel.certificates=(*rel.certificates,rel.certificates[1])
    elif mutation=='type':rel.certificates=(rel.certificates[0],SimpleNamespace(**rel.certificates[1].__dict__),rel.certificates[2])
    elif mutation=='digest':rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest='bad'),*rel.transition_specs[1:])
    elif mutation=='dependency':
        ch.states=(replace(ch.states[0],fact_ids=(*ch.states[0].fact_ids,'fact_ao')),ch.states[1])
    elif mutation=='anchor':
        ch.anchor_fact=SimpleNamespace(fact_id='anchor',kind='tensor_shape',side='pm',tid=8000)
        ch.states=tuple(replace(st,fact_ids=(*st.fact_ids,'anchor')) for st in ch.states)
    elif mutation=='retained':
        ir.pm_nodes.append(Node(0,'FW_neg',[999],[7000],[]))
        ch.segments=(replace(ch.segments[0],pm_range=(0,len(ir.pm_nodes))),)
    else:
        c=rel.certificates[1];old=c.input_fact
        if mutation=='axis':f=replace(old,gather_dim=2)
        elif mutation=='source':f=replace(old,step_triple=('init:702',*old.step_triple[1:]))
        else:
            ir.sm_nodes.append(Node(0,'FW_neg',[999],[700],[]))
            f=replace(old,step_triple=('sm:2:0',*old.step_triple[1:]))
        c=replace(c,input_fact=f)
        ch.relation_facts=tuple(replace(r,source=f) if r.source==old else r for r in ch.relation_facts)
        rel.certificates=(rel.certificates[0],c,rel.certificates[2])
        rel.transition_specs=(rel.transition_specs[0],replace(rel.transition_specs[1],pre_facts=(f,),certificate_digest=_typed_certificate_digest(c)),rel.transition_specs[2])
    with pytest.raises(ValueError):render(ir,rel)


def test_cross_store_overlap_and_retained_input():
    from dataclasses import replace
    ir,rel=renderer_fixture(scalar=0,b=3,s=2,n=2,d=5)
    assert render(ir,rel)
    ch=rel.dependent_chain_plan
    ir.sm_nodes[1].outs=[8000]
    ch.relation_facts=tuple(replace(r,sm_tid=8000) if r.fact_id==ch.relation_facts[1].fact_id else r for r in ch.relation_facts)
    ch.states=(ch.states[0],replace(ch.states[1],fact_ids=(*ch.states[1].fact_ids,*ch.states[0].fact_ids)))
    source=render(ir,rel)
    ch.segments=(replace(ch.segments[0],transition_ids=tuple(reversed(ch.segments[0].transition_ids))),)
    assert render(ir,rel)==source
