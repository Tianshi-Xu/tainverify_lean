import importlib
import pytest
from dataclasses import replace
from scripts.tests.bw_softmax_transpose_witness import renderer_fixture, witness_source, T_THEOREM, S_THEOREM


def render(ir,rel):
    try:mod=importlib.import_module('trainverify.bridge_emitter.bw_softmax_transpose_renderer')
    except ModuleNotFoundError:pytest.fail('production BWsoftmax dim1 + transpose has no atomic backend')
    return mod.render_closed_bw_softmax_transpose_segment(ir,rel,rel.dependent_chain_plan.segments[0].segment_id)




@pytest.mark.parametrize('k',(2,3,4))
def test_portable(k):
    ir,rel=renderer_fixture(k)
    source=render(ir,rel)
    assert source.count('private def segment_000000_sm_final')==1
    assert source.count('private def segment_000000_pm_final')==1
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,transition_ids=tuple(reversed(seg.transition_ids))),)
    assert render(ir,rel)==source
    assert '#print axioms segment_000000' in witness_source(k)
    assert witness_source(k)==witness_source(k)


@pytest.mark.parametrize('mutation',('axis','source','latest','rank','header','order','roles','digest','duplicate','type','protected','anchor','shape'))
def test_valid_control_then_reject(mutation):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import Node
    from types import SimpleNamespace
    ir,rel=renderer_fixture()
    assert render(ir,rel)
    ch=rel.dependent_chain_plan
    if mutation=='rank':ir.pm_nodes[2].rank=0
    elif mutation=='header':ir.pm_num_ranks=4
    elif mutation=='order':ir.pm_nodes[1],ir.pm_nodes[3]=ir.pm_nodes[3],ir.pm_nodes[1]
    elif mutation=='digest':rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest='bad'),rel.transition_specs[1])
    elif mutation=='duplicate':rel.certificates+=rel.certificates[:1]
    elif mutation=='type':rel.certificates=(SimpleNamespace(**rel.certificates[0].__dict__),rel.certificates[1])
    elif mutation=='shape':ch.relation_facts=tuple(replace(r,shard_shape=(2,3,5,0)) if r.fact_id=='fg' else r for r in ch.relation_facts)
    elif mutation=='protected':
        ir.pm_nodes.append(Node(0,'FW_neg',[99],[5000],[]))
        ch.segments=(replace(ch.segments[0],pm_range=(0,len(ir.pm_nodes))),)
    elif mutation=='anchor':
        ch.anchor_fact=SimpleNamespace(fact_id='anchor',kind='tensor_shape',side='sm',tid=300)
        ch.states=tuple(replace(s,fact_ids=(*s.fact_ids,'anchor')) for s in ch.states)
    else:
        index=0 if mutation=='roles' else 1
        c=rel.certificates[index];t=rel.transition_specs[index]
        if mutation=='roles':c=replace(c,gradient_fact=c.activation_fact,activation_fact=c.gradient_fact)
        else:
            old=c.input_fact
            if mutation=='axis':new=replace(old,gather_dim=1)
            elif mutation=='source':new=replace(old,step_triple=('init:401',*old.step_triple[1:]))
            else:
                ir.sm_nodes.append(Node(0,'FW_neg',[99],[400],[]))
                new=replace(old,step_triple=('sm:2:0',*old.step_triple[1:]))
            c=replace(c,input_fact=new);t=replace(t,pre_facts=(new,))
            ch.relation_facts=tuple(replace(r,source=new) if r.source==old else r for r in ch.relation_facts)
        rel.certificates=tuple(c if i==index else x for i,x in enumerate(rel.certificates))
        rel.transition_specs=tuple(replace(t,certificate_digest=_typed_certificate_digest(c)) if i==index else x for i,x in enumerate(rel.transition_specs))
    with pytest.raises(ValueError):render(ir,rel)


def test_store_scoped_overlap_and_unrelated_certificate():
    ir,rel=renderer_fixture()
    ir.sm_nodes[0].outs=[5000]
    ch=rel.dependent_chain_plan
    ch.relation_facts=tuple(replace(r,sm_tid=5000) if r.fact_id=='fo' else r for r in ch.relation_facts)
    source=render(ir,rel)
    c=rel.certificates[0]
    rel.certificates+=(replace(c,output_fact=replace(c.output_fact,step_triple=('sm:99:0',))),)
    assert render(ir,rel)==source


def test_top_level_mode(monkeypatch):
    import sys
    from pathlib import Path
    from trainverify.bridge_emitter import relation_compiler as rc
    monkeypatch.syspath_prepend(str(Path(__file__).resolve().parents[2]/'trainverify/bridge_emitter'))
    monkeypatch.setitem(sys.modules,'relation_compiler',rc)
    module=importlib.import_module('bw_softmax_transpose_renderer')
    ir,rel=renderer_fixture()
    assert module.render_closed_bw_softmax_transpose_segment(ir,rel,'segment_000000')==render(ir,rel)
