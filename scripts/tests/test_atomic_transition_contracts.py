"""Review regressions across sibling atomic public-dispatch paths."""
import importlib
from dataclasses import replace
import pytest
from scripts.tests.test_atomic_wave2_dispatch import CASES as W2
from scripts.tests.test_atomic_wave3_dispatch import CASES as W3
from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.relation_compiler import ClosedTensorShapeFactRecord
CASES=[(s,f) for _,s,f,_ in W2]+[(s,'renderer_fixture') for _,s,_ in W3]
def fixture(stem,name):
    ir,rel,*_=getattr(importlib.import_module('scripts.tests.'+stem+'_witness'),name)(3)
    return ir,rel,rel.dependent_chain_plan.segments[0].segment_id
@pytest.mark.parametrize('stem,name',CASES)
@pytest.mark.parametrize('field',['fact_only','authority_requirements'])
def test_transition_contract_not_silently_dropped(stem,name,field):
    _,initial,_=fixture(stem,name)
    for i in range(len(initial.transition_specs)):
        ir,rel,sid=fixture(stem,name)
        assert render_closed_segment(ir,rel,sid)
        ts=list(rel.transition_specs);ts[i]=replace(ts[i],**{field:True if field=='fact_only' else ('phantom',)})
        rel.transition_specs=tuple(ts)
        with pytest.raises(ValueError):render_closed_segment(ir,rel,sid)
@pytest.mark.parametrize('stem,name',CASES)
@pytest.mark.parametrize('which',[0,1])
def test_explicit_anchor_must_remain_live(stem,name,which):
    ir,rel,sid=fixture(stem,name);ch=rel.dependent_chain_plan
    anchor=ch.anchor_fact or ClosedTensorShapeFactRecord('audit_anchor','sm',987654,(1,),987654)
    ch.anchor_fact=anchor
    ch.states=tuple(replace(s,fact_ids=tuple(dict.fromkeys((*s.fact_ids,anchor.fact_id)))) for s in ch.states)
    assert render_closed_segment(ir,rel,sid)
    states=list(ch.states);states[which]=replace(states[which],fact_ids=tuple(f for f in states[which].fact_ids if f!=anchor.fact_id));ch.states=tuple(states)
    with pytest.raises(ValueError):render_closed_segment(ir,rel,sid)
