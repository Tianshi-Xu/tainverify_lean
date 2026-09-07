"""Exact legacy-graph consumers of the generic sequence-dW rule."""
from copy import deepcopy
from dataclasses import replace
from types import SimpleNamespace
import pytest
from trainverify.bridge_emitter.composer import render_closed_segment, _typed_certificate_digest
from trainverify.bridge_emitter import relation_compiler as rc


def mixed_fixture(sid):
    from scripts.tests.test_dw_row_reconstruction_consumer import base_fixture
    from scripts.tests.test_migrated_source_axis_agreement import add_linear_dw
    ir, base = deepcopy(base_fixture())
    rel = SimpleNamespace(**vars(base))
    assert render_closed_segment(ir, rel, sid)
    add_linear_dw(ir, rel, sid)
    # The extra projection's shape comes from its shared weight authority.
    c = rel.certificates[-1]
    chain = rel.dependent_chain_plan
    weight = next(r for r in chain.relation_facts if r.source == c.weight_fact)
    rel.dependent_chain_plan = replace(chain, relation_facts=tuple(
        replace(r,full_shape=weight.full_shape,shard_shape=weight.full_shape)
        if r.source==c.output_fact else r for r in chain.relation_facts))
    return ir, rel


@pytest.mark.parametrize('sid',['segment_000223','segment_000264'])
def test_mixed_dw_preserves_input_roles(sid):
    ir, rel = mixed_fixture(sid)
    assert render_closed_segment(ir, rel, sid)
    c = rel.certificates[-1]
    changed = replace(c,gradient_fact=c.activation_fact,activation_fact=c.gradient_fact)
    rel.certificates = (*rel.certificates[:-1],changed)
    rel.transition_specs = tuple(replace(t,certificate_digest=_typed_certificate_digest(changed))
        if t.certificate_digest==_typed_certificate_digest(c) else t for t in rel.transition_specs)
    with pytest.raises(ValueError):
        render_closed_segment(ir, rel, sid)


@pytest.mark.parametrize('field,value',[('rank_count',3),('shard_dim',2)])
def test_transpose_mixed_dw_checks_rank_and_axis(field,value):
    ir,rel=mixed_fixture('segment_000264')
    assert render_closed_segment(ir,rel,'segment_000264')
    c=rel.certificates[-1];changed=replace(c,**{field:value})
    rel.certificates=(*rel.certificates[:-1],changed)
    rel.transition_specs=tuple(replace(t,certificate_digest=_typed_certificate_digest(changed))
        if t.certificate_digest==_typed_certificate_digest(c) else t for t in rel.transition_specs)
    with pytest.raises(ValueError):render_closed_segment(ir,rel,'segment_000264')


@pytest.mark.parametrize('sid',['segment_000223','segment_000264'])
def test_checked_mixed_witness_bytes(sid):
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]
    path=root/f'trainverify/denote/GeneratedBWLinearDwSequenceMixed{sid[-3:]}.lean'
    assert path.read_text()==witness_source(sid)


def witness_source(sid):
    from trainverify.bridge_emitter.composer import render_closed_relation_declarations
    ir, rel = mixed_fixture(sid)
    chain = rel.dependent_chain_plan
    seg = next(s for s in chain.segments if s.segment_id==sid)
    states = tuple(s for s in chain.states if s.state_id in (seg.pre_state_id,seg.post_state_id))
    live = {f for s in states for f in s.fact_ids}
    sources = {f for t in rel.transition_specs if t.transition_id in seg.transition_ids for f in (*t.pre_facts,*t.post_facts)}
    live.update(r.fact_id for r in chain.relation_facts if r.source in sources)
    universe = SimpleNamespace(complete=True,states=states,anchor_fact=chain.anchor_fact,
        relation_facts=tuple(r for r in chain.relation_facts if r.fact_id in live),
        authority_facts=tuple(a for a in chain.authority_facts if a.fact_id in live))
    ns='SequenceDwMixed'+sid
    imports=[ir.public_statement_module,'denote.KRankBWLinearDwSequenceGeneral','denote.KRankBWLinearDxSequence','denote.KRankBWMatmulHead']
    return ('\n'.join('import '+m for m in imports)+'\n'+render_closed_relation_declarations(universe,ns)
        +'\nnamespace TrainVerify.Denote.'+ns+'\nset_option maxHeartbeats 500000\nnoncomputable section\n'
        +render_closed_segment(ir,rel,sid)+f'\n#print axioms {sid}\nend\nend TrainVerify.Denote.{ns}\n')
