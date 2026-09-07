"""Atomic prefix regressions; no generated Lean or cache writes."""
import importlib
import importlib.util
from dataclasses import replace
import pytest
from embedding_hidden_ids_witness import renderer_fixture, witness_source


def render(ir, relation, sid):
    name = 'trainverify.bridge_emitter.embedding_hidden_ids_renderer'
    assert importlib.util.find_spec(name) is not None, 'atomic hidden/IDs renderer is missing'
    return importlib.import_module(name).render_closed_embedding_hidden_ids_segment(ir, relation, sid)


@pytest.mark.parametrize('k', [2, 3])
def test_interleaved_positive(k):
    fixture = renderer_fixture(k)
    source = render(*fixture)
    assert source == render(*fixture)
    assert source.count('private def segment_000000_smNodes') == 1
    assert source.count('private def segment_000000_pmNodes') == 1
    assert source.count('RelationState.Holds.fold_frame') == 1
    assert 'fw_embedding_hidden_shards_k_rank' in source
    assert 'ShardedRel.fw_embedding_shared_weight_dim1' in source
    assert 'allGatherPrimDimN_chunks_ofFn' in source
    assert 'hstate ids_out' not in source
    assert 'sorry' not in source and 'admit' not in source
    from pathlib import Path
    expected = Path(__file__).resolve().parents[2] / 'trainverify' / 'denote' / f'GeneratedEmbeddingHiddenIdsK{k}.lean'
    assert witness_source(k) == expected.read_text()


@pytest.mark.parametrize('mutation', ['writer', 'order', 'ids-authority', 'chunk-fact', 'frame', 'duplicate-certificate', 'duplicate-transition', 'unproved-post'])
def test_fail_closed_after_successful_baseline(mutation):
    from trainverify.bridge_emitter.parser import Node
    ir, relation, sid = renderer_fixture(3)
    assert render(ir, relation, sid)
    chain = relation.dependent_chain_plan
    if mutation == 'writer':
        ir.pm_nodes[0].ins[1] = 51
    elif mutation == 'order':
        ir.pm_nodes[1], ir.pm_nodes[6] = ir.pm_nodes[6], ir.pm_nodes[1]
    elif mutation == 'ids-authority':
        chain.authority_facts = tuple(x for x in chain.authority_facts if x.fact_id != 'eq_41')
    elif mutation == 'chunk-fact':
        chain.relation_facts = tuple(replace(x, pm_tids=tuple(reversed(x.pm_tids))) if x.fact_id == 'ids_out' else x for x in chain.relation_facts)
    elif mutation == 'frame':
        ir.sm_nodes.append(Node(0, 'FW_float', [40], [999], []))
        chain.segments = (replace(chain.segments[0], sm_range=(0, 3)),)
    elif mutation == 'duplicate-certificate':
        relation.certificates += (relation.certificates[0],)
    elif mutation == 'duplicate-transition':
        chain.segments = (replace(chain.segments[0], transition_ids=('sequence', 'sequence')),)
    else:
        chain.states = (chain.states[0], replace(chain.states[1], fact_ids=(*chain.states[1].fact_ids, 'unproved')))
    with pytest.raises(ValueError):
        render(ir, relation, sid)


def test_unrelated_certificate_and_safe_complete_frame():
    from trainverify.bridge_emitter.parser import Node
    ir, relation, sid = renderer_fixture(2)
    source = render(ir, relation, sid)
    relation.certificates += (replace(relation.certificates[0], ids_tid=700),)
    assert source == render(ir, relation, sid)
    ir.sm_nodes.append(Node(0, 'FW_float', [999], [1000], []))
    chain = relation.dependent_chain_plan
    chain.segments = (replace(chain.segments[0], sm_range=(0, 3)),)
    expanded = render(ir, relation, sid)
    assert 'outs := [1000]' in expanded
    assert expanded.count('RelationState.Holds.fold_frame') == 1


@pytest.mark.parametrize('mutation',['source-axis','source-tid'])
def test_selected_source_record_authority_is_coherent(mutation):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel,sid=renderer_fixture(2)
    assert render(ir,rel,sid)
    chain=rel.dependent_chain_plan;record=chain.relation_facts[0]
    if mutation=='source-axis':
        source=replace(record.source,gather_dim=0)
        c=replace(rel.certificates[0],weight_fact=source)
        rel.certificates=(c,rel.certificates[1])
        rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=(source,),certificate_digest=_typed_certificate_digest(c)),rel.transition_specs[1])
        chain.relation_facts=(replace(record,source=source),*chain.relation_facts[1:])
    else:
        chain.relation_facts=(replace(record,sm_tid=500),*chain.relation_facts[1:])
        ir.sm_nodes[0].ins[1]=500
    with pytest.raises(ValueError):render(ir,rel,sid)


def test_exact_conditional_prefix_witness():
    from embedding_hidden_ids_witness import conditional_prefix_witness
    fixture = renderer_fixture(3)
    source = conditional_prefix_witness(*fixture)
    assert render(*fixture) in source
    assert source == conditional_prefix_witness(*fixture)
    assert '#print axioms segment_000000' in source
    assert 'import denote.EmbeddingHiddenShard' in source
    assert 'import denote.EmbeddingSequenceShard' in source
    import re
    assert all(int(x) <= 500000 for x in re.findall(r'maxHeartbeats (\d+)', source))
