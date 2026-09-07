from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter.parser import LineageGoal
from trainverify.bridge_emitter.relation_compiler import (
    advance_k_rank_bw_embedding_sequence_reduction_frontiers,
)


def fixture(k, b, s, hidden, vocab):
    ids, weight = 'init:2', 'init:3'
    full_g, local_g = (b, s * k, hidden), (b, s, hidden)
    full_ids, local_ids, wshape = (b, s * k), (b, s), (vocab, hidden)
    sm = SimpleNamespace(step_id='sm:0:0', side='sm', rank=0,
        op='BW_embedding', input_bindings=('sm:g:0', ids, weight),
        input_shapes=(full_g, full_ids, wshape), output_shape=wshape, parameters=())
    chunks = tuple(SimpleNamespace(step_id=f'pm:{r}:0', side='pm', rank=r,
        op='ChunkPrim', parameters=(1,), input_bindings=(ids,),
        output_shape=local_ids) for r in range(k))
    pms = tuple(SimpleNamespace(step_id=f'pm:{k+r}:0', side='pm', rank=r,
        op='BW_embedding', input_bindings=(f'pm:g:{r}', chunks[r].step_id, weight),
        input_shapes=(local_g, local_ids, wshape), output_shape=wshape, parameters=())
        for r in range(k))
    ir = SimpleNamespace(pm_num_ranks=k, init_lineages={
        2: LineageGoal(2, list(full_ids), [(0, 2)], [list(full_ids)]),
        3: LineageGoal(3, list(wshape), [(0, 3)], [list(wshape)]),
    })
    plan = SimpleNamespace(steps=(sm, *chunks, *pms))
    frontier = (sm.step_id, *(x.step_id for x in pms))
    return plan, ir, frontier


def renderer_fixture(k=3, b=2, s=5, hidden=7, vocab=13):
    from dataclasses import replace
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    plan, ir, frontier = fixture(k, b, s, hidden, vocab)
    certs, _, _ = advance_k_rank_bw_embedding_sequence_reduction_frontiers(
        plan, ir, (frontier,), ('reduction',))
    cert = certs[0]
    gradients, ids_tids, outputs = tuple(range(100, 100+k)), tuple(range(200, 200+k)), tuple(range(300, 300+k))
    records = (
        rc.ClosedRelationFactRecord('fact_g', cert.gradient_fact, 'sharded', 1, gradients, None, None,
                                   (b, s*k, hidden), (b, s, hidden), gather_dim=1),
        rc.ClosedRelationFactRecord('fact_i', cert.ids_chunks_fact, 'chunked', 2, ids_tids, None, None,
                                   (b, s*k), (b, s), gather_dim=1),
        rc.ClosedRelationFactRecord('fact_w', cert.weight_fact, 'sharded', 3, (3,), None, None,
                                   (vocab, hidden), (vocab, hidden), gather_dim=0),
        rc.ClosedRelationFactRecord('fact_o', cert.output_fact, 'reduction', 4, outputs, None, None,
                                   (vocab, hidden), (vocab, hidden)),
    )
    before = rc.ClosedRelationStateRecord('state_before', ('fact_g', 'fact_i', 'fact_w'))
    after = rc.ClosedRelationStateRecord('state_after', ('fact_g', 'fact_i', 'fact_w', 'fact_o'))
    transition = replace(rc.CertificateTransitionSpec(
        'transition_000000', cert.rule_id,
        tuple(sorted((cert.gradient_fact, cert.ids_chunks_fact, cert.weight_fact))),
        (cert.output_fact,), (0,), tuple(range(k, 2*k)), cert.lean_theorem),
        certificate_digest=_typed_certificate_digest(cert))
    segment = rc.ClosedDependentSegmentRecord('segment_000000', 'component_000000',
        before.state_id, after.state_id, (transition.transition_id,), (0, 1), (k, 2*k))
    ir.sm_nodes = [Node(0, 'BW_embedding', [1, 2, 3], [4], [])]
    ir.pm_nodes = ([Node(r, 'ChunkPrim', [2], [ids_tids[r]], [1]) for r in range(k)] +
                   [Node(r, 'BW_embedding', [gradients[r], ids_tids[r], 3], [outputs[r]], []) for r in range(k)])
    ir.sm_graph_ref, ir.pm_graph_ref = 'Fixture.sm', 'Fixture.pm'
    chain = SimpleNamespace(relation_facts=records, authority_facts=(),
                            states=(before, after), segments=(segment,))
    relation = SimpleNamespace(certificates=certs, transition_specs=(transition,), dependent_chain_plan=chain)
    return ir, relation, segment.segment_id


@pytest.mark.parametrize('dims', [(2, 1, 8, 64, 16), (4, 1, 4, 64, 16),
                                  (3, 2, 5, 7, 13), (1, 3, 2, 5, 11)])
def test_sequence_embedding_renderer_uses_general_theorem(dims):
    from trainverify.bridge_emitter.bw_embedding_sequence_renderer import render_closed_k_rank_bw_embedding_sequence_segment
    ir, relation, segment = renderer_fixture(*dims)
    source = render_closed_k_rank_bw_embedding_sequence_segment(ir, relation, segment)
    k, b, s, hidden, vocab = dims
    assert f'bw_embedding_seqchunk_K {k} {b} {s} {hidden} {vocab}' in source
    assert 'bw_embedding_seqchunk_4shards_1_8_32' not in source
    # Writer lemmas may mention the same fold; the final stores are defined once.
    assert source.count('private def segment_000000_sm_final') == 1
    assert source.count('private def segment_000000_pm_final') == 1


@pytest.mark.parametrize('case', ['rank-order', 'graph-ranks', 'gradient-shape',
                                  'offset', 'ids-source', 'initial-shape'])
def test_sequence_embedding_rejects_mismatched_authority(case):
    from trainverify.bridge_emitter.relation_compiler import RelationCompositionError
    plan, ir, frontier = fixture(3, 2, 5, 7, 13)
    sm, *rest = plan.steps
    if case == 'rank-order':
        plan.steps[-1].rank = 0
    elif case == 'graph-ranks':
        ir.pm_num_ranks = 4
    elif case == 'gradient-shape':
        pm = plan.steps[-1]
        pm.input_shapes = ((2, 6, 7), *pm.input_shapes[1:])
    elif case == 'offset':
        plan.steps[-1].parameters = (0,)
    elif case == 'ids-source':
        plan.steps[1].input_bindings = ('init:99',)
    else:
        ir.init_lineages[3].tsShape = [14, 7]
        ir.init_lineages[3].tpShapes = [[14, 7]]
    with pytest.raises(RelationCompositionError):
        advance_k_rank_bw_embedding_sequence_reduction_frontiers(plan, ir, (frontier,), ('reduction',))


def test_sequence_renderer_rejects_coordinated_certificate_dimension_change():
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.bw_embedding_sequence_renderer import render_closed_k_rank_bw_embedding_sequence_segment
    ir, relation, segment = renderer_fixture()
    bad = replace(relation.certificates[0], batch_size=3)
    relation.certificates = (bad,)
    relation.transition_specs = (replace(relation.transition_specs[0], certificate_digest=_typed_certificate_digest(bad)),)
    with pytest.raises(ValueError, match='relation metadata'):
        render_closed_k_rank_bw_embedding_sequence_segment(ir, relation, segment)


def vocab_renderer_fixture(k=3, shard_rows=5, hidden=7):
    from dataclasses import replace
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    rule = rc.get_closed_rule_spec('bw-embedding-vocab-sharded-k-rank')
    g = rc.RelationFactSpec('joined', ('sm:g:0',), joined_pm_step='pm:g:0')
    i = rc.RelationFactSpec('sharded', ('init:2', 'init:2'), gather_dim=0)
    weights, outputs = tuple(range(100, 100+k)), tuple(range(300, 300+k))
    w = rc.RelationFactSpec('sharded', ('init:3', *(f'init:{tid}' for tid in weights)), gather_dim=0)
    o = rc.RelationFactSpec('sharded', ('sm:0:0', *(f'pm:{r}:0' for r in range(k))), gather_dim=0)
    full, shard = (k*shard_rows, hidden), (shard_rows, hidden)
    cert = rc.KRankBWEmbeddingVocabCertificate(rule.rule_id, k, 0, shard_rows, hidden,
        full, shard, g, i, w, o, 'sm:0:0', tuple(f'pm:{r}:0' for r in range(k)), rule.lean_theorems[0])
    records = (
        rc.ClosedRelationFactRecord('fact_g', g, 'joined', 1, (), None, None, (2, 5, hidden), (2, 5, hidden), joined_pm_tid=10),
        rc.ClosedRelationFactRecord('fact_i', i, 'sharded', 2, (2,), None, None, (2, 5), (2, 5), gather_dim=0),
        rc.ClosedRelationFactRecord('fact_w', w, 'sharded', 3, weights, None, None, full, shard, gather_dim=0),
        rc.ClosedRelationFactRecord('fact_o', o, 'sharded', 4, outputs, None, None, full, shard, gather_dim=0),
    )
    before = rc.ClosedRelationStateRecord('state_before', ('fact_g', 'fact_i', 'fact_w'))
    after = rc.ClosedRelationStateRecord('state_after', (*before.fact_ids, 'fact_o'))
    transition = replace(rc.CertificateTransitionSpec('transition_000000', rule.rule_id,
        tuple(sorted((g, i, w))), (o,), (0,), tuple(range(k)), cert.lean_theorem),
        certificate_digest=_typed_certificate_digest(cert))
    segment = rc.ClosedDependentSegmentRecord('segment_000000', 'component_000000', before.state_id,
        after.state_id, (transition.transition_id,), (0, 1), (0, k))
    chain = SimpleNamespace(relation_facts=records, authority_facts=(), states=(before, after), segments=(segment,))
    ir = SimpleNamespace(pm_num_ranks=k, sm_graph_ref='Fixture.sm', pm_graph_ref='Fixture.pm',
        sm_nodes=[Node(0, 'BW_embedding', [1, 2, 3], [4], [])],
        pm_nodes=[Node(r, 'BW_embedding', [10, 2, weights[r]], [outputs[r]], [r*shard_rows]) for r in range(k)])
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain)
    return ir, relation, segment.segment_id


@pytest.mark.parametrize('k', [1, 2, 3, 4])
def test_vocab_renderer_has_no_fixed_rank_limit(k):
    from trainverify.bridge_emitter.bw_embedding_vocab_renderer import render_closed_k_rank_bw_embedding_vocab_segment
    ir, relation, segment = vocab_renderer_fixture(k)
    text = render_closed_k_rank_bw_embedding_vocab_segment(ir, relation, segment)
    assert f'bw_embedding_eq_allGather_offset_k {k} 5 7' in text


def test_vocab_registry_uses_arbitrary_rank_theorem():
    from trainverify.bridge_emitter.relation_compiler import get_closed_rule_spec
    spec = get_closed_rule_spec('bw-embedding-vocab-sharded-k-rank')
    assert spec.lean_theorems == ('TrainVerify.Denote.bw_embedding_eq_allGather_offset_k',)
    assert 'denote.BWEmbeddingVocabShardK' in spec.lean_imports


def test_sequence_renderer_exact_source():
    from pathlib import Path
    from scripts.tests.bw_embedding_sequence_witness import render
    root = Path(__file__).resolve().parents[2]
    assert (root / 'trainverify/denote/GeneratedBWEmbeddingSequenceKWitness.lean').read_text() == render()


@pytest.mark.parametrize('dims', [(2, 1, 8, 64, 16), (4, 1, 4, 64, 16),
                                  (3, 2, 5, 7, 13), (1, 3, 2, 5, 11)])
def test_sequence_embedding_derives_rank_and_dimensions(dims):
    plan, ir, frontier = fixture(*dims)
    certs, roots, layouts = advance_k_rank_bw_embedding_sequence_reduction_frontiers(
        plan, ir, (frontier,), ('reduction',))
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rank_count == dims[0]
    assert (cert.batch_size, cert.shard_sequence, cert.hidden_size, cert.vocab_size) == dims[1:]
    assert cert.rule_id == 'bw-embedding-sequence-reduction-k-rank'
    assert cert.lean_theorem == 'TrainVerify.Denote.bw_embedding_seqchunk_K'
    assert roots[0] == cert.gradient_fact.step_triple
    assert layouts[0] == 'sharded'
