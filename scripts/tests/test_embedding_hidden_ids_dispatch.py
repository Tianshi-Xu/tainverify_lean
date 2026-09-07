import pytest
from trainverify.bridge_emitter.compound_rule_dispatch import select_compound_renderer
from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports

HIDDEN='embedding-hidden-sharded-k-rank'
IDS='embedding-sharded-ids-k-rank'
BINDING='embedding_hidden_ids_renderer:render_closed_embedding_hidden_ids_segment'


@pytest.mark.parametrize('family',[(HIDDEN,IDS),(IDS,HIDDEN)])
def test_mixed_embedding_dispatch_and_imports(family):
    assert select_compound_renderer(family)==BINDING
    theorem={HIDDEN:'TrainVerify.Denote.fw_embedding_hidden_shards_k_rank',
             IDS:'TrainVerify.Denote.fw_embedding_allGatherPrimDimN_dim1_shared_weight'}
    imports=plan_closed_segment_imports(family,tuple(theorem[r] for r in family))
    assert set(imports)=={'denote.EmbeddingHiddenShard','denote.EmbeddingSequenceShard'}


def test_public_dispatch_preserves_transition_order_independence():
    from dataclasses import replace
    from scripts.tests.embedding_hidden_ids_witness import renderer_fixture
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel,sid=renderer_fixture(2)
    baseline=render_closed_segment(ir,rel,sid)
    seg=rel.dependent_chain_plan.segments[0]
    rel.dependent_chain_plan.segments=(replace(seg,transition_ids=tuple(reversed(seg.transition_ids))),)
    assert render_closed_segment(ir,rel,sid)==baseline


@pytest.mark.parametrize('family',[(HIDDEN,HIDDEN),(IDS,IDS),(HIDDEN,IDS,IDS),(HIDDEN,IDS,'bw-view-joined')])
def test_mixed_embedding_dispatch_does_not_absorb_other_families(family):
    assert select_compound_renderer(family)!=BINDING
