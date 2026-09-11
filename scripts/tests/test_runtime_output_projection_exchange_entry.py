"""Ordered helper admission for the output-exchange canonical entry."""
import pytest
from scripts.tests.test_runtime_initial_relation_entry import world
from Verdict.runtime_world import _proof_bundle

HELPERS = """SourceParameterFrame SourceInitialInputEncoding SourceEmbeddingRead
SourceEmbeddingFacts SourceAddRead SourceAddUnit SourceAddFacts SourceMultirefRead
SourceHiddenSequenceExchange SourceLayernormRead SourceLayernormUnit SourceLinearRead
SourceAllGatherRead SourceLinearUnit SourceLayoutRead SourceViewUnit SourceRank4Exchange
SourceTransposeUnit SourceTranspose23Unit SourceRank4ReverseExchange SourceRank4MiddleExchange
SourceMatmulRead SourceMatmulUnit SourceDivRead SourceDivUnit SourceSoftmaxRead
SourceSoftmaxUnit SourceRank4InnerExchange SourceQueryMatmulUnit SourceQueryTransposeUnit
SourceContiguousRead SourceViewFlattenUnit SourceSequenceHiddenExchange
SourcePrimitiveRead SourceEmbeddingPositionUnit SourceEmbeddingUnit""".split()


def source(helpers):
    w = world()
    wtext = w.lean.replace('import denote.SourceScopedPrefix\n',
        'import denote.SourceScopedPrefix\n' + ''.join(f'import denote.{h}\n' for h in helpers), 1)
    return wtext, w.supporting_sources


def test_output_exchange_helper_order_is_admitted():
    text, supporting = source(HELPERS)
    bundle = _proof_bundle(text, supporting)
    assert 'denote.SourceSequenceHiddenExchange' in bundle['modules'][-1]['imports']


@pytest.mark.parametrize('fault', ['duplicate', 'reorder', 'missing-predecessor'])
def test_output_exchange_helper_order_is_not_repaired(fault):
    hs = list(HELPERS)
    i = hs.index('SourceSequenceHiddenExchange')
    if fault == 'duplicate': hs.insert(i, hs[i])
    elif fault == 'reorder': hs[i-1], hs[i] = hs[i], hs[i-1]
    else: hs.remove('SourceViewFlattenUnit')
    text, supporting = source(hs)
    with pytest.raises(ValueError): _proof_bundle(text, supporting)


def test_previous_helper_chain_still_admitted():
    text, supporting = source([h for h in HELPERS if h != 'SourceSequenceHiddenExchange'])
    assert _proof_bundle(text, supporting)['modules'][-1]['role'] == 'entry'
