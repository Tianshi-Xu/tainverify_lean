"""Proof-only Read/Written source sharing; ordered writer semantics stay explicit."""
import re
from types import SimpleNamespace as NS
from Verdict import runtime_prefix as p


def fixture():
    rows = [dict(index=j, op='FW_multiref', ins=[NS(tid=70000001)],
                 outs=[NS(tid=100+j), NS(tid=200+j)], scope=None,
                 input_shapes=[[1]], output_shapes=[[1], [1]], params=[])
            for j in range(16)]
    rows[0].update(op='AllToAllPrim', outs=[NS(tid=100)], output_shapes=[[1]],
                   scope=NS(ranks=(0,), local_index=0, params=(0, 0)))
    rows[4]['outs'] = [NS(tid=104), NS(tid=104)]
    rows[5].update(op='FW_add', ins=[NS(tid=104), NS(tid=104)],
                   outs=[NS(tid=104)], input_shapes=[[1], [1]], output_shapes=[[1]])
    rows[6]['ins'] = [NS(tid=104)]
    rows[-1]['ins'] = [NS(tid=80000001)]
    groups, receipt = p._render('p', rows, {},
        {t: dict(tid=t, shape=[1]) for t in (70000001, 80000001)}, None, structured=True)
    return '\n'.join(g.text for g in groups), receipt


def seeded_kernel_fixture(root):
    """Small production-rendered seed/external/duplicate/two-output BW case."""
    from scripts.tests.test_runtime_seeded_prefix import linear_world
    return linear_world(root, 2, layout=(
        'BW_transpose', {'dim0': 1, 'dim1': 2}, (1, 4, 3)))


def test_seeded_kernel_fixture_covers_read_written_boundaries(tmp_path):
    fed = seeded_kernel_fixture(tmp_path)
    text = '\n'.join(p.expand_names(s) for s in [*fed.supporting_sources.values(), fed.lean])
    receipt = fed.receipt['scoped_prefix']['pm']
    # These nodes are inside the checked prefix, not merely present in Data.
    assert receipt['prefix_nodes'][11] == 11
    assert receipt['prefix_nodes'][14] == 14
    assert 'op := "OpName.BW_linear", ins := [11, 8, 3], outs := [12, 13]' in text
    assert 'op := "OpName.BW_contiguous", ins := [17, 17], outs := [18]' in text
    for port, tid in enumerate((12, 13)):
        assert (f'(pmSeededPrefixState_12 init) {tid} = '
                f'pmSeededPrefixValue_11_{port} init') in text
    assert 'pmSeededPrefixRead_7_1 init' in body(text, 'pmSeededPrefixRead_11_2')
    assert 'pmSeededPrefixInitialRead_4 init' in body(text, 'pmSeededPrefixRead_7_1')
    assert 'pmInitialWithSeeds_seed_0 init' in body(text, 'pmSeededPrefixRead_10_0')
    assert body(text, 'pmSeededPrefixRead_14_1').strip() == 'pmSeededPrefixRead_14_0 init'
    for suffix in ('Success', 'Output', 'OutputShape', 'Frame', 'Continuation'):
        assert 'pmSeededPrefix' + suffix in receipt['kernel_checks']
    assert text.count('#print axioms') == sum(
        len(m['theorems']) for m in fed.receipt['proof_bundle']['modules'])


def body(text, name):
    return text.split('theorem '+name+' ', 1)[1].split(' := ', 1)[1].split('#print', 1)[0]


def test_read_direct_composition_omits_repeated_tid_and_keeps_latest_anchors():
    text, receipt = fixture()
    last = body(text, 'pPrefixRead_15_0')
    assert '80000001' not in last
    assert 'prefixRead' in last and 'pPrefixNoWrite_0_8 init' in last
    assert 'pPrefixWritten_4_1 init' in body(text, 'pPrefixRead_5_0')
    assert 'pPrefixRead_5_0 init' in body(text, 'pPrefixRead_5_1')
    assert 'pPrefixWritten_5_0 init' in body(text, 'pPrefixRead_6_0')
    assert receipt['prefix_length'] == 16
    assert text.count('#print axioms') == len(receipt['kernel_checks'])


def test_written_reduces_only_current_store_without_computed_expression_copy():
    text, _ = fixture()
    written = body(text, 'pPrefixWritten_5_0')
    assert 'elemwiseAdd' not in written
    assert 'pPrefixState_6' in written
    assert 'pPrefixValue_5_0' in written
    assert 'pPrefixRead_5_0 init' in written
    assert 'pPrefixRead_5_1 init' in written
    assert 'unfold pPrefixState_5' not in written
