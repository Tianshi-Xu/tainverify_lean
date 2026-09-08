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
