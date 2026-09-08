"""Exact-local metadata is separate from immediate attribute timing."""
from unittest.mock import patch
from Verdict import runtime_prefix as p


def test_support_accounted_and_metadata_preserves_mismatched_order_and_duplicates():
    groups = [p.ProofGroup('def a := 1\ndef b := 2\nattribute [local irreducible] a\n', 2, ('b', 'a', 'b')),
              p.ProofGroup('theorem done : True := trivial\n', 1, (), True)]
    with patch.object(p, 'PROOF_DECLARATION_BUDGET', 2):
        entry, support = p.pack_proofs([groups])
    assert 'TrainVerifyRuntimePrefixSupport.lean' in support
    chunk = support['TrainVerifyRuntimePrefix0000.lean']
    assert groups[0].text in chunk
    assert 'record_prefix_opacity b a b\n' in chunk
    assert 'restore_prefix_opacity\n' in entry
    assert 'attribute [local irreducible] b a b' not in entry
    assert 'Attribute.add n `irreducible Syntax.missing .local' in support['TrainVerifyRuntimePrefixSupport.lean']
    assert 'validate' not in support['TrainVerifyRuntimePrefixSupport.lean']


def test_direct_skip_and_generic_no_write_preserve_inventory():
    from types import SimpleNamespace as NS
    rows = [dict(index=j, op='FW_multiref', ins=[NS(tid=7)],
                 outs=[NS(tid=100+j), NS(tid=200+j)], scope=None,
                 input_shapes=[[1]], output_shapes=[[1], [1]], params=[])
            for j in range(16)]
    rows[0].update(op='AllToAllPrim', outs=[NS(tid=100)], output_shapes=[[1]],
                   scope=NS(ranks=(0,), local_index=0, params=(0, 0)))
    rows[-1]['ins'] = [NS(tid=8)]
    groups, receipt = p._render('p', rows, {},
        {t: dict(tid=t, shape=[1]) for t in (7, 8)}, None, structured=True)
    text = '\n'.join(g.text for g in groups)
    assert 'unfold pPrefixState_1' in text
    assert 'change storeSet' not in text
    assert 'exact prefixFrame_trans' in text
    assert '(([100] ++ [101, 201]) ++ ([102, 202] ++ [103, 203]))' in text
    assert receipt['prefix_length'] == 16
    assert text.count('#print axioms') == len(receipt['kernel_checks'])
    assert '#print axioms prefixFrame_trans' in p.support_source()


def test_support_missing_tampered_and_staging_failure_are_atomic(tmp_path):
    from dataclasses import replace
    import pytest
    from Verdict.runtime_world import publish
    from scripts.tests.test_runtime_scoped_prefix import collective_world
    fed = collective_world(tmp_path, 2, chain=True)
    for fault in ('missing', 'tamper', 'escape'):
        support = dict(fed.supporting_sources)
        if fault == 'missing': del support[p.SUPPORT_FILE]
        else: support[p.SUPPORT_FILE] += '\naxiom forged : True\n' if fault == 'escape' else '-- changed\n'
        with pytest.raises(ValueError):
            publish(replace(fed, supporting_sources=support), tmp_path/fault/'World.lean')
        assert not (tmp_path/fault).exists()
    from pathlib import Path
    original = Path.write_text
    def fail(path, text, *args, **kwargs):
        if path.name == p.SUPPORT_FILE: raise OSError('support write failure')
        return original(path, text, *args, **kwargs)
    with patch.object(Path, 'write_text', fail), pytest.raises(OSError):
        publish(fed, tmp_path/'write-failure'/'World.lean')
    assert not (tmp_path/'write-failure').exists()
    assert not list(tmp_path.glob('trainverify-world-*'))
