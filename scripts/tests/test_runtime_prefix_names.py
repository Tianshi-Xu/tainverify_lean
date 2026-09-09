"""Lossless syntax compaction, not a changed proof or a relaxed byte limit."""
from Verdict import runtime_prefix as p


def sample():
    return ('import TrainVerifyRuntimePrefixSupport\n' + p._HEADER
        + '\n'.join(
            f'theorem pmSeededPrefixRead_{i}_0 (init : Store) : '
            f'(pmSeededPrefixState_{i} init) 7 = pmSeededPrefixValue_0_0 init := '
            f'prefixRead (pmSeededPrefixSkip_{i-1} init) '
            f'(pmSeededPrefixRead_{i-1}_0 init)\n'
            f'#print axioms pmSeededPrefixRead_{i}_0' for i in range(1, 50))
        + p._FOOTER)


def test_compact_roundtrip_preserves_all_declarations_and_proofs():
    source = sample()
    compact = p.compact_names(source)
    assert compact != source
    assert len(compact.encode()) < len(source.encode()) * 0.8
    assert compact.startswith('import TrainVerifyRuntimePrefixSupport\n')
    assert p.expand_names(compact) == source
    assert p.compact_names(source) == compact
    assert p.compact_names(compact) == compact


def test_compaction_does_not_capture_existing_names_or_strings():
    for extra in ('def s_1 := 1\n', 'def literal := "pmSeededPrefixRead_1_0"\n',
                  '/- nested /- comment -/ -/\n', 'def «quoted» := 1\n'):
        source = sample() + extra
        assert p.compact_names(source) == source
    source = sample().replace('theorem pmSeededPrefixRead_1_0',
                              '-- pmSeededPrefixRead_99_0\ntheorem pmSeededPrefixRead_1_0')
    assert p.expand_names(p.compact_names(source)) == source


def test_qualified_and_extended_identifiers_are_not_partial_matches():
    extra = '#check Other.pmSeededPrefixState_1\n#check pmSeededPrefixState_1prime\n#check αpmSeededPrefixState_1\n'
    extra += "#check pmSeededPrefixState_1'\n#check pmSeededPrefixState_1?\n"
    source = sample() + extra
    compact = p.compact_names(source)
    assert all(line in compact for line in extra.splitlines())
    assert p.expand_names(compact) == source


def test_every_family_and_index_is_restored_without_sorting():
    families = ('State', 'Value', 'Read', 'Written', 'Shape', 'Skip', 'Step',
                'NoWrite', 'Guard', 'InitialShape', 'InitialRead', 'Requests', 'Run')
    source = '\n'.join(f'#check pPrefix{family}_12_3' for family in families) + '\n'
    assert p.expand_names(p.compact_names(source)) == source
    mixed = source + '#check otherPrefixState_1\n'
    assert p.compact_names(mixed) == mixed


def test_initial_shapes_project_only_the_required_conjunct():
    from types import SimpleNamespace as NS
    row = dict(index=0, op='AllToAllPrim', ins=[NS(tid=0)], outs=[NS(tid=1000)],
               scope=NS(ranks=(0,), local_index=0, params=(0, 0)),
               input_shapes=[[1]], output_shapes=[[1]], params=[])
    for count in (1, 2, 100):
        initial = {i: dict(tid=i, shape=[1]) for i in range(count)}
        groups, _ = p._render('p', [row], {}, initial, None, structured=True)
        source = '\n'.join(g.text for g in groups)
        for i in range(count):
            proof = source.split(f'theorem pPrefixInitialShape_{i} ', 1)[1].split('#print', 1)[0]
            projection = 'hInitShapes' + '.2' * i + ('.1' if i < count - 1 else '')
            assert f'(init {i}).shape = [1] := by\n  exact {projection}\n' in proof
            assert 'rcases' not in proof


def test_large_footprint_is_typed_and_preserves_every_ordered_port():
    from types import SimpleNamespace as NS
    rows = [dict(index=j, op='FW_multiref', ins=[NS(tid=7)],
                 outs=[NS(tid=100+j)], scope=None, input_shapes=[[1]],
                 output_shapes=[[1]], params=[]) for j in range(513)]
    rows[0].update(op='AllToAllPrim', scope=NS(ranks=(0,), local_index=0, params=(0, 0)))
    rows[10].update(outs=[NS(tid=110), NS(tid=110)], output_shapes=[[1], [1]])
    rows[11].update(outs=[NS(tid=211), NS(tid=111)], output_shapes=[[1], [1]])
    rows[-1]['ins'] = [NS(tid=8)]
    initial = {i: dict(tid=i, shape=[1]) for i in (7, 8)}
    groups, _ = p._render('p', rows, {}, initial, None, structured=True)
    text = '\n'.join(g.text for g in groups)
    expected = [t.tid for row in rows[:512] for t in row['outs']]
    header = text.split('theorem pPrefixNoWrite_0_512 ', 1)[1].split(' := ', 1)[0]
    assert f'(h : tid ∉ ({expected} : List Tid))' in header
    assert expected[10:14] == [110, 110, 211, 111]


def test_compacted_inventory_retains_original_full_theorem_names(tmp_path):
    from scripts.tests.test_runtime_scoped_prefix import collective_world
    from Verdict.runtime_world import _proof_bundle
    fed = collective_world(tmp_path, 2, chain=True)
    originals = [name for m in fed.receipt['proof_bundle']['modules'] for name in m['theorems']]
    assert any(n.startswith('pmPrefixRead_') for n in originals)
    assert all(not n.startswith(('s_', 'r_', 'v_')) for n in originals)
    assert _proof_bundle(fed.lean, fed.supporting_sources) == fed.receipt['proof_bundle']
