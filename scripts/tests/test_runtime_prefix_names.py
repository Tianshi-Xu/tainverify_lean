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


def test_axiom_query_compaction_is_exact_ordered_and_bounded():
    import re
    source = sample() + '#print axioms Other.fact\n#print axioms pmSeededPrefixRead_1_0  \n'
    compact = p.compact_names(source)
    assert 'prefix_names pmSeededPrefix + ! where\n' in compact
    assert '#print axioms ' not in compact
    assert compact.count('#a ') == source.count('#print axioms ')
    assert '#a Other.fact\n' in compact
    assert p.expand_names(compact) == source
    assert re.findall(r'^#print axioms (\S+)', p.expand_names(compact), re.M) == re.findall(
        r'^#print axioms (\S+)', source, re.M)
    suffix = '#print axioms Outside.fact\n'
    assert p.expand_names(compact + suffix) == source + suffix
    for replacement in ('#print axioms pmSeededPrefixRead_1_0\t\n',
                        '  #print axioms pmSeededPrefixRead_1_0\n',
                        "#print axioms Other.fact'\n"):
        extended = sample() + replacement
        assert p.expand_names(p.compact_names(extended)) == extended


def test_axiom_query_unsupported_forms_fall_back_whole_source():
    for extra in ('#a pmSeededPrefixRead_1_0\n', '-- #a collision\n',
                  'def literal := "#a collision"\n',
                  '#print  axioms pmSeededPrefixRead_1_0\n',
                  '#print\taxioms pmSeededPrefixRead_1_0\n',
                  '#print axioms\tpmSeededPrefixRead_1_0\n',
                  '#print axioms pmSeededPrefixRead_1_0 -- comment\n',
                  '-- #print axioms pmSeededPrefixRead_1_0\n',
                  '#print axioms (pmSeededPrefixRead_1_0)\n',
                  '#print axioms pmSeededPrefixRead_1_0 Other.fact\n',
                  '#print axioms «quoted»\n', '/- #print axioms x -/\n',
                  '#print axioms\npmSeededPrefixRead_1_0\n'):
        source = sample() + extra
        assert p.compact_names(source) == source, extra


def test_axiom_query_markers_preserve_legacy_bindings_and_queries():
    for indent in (' ', '  '):
        for helper in ('', ' +'):
            for query in ('', ' !'):
                packed = ('prefix_names tinyPrefix' + helper + query + ' where\n'
                          + indent + 'def r_0 (pR : Nat) := pR\n'
                          + indent + ('#a' if query else '#print axioms') + ' r_0\n')
                name = 'prefixRead' if helper else 'pR'
                expected = f'def tinyPrefixRead_0 ({name} : Nat) := {name}\n#print axioms tinyPrefixRead_0\n'
                assert p.expand_names(packed) == expected
            legacy = 'prefix_names tinyPrefix' + helper + ' where\n' + indent + '#a r_0\n'
            assert p.expand_names(legacy) == '#a tinyPrefixRead_0\n'
    no_queries = sample().replace('#print axioms ', '#check ')
    assert ' ! where' not in p.compact_names(no_queries)


def test_axiom_alias_is_exact_native_macro_after_name_restoration():
    support = p.support_source()
    assert 'macro "#a " id:ident : command => `(#print axioms $id)' in support
    assert 'elabCommand (expand pref helpers helpersV2 cmd)' in support


def test_fixed_helper_is_compacted_in_declarations_and_applications():
    source = sample() + 'def prefixRead (x : Nat) := x\n'
    compact = p.compact_names(source)
    assert 'def pR (x : Nat) := x' in compact
    assert 'pR (k_0 z) (r_0_0 z)' in compact
    assert 'prefixRead' not in compact
    assert p.expand_names(compact) == source


def test_one_space_wrapper_preserves_legacy_and_current_expansion():
    source = sample()
    compact = p.compact_names(source)
    header, marker, body = compact.partition(' where\n')
    assert marker and body.startswith(' namespace ')
    assert p.expand_names(compact) == source
    legacy = header + marker + ''.join(' ' + line if line.strip() else line
                                       for line in body.splitlines(keepends=True))
    assert p.expand_names(legacy) == source
    assert len(legacy) - len(compact) == sum(bool(line.strip()) for line in body.splitlines())


def test_indented_source_is_not_mistaken_for_wrapper_offset():
    source = sample().replace(p._HEADER, '  ' + p._HEADER.replace('\n', '\n  '))
    assert p.compact_names(source) == source


def test_frequent_binders_are_losslessly_compacted():
    source = sample().replace('(init : Store)', '(init : Store) (hInitShapes : True)')
    compact = p.compact_names(source)
    assert '(z : Store) (z_ : True)' in compact
    assert p.expand_names(compact) == source
    for extra in ('def z := 1\n', 'def z_ := 1\n'):
        assert p.compact_names(source + extra) == source + extra
    extended = source + '#check Other.init\n#check Other.hInitShapes\n'
    assert p.expand_names(p.compact_names(extended)) == extended


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


def test_legacy_unmarked_helper_alias_is_not_reinterpreted():
    for indent in (' ', '  '):
        source = 'def tinyPrefixRead_0 (pR : Nat) := pR\n'
        legacy = 'prefix_names tinyPrefix where\n' + indent + 'def r_0 (pR : Nat) := pR\n'
        assert p.expand_names(legacy) == source


def test_helper_marker_is_emitted_only_for_actual_helper_replacement():
    source = sample()
    compact = p.compact_names(source)
    assert 'prefix_names pmSeededPrefix + ! where\n' in compact
    assert p.expand_names(compact) == source
    without_helper = source.replace('prefixRead ', 'otherRead ')
    compact = p.compact_names(without_helper)
    assert 'prefix_names pmSeededPrefix ! where\n' in compact
    assert p.expand_names(compact) == without_helper
    imports_only = without_helper.replace('import TrainVerifyRuntimePrefixSupport\n',
                                         'import prefixRead\n') + '-- prefixRead\n'
    assert ' + ! where' not in p.compact_names(imports_only)
    assert p.expand_names(p.compact_names(imports_only)) == imports_only


def test_fixed_helper_collision_returns_exact_original_source():
    for extra in ('def pR := 1\n', '#check pR\n',
                  'example (pR : Nat) := pR\n'):
        source = sample() + extra
        assert p.compact_names(source) == source


def test_fixed_helper_imports_and_whole_token_comment_policy():
    imports = 'import TrainVerifyRuntimePrefixSupport\nimport Other.prefixRead\nimport prefixRead\n'
    tokens = ('Other.prefixRead', 'prefixRead.foo', 'prefixRead_more',
              'prefixRead1', 'αprefixRead', 'prefixReadα', "prefixRead'",
              'prefixRead?', 'prefixRead!', 'Other.pR', 'pR.foo',
              'pR_more', 'pR1', 'αpR', "pR'", 'pR?', 'pR!')
    extra = ''.join(f'#check {token}\n' for token in tokens)
    extra += '-- prefixRead pR init z pmSeededPrefixRead_99_0 r_99_0\n'
    source = sample().replace('import TrainVerifyRuntimePrefixSupport\n', imports) + extra
    compact = p.compact_names(source)
    assert compact != source
    assert compact.startswith(imports)
    assert all(line in compact for line in extra.splitlines())
    assert p.expand_names(compact) == source
    for unsupported in ('/- prefixRead pR -/\n',
                        'def literal := "prefixRead"\n'):
        assert p.compact_names(source + unsupported) == source + unsupported


def test_fixed_helper_legacy_and_new_inverse():
    original = ('import TrainVerifyRuntimePrefixSupport\n'
                '#check tinyPrefixRead_1_0\n#check prefixRead\n'
                '#check init\n#check hInitShapes\n')
    for helper in ('prefixRead', 'pR'):
        for indent in (' ', '  '):
            compact = ('import TrainVerifyRuntimePrefixSupport\n'
                       + ('prefix_names tinyPrefix + where\n' if helper == 'pR'
                          else 'prefix_names tinyPrefix where\n') + ''.join(
                           indent + line + '\n' for line in
                           ('#check r_1_0', f'#check {helper}', '#check z', '#check z_')))
            assert p.expand_names(compact) == original


def helper_kernel_fixture():
    """Portable real-helper source for the parent-owned Lean kernel check."""
    return ('import TrainVerifyRuntimePrefixSupport\n'
            'set_option maxHeartbeats 500000\n'
            'namespace TrainVerify.Denote.HelperAliasFixture\n'
            'theorem tinyPrefixRead_0 (init : Store) : init 0 = init 0 := rfl\n'
            + ''.join(
                f'theorem tinyPrefixRead_{i} (init : Store) : init 0 = init 0 :=\n'
                f'  prefixRead (xs := []) (fun _ _ => rfl) (tinyPrefixRead_{i-1} init)\n'
                for i in range(1, 4))
            + 'end TrainVerify.Denote.HelperAliasFixture\n'
            '#check TrainVerify.Denote.HelperAliasFixture.tinyPrefixRead_3\n')


def test_real_helper_fixture_is_lossless_and_profitable():
    source = helper_kernel_fixture()
    compact = p.compact_names(source)
    assert compact.count('pR (xs := [])') == 3
    assert p.expand_names(compact) == source
    legacy = compact.replace('pR (xs := [])', 'prefixRead (xs := [])')
    assert p.expand_names(legacy) == source
    assert len(legacy.encode()) - len(compact.encode()) == 3 * (len('prefixRead') - len('pR'))
    assert len(compact.encode()) < len(source.encode())
    tiny = 'def xPrefixRead_0 := prefixRead\n'
    assert p.compact_names(tiny) == tiny


def test_support_restores_unqualified_helper_before_sequential_elaboration():
    support = p.support_source()
    expansion = support.split('private def expandName', 1)[1].split('private partial def expand', 1)[0]
    assert 'let .str .anonymous text := n | return n' in expansion
    assert 'if helpers && text == "pR" then return Name.mkSimple "prefixRead"' in expansion
    assert 'for cmd in stx[6].getArgs do\n    elabCommand (expand pref helpers helpersV2 cmd)' in support


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
