"""The isolated localStep syntax vocabulary must preserve canonical bytes."""
import pytest
from Verdict import runtime_prefix as p

MODULE = 'TrainVerifyRuntimePrefixNamesV3'
IMPORT = f'import {MODULE}\n'
HELPER = 'AllToAllSourceFaithful.localStep'


def sample(helper=HELPER):
    return ('import TrainVerifyRuntimePrefixSupport\n\n' + p._HEADER
            + ''.join(f'def tinyPrefixStep_{i} (init : Store) :=\n'
                      f'  {helper} tinyPrefixState_0 init\n'
                      f'#print axioms tinyPrefixStep_{i}\n' for i in range(12))
            + p._FOOTER + '\n#print axioms Other.fact  \n')


def test_public_qualified_codec_is_versioned_and_canonical():
    source = sample()
    encoded = p.compact_names(source)
    assert 'prefix_names_v3 tinyPrefix ! where\n' in encoded
    assert encoded.count(IMPORT) == 1
    assert encoded.count('pL s_0 z') == 12
    assert HELPER not in encoded
    assert len(encoded.encode()) < len(source.encode())
    assert p.expand_names(encoded) == source
    assert p.compact_names(encoded) == encoded
    suffix = '#print axioms Outside.fact\n'
    assert p.expand_names(encoded + suffix) == source + suffix


@pytest.mark.parametrize('where', ['single', 'final_only', 'chunk', 'final', 'both', 'neither'])
def test_pack_adds_exact_support_only_where_used(where):
    from pathlib import Path
    plain = sample('ordinaryStep').split(p._HEADER, 1)[1].split(p._FOOTER)[0]
    qualified = plain.replace('ordinaryStep', HELPER)
    if where in ('single', 'final_only'):
        groups = [p.ProofGroup(qualified, 1, (), final=where == 'final_only')]
    else:
        groups = [p.ProofGroup(qualified if where in ('chunk', 'both') else plain, 50, ()),
                  p.ProofGroup(plain, 50, ()),
                  p.ProofGroup(qualified if where in ('final', 'both') else plain, 1, (), final=True)]
    entry, supporting = p.pack_proofs([groups], names_v3=True)
    assert supporting[p.SUPPORT_FILE] == p.support_source()
    expected = where != 'neither'
    assert (MODULE + '.lean' in supporting) == expected
    if expected:
        assert p.NAMES_V3_MODULE == MODULE
        assert p.NAMES_V3_FILE == MODULE + '.lean'
        assert supporting[p.NAMES_V3_FILE] == p.names_v3_source()
        assert p.names_v3_source() == Path(p.__file__).with_name('runtime_prefix_names_v3.lean').read_text()
    sources = [entry] + [s for n, s in supporting.items() if n.startswith(p.PREFIX_MODULE) and n not in (p.SUPPORT_FILE, MODULE + '.lean')]
    for source in sources:
        canonical = p.expand_names(source)
        assert (IMPORT in source) == (HELPER in canonical)
        assert IMPORT not in canonical
        assert p.expand_names(p.compact_names(canonical)) == canonical
    assert (IMPORT in entry) == (where in ('single', 'final_only', 'final', 'both'))


@pytest.mark.parametrize('extra', [
    'def pL := 1\n', '#check pL\n', 'example (pL : Nat) := pL\n',
    'def literal := "AllToAllSourceFaithful.localStep"\n',
    '#check «AllToAllSourceFaithful.localStep»\n',
    '#check `AllToAllSourceFaithful.localStep\n', '/- localStep -/\n',
    IMPORT, 'import TrainVerifyRuntimePrefixNamesV3 Other\n',
])
def test_collision_and_unsupported_source_are_preserved_whole(extra):
    source = sample() + extra
    assert p.compact_names(source) == source


@pytest.mark.parametrize('token', [
    'Other.AllToAllSourceFaithful.localStep', HELPER + '.more', HELPER + "'",
    HELPER + '?', HELPER + '!', HELPER + '_more', 'α' + HELPER,
    'Other.pL', 'pL.more', "pL'", 'pL?', 'pL!', 'pL_more',
])
def test_only_exact_qualified_name_changes(token):
    extra = f'#check {token}\n-- {HELPER} pL tinyPrefixStep_99\n'
    source = sample() + extra
    encoded = p.compact_names(source)
    assert 'prefix_names_v3 ' in encoded
    assert all(line in encoded for line in extra.splitlines())
    assert p.expand_names(encoded) == source


@pytest.mark.parametrize('plus', ['', ' +', ' + +'])
@pytest.mark.parametrize('query', ['', ' !'])
@pytest.mark.parametrize('indent', [' ', '  '])
def test_legacy_vocabularies_and_v3_reuse_exact_old_suffixes(plus, query, indent):
    body = 'def r_0 (pL pS pF v2 : Nat) := pL\n'
    query_body = ('#a' if query else '#print axioms') + ' r_0\n'
    encoded_body = ''.join(indent + line for line in (body + query_body).splitlines(keepends=True))
    old = f'prefix_names tinyPrefix{plus}{query} where\n' + encoded_body
    expected = body.replace('r_0', 'tinyPrefixRead_0') + '#print axioms tinyPrefixRead_0\n'
    if plus == ' + +':
        expected = expected.replace('pS', 'storeSet_eq_of_not_mem_fst').replace('pF', 'prefixFrame_trans')
    assert p.expand_names(old) == expected
    new = IMPORT + old.replace('prefix_names ', 'prefix_names_v3 ', 1)
    assert p.expand_names(new) == expected.replace('pL', HELPER)
    assert p.expand_names(new + old) == expected.replace('pL', HELPER) + expected


@pytest.mark.parametrize('bad', ['prefix_names_v5 tinyPrefix where\n def r_0 := 0\n',
                                  'prefix_names tinyPrefix + + + where\n def r_0 := 0\n',
                                  'prefix_names_v3 tinyPrefix + + + where\n def r_0 := 0\n'])
def test_unknown_headers_rejected_even_before_valid_suffix(bad):
    with pytest.raises(ValueError):
        p.expand_names(bad)
    with pytest.raises(ValueError):
        p.expand_names(bad + 'prefix_names tinyPrefix where\n def r_0 := 0\n')


@pytest.mark.parametrize('preamble', ['', IMPORT + IMPORT, IMPORT + '\n'])
def test_v3_import_ownership_is_closed(preamble):
    with pytest.raises(ValueError, match='import'):
        p.expand_names(preamble + 'prefix_names_v3 tinyPrefix where\n def t_0 := pL\n')


def test_no_qualified_helper_keeps_exact_legacy_output_and_imports():
    imports = 'import TrainVerifyRuntimePrefixSupport\nimport AllToAllSourceFaithful.localStep\n'
    source = imports + ''.join(f'def tinyPrefixStep_{i} (init : Nat) := init\n' for i in range(12))
    expected = imports + 'prefix_names tinyPrefix where\n' + ''.join(f' def t_{i} (z : Nat) := z\n' for i in range(12))
    assert p.compact_names(source) == expected
    assert p.expand_names(expected) == source
    ordinary = source + 'def ordinary (pL v2 : Nat) := pL + v2\n'
    assert p.compact_names(ordinary) == expected + ' def ordinary (pL v2 : Nat) := pL + v2\n'


@pytest.mark.parametrize('stem', ['ordinary', 'pL'])
@pytest.mark.parametrize('wrapper', ['prefix_names', 'prefix_names_v3'])
def test_wrapper_stem_metadata_preserves_legacy_identifier_domain(stem, wrapper):
    imported = IMPORT if wrapper == 'prefix_names_v3' else ''
    text = imported + f'{wrapper} {stem} where\n def r_0 : Nat := 7\n'
    assert p.expand_names(text) == f'def {stem}Read_0 : Nat := 7\n'


@pytest.mark.parametrize('split', [False, True])
def test_default_pack_never_changes_legacy_helper_bundles(split):
    body = sample().split(p._HEADER, 1)[1].split(p._FOOTER)[0]
    groups = [p.ProofGroup(body, 50 if split else 1, ())]
    if split:
        groups.append(p.ProofGroup(body, 50, (), True))
    entry, supporting = p.pack_proofs([groups])
    assert MODULE + '.lean' not in supporting
    for source in [entry, *supporting.values()]:
        assert IMPORT not in source
        assert 'prefix_names_v3 ' not in source
    assert HELPER in p.expand_names(entry)
