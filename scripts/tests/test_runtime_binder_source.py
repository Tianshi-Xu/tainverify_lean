"""Lossless scoped binder representation; Lean validation belongs to the caller."""
import importlib
import importlib.util
import re

import pytest


FOUR = (' (s p t q : Store)\n'
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)')
WITH_H = FOUR + '\n    (h : InitialParameterValues s p)'
SM = ' (s t : Store) (h : smDenoteWithInputs s = some t)'
PM = ' (s t : Store) (h : pmDenoteWithInputs s = some t)'


def api():
    assert importlib.util.find_spec('Verdict.runtime_binder_source'), 'binder compactor missing'
    return importlib.import_module('Verdict.runtime_binder_source')


def family(header=WITH_H, count=8, prefix='probe'):
    return ''.join(f'theorem {prefix}_{i}{header} : t = t := by\n'
                   f'  exact rfl\n#print axioms {prefix}_{i}\n' for i in range(count))


@pytest.mark.parametrize('header,names', [
    (' (smInit pmInit smFinal pmFinal : Store) (hs : smDenoteWithInputs smInit = some smFinal) (hp : pmDenoteWithInputs pmInit = some pmFinal)', 'smInit pmInit smFinal pmFinal hs hp'),
    (' (init final : Store) (h : pmDenoteWithInputs init = some final)', 'init final h'),
    (' (init final : Store) (h : smDenoteWithInputs init = some final)', 'init final h')])
def test_original_input_relation_and_read_headers(header, names):
    text = family(header).replace(' : t = t :=', ' : True :=').replace('exact rfl', 'trivial')
    packed = api().compact(text)
    assert len(packed.encode()) < len(text.encode())
    assert 'include ' + names + '\n' in packed
    assert api().expand(packed) == text


def test_exact_inverse_names_headers_and_proofs():
    source = 'namespace TrainVerify.Denote.RuntimeWorld\n' + family() + 'end\n'
    module = api()
    result = module.compact(source)
    assert len(result.encode()) < len(source.encode())
    assert 'variable' + WITH_H + '\ninclude s p t q hs hp h\n' in result
    assert module.expand(result) == source
    assert re.findall(r'^theorem (\w+)', result, re.M) == re.findall(r'^theorem (\w+)', source, re.M)
    assert re.findall(r'^#print.*$', result, re.M) == re.findall(r'^#print.*$', source, re.M)
    assert result.count(' : t = t := by\n  exact rfl\n') == 8
    assert module.compact(result) == result
    assert module.expand(module.expand(result)) == source


@pytest.mark.parametrize('header,names', [(FOUR, 's p t q hs hp'),
                                         (SM, 's t h'), (PM, 's t h')])
def test_other_exact_headers(header, names):
    source = family(header)
    result = api().compact(source)
    assert len(result.encode()) < len(source.encode())
    assert f'variable{header}\ninclude {names}\n' in result
    assert api().expand(result) == source


def test_different_headers_and_commands_close_scopes():
    pieces = [family(WITH_H, prefix='a'), family(SM, prefix='b'),
              'theorem alone (x : Nat) : x = x := rfl\n#print axioms alone\n',
              family(FOUR, prefix='c'), 'end\nnamespace Next\n',
              family(PM, prefix='d')]
    source = ''.join(pieces)
    result = api().compact(source)
    assert result.count('section RBS_') == 4
    assert api().expand(result) == source
    # Every original theorem occurs in order, with exactly its own header's scope.
    active = None
    for line in result.splitlines():
        if line.startswith('section RBS_'):
            assert active is None
            active = line.removeprefix('section ')
        elif line.startswith('end RBS_'):
            assert active is not None
            assert line == 'end ' + active
            active = None
        elif line.startswith('theorem alone') or line == 'namespace Next':
            assert active is None
    assert active is None


@pytest.mark.parametrize('prefix', [
    '/- nested /- block -/ comment -/\n', 'def quoted := "hello"\n',
    'def quoted := "\n', '`(theorem fake : True := by trivial)\n',
    'variable (s : Store)\n', 'include s\n', 'omit s\n',
    'def Store := Nat\n', 'namespace X\ndef smDenoteWithInputs := id\nend X\n',
    'abbrev pmDenoteWithInputs := id\n', 'axiom InitialParameterValues : Prop\n',
    'def Option.some := id\n', 'def RBS_0 := 0\n',
    '-- RBS_99\n',
])
def test_unsupported_and_collisions_preserve_input(prefix):
    source = prefix + family()
    assert api().compact(source) == source
    assert api().expand(source) == source


@pytest.mark.parametrize('change', [
    lambda s: s.replace('(s p t q : Store)', '(p s t q : Store)'),
    lambda s: s.replace('(h : InitialParameterValues s p)', '(h : InitialParameterValues p s)'),
    lambda s: s.replace('(h : InitialParameterValues s p)', '{h : InitialParameterValues s p}'),
    lambda s: s.replace(' : t = t', ' (tid : Nat) : t = t'),
    lambda s: s.replace('  exact rfl', '  have q := "quoted"\n  exact rfl'),
    lambda s: s.replace('theorem probe_', 'theorem «probe_'),
    lambda s: s.replace('\n', '\r\n'),
    lambda s: s.replace('#print axioms ', '#check '),
])
def test_unsupported_records_are_not_partially_parsed(change):
    source = change(family())
    assert api().compact(source) == source


def test_singletons_boundaries_and_small_pair_cost():
    module = api()
    pair = family(PM, count=2)
    packed = module.compact(pair)
    assert len(packed.encode()) < len(pair.encode())
    assert module.expand(packed) == pair
    for source in ['', family(count=1),
                   family(count=1) + '\n' + family(count=1, prefix='next'),
                   family(count=1) + '#check Store\n' + family(count=1, prefix='next')]:
        assert module.compact(source) == source
        assert module.expand(source) == source


def test_prefix_and_existing_term_notation_remain_exact():
    prefix = ('import SourceData\n-- keep prefix bytes\n'
              'section RuntimeRelationSource\n'
              'local notation "r0" => pmInputRequests.drop\n'
              'open TrainVerify.Denote.RuntimeWorld\n')
    source = prefix + family() + 'end RuntimeRelationSource\n'
    result = api().compact(source)
    assert result.startswith(prefix)
    assert len(result) < len(source)
    assert api().expand(result) == source
    assert api().expand('untouched prefix\n' + result) == 'untouched prefix\n' + source


def test_scope_modifiers_are_not_moved_onto_section():
    for prefix in ['set_option maxHeartbeats 500000 in\n', '@[simp]\n', 'private\n']:
        source = prefix + family()
        assert api().compact(source) == source


def test_canonical_parameter_definition_and_mixed_families():
    parameter = ('def InitialParameterValues (initSM initPM : Store) : Prop :=\n'
                 '  All (fun spec => spec.values initSM initPM) initialParameterSpecs\n')
    source = ('namespace TrainVerify.Denote.RuntimeWorld\n' + parameter +
              'set_option maxHeartbeats 500000\n' + family(WITH_H, prefix='value') +
              family(PM, prefix='read') + 'end\n')
    result = api().compact(source)
    assert len(result.encode()) < len(source.encode())
    assert api().expand(result) == source
    assert re.findall(r'^theorem (\w+)', result, re.M) == re.findall(r'^theorem (\w+)', source, re.M)
    assert re.findall(r'^#print.*$', result, re.M) == re.findall(r'^#print.*$', source, re.M)


@pytest.mark.parametrize('command', ['theorem extra : True := True.intro', 'def extra : Nat := 0',
    'example : True := True.intro', '#check True', 'namespace Other'])
def test_indented_commands_are_not_theorem_continuations(command):
    text = family(SM, count=4).replace(' : t = t := by\n  exact rfl\n', ' : True := True.intro\n')
    text = text.replace('#print axioms probe_0\n', '  '+command+'\n#print axioms probe_0\n', 1)
    packed = api().compact(text)
    assert api().expand(packed) == text
    assert 'section RBS_' not in packed[:packed.index('  '+command)]


def test_invalid_encoded_scope_is_not_silently_expanded():
    result = api().compact(family())
    with pytest.raises(ValueError):
        api().expand(result.replace('include s p t q hs hp h', 'include s'))
    with pytest.raises(ValueError):
        api().expand(result.replace('end RBS_0\n', ''))
    with pytest.raises(ValueError):
        api().expand(result.replace('#print axioms probe_0', '#check probe_0'))


@pytest.mark.parametrize('count', [2, 7])
def test_exact_hvalues_header_shares_without_dropping_contract(count):
    header = FOUR + '\n    (hvalues : InitialParameterValues s p)'
    source = family(header, count=count, prefix='full_values')
    packed = api().compact(source)
    assert len(packed.encode()) < len(source.encode())
    assert 'variable' + header + '\ninclude s p t q hs hp hvalues\n' in packed
    assert api().expand(packed) == source
    assert api().compact(packed) == packed
    assert re.findall(r'^theorem (\w+)', packed, re.M) == re.findall(r'^theorem (\w+)', source, re.M)
    assert re.findall(r'^#print.*$', packed, re.M) == re.findall(r'^#print.*$', source, re.M)


def test_hvalues_and_legacy_headers_do_not_merge_scopes():
    header = FOUR + '\n    (hvalues : InitialParameterValues s p)'
    source = family(WITH_H, count=2, prefix='legacy') + family(header, count=2, prefix='full_values')
    packed = api().compact(source)
    assert packed.count('section RBS_') == 2
    assert 'include s p t q hs hp h\n' in packed
    assert 'include s p t q hs hp hvalues\n' in packed
    assert api().expand(packed) == source
