"""Finite v3 vocabulary and inherited conservative guard coverage."""
import re
import pytest
from Verdict import runtime_read_source as codec
from test_runtime_read_source_v3 import sample

NEW_TERMS = codec._ENTRY_TERMS_V3[len(codec._ENTRY_TERMS):]
NEW_HELPERS = codec._HELPERS_V3[len(codec._HELPERS):]


def terms_source(term):
    return ''.join(f'def probe{i} := {term}\n' for i in range(40))


@pytest.mark.parametrize('term', NEW_TERMS)
def test_every_fixed_term_and_exact_token_roundtrip(term):
    untouched = f'-- {term}\ndef external := Other.{term}\ndef field := {term}.field\n'
    text = terms_source(term) + untouched
    packed = codec.compact(text, version=3)
    assert '-- RuntimeReadSource v3\n' in packed
    assert untouched in packed
    assert codec.expand(packed) == text
    assert codec.compact(packed, version=3) == packed
    assert codec.expand(codec.compact(text)) == text


@pytest.mark.parametrize('helper', NEW_HELPERS)
@pytest.mark.parametrize('world', ['pm', 'sm'])
@pytest.mark.parametrize('aliased', [False, True])
def test_every_fixed_helper_world_and_legacy_alias(helper, world, aliased):
    text = sample(helper).replace('pm', world)
    if aliased:
        text = ('section RuntimeRelationSource\n' + f'local notation "r1" => {helper}\n' +
                text.replace(helper, 'r1') + 'end RuntimeRelationSource\n')
    packed = codec.compact(text, version=3)
    assert '-- RuntimeReadSource v3\n' in packed
    assert codec.expand(packed) == text


@pytest.mark.parametrize('name', sorted({p for t in NEW_TERMS+NEW_HELPERS for p in (t,*t.split('.'))}))
@pytest.mark.parametrize('binding', ['def Other.{name} := other', 'variable ({name} : Type)',
    'def f := fun {name} => other', 'def f := by\n  intro {name}', '#print {name}'])
def test_new_roots_members_and_names_are_protected(name, binding):
    text = binding.format(name=name) + '\n' + sample()
    assert codec.compact(text, version=3) == text


@pytest.mark.parametrize('prefix', ['-- c0 collision\n', '-- vP0 collision\n', 'namespace Other\n',
    'open Other\n', '/- comment -/\n', 'def str := "text"\n', 'axiom p : True\n',
    'def p := by\n  rcases pair with ⟨x, y⟩\n', 'local notation "foo" => transposeAxes\n'])
def test_v3_keeps_existing_unknown_syntax_guards(prefix):
    text = prefix + sample()
    assert codec.compact(text, version=3) == text


@pytest.mark.parametrize('damage', [
    lambda p: p.replace('-- RuntimeReadSource v3\n', '-- RuntimeReadSource v2\n'),
    lambda p: p.replace('-- RuntimeReadSource v3\n', '-- RuntimeReadSource v4\n'),
    lambda p: p.replace('-- RuntimeReadSource v3\n', '-- RuntimeReadSource v3\n'*2),
    lambda p: p.replace('"vP0"', '"vP1"'),
    lambda p: p.replace('"c0"', '"c1"'),
    lambda p: p.replace('=> transposeAxes', '=> Other.transposeAxes'),
    lambda p: p.replace('end RuntimeReadSource\n', ''),
    lambda p: p + 'def outside := c0\n',
    lambda p: p.replace('def probe0', 'def transposeAxes'),
    lambda p: p.replace('section RuntimeReadSource\n', 'import Other\nsection RuntimeReadSource\nnamespace Other\n'),
])
def test_v3_strict_canonical_wrapper_and_metadata(damage):
    packed = codec.compact(sample() + terms_source('transposeAxes'), version=3)
    changed = damage(packed)
    assert changed != packed
    with pytest.raises(ValueError):
        codec.expand(changed)


@pytest.mark.parametrize('world', ['pm','sm'])
def test_field_precedence_membership_and_initial_declarations(world):
    requests=world+'InputRequests'
    initial='private def initialParameterSpecs := 0\ndef InitialParameterValues := True\n'
    text = (initial + ''.join(f'def combined{i} := {requests}.take 2 ++ {requests}.drop 2\n' for i in range(20)) +
            f'variable (h : ∀ row ∈ {requests}.drop 17, True)\n' + sample())
    packed = codec.compact(text, version=3)
    assert initial in packed
    assert re.search(r'c\d+ 2 \+\+ c\d+ 2', packed)
    assert codec.expand(packed) == text


@pytest.mark.parametrize('context', ['@pmInputRequests.take 2', 'f pmInputRequests.take 2',
    'pmInputRequests.take n', 'pmInputRequests.take (2)'])
def test_unsupported_field_syntax_still_falls_back(context):
    text = 'def bad := ' + context + '\n' + sample()
    assert codec.compact(text, version=3) == text


@pytest.mark.parametrize('version', [True, None, 1, 4, '3'])
def test_unknown_policy_is_rejected(version):
    with pytest.raises(ValueError):
        codec.compact(sample(), version=version)
