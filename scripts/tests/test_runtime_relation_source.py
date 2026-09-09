"""Scoped term notation preserves generated contracts and complete proof source."""
import importlib
import importlib.util
import pytest


def api():
    assert importlib.util.find_spec('Verdict.runtime_relation_source'), 'relation source compactor missing'
    return importlib.import_module('Verdict.runtime_relation_source')


def test_lossless_profitable_term_aliases():
    source = 'namespace TrainVerify.Denote.RuntimeWorld\n' + ''.join(
        f'theorem probe_{i} := List.take_append_drop {i} pmInputRequests\n'
        for i in range(30)) + 'end TrainVerify.Denote.RuntimeWorld\n'
    module = api()
    compact = module.compact(source)
    assert len(compact.encode()) < len(source.encode())
    assert 'local notation' in compact
    assert module.expand(compact) == source
    assert [line.split(' :=')[0] for line in compact.splitlines() if line.startswith('theorem ')] == [line.split(' :=')[0] for line in source.splitlines() if line.startswith('theorem ')]


@pytest.mark.parametrize('text', ['-- comment\n', '"quoted"', '«quoted»', '/- comment -/', '`quoted', 'theorem x := r0\n'])
def test_unsupported_lexical_forms_or_alias_collision_stay_unchanged(text):
    source = text + ('#check List.take_append_drop\n' * 30)
    assert api().compact(source) == source


def test_extended_identifiers_and_unprofitable_source_stay_unchanged():
    module = api()
    source = 'theorem x := List.take_append_drop_extra\n'
    assert module.compact(source) == source
    assert module.expand(source) == source


@pytest.mark.parametrize('suffix', ['?', '!', "'", '.extra', '_extra'])
def test_compaction_preserves_extended_helper_tokens(suffix):
    source = '#check List.take_append_drop' + suffix + '\n' + '#check List.take_append_drop\n' * 30
    compact = api().compact(source)
    assert '#check List.take_append_drop' + suffix + '\n' in compact
    assert api().expand(compact) == source


@pytest.mark.parametrize('binding', [
    'noncomputable def List.take_append_drop := 1',
    '@[simp] theorem List.take_append_drop : True := True.intro',
    'opaque List.take_append_drop : Nat := 1',
    'theorem foo (List.take_append_drop : Nat) : Nat := List.take_append_drop',
    'theorem foo (x List.take_append_drop y : Nat) : Nat := x',
    'def foo := fun List.take_append_drop x => x',
    'def foo := fun (x : Nat) (List.take_append_drop : Nat) => x',
    'def foo := fun\n  List.take_append_drop\n  x => x',
    'theorem foo (x\n  List.take_append_drop\n  y : Nat) : Nat := x',
    'def foo := ∀ List.take_append_drop : Nat, True',
    'def foo := let List.take_append_drop := 1; List.take_append_drop',
    'theorem foo : True := by\n  have List.take_append_drop := True.intro\n  exact List.take_append_drop',
    'namespace List\ndef take_append_drop := 1\nend List',
])
def test_unsupported_declarations_and_bindings_are_not_rewritten(binding):
    source = binding + '\n' + '#check List.take_append_drop\n' * 30
    assert api().compact(source) == source


def test_compaction_does_not_change_term_declarations():
    source = 'def List.take_append_drop := 1\n' + '#check List.take_append_drop\n' * 30
    assert api().compact(source) == source
