import importlib
import importlib.util
import pytest

PREFIX='SourcePrimitiveRead.allToAll_value_of_split pmGraph pmScope pmPeers pmGraph.nodes\n    pmInputRequests'

def api():
    assert importlib.util.find_spec('Verdict.runtime_read_source'), 'read source compactor missing'
    return importlib.import_module('Verdict.runtime_read_source')

def source(prefix=PREFIX):
    return ('namespace TrainVerify.Denote.RuntimeWorld\n' +
        ''.join(f'theorem p{i} : True := by\n  apply {prefix} xs\n#print axioms p{i}\n' for i in range(12)) +
        'end TrainVerify.Denote.RuntimeWorld\n')

def test_partial_calls_roundtrip_without_argument_or_body_changes():
    text=source();m=api();packed=m.compact(text)
    assert len(packed.encode())<len(text.encode())
    assert m.expand(packed)==text
    assert m.compact(packed)==packed
    assert packed.count(' xs\n')==12


def test_existing_term_aliases_keep_their_original_spelling():
    text=('section RuntimeRelationSource\nlocal notation "r1" => SourcePrimitiveRead.allToAll_value_of_split\n'+
          source(PREFIX.replace('SourcePrimitiveRead.allToAll_value_of_split','r1'))+'end RuntimeRelationSource\n')
    packed=api().compact(text)
    assert len(packed.encode())<len(text.encode())
    assert api().expand(packed)==text


@pytest.mark.parametrize('prefix', ['variable (pmGraph : GraphDecl)\n','def pmGraph := g\n',
    'namespace Other\n','  namespace Other\n','\tnamespace Other\n','open Other\n',
    'opaque pmGraph : GraphDecl := g\n','axiom pmGraph : GraphDecl\n','constant pmGraph : GraphDecl\n',
    '/- block -/\n','def s := "quoted"\n', '-- vP0 collision\n'])
def test_unsupported_scope_or_shadowing_is_unchanged(prefix):
    text=prefix+source()
    assert api().compact(text)==text


@pytest.mark.parametrize('binding', ['rcases pair with ⟨pmGraph, h⟩', 'obtain ⟨pmGraph, h⟩ := pair',
    'cases pair with', 'induction xs with', 'case cons pmGraph rest =>', 'match g with', '| pmGraph =>'])
def test_unknown_tactic_binders_preserve_source(binding):
    text=source().replace('  apply ', f'  {binding}\n  apply ')
    assert api().compact(text)==text


def test_multiple_old_alias_scopes_are_not_merged():
    block='section RuntimeRelationSource\nlocal notation "r1" => SourcePrimitiveRead.allToAll_value_of_split\n'+source()+'end RuntimeRelationSource\n'
    assert api().compact(block+block)==block+block


def test_unprofitable_and_unknown_calls_unchanged():
    for text in ['',source().split('#print axioms p0\n')[0]+'#print axioms p0\n',source('Unknown.helper pmGraph')]:
        assert api().compact(text)==text


def test_expansion_rejects_damaged_scopes_and_helpers():
    p=api().compact(source())
    with pytest.raises(ValueError):api().expand(p.replace('end RuntimeReadSource\n',''))
    with pytest.raises(ValueError):api().expand(p.replace('=> SourcePrimitiveRead.', '=> Unknown.'))
