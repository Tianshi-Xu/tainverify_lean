import importlib
from hashlib import sha256
import importlib.util
import pytest
import re

ENTRY_TERMS = (
    'pmInputRequests.drop', 'pmInputRequests.take', 'pmInputRequests',
    'chunkPrimDimN', 'List.take_append_drop', 'AllToAllSourceFaithful.tensor',
    'List.mem_cons_self', 'pmDenoteWithInputs', 'allGatherPrimDimN',
    'smInputRequests', 'smInputRequests.drop', 'smDenoteWithInputs',
    'List.mem_cons_of_mem', 'congrArg₂', 'fw_embedding', 'List.Forall₂.cons',
    'SourceLayernormRead.layernorm_value_of_split', 'RelationCompiler.ReplicatedRel',
    'fw_layernorm', 'smInputRequests.take', 'List.not_mem_nil', 'List.cons',
    'chunkPrimDimN_shape',
    'TrainVerify.Denote.source_add_unit_output_facts',
)


ENTRY_METHODS = {w + 'InputRequests.' + op for w in ('sm', 'pm') for op in ('take', 'drop')}


def entry_term(term):
    return term + ' 7' if term in ENTRY_METHODS else term


def entry_source(terms=ENTRY_TERMS):
    return ('import Example\nnamespace TrainVerify.Denote.RuntimeWorld\n' +
            ''.join(f'def p{i} := ({entry_term(term)})\n' for i, term in
                    enumerate(terms * 40)) +
            'end TrainVerify.Denote.RuntimeWorld\n')


@pytest.mark.parametrize('terms', [(term,) for term in ENTRY_TERMS] + [ENTRY_TERMS])
def test_entry_terms_c_only_exact_utf8_roundtrip(terms):
    m = api(); text = entry_source(terms); packed = m.compact(text)
    assert re.search(r'local notation(?::max)? "c0"', packed)
    assert 'local notation "vP' not in packed
    assert tuple(m._ENTRY_TERMS) == ENTRY_TERMS
    assert len(packed.encode('utf-8')) < len(text.encode('utf-8'))
    assert m.expand(packed) == text
    assert m.compact(packed) == packed
    assert packed.count('section RuntimeReadSource\n') == 1
    assert packed.startswith('import Example\n')
    assert re.findall(r'\bdef (\w+)', packed) == re.findall(r'\bdef (\w+)', text)


def test_entry_mixed_preserves_old_definitions_and_nested_relation_scope():
    m = api()
    old = source()
    old_defs = re.findall(r'^local notation "vP.*$', m.compact(old), re.M)
    text = old + ('section RuntimeRelationSource\n'
        'local notation "r1" => SourcePrimitiveRead.allToAll_value_of_split\n' +
        source(PREFIX.replace('SourcePrimitiveRead.allToAll_value_of_split', 'r1')) +
        entry_source().removeprefix('import Example\n') + 'end RuntimeRelationSource\n')
    packed = m.compact(text)
    assert old_defs[0] in packed
    assert packed.index('local notation "vP') < packed.index('local notation "c')
    assert 'local notation "r1" => SourcePrimitiveRead.allToAll_value_of_split\n' in packed
    assert m.expand(packed) == text


@pytest.mark.parametrize('term', ENTRY_TERMS)
def test_entry_tokens_only_not_comments_alias_definitions_or_extended_names(term):
    m = api()
    untouched = (f'-- {term}\n' + ''.join(
        f'def extra{i} := {name}\n' for i, name in enumerate([
            term+"'", term+'!', term+'?', term+'Extra', 'Other.'+term, term+'.field'])))
    text = (entry_source((term,)).replace(f'({entry_term(term)})\n', f'({entry_term(term)}) -- {term}\n') +
            'section RuntimeRelationSource\n' +
            f'local notation "r9" => {term}\n' + untouched + 'end RuntimeRelationSource\n')
    packed = m.compact(text)
    assert re.search(r'local notation(?::max)? "c0"', packed)
    assert untouched in packed
    assert f'local notation "r9" => {term}\n' in packed
    assert packed.count(f'-- {term}\n') == text.count(f'-- {term}\n')
    assert m.expand(packed) == text


@pytest.mark.parametrize('command', ['intro x', 'intros x', 'intro _ _\n  rename_i x'])
@pytest.mark.parametrize('gap', ['', '\n    -- continued binder\n'])
def test_multiline_tactic_binders_preserve_exact_source(command, gap):
    text = entry_source(('pmInputRequests',)).replace(
        'end TrainVerify.Denote.RuntimeWorld\n',
        'def auditShadow : Nat → Nat → Nat := by\n  ' + command + '\n' + gap +
        '    pmInputRequests\n  exact pmInputRequests\nend TrainVerify.Denote.RuntimeWorld\n')
    assert api().compact(text) == text


def test_bullet_intro_followed_by_same_column_proof_still_compacts():
    text = entry_source(('pmInputRequests',)).replace(
        'end TrainVerify.Denote.RuntimeWorld\n',
        'theorem auditBranch : (∀ x : Nat, x = x) ∧ True := by\n'
        '  constructor\n  · intro x\n    rfl\n  · trivial\nend TrainVerify.Denote.RuntimeWorld\n')
    packed = api().compact(text)
    assert packed != text
    assert api().expand(packed) == text


def test_entry_variable_header_types_and_membership_quantifiers_are_terms():
    text = ('section Shared\nvariable (h : ∀ x ∈ pmInputRequests, True)\ninclude h\n' +
            entry_source(('pmInputRequests',)) + 'end Shared\n')
    packed = api().compact(text)
    assert 'variable (h : ∀ x ∈ c0, True)' in packed
    assert api().expand(packed) == text


@pytest.mark.parametrize('binding', [
    'def chunkPrimDimN := other', 'theorem Other.tensor : True := by trivial',
    'variable (List : Type)', 'variable {chunkPrimDimN : Type}',
    'def f := fun\n  chunkPrimDimN => chunkPrimDimN',
    'def f := ∀ chunkPrimDimN : Nat, True',
    'def f := ∀ chunkPrimDimN ∈ xs, True',
    'def f := ∃ tensor, tensor = tensor',
    'def f := forall chunkPrimDimN, True',
    'def f := exists chunkPrimDimN, True',
    'def f := by\n  intro chunkPrimDimN',
    'def f := by\n  rename_i tensor',
    'def f := by\n  have tensor := other',
    'def f := let chunkPrimDimN := other; chunkPrimDimN',
    'def f := let x chunkPrimDimN := other; x',
    'variable (x chunkPrimDimN : Type)',
    'namespace List', 'open List', 'local notation "x" => chunkPrimDimN',
    'notation:65 x => chunkPrimDimN', 'infix:65 "foo" => chunkPrimDimN',
    'scoped notation "foo" => chunkPrimDimN',
    '-- c0 collision',
    'def f := by\n  unfold chunkPrimDimN',
    'def f := by\n  delta\n    chunkPrimDimN',
    'attribute [simp] chunkPrimDimN', '#print chunkPrimDimN',
    'export List (cons)', 'include chunkPrimDimN', 'omit chunkPrimDimN',
])
def test_entry_unsupported_shadow_or_name_context_is_whole_input_fallback(binding):
    text = binding + '\n' + source() + entry_source()
    assert api().compact(text) == text


@pytest.mark.parametrize('damage', [
    lambda p: p.replace('"c0"', '"c1"', 1),
    lambda p: p.replace('=> pmInputRequests.drop', '=> Unknown.term', 1),
    lambda p: p.replace('=> pmInputRequests.take n', '=> pmInputRequests.drop n', 1),
    lambda p: p.replace('end RuntimeReadSource\n', ''),
    lambda p: p.replace('end RuntimeReadSource\n', 'end RuntimeReadSource\nend RuntimeReadSource\n'),
    lambda p: p.replace('section RuntimeReadSource\n', 'section RuntimeReadSource\nsection RuntimeReadSource\n'),
    lambda p: p.replace('open TrainVerify.Denote TrainVerify.Denote.RuntimeWorld\n', 'open Other\n', 1),
    lambda p: p.replace('"c1"', '"c0"', 1),
    lambda p: p.replace('end TrainVerify.Denote.RuntimeWorld\n', ''),
    lambda p: p + 'def escaped := c0\n',
    lambda p: p.replace('def p0', 'def chunkPrimDimN', 1),
])
def test_entry_inverse_rejects_malformed_metadata_and_scope(damage):
    packed = api().compact(entry_source())
    with pytest.raises(ValueError):
        api().expand(damage(packed))


@pytest.mark.parametrize('term', sorted(ENTRY_METHODS))
@pytest.mark.parametrize('index', ['0', '3', '123456789'])
def test_method_alias_has_parameter_and_preserves_decimal_application(term, index):
    text = entry_source((term,)).replace(' 7)', ' ' + index + ')')
    packed = api().compact(text)
    assert f'local notation:max "c0" n:max => {term} n\n' in packed
    assert f'(c0 {index})' in packed
    assert api().expand(packed) == text
    with pytest.raises(ValueError):
        api().expand(packed.replace(f'local notation:max "c0" n:max => {term} n', f'local notation "c0" => {term}'))


@pytest.mark.parametrize('term', sorted(ENTRY_METHODS))
@pytest.mark.parametrize('application', ['', ' n', ' (7)', ' (n + 1)', ' 07', ' 7foo', ' 7.1'])
def test_unsupported_method_application_preserves_whole_input(term, application):
    text = 'def unsupported := ' + term + application + '\n' + source() + entry_source()
    assert api().compact(text) == text


@pytest.mark.parametrize('term', sorted(ENTRY_METHODS))
@pytest.mark.parametrize('context', ['f {term} 2', '@{term} 2', 'f\n {term} 2'])
def test_method_alias_rejects_argument_position(term, context):
    text = 'def bad := ' + context.format(term=term) + '\n' + entry_source()
    assert api().compact(text) == text


@pytest.mark.parametrize('world', ['pm', 'sm'])
def test_method_alias_keeps_append_and_membership_syntax(world):
    requests = world + 'InputRequests'
    text = ('def combined := ' + requests + '.take 2 ++ ' + requests + '.drop 2\n' +
            'variable (h : ∀ row ∈ ' + requests + '.drop 17, True)\n' + entry_source())
    packed = api().compact(text)
    assert re.search(r'c\d+ 2 \+\+ c\d+ 2', packed)
    assert api().expand(packed) == text


def test_entry_utf8_profit_charges_scope_and_definitions():
    m = api()
    term = 'congrArg₂'
    assert m.compact('def x := congrArg₂\n') == 'def x := congrArg₂\n'
    # Unicode savings, not Python character counts, cross the wrapper threshold.
    text = 'def x := ' + ' '.join([term] * 24) + '\n'
    packed = m.compact(text)
    assert re.search(r'local notation(?::max)? "c0"', packed)
    assert m.expand(packed) == text


@pytest.mark.parametrize('scope', ['noncomputable section', 'section'])
def test_entry_anonymous_scoped_headers_roundtrip(scope):
    text = ('namespace TrainVerify.Denote.RuntimeWorld\n' + scope + '\n' +
            entry_source(('chunkPrimDimN',)).removeprefix('import Example\n') +
            'end\nend TrainVerify.Denote.RuntimeWorld\n')
    packed = api().compact(text)
    assert re.search(r'local notation(?::max)? "c0"', packed)
    assert api().expand(packed) == text
    old = api()._START + ('local notation "vP0" => ' + PREFIX.replace('\n    ', ' ') + '\n')
    old += scope + '\n' + source('vP0') + 'end\n' + api()._END
    assert api().expand(old) == scope + '\n' + source() + 'end\n'


@pytest.mark.parametrize('name', sorted({p for term in ENTRY_TERMS for p in term.split('.')}))
@pytest.mark.parametrize('binding', ['variable ({name} : Type)',
    'def Other.{name} := other', 'def f := fun\n {name} => other'])
def test_every_entry_root_and_member_is_protected(name, binding):
    text = binding.format(name=name) + '\n' + source() + entry_source()
    assert api().compact(text) == text


@pytest.mark.parametrize('prefix', ['section chunkPrimDimN\nend chunkPrimDimN\n',
    'def f := by\n  generalize h : value = chunkPrimDimN\n',
    'def f := by\n  set chunkPrimDimN := value\n',
    'variable chunkPrimDimN\n', 'def f := by\n  intro\n    chunkPrimDimN\n'])
def test_entry_additional_name_and_binding_contexts_fallback(prefix):
    text = prefix + source() + entry_source()
    assert api().compact(text) == text


def test_entry_safe_proof_term_contexts_and_unrelated_unfold():
    proof = ('theorem termUse : True := by\n'
             '  unfold unrelated\n'
             '  rw [List.take_append_drop]\n'
             '  simp only [List.mem_cons_self]\n'
             '  change pmInputRequests = pmInputRequests\n')
    text = proof + entry_source()
    packed = api().compact(text)
    assert '  unfold unrelated\n' in packed
    assert '  rw [c' in packed and '  simp only [c' in packed
    assert '  change c' in packed
    assert api().expand(packed) == text


def test_vp_comments_are_not_rewritten_or_counted_as_uses():
    text = ('-- ' + PREFIX.replace('\n', '\n-- ') + '\n') * 20
    assert api().compact(text) == text
    text += source()
    packed = api().compact(text)
    assert packed.count('-- ' + PREFIX.splitlines()[0]) == 20
    assert api().expand(packed) == text


def test_old_vp_only_inverse_remains_supported():
    m = api()
    definition = ('local notation "vP0" => ' + PREFIX.replace('\n    ', ' ') + '\n')
    packed = m._START + definition + source('vP0') + m._END
    assert m.expand(packed) == source()


@pytest.mark.parametrize('damage', [
    lambda p: p.replace('"vP0"', '"vP1"', 1),
    lambda p: p.replace('local notation "vP0"', 'local notation "vP00"', 1),
    lambda p: p.replace('end RuntimeReadSource\n', 'end RuntimeReadSource\nend RuntimeReadSource\n'),
])
def test_old_inverse_rejects_invalid_sequence_and_scope(damage):
    with pytest.raises(ValueError):
        api().expand(damage(api().compact(source())))

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


EXTENDED_HELPERS = (
    'SourceAllGatherRead.allGather_value_of_split',
    'SourceLayernormRead.layernorm_value_of_split',
    'SourceLayoutRead.transposeAxes_value_of_split',
    'SourceLayoutRead.view_value_of_split',
    'SourceLinearRead.linear_value_of_split',
)
VERSION = '-- RuntimeReadSource v2\n'


def extended_source(helper, world='pm', aliased=False):
    spelling = 'r1' if aliased else helper
    prefix = (f'{spelling} {world}Graph {world}Scope {world}Peers {world}Graph.nodes\n'
              f'    {world}InputRequests')
    text = source(prefix).replace(' xs\n', ' xs θ₁\n')
    if aliased:
        text = (f'section RuntimeRelationSource\nlocal notation "r1" => {helper}\n' +
                text + 'end RuntimeRelationSource\n')
    return text


@pytest.mark.parametrize('helper', EXTENDED_HELPERS)
@pytest.mark.parametrize('world', ['sm', 'pm'])
@pytest.mark.parametrize('aliased', [False, True])
def test_extended_prefix_alias_exact_utf8_inverse(helper, world, aliased):
    m = api(); text = extended_source(helper, world, aliased); packed = m.compact(text)
    rhs = f'{helper} {world}Graph {world}Scope {world}Peers {world}Graph.nodes {world}InputRequests'
    assert f'local notation "vP0" => {rhs}' in packed
    assert m._START + VERSION in packed
    assert packed.count(VERSION) == 1
    assert len(packed.encode('utf-8')) < len(text.encode('utf-8'))
    assert packed.count(' xs θ₁\n') == 12
    assert m.expand(packed).encode('utf-8') == text.encode('utf-8')
    assert m.compact(packed) == packed


def legacy_source():
    prefix = 'r1 pmGraph pmScope pmPeers pmGraph.nodes\n    pmInputRequests'
    return ('section RuntimeRelationSource\n'
            'local notation "r1" => SourceLinearRead.linear_value_of_split\n' +
            ''.join(f'def p{i} := {prefix} θ₁\n' for i in range(12)) +
            'end RuntimeRelationSource\n')


# Frozen output generated with the baseline (84272743) algorithm, not the new encoder.
_LEGACY_PACKED = ('section RuntimeReadSource\n'
 'open TrainVerify.Denote TrainVerify.Denote.RuntimeWorld\n'
 'local notation "c0" => pmInputRequests\n'
 'section RuntimeRelationSource\n'
 'local notation "r1" => SourceLinearRead.linear_value_of_split\n'
 'def p0 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p1 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p2 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p3 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p4 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p5 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p6 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p7 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p8 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p9 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p10 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'def p11 := r1 pmGraph pmScope pmPeers pmGraph.nodes\n'
 '    c0 θ₁\n'
 'end RuntimeRelationSource\n'
 'end RuntimeReadSource\n')


def test_legacy_packed_extended_calls_still_decode_canonically():
    m = api(); text = legacy_source()
    assert m.expand(_LEGACY_PACKED) == text
    assert VERSION not in _LEGACY_PACKED
    assert m.compact(text) != _LEGACY_PACKED
    assert m.expand(m.compact(text)) == text
    with pytest.raises(ValueError):
        m.expand(_LEGACY_PACKED.replace('def p0', 'def pmGraph', 1))
    with pytest.raises(ValueError):
        m.expand(_LEGACY_PACKED.replace(m._START, m._START + VERSION, 1))


@pytest.mark.parametrize('damage', [
    lambda p: p.replace(VERSION, '', 1),
    lambda p: p.replace(VERSION, '-- RuntimeReadSource v3\n', 1),
    lambda p: p.replace(VERSION, VERSION * 2, 1),
    lambda p: p.replace(VERSION, '', 1).replace('end RuntimeReadSource\n', VERSION + 'end RuntimeReadSource\n'),
    lambda p: p.replace('"vP0"', '"vP1"', 1),
    lambda p: p.replace('=> SourceLinearRead.', '=> Unknown.'),
    lambda p: p.replace('pmScope pmPeers', 'smScope pmPeers', 1),
    lambda p: p.replace('pmGraph.nodes pmInputRequests', 'pmGraph.nodes smInputRequests', 1),
    lambda p: p.replace(' -- r1\n', ' -- r2\n', 1),
    lambda p: p.replace('def p0', 'def linear_value_of_split', 1),
])
def test_extended_inverse_rejects_corrupt_version_or_metadata(damage):
    packed = api().compact(legacy_source())
    assert VERSION in packed
    damaged = damage(packed)
    assert damaged != packed
    with pytest.raises(ValueError):
        api().expand(damaged)


@pytest.mark.parametrize('name', sorted({p for h in EXTENDED_HELPERS for p in (h, *h.split('.'))}))
@pytest.mark.parametrize('binding', [
    'variable ({name} : Type)', 'def Other.{name} := other',
    'def f := fun\n  {name} => other', 'def f := by\n  intro {name}',
    'def f := by\n  delta\n    {name}', '#print {name}',
])
def test_extended_protected_shadow_and_name_context_fallback(name, binding):
    text = binding.format(name=name) + '\n' + extended_source(EXTENDED_HELPERS[-1])
    assert api().compact(text) == text


@pytest.mark.parametrize('helper', EXTENDED_HELPERS)
def test_extended_exact_tokens_comments_and_alias_scope(helper):
    text = extended_source(helper)
    untouched = ''.join(f'def extra{i} := {name} pmGraph pmScope pmPeers pmGraph.nodes\n    pmInputRequests xs\n'
        for i, name in enumerate([helper + s for s in ["'", '!', '?', 'Extra', '.field', '₁']] + ['Other.' + helper]))
    comments = ('-- ' + helper + ' pmGraph pmScope pmPeers pmGraph.nodes\n--     pmInputRequests\n') * 12
    text += untouched + comments
    packed = api().compact(text)
    assert api()._START + VERSION in packed
    # Entry-term shortening is independent; expand must retain every exact byte.
    assert all(name in packed for name in [helper + "'", 'Other.' + helper, helper + '₁'])
    assert comments in packed
    assert api().expand(packed) == text
    aliased = extended_source(helper, aliased=True)
    outside = 'def outside := r1 pmGraph pmScope pmPeers pmGraph.nodes\n    pmInputRequests xs\n'
    packed = api().compact(aliased + outside)
    assert 'local notation "vP' not in packed
    assert api().expand(packed) == aliased + outside


@pytest.mark.parametrize('prefix', ['namespace Other\n', 'open Other\n', '/- block -/\n',
    'def x := "quoted"\n', 'def f := by\n  rcases pair with ⟨SourceLinearRead, h⟩\n'])
def test_extended_unsupported_guards_preserve_whole_input(prefix):
    text = prefix + extended_source(EXTENDED_HELPERS[-1])
    assert api().compact(text) == text


@pytest.mark.parametrize('text', [source(), entry_source(('pmInputRequests',)), 'def x := SourceLinearRead.linear_value_of_split\n'])
def test_no_added_profitable_prefix_preserves_legacy_bytes(text):
    assert sha256(api().compact(text).encode()).hexdigest() == LEGACY_OUTPUTS[sha256(text.encode()).hexdigest()]


LEGACY_OUTPUTS = {'6581088cc941809b3e6634d1a8db8085c600eacee310785aef7c8a79fb41b825': '8d996505d102aa2fbb19f4665593eea4d0f12d0c36249af9bfb87f955d86ca81',
 '9defb9dfe9b1f1d85a86078a181aa687574ff405750b942b4d7320fd942dfd44': '4288b38a78fc258a36a1e921b9dd6768f240c441b6ea91fa58f624c2b4019d3b',
 'de74babaa0b729c099f046abba06b9339460415e56ac3b98255988c6bd71461d': 'de74babaa0b729c099f046abba06b9339460415e56ac3b98255988c6bd71461d'}
