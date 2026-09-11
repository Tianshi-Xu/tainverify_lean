"""Finite helper enum v2; legacy '+' retains its pinned helper vocabulary."""
import pytest

from Verdict import runtime_prefix as p
from scripts.tests.test_runtime_prefix_names import sample


HELPERS = (('storeSet_eq_of_not_mem_fst', 'pS'), ('prefixFrame_trans', 'pF'))


@pytest.mark.parametrize('name,alias', HELPERS)
def test_extended_helper_exact_declaration_and_application_roundtrip(name, alias):
    source = sample() + f'def {name} (x : Nat) := x\n#check {name}\n'
    compact = p.compact_names(source)
    assert 'prefix_names pmSeededPrefix + + ! where\n' in compact
    assert f'def {alias} (x : Nat) := x\n' in compact
    assert f'#check {alias}\n' in compact
    assert p.expand_names(compact) == source
    assert p.compact_names(p.expand_names(compact)) == compact
    assert p.compact_names(compact) == compact


@pytest.mark.parametrize('indent', (' ', '  '))
@pytest.mark.parametrize('marker', ('', ' +', ' !', ' + !'))
def test_old_wrappers_preserve_literal_extended_aliases(indent, marker):
    packed = ('prefix_names tinyPrefix' + marker + ' where\n'
              + indent + 'def r_0 (pS pF : Nat) := pS + pF\n'
              + indent + '#check pR\n')
    helper = 'prefixRead' if '+' in marker else 'pR'
    expected = ('def tinyPrefixRead_0 (pS pF : Nat) := pS + pF\n'
                f'#check {helper}\n')
    assert p.expand_names(packed) == expected


def test_support_gates_finite_v2_aliases_before_ordered_elaboration():
    support = p.support_source()
    expansion = support.split('private def expandName', 1)[1].split('private partial def expand', 1)[0]
    assert 'let .str .anonymous text := n | return n' in expansion
    assert 'if helpers && text == "pR" then return Name.mkSimple "prefixRead"' in expansion
    for name, alias in HELPERS:
        assert f'if helpers && helpersV2 && text == "{alias}" then return Name.mkSimple "{name}"' in expansion
    assert '(" +")? (" +")? (" !")?' in support
    assert '" v2"' not in support
    assert 'let helpersV2 := !stx[3].isNone' in support
    assert 'if helpersV2 && !helpers then throwError "prefix helper v2 requires +"' in support
    assert 'expandName stemPrefix helpers helpersV2 n' in support
    assert 'args.map (expand stemPrefix helpers helpersV2)' in support
    assert 'for cmd in stx[6].getArgs do\n    elabCommand (expand pref helpers helpersV2 cmd)' in support


@pytest.mark.parametrize('name,alias', HELPERS)
def test_extended_helper_collision_falls_back_for_entire_source(name, alias):
    for extra in (f'def {alias} := 1\n', f'#check {alias}\n',
                  f'example ({alias} : Nat) := {alias}\n', f'import {alias}\n'):
        source = sample() + f'#check {name}\n' + extra
        assert p.compact_names(source) == source


@pytest.mark.parametrize('name,alias', HELPERS)
def test_extended_helper_qualified_near_matches_comments_and_imports_are_literal(name, alias):
    variants = ('Other.{}', '{}.foo', '{}_more', '{}1', 'α{}', '{}α',
                "{}'", '{}?', '{}!')
    extra = ''.join(f'#check {variant.format(token)}\n'
                    for token in (name, alias) for variant in variants)
    extra += f'-- {name} {alias}\n'
    imports = f'import {name}\nimport Other.{name}\n'
    source = imports + sample() + f'#check {name}\n' + extra
    compact = p.compact_names(source)
    assert compact != source
    assert compact.startswith(imports)
    assert all(line in compact for line in extra.splitlines())
    assert p.expand_names(compact) == source
    without_helper = source.replace(f'#check {name}\n', '')
    assert ' + + ' not in p.compact_names(without_helper)
    assert p.expand_names(p.compact_names(without_helper)) == without_helper
    for unsupported in (f'/- {name} {alias} -/\n',
                        f'def literal := "{name}"\n', f'#check «{name}»\n'):
        assert p.compact_names(source + unsupported) == source + unsupported


@pytest.mark.parametrize('marker', (' v2', ' v2 !', ' v2 +', ' + v2', ' + v3',
                                   ' + + v2', ' + ! v2', ' + + +', ' + ! +'))
def test_malformed_helper_versions_are_rejected(marker):
    with pytest.raises(ValueError, match='invalid compact prefix header'):
        p.expand_names(f'prefix_names tinyPrefix{marker} where\n #check pS\n')


@pytest.mark.parametrize('body', ('   #check pS\n', '  #check pS\n #check pF\n'))
def test_v2_keeps_invalid_outer_indentation_rejection(body):
    with pytest.raises(ValueError, match='invalid compact prefix indentation'):
        p.expand_names('prefix_names tinyPrefix + + where\n' + body)


def test_v2_keeps_query_order_opacity_and_wrapper_scope():
    source = (sample() + '#check storeSet_eq_of_not_mem_fst\n#check prefixFrame_trans\n'
              'attribute [local irreducible] pmSeededPrefixState_1\n'
              'record_prefix_opacity pmSeededPrefixState_1 pmSeededPrefixState_2\n'
              'restore_prefix_opacity\n')
    compact = p.compact_names(source)
    assert 'attribute [local irreducible] s_1' in compact
    assert 'record_prefix_opacity s_1 s_2' in compact
    assert 'restore_prefix_opacity' in compact
    for query in ('', ' !'):
        old = f'prefix_names tinyPrefix +{query} where\n #check pS\n #check pF\n #check pR\n'
        suffix = '#check pS\n#check pF\n'
        expected = '#check pS\n#check pF\n#check prefixRead\n'
        assert p.expand_names(compact + old + suffix) == source + expected + suffix
        assert p.expand_names(old + compact + suffix) == expected + source + suffix
    no_queries = source.replace('#print axioms ', '#check ')
    assert ' + + where\n' in p.compact_names(no_queries)
    assert p.expand_names(p.compact_names(no_queries)) == no_queries


def test_version_marker_preserves_literal_version_identifier():
    source = sample() + ('def v2 : Nat := 3\nexample : v2 = 3 := rfl\n'
                         '#check storeSet_eq_of_not_mem_fst\n')
    compact = p.compact_names(source)
    assert ' + + ! where\n' in compact
    assert 'def v2 : Nat := 3\n' in compact
    assert 'example : v2 = 3 := rfl\n' in compact
    assert p.expand_names(compact) == source


def pinned_old_codec():
    """Execute only the codec AST from the immutable, pre-enum checkpoint."""
    import ast
    import subprocess
    from pathlib import Path
    from types import SimpleNamespace

    sha = '5954a547a6c7ef30b21222ee34fb8f2bad38c6fb'
    source = subprocess.check_output(
        ['git', 'show', f'{sha}:Verdict/runtime_prefix.py'],
        cwd=Path(__file__).resolve().parents[2], text=True)
    names = {'_NAME_CODES', '_LOCAL_CODES', '_HELPER_CODES', 'compact_names', 'expand_names'}
    tree = ast.parse(source)
    selected = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name in names:
            selected.append(node)
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if any(isinstance(target, ast.Name) and target.id in names for target in targets):
                selected.append(node)
    namespace = {}
    exec(compile(ast.Module(body=selected, type_ignores=[]), f'{sha}:prefix-codec', 'exec'), namespace)
    assert namespace['_HELPER_CODES'] == {'prefixRead': 'pR'}
    return SimpleNamespace(**{name: namespace[name] for name in names})


def test_pinned_old_decode_new_reencode_preserves_complete_plaintext():
    old = pinned_old_codec()
    source = sample() + '#check storeSet_eq_of_not_mem_fst\n#check prefixFrame_trans\n'
    legacy = old.compact_names(source)
    plaintext = old.expand_names(legacy)
    assert old.compact_names(plaintext) == legacy
    assert p.expand_names(legacy) == plaintext == source
    compact = p.compact_names(plaintext)
    assert compact != legacy
    assert p.expand_names(compact) == plaintext
    assert p.compact_names(p.expand_names(compact)) == compact
    with pytest.raises(ValueError, match='invalid compact prefix header'):
        old.expand_names(compact)
    for _, alias in HELPERS:
        colliding = source + f'example ({alias} : Nat) := {alias}\n'
        legacy = old.compact_names(colliding)
        assert ' + ! where\n' in legacy
        assert old.expand_names(legacy) == p.expand_names(legacy) == colliding
        assert p.compact_names(old.expand_names(legacy)) == colliding
