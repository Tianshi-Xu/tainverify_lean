"""Closed syntax-support admission; unit fixtures are not Lean/kernel evidence."""
import pytest
from Verdict import runtime_prefix as p, runtime_world as w

V3 = 'TrainVerifyRuntimePrefixNamesV3'
V3_FILE = V3 + '.lean'


@pytest.fixture
def case(monkeypatch):
    # Isolate inventory validation from the independently tested codec/template.
    source = 'import TrainVerifyRuntimePrefixSupport\n-- source-only admission fixture\n'
    monkeypatch.setattr(p, 'NAMES_V3_MODULE', V3, raising=False)
    monkeypatch.setattr(p, 'NAMES_V3_FILE', V3_FILE, raising=False)
    monkeypatch.setattr(p, 'names_v3_source', lambda: source, raising=False)
    base = (f'import {w.WORLD_DATA_MODULE}\nimport denote.SourceScopedPrefix\n'
            f'import {p.SUPPORT_MODULE}\n')
    lean = base + f'import {V3}\nprefix_names_v3 tinyPrefix where\n def s_0 := pL\n'
    sources = {w.WORLD_DATA_FILE: 'import denote.SourceScopedEval\n',
               p.SUPPORT_FILE: p.support_source(), V3_FILE: source}
    return base, lean, sources


def test_single_entry_accepts_exact_required_names_support(case):
    _, lean, sources = case
    result = w._proof_bundle(lean, sources)
    assert result['dependency_order'] == [w.WORLD_DATA_FILE, p.SUPPORT_FILE, V3_FILE, '$entry']
    assert [m['file'] for m in result['modules']] == result['dependency_order']
    assert result['modules'][2]['imports'] == [p.SUPPORT_MODULE]
    assert result['kernel_checked'] is False


def test_prefix_chain_adds_support_before_first_user_and_keeps_edges(case):
    base, lean, sources = case
    name = p.PREFIX_MODULE+'0000'
    sources[name+'.lean'] = lean
    result = w._proof_bundle(base+f'import {name}\n', sources)
    assert result['dependency_order'] == [w.WORLD_DATA_FILE,p.SUPPORT_FILE,V3_FILE,name+'.lean','$entry']
    assert result['modules'][-1]['imports'][-1] == name


@pytest.mark.parametrize('fault', ['missing','tampered','unused','missing-import','duplicate-import',
                                   'unmarked-import','unknown-support','extra-import'])
def test_invalid_optional_support_is_rejected(case, fault):
    base, lean, sources = case
    if fault == 'missing': sources.pop(V3_FILE)
    elif fault == 'tampered': sources[V3_FILE] += '-- changed\n'
    elif fault == 'unused': lean = base
    elif fault == 'missing-import': lean = lean.replace(f'import {V3}\n','')
    elif fault == 'duplicate-import': lean = lean.replace(f'import {V3}\n',f'import {V3}\n'*2)
    elif fault == 'unmarked-import': lean = base+f'import {V3}\n'
    elif fault == 'unknown-support': sources['UnknownSyntaxSupport.lean'] = sources[V3_FILE]
    else: lean = lean.replace(f'import {V3}\n',f'import {V3}\nimport Other\n')
    with pytest.raises(ValueError): w._proof_bundle(lean,sources)


def test_seeded_feed_selects_v3_without_changing_default_path():
    import ast
    import inspect
    from Verdict import runtime_input_feed as feed
    tree = ast.parse(inspect.getsource(feed))
    call, = [n for n in ast.walk(tree) if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Name) and n.func.id == 'pack_proofs']
    assert len(call.args) == 1 and isinstance(call.args[0], ast.Name) and call.args[0].id == 'prefixes'
    assert [k.arg for k in call.keywords] == ['names_v3']
    for seeds, expected in [(None, False), ({'inventories': {}}, True)]:
        seen = []
        prefixes = object()
        run = lambda *a, **kw: seen.append((a,kw))
        eval(compile(ast.Expression(call), '<feed-packing-call>', 'eval'),
             dict(pack_proofs=run,prefixes=prefixes,seeds=seeds))
        assert seen == [((prefixes,), dict(names_v3=expected))]


def test_real_codec_pack_matches_closed_optional_support_inventory():
    text = ''.join(f'def tinyPrefixStep_{i} := AllToAllSourceFaithful.localStep\n' for i in range(12))
    entry, sources = p.pack_proofs([[p.ProofGroup(text,12,())]], names_v3=True)
    assert V3_FILE in sources
    sources[w.WORLD_DATA_FILE] = 'import denote.SourceScopedEval\n'
    result = w._proof_bundle(entry,sources)
    assert result['dependency_order'] == [w.WORLD_DATA_FILE,p.SUPPORT_FILE,V3_FILE,'$entry']


def test_unmodified_legacy_inventory_has_no_optional_support(case):
    base, _, sources = case
    sources.pop(V3_FILE)
    result = w._proof_bundle(base,sources)
    assert result['dependency_order'] == [w.WORLD_DATA_FILE,p.SUPPORT_FILE,'$entry']
    assert len(result['modules']) == 3
