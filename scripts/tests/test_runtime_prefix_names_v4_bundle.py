"""Finite v4 support admission; source inventory is not kernel proof."""
import ast
import copy
import inspect

import pytest
from Verdict import runtime_prefix as p, runtime_world as w

V4 = 'TrainVerifyRuntimePrefixNamesV4'
V4_FILE = V4 + '.lean'
IMPORT = f'import {V4}\n'


@pytest.fixture
def case(monkeypatch):
    # Isolate source-inventory guards; real pack integration is tested below.
    source = 'import TrainVerifyRuntimePrefixSupport\n-- v4 admission fixture\n'
    monkeypatch.setattr(p, 'NAMES_V4_MODULE', V4, raising=False)
    monkeypatch.setattr(p, 'NAMES_V4_FILE', V4_FILE, raising=False)
    monkeypatch.setattr(p, 'names_v4_source', lambda: source, raising=False)
    # Only the admission fixture lacks a real decoder before codec integration.
    original = p.expand_names
    monkeypatch.setattr(p, 'expand_names', lambda text: original(text.replace(
        IMPORT, '').replace('prefix_names_v4 ', 'prefix_names ')))
    base = (f'import {w.WORLD_DATA_MODULE}\nimport denote.SourceScopedPrefix\n'
            f'import {p.SUPPORT_MODULE}\n')
    lean = base + IMPORT + 'prefix_names_v4 tinyPrefix where\n theorem w_0 : True := True.intro\n'
    sources = {w.WORLD_DATA_FILE: 'import denote.SourceScopedEval\n',
               p.SUPPORT_FILE: p.support_source(), V4_FILE: source}
    return base, lean, sources


def test_v4_admission_orders_support_and_counts_exact_bytes(case):
    _, lean, sources = case
    result = w._proof_bundle(lean, sources)
    assert result['dependency_order'] == [w.WORLD_DATA_FILE, p.SUPPORT_FILE, V4_FILE, '$entry']
    assert result['modules'][2]['imports'] == [p.SUPPORT_MODULE]
    assert result['modules'][-1]['theorems'] == ['tinyPrefixWritten_0']
    assert result['kernel_checked'] is False


@pytest.mark.parametrize('fault', ['missing', 'tampered', 'unused', 'missing-import',
    'duplicate-import', 'unmarked-import', 'unknown-support', 'extra-import', 'wrong-support-import'])
def test_v4_admission_fails_closed(case, fault):
    base, lean, sources = case
    if fault == 'missing': sources.pop(V4_FILE)
    elif fault == 'tampered': sources[V4_FILE] += '-- tampered\n'
    elif fault == 'unused': lean = base
    elif fault == 'missing-import': lean = lean.replace(IMPORT, '')
    elif fault == 'duplicate-import': lean = lean.replace(IMPORT, IMPORT*2)
    elif fault == 'unmarked-import': lean = base + IMPORT
    elif fault == 'unknown-support': sources['UnknownPrefixSupport.lean'] = sources[V4_FILE]
    elif fault == 'extra-import': lean = lean.replace(IMPORT, IMPORT+'import Other\n')
    else: sources[V4_FILE] = sources[V4_FILE].replace(p.SUPPORT_MODULE, p.NAMES_V3_MODULE)
    with pytest.raises(ValueError): w._proof_bundle(lean, sources)


def test_v4_mixed_v3_chain_keeps_support_membership_and_prior_edges(case):
    base, lean, sources = case
    first = p.PREFIX_MODULE+'0000'
    second = p.PREFIX_MODULE+'0001'
    sources[p.NAMES_V3_FILE] = p.names_v3_source()
    sources[first+'.lean'] = base+f'import {p.NAMES_V3_MODULE}\n'+'prefix_names_v3 tinyPrefix where\n def t_0 := pL\n'
    sources[second+'.lean'] = lean.replace(IMPORT, f'import {first}\n'+IMPORT)
    entry = base+f'import {second}\n'
    receipt = w._proof_bundle(entry,sources)
    assert receipt['dependency_order'] == [w.WORLD_DATA_FILE,p.SUPPORT_FILE,p.NAMES_V3_FILE,V4_FILE,first+'.lean',second+'.lean','$entry']
    assert receipt['modules'][-2]['imports'][-2:] == [first,V4]
    assert receipt['modules'][-1]['imports'][-1] == second
    malformed = dict(sources)
    malformed[second+'.lean'] = sources[second+'.lean'].replace(f'import {first}\n', '')
    with pytest.raises(ValueError, match='import membership'): w._proof_bundle(entry,malformed)


@pytest.mark.parametrize('delta,accepted', [(1,True),(0,False),(-1,False)])
def test_v4_support_bytes_are_not_exempt_from_strict_cap(case,monkeypatch,delta,accepted):
    from Verdict import graph_to_lean as c
    _, lean, sources = case
    total = len(lean.encode())+sum(len(s.encode()) for s in sources.values())
    monkeypatch.setattr(c,'GENERATED_LEAN_SOURCE_LIMIT',total+delta)
    if accepted: assert w._proof_bundle(lean,sources)['kernel_checked'] is False
    else:
        with pytest.raises(ValueError,match='byte limit'): w._proof_bundle(lean,sources)


def test_seeded_feed_selects_both_finite_vocabularies_only_when_seeded():
    from Verdict import runtime_input_feed as feed
    tree = ast.parse(inspect.getsource(feed))
    call, = [n for n in ast.walk(tree) if isinstance(n,ast.Call)
             and isinstance(n.func,ast.Name) and n.func.id == 'pack_proofs']
    assert [k.arg for k in call.keywords] == ['names_v3','names_v4','names_v5','entry_names_v5']
    for seeds,expected in [(None,False),({'inventories':{}},True)]:
        seen=[]; prefixes=object()
        eval(compile(ast.Expression(call),'<v4-feed-call>','eval'),
             dict(pack_proofs=lambda *a,**kw:seen.append((a,kw)),prefixes=prefixes,seeds=seeds))
        assert seen == [((prefixes,),dict(names_v3=expected,names_v4=expected,names_v5=expected,entry_names_v5=False))]


def test_real_v4_codec_pack_admitted_and_default_unchanged():
    text = ''.join(f'theorem tinyPrefixWritten_{i} : (1 : Nat) = 1 := by\n  simp only [Nat.reduceEqDiff]\n' for i in range(20))
    groups = [[p.ProofGroup(text,20,())]]
    old = p.pack_proofs(groups)
    entry,sources = p.pack_proofs(groups,names_v3=True,names_v4=True)
    assert V4_FILE in sources and p.NAMES_V3_FILE not in sources
    assert p.expand_names(entry) == p.expand_names(old[0])
    assert p.pack_proofs(groups) == old
    sources[w.WORLD_DATA_FILE] = 'import denote.SourceScopedEval\n'
    receipt = w._proof_bundle(entry,sources)
    assert receipt['dependency_order'] == [w.WORLD_DATA_FILE,p.SUPPORT_FILE,V4_FILE,'$entry']
    assert receipt['modules'][-1]['theorems'] == [f'tinyPrefixWritten_{i}' for i in range(20)]


def test_real_v4_publish_revalidates_support_before_writes(tmp_path):
    text = ''.join(f'theorem tinyPrefixWritten_{i} : (1 : Nat) = 1 := by\n  simp only [Nat.reduceEqDiff]\n' for i in range(20))
    entry,sources = p.pack_proofs([[p.ProofGroup(text,20,())]],names_v4=True)
    sources[w.WORLD_DATA_FILE] = 'import denote.SourceScopedEval\n'
    receipt = dict(proof_bundle=w._proof_bundle(entry,sources))
    malformed = dict(sources); malformed[V4_FILE] += '-- tampered\n'
    with pytest.raises(ValueError):
        w.publish(w.WorldDefinitions(entry,receipt,malformed),tmp_path/'bad'/'RuntimeWorld.lean')
    assert not (tmp_path/'bad').exists()
    target=tmp_path/'good'/'RuntimeWorld.lean'
    w.publish(w.WorldDefinitions(entry,receipt,sources),target)
    assert target.read_text() == entry
    assert (target.parent/V4_FILE).read_text() == p.names_v4_source()
