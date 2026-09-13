"""V5 bundle gates; these inventory tests are not kernel acceptance."""
import ast
import inspect
import pytest
from Verdict import runtime_prefix as p, runtime_world as w

def test_v5_can_preserve_extensible_final_entry_bytes():
    body=''.join(f'theorem tinyPrefixWritten_{i} (h : tinyPrefixInitShapes) : True := True.intro\n' for i in range(20))
    groups=[[p.ProofGroup(body,50,()),p.ProofGroup(body,50,()),p.ProofGroup(body,20,(),final=True)]]
    old_entry,_=p.pack_proofs(groups,names_v3=True,names_v4=True)
    entry,support=p.pack_proofs(groups,names_v3=True,names_v4=True,names_v5=True,entry_names_v5=False)
    assert entry==old_entry
    assert p.NAMES_V5_FILE in support  # immutable chunks still opt in
    assert 'prefix_names_v5 ' not in entry
    entry,support=p.pack_proofs([[p.ProofGroup(body,20,(),final=True)]],names_v5=True,entry_names_v5=False)
    assert p.NAMES_V5_FILE not in support


def test_extensible_final_entry_survives_read_notation_composition():
    from Verdict.runtime_read_source import compact,expand
    body=''.join(f'theorem tinyPrefixWritten_{i} (h : tinyPrefixInitShapes) : True := True.intro\n' for i in range(20))
    entry,support=p.pack_proofs([[p.ProofGroup(body,20,(),final=True)]],names_v3=True,names_v4=True,names_v5=True,entry_names_v5=False)
    suffix='\nnamespace TrainVerify.Denote.RuntimeWorld\n'+''.join(f'def requestAlias_{i} := pmInputRequests\n' for i in range(30))+'end TrainVerify.Denote.RuntimeWorld\n'
    compacted=compact(entry+suffix)
    assert 'section RuntimeReadSource' in compacted
    assert expand(compacted)==entry+suffix
    support[w.WORLD_DATA_FILE]='import denote.SourceScopedEval\n'
    w._proof_bundle(compacted,support)


MODULE='TrainVerifyRuntimePrefixNamesV5'
FILE=MODULE+'.lean'
IMPORT=f'import {MODULE}\n'

@pytest.fixture
def fixture(monkeypatch):
    source='import TrainVerifyRuntimePrefixSupport\n-- v5 fixture\n'
    monkeypatch.setattr(p,'NAMES_V5_MODULE',MODULE,raising=False)
    monkeypatch.setattr(p,'NAMES_V5_FILE',FILE,raising=False)
    monkeypatch.setattr(p,'names_v5_source',lambda:source,raising=False)
    original=p.expand_names
    monkeypatch.setattr(p,'expand_names',lambda t:original(t.replace(IMPORT,'').replace('prefix_names_v5 ','prefix_names ')))
    base=f'import {w.WORLD_DATA_MODULE}\nimport denote.SourceScopedPrefix\nimport {p.SUPPORT_MODULE}\n'
    entry=base+IMPORT+'prefix_names_v5 tinyPrefix where\n theorem w_0 : True := True.intro\n'
    sources={w.WORLD_DATA_FILE:'import denote.SourceScopedEval\n',p.SUPPORT_FILE:p.support_source(),FILE:source}
    return base,entry,sources

def test_v5_support_is_closed_and_ordered(fixture):
    _,entry,sources=fixture
    r=w._proof_bundle(entry,sources)
    assert r['dependency_order']==[w.WORLD_DATA_FILE,p.SUPPORT_FILE,FILE,'$entry']
    assert r['modules'][-1]['theorems']==['tinyPrefixWritten_0']
    assert r['modules'][2]['imports']==[p.SUPPORT_MODULE]
    assert r['kernel_checked'] is False

@pytest.mark.parametrize('fault',['missing','changed','unused','no-import','double-import','unmarked','unknown','wrong-support'])
def test_v5_inventory_rejects(fixture,fault):
    base,entry,sources=fixture
    if fault=='missing':sources.pop(FILE)
    elif fault=='changed':sources[FILE]+='-- changed\n'
    elif fault=='unused':entry=base
    elif fault=='no-import':entry=entry.replace(IMPORT,'')
    elif fault=='double-import':entry=entry.replace(IMPORT,IMPORT*2)
    elif fault=='unmarked':entry=base+IMPORT
    elif fault=='unknown':sources['Unapproved.lean']=sources[FILE]
    else:sources[FILE]=sources[FILE].replace(p.SUPPORT_MODULE,p.NAMES_V4_MODULE)
    with pytest.raises(ValueError):w._proof_bundle(entry,sources)

def test_v5_support_still_counts_at_exact_aggregate_limit(fixture,monkeypatch):
    from Verdict import graph_to_lean as c
    _,entry,sources=fixture
    total=len(entry.encode())+sum(len(t.encode()) for t in sources.values())
    monkeypatch.setattr(c,'GENERATED_LEAN_SOURCE_LIMIT',total+1)
    w._proof_bundle(entry,sources)
    monkeypatch.setattr(c,'GENERATED_LEAN_SOURCE_LIMIT',total)
    with pytest.raises(ValueError,match='byte limit'):w._proof_bundle(entry,sources)

def test_feed_opts_into_v5_only_for_seeded_inputs():
    from Verdict import runtime_input_feed as feed
    tree=ast.parse(inspect.getsource(feed))
    call,=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='pack_proofs']
    assert [k.arg for k in call.keywords]==['names_v3','names_v4','names_v5','entry_names_v5']
    for seeds,expected in [(None,False),({'inventories':{}},True)]:
        seen=[];prefixes=object()
        eval(compile(ast.Expression(call),'<feed-call>','eval'),dict(pack_proofs=lambda *a,**kw:seen.append((a,kw)),prefixes=prefixes,seeds=seeds))
        assert seen==[((prefixes,),dict(names_v3=expected,names_v4=expected,names_v5=expected,entry_names_v5=False))]

def test_mixed_versions_keep_exact_prior_edges(fixture):
    base,entry,sources=fixture
    v3,v4,v5=[p.PREFIX_MODULE+f'{i:04d}' for i in range(3)]
    sources[p.NAMES_V3_FILE]=p.names_v3_source();sources[p.NAMES_V4_FILE]=p.names_v4_source()
    sources[v3+'.lean']=base+f'import {p.NAMES_V3_MODULE}\nprefix_names_v3 tinyPrefix where\n def t_0 := pL\n'
    sources[v4+'.lean']=base+f'import {v3}\nimport {p.NAMES_V4_MODULE}\nprefix_names_v4 tinyPrefix where\n def t_1 := pE\n'
    sources[v5+'.lean']=entry.replace(IMPORT,f'import {v4}\n'+IMPORT)
    r=w._proof_bundle(base+f'import {v5}\n',sources)
    assert r['dependency_order']==[w.WORLD_DATA_FILE,p.SUPPORT_FILE,p.NAMES_V3_FILE,p.NAMES_V4_FILE,FILE,v3+'.lean',v4+'.lean',v5+'.lean','$entry']
    assert r['modules'][-2]['imports'][-2:]==[v4,MODULE]
    sources[v5+'.lean']=sources[v5+'.lean'].replace(f'import {v4}\n','')
    with pytest.raises(ValueError,match='import membership'):w._proof_bundle(base+f'import {v5}\n',sources)
