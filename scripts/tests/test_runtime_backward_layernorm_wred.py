import importlib,importlib.util,os
from pathlib import Path
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_layernorm_shapes import indices


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_layernorm_wred'), 'missing original LayerNorm affine-gradient reducer bridge'
    return importlib.import_module('Verdict.runtime_backward_layernorm_wred')

@pytest.fixture(scope='module')
def paths():
    r=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/'p2-r4'
    return str(r/'capture.pkl'),str(r/'code/_parallel_modules/genmodel/model/gpt/GPT/_')


def test_original_affine_reducers_cover_dp_and_tp_once(worlds,paths):
    text,detail=api().render(worlds,indices(worlds),*paths)
    assert len(detail['reads'])==8
    assert {r['role'] for r in detail['reads']}=={'dgamma','dbeta'}
    for r in detail['reads']:
        assert r['ranks']==[0,1,2,3]
        assert r['coordinates']==[[0,0],[0,1],[1,0],[1,1]]
        assert r['reduce_op']=='sum' and r['nreplicas']==1 and r['zero']==0
        assert len(r['contributions'])==4
        assert all(c['theorem'].endswith('_'+r['role']) for c in r['contributions'])
    assert 'SourceWREDRead.wred_value_of_split' in text
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))

@pytest.fixture(scope='module')
def admitted(worlds,paths):
    from Verdict import graph_to_lean as c
    source=c._load_chunk_source(*paths)
    c.attach_wred_scopes(worlds[1][0],source,source.raw_writers,source.raw_rank_sources)
    return source

@pytest.mark.parametrize('fault',['mean','replicas','bool-coordinate','duplicate-coordinate','distinct-wrong-coordinate','peer-order','parameter-role','parameter-parent','missing-contribution'])
def test_affine_reducer_rejects_after_original_positive(worlds,admitted,monkeypatch,fault):
    from dataclasses import replace
    v,c,_,o,_=worlds[1]; selected=indices(worlds); i=selected[0]
    text,good=api()._read(v,c,admitted,o,i,selected,'dbeta')
    node=c[good['source_index']].node; scope=v.wred_scopes[node]
    writer=next(w for w in admitted['writers'] if w['export_id']==scope.source_writer)
    raw=admitted.raw_writers[node]
    with monkeypatch.context() as m:
        if fault=='mean': m.setitem(writer['reducer'],'reduce_op','mean')
        elif fault=='replicas': m.setitem(writer['reducer'],'nreplicas',2)
        elif fault=='bool-coordinate': m.setitem(raw['placement'],'plan_rank',False)
        elif fault=='duplicate-coordinate':
            second=api()._reducer(c,c[selected[1]].outputs[2])
            m.setitem(admitted.raw_writers[second.node]['placement'],'plan_rank',raw['placement']['plan_rank'])
        elif fault=='distinct-wrong-coordinate': m.setitem(raw['placement'],'plan_rank',9)
        elif fault=='peer-order': m.setitem(v.wred_scopes,node,replace(scope,input_tids=tuple(reversed(scope.input_tids))))
        elif fault=='parameter-role': m.setitem(v.wred_scopes,node,replace(scope,parameter=tuple(c[i].inputs[2])))
        elif fault=='parameter-parent': m.setitem(raw['placement'],'parent_tid',raw['placement']['parent_tid']+1)
        else: selected.pop()
        with pytest.raises(ValueError): api()._read(v,c,admitted,o,i,selected,'dbeta')
    assert api()._read(v,c,admitted,o,i,indices(worlds),'dbeta')==(text,good)
