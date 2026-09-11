"""Actual backward collective connects authenticated BW_sum to BW_linear."""
import importlib
import importlib.util
import os
from pathlib import Path
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_cotangent_reads'), 'missing backward cotangent source connection'
    return importlib.import_module('Verdict.runtime_backward_cotangent_reads')


@pytest.fixture(scope='module')
def rank_code():
    return str(Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_')


def test_actual_backward_scope_not_forward_looking_kwargs(worlds,config,rank_code):
    text,detail=api().render(worlds,config,config['pm_run'],rank_code)
    assert len(detail['reads'])==worlds[1][0].W.runtime_ndevs
    for r in detail['reads']:
        assert r['raw_kwargs']['idim']==2 and r['raw_kwargs']['odim']==1
        assert r['params']==[1,2]
        assert r['backward_context_status']=='structurally-bound'
        assert len(r['predecessors'])==len(r['ranks'])
        assert r['input_ranks']==r['ranks']
        assert 'backwardSeed_pm_' in text
        assert r['output_ref']==r['linear_input_ref']
    assert 'SourcePrimitiveRead.allToAll_value_of_split' in text
    assert 'AllToAllSourceFaithful.tensor' in text
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))


@pytest.fixture(scope='module')
def admitted(worlds,config,rank_code):
    from Verdict import runtime_backward_seed_reads as seeds, graph_to_lean as c
    _,prior=seeds.render(worlds,config,config['pm_run'])
    snapshot=c._load_chunk_source(str(Path(config['pm_capture'])/'capture.pkl'),rank_code)
    c.attach_collective_scopes(worlds[1][0],snapshot)
    return prior,snapshot


@pytest.mark.parametrize('fault',['context','dimensions','peers','gradient-version','missing-contribution','duplicate-contribution'])
def test_actual_reverse_boundary_rejects_mismatched_context_and_contributions(worlds,admitted,monkeypatch,fault):
    import copy
    from dataclasses import replace
    prior,snapshot=admitted;view,cells,_,order,_=worlds[1]
    seed=next(r for r in prior['reads'] if r['world']=='pm')
    _,good=api()._read(view,cells,snapshot,order,prior,seed)
    source=copy.deepcopy(snapshot);previous=copy.deepcopy(prior)
    node=view.nodes()[good['source_index']];scope=view.collective_scopes[node]
    writer=next(w for w in source['writers'] if w['export_id']==scope.source_writer)
    with monkeypatch.context() as m:
        if fault=='context': writer['adapter']['backward_context']['status']='missing'
        elif fault=='dimensions': m.setitem(view.collective_scopes,node,replace(scope,params=(2,1)))
        elif fault=='peers': m.setitem(view.collective_scopes,node,replace(scope,input_tids=tuple(reversed(scope.input_tids))))
        elif fault=='gradient-version': writer['adapter']['backward_context']['output_gradient'][0]['version']+=1
        else:
            contributor=next(r for r in previous['reads'] if r['theorems'][2]==good['predecessors'][1])
            if fault=='missing-contribution': previous['reads'].remove(contributor)
            else: previous['reads'].append(copy.deepcopy(contributor))
        with pytest.raises(ValueError,match='bw-cotangent'):
            api()._read(view,cells,source,order,previous,seed)
    assert api()._read(view,cells,snapshot,order,prior,seed)[1]==good
