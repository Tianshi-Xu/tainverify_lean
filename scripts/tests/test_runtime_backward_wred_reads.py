"""Actual local linear parameter gradients -> original DP SUM reducers."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_cotangent_reads import rank_code
from scripts.tests.test_runtime_backward_seed_reads import config
from pathlib import Path


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_wred_reads'), 'missing original dW/WRED source-read bridge'
    return importlib.import_module('Verdict.runtime_backward_wred_reads')


def selected(worlds):
    view,cells,_,_,_=worlds[1]
    return [next(i for i,c in enumerate(cells) if c.rank==rank and c.opname.name=='BW_linear')
            for rank in range(view.W.runtime_ndevs)]


def test_actual_dw_reducer_identity_sum_and_order(worlds,rank_code,config):
    text,detail=api().render(worlds,selected(worlds),str(Path(config['pm_capture'])/'capture.pkl'),rank_code)
    assert len(detail['reads'])==4
    assert [r['ranks'] for r in detail['reads']]==[[0,2],[1,3],[0,2],[1,3]]
    for row in detail['reads']:
        assert row['parameter_placement']['name']=='lm_head.weight'
        assert row['reduce_op']=='sum' and row['nreplicas']==1 and row['zero']==0
        assert row['source_writer_ref']['call_instance']==5
        assert len(row['contributions'])==len(row['ranks'])
        for rank,c in zip(row['ranks'],row['contributions'],strict=True):
            assert c['gradient_ref'][1]==c['parameter_ref'][1]==rank
            assert c['gradient_ref'][4]==1
        assert row['output_ref'][4]==2
    assert 'SourceWREDRead.wred_value_of_split' in text
    assert 'cross_dp_wred' in text and 'backwardLinearRead_pm_' in text
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))


@pytest.fixture(scope='module')
def admitted(worlds,config,rank_code):
    from Verdict import graph_to_lean as c
    s=c._load_chunk_source(str(Path(config['pm_capture'])/'capture.pkl'),rank_code)
    c.attach_wred_scopes(worlds[1][0],s,s.raw_writers,s.raw_rank_sources)
    return s


@pytest.mark.parametrize('fault',['mean','replica','bool-replica','peer-order','peer-placement','peer-slice','parameter-ref','gradient-version','duplicate-unit','unit-type','missing-contribution'])
def test_wred_boundary_after_original_attachment(worlds,admitted,monkeypatch,fault):
    import copy
    from dataclasses import replace
    view,cells,_,order,_=worlds[1];indices=selected(worlds)
    _,good=api()._read(view,cells,admitted,order,indices[0],indices)
    snapshot=copy.deepcopy(admitted);node=view.nodes()[good['source_index']];scope=view.wred_scopes[node]
    writer=next(w for w in snapshot['writers'] if w['export_id']==scope.source_writer)
    peer_grad=good['contributions'][1]['gradient_ref']
    peer=next(n for n,s in view.wred_scopes.items() if n.rank==peer_grad[1] and s.parameter[3]==scope.parameter[3])
    with monkeypatch.context() as m:
        if fault=='mean':writer['reducer']['reduce_op']='mean'
        elif fault=='replica':writer['reducer']['nreplicas']=2
        elif fault=='bool-replica':writer['reducer']['nreplicas']=True
        elif fault=='peer-order':m.setitem(view.wred_scopes,node,replace(scope,input_tids=tuple(reversed(scope.input_tids))))
        elif fault=='peer-placement':snapshot.raw_writers[peer]['placement']['name']='different.weight'
        elif fault=='peer-slice':snapshot.raw_writers[peer]['placement']['indmap'][0]=[128,256]
        elif fault=='parameter-ref':m.setitem(view.wred_scopes,node,replace(scope,parameter=(*scope.parameter[:4],1)))
        elif fault=='gradient-version':snapshot.raw_writers[peer]['grad_input']['version']=True
        elif fault=='duplicate-unit':snapshot.raw_writers[peer]['placement']['scale_unit']=snapshot.raw_writers[node]['placement']['scale_unit']
        elif fault=='unit-type':snapshot.raw_writers[node]['placement']['scale_unit']=False
        else:indices.remove(good['contributions'][1]['source_index'])
        with pytest.raises(ValueError,match='bw-wred'):
            api()._read(view,cells,snapshot,order,indices[0],indices)
