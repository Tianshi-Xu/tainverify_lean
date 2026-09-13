"""Original dX -> ReduceScatter; trusted existing captures, never recapture."""
import importlib
import importlib.util
import os
from pathlib import Path

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_reduce_scatter_reads'), 'missing original ReduceScatter source-read renderer'
    return importlib.import_module('Verdict.runtime_backward_reduce_scatter_reads')


def selected(worlds):
    view,cells,_,_,_=worlds[1]
    return [next(i for i,c in enumerate(cells) if c.rank==r and c.opname.name=='BW_linear')
            for r in range(view.W.runtime_ndevs)]


@pytest.fixture(scope='module')
def paths():
    root=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/'p2-r4'
    return str(root/'capture.pkl'),str(root/'code/_parallel_modules/genmodel/model/gpt/GPT/_')


def test_original_dx_to_reduce_scatter_same_final_store(worlds,paths):
    text,detail=api().render(worlds,selected(worlds),*paths)
    assert len(detail['reads'])==len(selected(worlds))
    for r in detail['reads']:
        assert r['params']==[1]
        assert r['raw_kwargs']['dim']==r['params'][0]
        assert r['backward_context_status']=='structurally-bound'
        assert r['input_ranks']==r['ranks']
        assert r['local_index']==r['ranks'].index(r['rank'])
        assert r['input_shape']==[1,16,64] and r['output_shape']==[1,8,64]
        assert [p['source_index'] for p in r['contributions']]==[i for i in selected(worlds) if worlds[1][1][i].rank in r['ranks']]
        assert all(p['theorem'].endswith('_dx') for p in r['contributions'])
        assert r['operand_nonwrite_source_indices']==worlds[1][3]['execution_to_source'][r['execution_index']:]
        assert len(r['theorems'])==2
    assert 'SourceReduceScatterRead.reduceScatter_value_of_split' in text
    assert 'chunkPrimDimN 1 2 0 (tensorSum' in text
    assert 'chunkPrimDimN 1 2 1 (tensorSum' in text
    assert 'backwardLinearRead_pm_' in text
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement','sm_pm_dx_equal'))
    assert api().render(worlds,selected(worlds),*paths)==(text,detail)


@pytest.fixture(scope='module')
def admitted(worlds,paths):
    from Verdict import graph_to_lean as c
    source=c._load_chunk_source(*paths)
    c.attach_collective_scopes(worlds[1][0],source)
    return source


@pytest.mark.parametrize('fault', ['raw-kwargs','lowered-op','raw-bool-dim','context','dim','bool-dim',
    'peers','local-world-rank','gradient-version','read-writer','peer-read-order','missing-dx',
    'same-shape','bool-shape','output-shape','nondivisible','scope-shape','execution-order'])
def test_fail_closed_original_boundary(worlds,admitted,monkeypatch,fault):
    import copy
    from dataclasses import replace
    from verdict.operators.names import OpName
    view,cells,_,order,_=worlds[1]; indices=selected(worlds)
    index=indices[-1] if fault=='local-world-rank' else indices[0]
    text,good=api()._read(view,cells,admitted,order,index,indices)
    source=copy.deepcopy(admitted); execution=copy.deepcopy(order)
    node=cells[good['source_index']].node; scope=view.collective_scopes[node]
    writer=next(w for w in source['writers'] if w['export_id']==scope.source_writer)
    ctx=writer['adapter']['backward_context']
    with monkeypatch.context() as m:
        if fault in ('raw-kwargs','raw-bool-dim'):
            m.setitem(view.source._node2kwargs,node,dict(view.node_kwargs(node),dim=0 if fault=='raw-kwargs' else True))
        elif fault=='lowered-op': m.setitem(view.source._node2opname,node,OpName.AllGatherPrim)
        elif fault=='context': ctx['status']='missing'
        elif fault=='dim': m.setitem(view.collective_scopes,node,replace(scope,params=(2,)))
        elif fault=='bool-dim': ctx['runtime']['backward']['kwargs']['dim']=True
        elif fault=='peers': m.setitem(view.collective_scopes,node,replace(scope,input_tids=tuple(reversed(scope.input_tids))))
        elif fault=='local-world-rank': m.setitem(view.collective_scopes,node,replace(scope,local_index=node.rank))
        elif fault=='gradient-version': ctx['output_gradient'][0]['version']+=1
        elif fault=='read-writer': ctx['gradient_read_points'][0]['writer']='forged'
        elif fault=='peer-read-order': writer['adapter']['read_points'].reverse()
        elif fault=='missing-dx': indices.remove(indices[1])
        elif fault=='scope-shape': m.setitem(view.collective_scopes,node,replace(scope,input_shape=(1,18,64)))
        elif fault=='execution-order': execution['execution_to_source'].reverse()
        else:
            shape=view.tensor_shape
            target=good['output_tid'] if fault=='output-shape' else good['input_tids'][-1]
            replacement=(True,16,64) if fault=='bool-shape' else (1,15,64) if fault=='nondivisible' else (1,18,64)
            m.setattr(view,'tensor_shape',lambda t: replacement if t.tid==target else shape(t))
        with pytest.raises(ValueError):
            api()._read(view,cells,source,execution,index,indices)
    assert api()._read(view,cells,admitted,order,index,selected(worlds))==(text,good)


@pytest.mark.parametrize('fault',['empty','duplicate','bool','missing-peer'])
def test_projection_rejected(worlds,paths,fault):
    indices=selected(worlds)
    if fault=='empty': indices=[]
    elif fault=='duplicate': indices.append(indices[0])
    elif fault=='bool': indices[0]=True
    else: indices.pop()
    with pytest.raises(ValueError): api().render(worlds,indices,*paths)


def test_replay_returns_exact_candidate_without_writes(worlds,paths):
    import json
    import hashlib
    path=Path(__file__).resolve().parents[2]/'iroha-tasks/trainverify-backward/render_actual_reduce_scatter.py'
    assert path.is_file(), 'missing read-only actual ReduceScatter replay'
    spec=importlib.util.spec_from_file_location('reduce_scatter_replay',path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    root=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
    receipt=json.loads((root/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
    text,detail=module.replay(worlds,receipt,*paths)
    assert text.startswith('import TrainVerifyRuntimeWorldData\nimport ActualBWLinearRead\nimport denote.SourceReduceScatterRead\n')
    assert detail['candidate_sha256']==hashlib.sha256(text.encode()).hexdigest()
    assert detail['theorem_count']==8 and detail['kernel_value_proved'] is False
    assert detail['source_execution_pairs']==[[110,220],[346,223],[582,642],[818,645]]
    receipt['execution_order']['pm']['execution_to_source'].reverse()
    with pytest.raises(ValueError,match='replay'):
        module.replay(worlds,receipt,*paths)
