"""Layernorm saved-primal shapes reuse the existing PM prefix DAG."""
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_prefix_shapes import prefix
from Verdict.runtime_backward_prefix_shapes import render


def indices(worlds):
    view,cells,_,order,_=worlds[1]
    return [next(i for i in order['execution_to_source'] if cells[i].rank==r and cells[i].opname.name=='BW_layernorm') for r in range(view.W.runtime_ndevs)]


def test_layernorm_saved_shapes_share_existing_final_state(worlds,prefix):
    text,detail=render(worlds,[],prefix,layernorm_indices=indices(worlds),include_run=False)
    assert len(detail['reads'])==4
    assert {r['tid'] for r in detail['reads']}=={272,575,878,1181}
    assert all(r['shape']==[1,8,64] for r in detail['reads'])
    assert 'theorem backwardPrefixRun_pm' not in text
    assert 'backwardPrefixFinal_pm s t hi hrun' in text

@pytest.mark.parametrize('fault',['duplicate','bool','wrong-kind','source-epsilon'])
def test_layernorm_projection_authenticates_before_selecting_shape(worlds,prefix,monkeypatch,fault):
    selected=indices(worlds); render(worlds,[],prefix,layernorm_indices=selected,include_run=False)
    with monkeypatch.context() as m:
        if fault=='duplicate': selected.append(selected[0])
        elif fault=='bool': selected[0]=True
        elif fault=='wrong-kind': selected[0]-=1
        else:
            cell=worlds[1][1][selected[0]]
            m.setattr(cell,'kwargs',dict(cell.kwargs,eps=1e-4))
        with pytest.raises(ValueError): render(worlds,[],prefix,layernorm_indices=selected,include_run=False)
