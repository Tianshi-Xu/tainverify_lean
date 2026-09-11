"""Actual authenticated seed -> original BW_sum final-Store fragments."""
import importlib
import importlib.util
import json
import os
from pathlib import Path

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


@pytest.fixture(scope='module')
def config():
    return json.loads((Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/
        'dp-prefix-bwembedding-implementation/seed-config.json').read_text())


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_seed_reads'), 'missing authenticated BW_sum source reads'
    return importlib.import_module('Verdict.runtime_backward_seed_reads')


def test_actual_authenticated_seeds_feed_original_bw_sum(worlds,config):
    text,detail=api().render(worlds,config,config['pm_run'])
    assert len(detail['reads'])==sum(len(v) for v in detail['inventories'].values())
    for row in detail['reads']:
        label=row['world'];view,cells,_,order,_=next(w for w in worlds if w[-1]==label)
        cell=cells[row['source_index']]
        assert cell.opname.name=='BW_sum'
        assert row['execution_index']==order['source_to_execution'][row['source_index']]
        assert row['input_refs']==[list(r) for r in cell.inputs]
        assert row['seed']['value']==1  # freshly validated observed seed, not a default
        assert row['operand_nonwrite_source_indices']==order['execution_to_source'][row['execution_index']:]
        assert f'{label}SeededDenoteWithInputs' in text
    assert 'SourceBWSumRead.bw_sum_value_of_split' in text
    assert 'SourceParameterFrame.runWithInputs_frame' in text
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))


@pytest.fixture(scope='module')
def admitted(worlds,config):
    return api().render(worlds,config,config['pm_run'])[1]


@pytest.mark.parametrize('fault',['seed-ref','seed-value','seed-type','signature','params','suffix'])
def test_new_sum_read_boundary_after_fresh_seed_authentication(worlds,admitted,monkeypatch,fault):
    import copy
    from Verdict import graph_to_lean
    for view,cells,snapshot,order,label in worlds:
        seed=copy.deepcopy(admitted['inventories'][label][0])
        api()._read(view,cells,snapshot,order,label,seed,0)
        cell=next(c for c in cells if list(c.node)==seed['consumer'])
        with monkeypatch.context() as m:
            if fault=='seed-ref': seed['ref']['version']+=1
            elif fault=='seed-value': seed['value']=3
            elif fault=='seed-type': seed['value']=True
            elif fault=='signature': m.setattr(cell.ir.mirror,'signature','torch.mean')
            elif fault=='params': m.setattr(graph_to_lean,'_get_node_params',lambda *a,**k:[False])
            else:
                # A complete future source node now writes the saved input.
                later=view.nodes()[-1]
                m.setitem(view._node2outputs,later,[view.node_inputs(cell.node)[1]])
                m.setitem(view.source._node2outputs,later,[cell.inputs[1]])
            with pytest.raises(ValueError): api()._read(view,cells,snapshot,order,label,seed,0)
