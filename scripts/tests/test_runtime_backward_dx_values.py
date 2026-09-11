"""Actual SM-PM dX reconstruction joins fresh backward/DP source authority."""
import importlib
import importlib.util
import json
import os
from pathlib import Path
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from scripts.tests.test_runtime_backward_prefix_shapes import prefix
from scripts.tests.test_runtime_backward_cotangent_reads import rank_code

@pytest.fixture(scope='module')
def initial_relations():
    path=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json'
    return json.loads(path.read_text())['initial_relations']

def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_dx_values'), 'missing original dX reconstruction'
    return importlib.import_module('Verdict.runtime_backward_dx_values')

def test_actual_dx_uses_separate_source_dp_units(worlds,config,prefix,rank_code,initial_relations):
    text,detail=api().render(worlds,config,prefix,rank_code,initial_relations)
    assert [(r['unit'],r['ranks'],r['dx_tids']) for r in detail['units']]==[(0,[0,1],[279,581]),(1,[2,3],[885,1187])]
    assert 'source_bw_linear_dx_batch_tp_unit' in text
    assert 'backwardSMShapesFromInitial' in text
    assert 'backwardSMConstant' in text
    assert 'InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p)' in text
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))

@pytest.fixture(scope='module')
def admitted(worlds,config,prefix,rank_code,initial_relations):
    from unittest.mock import patch
    module=api(); original=module._compose; saved=[]
    def capture(*args):
        saved.append(args)
        return original(*args)
    with patch.object(module,'_compose',capture):
        module.render(worlds,config,prefix,rank_code,initial_relations)
    return saved[0]

@pytest.mark.parametrize('fault',['bool-dp','mixed-dp','parameter-order','bounds','parent','missing-unit','cotangent-shape','wrong-axis'])
def test_composition_rejects_mismatch_after_fresh_predecessors(admitted,fault):
    import copy
    sm,cs,pm,placements,initial=copy.deepcopy(admitted)
    module=api(); module._compose(*admitted)
    first=next(iter(pm)); owner=placements[first]['parameter_placement']
    row=next(r for r in initial['relations'] if r['sm_binding']['ref']==sm['linear_binding']['input_refs'][2])
    if fault=='bool-dp': owner['scale_unit']=False
    elif fault=='mixed-dp': owner['scale_unit']+=1
    elif fault=='parameter-order': row['units'][0]['bindings'].reverse()
    elif fault=='bounds': row['units'][0]['bindings'][0]['bounds'][0][0]+=1
    elif fault=='parent': row['units'][0]['bindings'][0]['parent_tid']+=1
    elif fault=='missing-unit': row['units'].pop()
    elif fault=='cotangent-shape': cs['reads'][0]['shape'][1]+=1
    else: row['units'][0]['initial_goal']['dim']=1
    with pytest.raises(ValueError,match='bw-dx'):
        module._compose(sm,cs,pm,placements,initial)
