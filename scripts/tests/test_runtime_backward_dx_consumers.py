import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from scripts.tests.test_runtime_backward_prefix_shapes import prefix
from scripts.tests.test_runtime_backward_cotangent_reads import rank_code
from scripts.tests.test_runtime_backward_dx_values import initial_relations

def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_dx_consumers'), 'missing original reconstructed dX consumers'
    return importlib.import_module('Verdict.runtime_backward_dx_consumers')

def test_original_reduce_scatter_reads_reconstructed_dx(worlds,config,prefix,rank_code,initial_relations):
    text,detail=api().render(worlds,config,prefix,rank_code,initial_relations)
    assert [(r['output_tid'],r['unit'],r['local_index']) for r in detail['reads']]==[(276,0,0),(579,0,1),(882,1,0),(1185,1,1)]
    assert 'backwardDxUnit_0' in text and 'backwardDxUnit_1' in text
    assert 'backwardReduceScatter_pm_' in text
    assert ' = tensorSum' not in text
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

@pytest.mark.parametrize('fault',['ordered-inputs','wrong-dp','dimension','local-index','input-shape'])
def test_exact_consumer_join_after_fresh_source_predecessors(admitted,fault):
    import copy
    values,reads,sm=copy.deepcopy(admitted)
    module=api(); module._compose(*admitted)
    row=reads['reads'][0]
    if fault=='ordered-inputs': row['input_tids'].reverse()
    elif fault=='wrong-dp': row['ranks']=reads['reads'][-1]['ranks']
    elif fault=='dimension': row['params']=[0]
    elif fault=='local-index': row['local_index']=len(row['ranks'])
    else: row['input_shape'][1]+=1
    with pytest.raises(ValueError,match='bw-dx-consumer'):
        module._compose(values,reads,sm)
