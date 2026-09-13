import importlib,importlib.util
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from scripts.tests.test_runtime_backward_prefix_shapes import prefix
from scripts.tests.test_runtime_backward_cotangent_reads import rank_code
from scripts.tests.test_runtime_backward_dx_values import initial_relations
import pytest

@pytest.fixture(scope='module')
def admitted(worlds,config,prefix,rank_code,initial_relations):
    from unittest.mock import patch
    module=importlib.import_module('Verdict.runtime_backward_layernorm_dbeta_values')
    original=module._compose; saved=[]
    def record(*args):
        saved.append(args)
        return original(*args)
    with patch.object(module,'_compose',record): module.render(worlds,config,prefix,rank_code,initial_relations)
    return saved[0]

@pytest.mark.parametrize('fault',['source-dp','cotangent-join','reducer-order','missing-tp','peer-shape'])
def test_beta_composition_requires_exact_source_input_partitions(admitted,fault):
    import copy
    module=importlib.import_module('Verdict.runtime_backward_layernorm_dbeta_values')
    module._compose(*admitted)
    ctx,reds,dx=copy.deepcopy(admitted)
    beta=next(r for r in reds['reads'] if r['role']=='dbeta')
    if fault=='source-dp': beta['coordinates'][0][0]=1
    elif fault=='cotangent-join': ctx['pm_reads'][0]['input_tids'][0]+=1
    elif fault=='reducer-order': beta['input_tids'].reverse()
    elif fault=='missing-tp': dx['reads'].pop()
    else: dx['reads'][-1]['shape'][1]+=1
    with pytest.raises(ValueError): module._compose(ctx,reds,dx)

def test_source_beta_reconstructs_full_dp_tp_sum_without_saved_values(worlds,config,prefix,rank_code,initial_relations):
    assert importlib.util.find_spec('Verdict.runtime_backward_layernorm_dbeta_values'), 'missing original dBeta reconstruction'
    module=importlib.import_module('Verdict.runtime_backward_layernorm_dbeta_values')
    text,detail=module.render(worlds,config,prefix,rank_code,initial_relations)
    assert detail['sm_output']==1260
    assert detail['ordered_contributions']==[70,373,676,979]
    assert detail['outputs']==[71,374,677,980]
    assert 'source_bw_layernorm_dbeta_batch_reduction' in text
    assert 'source_bw_layernorm_dbeta_sequence_reduction' in text
    assert 'source_tensorSum_groups' in text
    assert detail['saved_value_premise'] is False
