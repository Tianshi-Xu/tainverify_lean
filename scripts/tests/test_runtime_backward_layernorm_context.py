import importlib,importlib.util
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_prefix_shapes import prefix
from scripts.tests.test_runtime_backward_dx_values import initial_relations

def test_ln_context_derives_shapes_and_affine_values_from_existing_contract(worlds,prefix,initial_relations):
    assert importlib.util.find_spec('Verdict.runtime_backward_layernorm_context'), 'missing layernorm input context projections'
    module=importlib.import_module('Verdict.runtime_backward_layernorm_context')
    text,detail=module.render(worlds,prefix,initial_relations)
    assert detail['sm_saved_tid']==1317
    assert {r['tid'] for r in detail['pm_saved_shapes']}=={272,575,878,1181}
    assert len(detail['parameters'])==8
    assert {r['sm_tid'] for r in detail['parameters']}=={1234,1235}
    assert 'backwardParameterValuesFinal' in text
    assert 'backwardSMShapesFromInitial' in text
    assert 'theorem backwardPrefixRun_pm' not in text
