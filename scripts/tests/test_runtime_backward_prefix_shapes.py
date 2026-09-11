"""Reuse the existing whole-prefix shape DAG, not capture shapes as premises."""
import importlib.util
import importlib
import json
import os
from pathlib import Path
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_wred_reads import selected
from scripts.tests.test_runtime_backward_seed_reads import config

@pytest.fixture(scope='module')
def prefix():
    path=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json'
    return json.loads(path.read_text())['scoped_prefix']['pm']

def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_prefix_shapes'), 'missing original final-store prefix shape projection'
    return importlib.import_module('Verdict.runtime_backward_prefix_shapes')

def test_actual_bw_inputs_use_shared_shape_dag(worlds,prefix):
    text,detail=api().render(worlds,selected(worlds),prefix)
    assert len(detail['reads'])==12
    assert {r['role'] for r in detail['reads']}=={'cotangent','saved_primal','dx'}
    assert 'pmSeededPrefixInitShapes' in text and 'pmSeededPrefixRun_0_' in text
    assert 'backwardPrefixFinal_pm' in text
    assert 'theorem backwardPrefixRun_pm' in text
    for row in detail['reads']:
        assert row['shape']==([1,16,128] if row['role']=='cotangent' else [1,16,64])
        assert row['frames'][0][1]==len(worlds[1][3]['execution_to_source'])
        assert row['frames'][-1][0]==row['writer_execution_index']+1
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))


def test_authenticated_sum_primals_are_shape_conclusions(worlds,prefix,config):
    text,detail=api().render(worlds,selected(worlds),prefix,seed_config=config)
    rows=[r for r in detail['reads'] if r['role']=='seed_primal']
    assert len(rows)==4
    for row in rows:
        assert row['shape']==[1,8,256]
        assert worlds[1][1][row['source_index']].opname.name=='BW_sum'
        assert row['ref']==list(worlds[1][1][row['source_index']].inputs[1])
        assert row['theorem'] in text


@pytest.mark.parametrize('fault',['coverage','order','run','shape','frame','duplicate'])
def test_prefix_projection_requires_complete_existing_certificates(worlds,prefix,fault):
    import copy
    indices=selected(worlds);_,good=api().render(worlds,indices,prefix)
    changed=copy.deepcopy(prefix)
    if fault=='coverage':changed['prefix_length']-=1
    elif fault=='order':changed['prefix_nodes'][0:2]=reversed(changed['prefix_nodes'][0:2])
    elif fault=='run':changed['kernel_checks'].remove(f"pmSeededPrefixRun_0_{prefix['prefix_length']}")
    elif fault=='shape':changed['kernel_checks'].remove(good['reads'][0]['dependencies'][1])
    elif fault=='frame':changed['kernel_checks'].remove(good['reads'][0]['dependencies'][2])
    else:indices.append(indices[0])
    with pytest.raises(ValueError,match='bw-prefix'):
        api().render(worlds,indices,changed)
