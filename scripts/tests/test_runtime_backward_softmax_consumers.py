import importlib
import importlib.util
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def test_original_matmul_first_output_to_softmax_same_store(worlds):
    assert importlib.util.find_spec('Verdict.runtime_backward_softmax_consumers'), 'missing matmul-softmax composition'
    api = importlib.import_module('Verdict.runtime_backward_softmax_consumers')
    text, detail = api.render(worlds)
    assert len(detail['reads']) == 5
    assert [(r['world'],r['matmul']['source_index'],r['softmax']['source_index']) for r in detail['reads']] == [
        ('sm',77,78),('pm',131,133),('pm',367,369),('pm',603,605),('pm',839,841)]
    for row in detail['reads']:
        m, s = row['matmul'], row['softmax']
        assert s['input_refs'][0] == m['output_refs'][0]
        assert s['input_tids'][0] == m['output_tids'][0]
        assert row['expression'] == 'bw_softmax ((bw_matmul ' + ' '.join(f'(t {i})' for i in m['input_tids']) + f').1) (t {s["input_tids"][1]})'
        assert f't {s["output_tid"]} = {row["expression"]} := by' in text
        assert m['theorems'][0]+' s t h' in text and s['theorems'][0]+' s t h' in text
    assert detail['source_text'].count('#print axioms') == 5
    assert text.count('#print axioms') == 5
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))
    assert api.render(worlds) == (text,detail)
