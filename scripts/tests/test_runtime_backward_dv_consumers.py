import importlib
import importlib.util
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_reduce_scatter_reads import paths


def test_original_second_output_contribution_composition(worlds, paths):
    assert importlib.util.find_spec('Verdict.runtime_backward_matmul_reduce_scatter_consumers'), 'missing original dV contribution composition'
    api = importlib.import_module('Verdict.runtime_backward_matmul_reduce_scatter_consumers')
    text, detail = api.render(worlds,*paths)
    assert [r['source_index'] for r in detail['reads']] == [132,368,604,840]
    for row in detail['reads']:
        assert row['opname'] == 'ReduceScatterPrim' and row['output_port'] == 1
        assert row['local_index'] == row['ranks'].index(worlds[1][1][row['source_index']].rank)
        assert len(row['predecessors']) == len(row['ranks'])
        for p,ref in zip(row['predecessors'],row['input_refs'],strict=True):
            assert p['output_refs'][1] == ref
            assert p['theorems'][1].endswith('_dy')
            assert p['theorems'][1]+' s t h' in text
        assert row['expression'].startswith('chunkPrimDimN ')
        assert row['expression'].count(').2')==len(row['ranks'])
        assert 'bw_linear' not in row['expression']
    assert text.count('#print axioms') == 4 and detail['source_text'].count('#print axioms') == 4
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))
