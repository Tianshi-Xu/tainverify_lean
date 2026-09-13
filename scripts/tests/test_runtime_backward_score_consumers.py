import importlib
import importlib.util
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_reduce_scatter_reads import paths


def test_original_score_path_keeps_both_exchanges_and_matmul_outputs(worlds,paths):
    assert importlib.util.find_spec('Verdict.runtime_backward_score_consumers'), 'missing original score backward DAG'
    api=importlib.import_module('Verdict.runtime_backward_score_consumers')
    text,detail=api.render(worlds,*paths)
    assert [(r['world'],r['source_index']) for r in detail['div_reads']] == [('sm',79),('pm',135),('pm',371),('pm',607),('pm',843)]
    assert [r['source_index'] for r in detail['collective_reads']] == [134,370,606,842,136,372,608,844]
    assert [(r['world'],r['source_index']) for r in detail['matmul_reads']] == [('sm',80),('pm',137),('pm',373),('pm',609),('pm',845)]
    assert len(detail['targets'])==10
    for row in detail['targets']:
        assert row['projection'] in (1,2)
        assert f').{row["projection"]}' in row['expression']
        assert row['source_node']['output_tids'][row['projection']-1] == row['output_tid']
        assert row['value_name']+' t' in text
    assert len({n['value_name'] for n in detail['dag']})==len(detail['dag'])
    assert text.count('#print axioms')==len(detail['dag'])
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))
