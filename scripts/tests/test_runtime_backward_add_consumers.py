"""Original LayerNorm dX feeds both ordered reverse residual branches."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_add_consumers'), 'missing original LN to ADD join'
    return importlib.import_module('Verdict.runtime_backward_add_consumers')


def test_original_layernorm_to_two_add_branches(worlds):
    text, detail = api().render(worlds)
    assert len(detail['reads']) == 5
    assert text.count('#print axioms') == 10
    assert [(r['world'], r['source_index'], r['execution_index']) for r in detail['reads']] == [
        ('sm', 66, 66), ('pm', 112, 222), ('pm', 348, 225), ('pm', 584, 644), ('pm', 820, 647)]
    for row in detail['reads']:
        assert len(row['theorems']) == 2
        assert '(bw_layernorm ' in text
    assert not detail['kernel_value_proved']


@pytest.mark.parametrize('fault', ['cotangent-tid', 'saved-primal-tid', 'mirror-index'])
def test_rejects_incoherent_predecessor_join(worlds, monkeypatch, fault):
    api().render(worlds)
    from Verdict import runtime_backward_layernorm_reads as predecessor
    real = predecessor.render_read
    def corrupted(*args):
        import copy
        text, row = real(*args); row = copy.deepcopy(row)
        if fault == 'cotangent-tid': row['output_tids'][0] += 100000
        elif fault == 'saved-primal-tid': row['input_tids'][1] += 100000
        else: row['source_contract']['fw_source_index'] += 1
        return text, row
    monkeypatch.setattr(predecessor, 'render_read', corrupted)
    with pytest.raises(ValueError): api().render(worlds)
