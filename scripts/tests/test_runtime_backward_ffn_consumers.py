"""Original residual-right -> fc2 dX -> exact GELU derivative source chain."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_ffn_consumers'), 'missing original FFN reverse chain'
    return importlib.import_module('Verdict.runtime_backward_ffn_consumers')


def test_actual_original_ffn_reverse_chain(worlds):
    text, detail = api().render(worlds)
    assert len(detail['reads']) == 5
    assert text.count('#print axioms') == 10
    for row in detail['reads']:
        assert row['gelu']['input_refs'][0] == row['linear']['output_refs'][0]
        assert row['linear']['input_refs'][0] == row['add']['output_refs'][1]
    assert '(bw_add2 ' in text and 'bw_gelu ((bw_linear ' in text
    assert not detail['kernel_value_proved']


@pytest.mark.parametrize('fault', ['gelu-input', 'gelu-output', 'linear-input', 'linear-output'])
def test_ffn_chain_refuses_mismatched_lowered_binding(worlds, monkeypatch, fault):
    import copy
    from Verdict import runtime_backward_gelu_reads as gelu, runtime_backward_linear_reads as linear
    api().render(worlds)
    module = gelu if fault.startswith('gelu') else linear
    original = module.render_read
    def corrupted(*args):
        text, row = original(*args); row = copy.deepcopy(row)
        row['input_tids' if fault.endswith('input') else 'output_tids'][0] += 10000
        return text, row
    monkeypatch.setattr(module, 'render_read', corrupted)
    with pytest.raises(ValueError): api().render(worlds)
