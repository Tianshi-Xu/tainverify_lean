"""Constant values must follow fresh seed/source and existing shape DAG reads."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from scripts.tests.test_runtime_backward_prefix_shapes import prefix
from scripts.tests.test_runtime_backward_cotangent_reads import rank_code


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_constant_cotangents'), 'missing constant cotangent DAG composition'
    return importlib.import_module('Verdict.runtime_backward_constant_cotangents')


def test_original_pm_constant_values_from_authenticated_seed_and_shape(worlds, config, prefix, rank_code):
    text, detail = api().render(worlds, config, prefix, rank_code)
    assert len(detail['reads']) == 4
    assert 'source_constant_alltoall12_rank3' in text
    assert 'theorem backwardPrefix' not in text
    for row in detail['reads']:
        assert row['shape'] == [1, 16, 128]
        assert len(row['shape_dependencies']) == len(row['ranks'])
        assert row['seed_dependency'] in text
        assert all(name in text for name in row['shape_dependencies'])
        assert row['theorem'] in text
    assert all(detail[key] is False for key in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.mark.parametrize('fault', ['missing-shape', 'wrong-seed', 'reversed-effective-dims'])
def test_predecessor_authority_not_bypassed(worlds, config, prefix, rank_code, monkeypatch, fault):
    import copy
    api().render(worlds, config, prefix, rank_code)
    changed = copy.deepcopy(prefix)
    if fault == 'missing-shape':
        from Verdict.runtime_backward_prefix_shapes import render
        from scripts.tests.test_runtime_backward_wred_reads import selected
        _, detail = render(worlds, selected(worlds), prefix, seed_config=config)
        row = next(r for r in detail['reads'] if r['role'] == 'seed_primal')
        changed['kernel_checks'].remove(row['dependencies'][1])
    elif fault == 'wrong-seed':
        from Verdict import runtime_backward_seed_reads as seeds
        def reject(*args, **kwargs):
            raise ValueError('authenticated seed rejected')
        monkeypatch.setattr(seeds, 'render', reject)
    else:
        from Verdict import runtime_backward_cotangent_reads as cotangents
        old = cotangents.render
        def mutate(*args, **kwargs):
            text, detail = old(*args, **kwargs)
            detail['reads'][0]['params'] = [2, 1]
            return text, detail
        monkeypatch.setattr(cotangents, 'render', mutate)
    with pytest.raises(ValueError):
        api().render(worlds, config, changed, rank_code)
