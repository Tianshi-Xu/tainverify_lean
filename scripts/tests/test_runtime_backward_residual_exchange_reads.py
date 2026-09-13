"""Retained residual gradient branch uses authenticated reverse-AA dimensions."""
import importlib
import importlib.util
from pathlib import Path
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from scripts.tests.test_runtime_backward_cotangent_reads import rank_code


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_residual_exchange_reads'), 'missing residual reverse exchange'
    return importlib.import_module('Verdict.runtime_backward_residual_exchange_reads')


def test_retained_exchange_exports_its_generated_expression(worlds, config, rank_code):
    text, detail = api().render(worlds, str(Path(config['pm_capture'])/'capture.pkl'), rank_code)
    for row in detail['reads']:
        assert f't {row["output_tid"]} = {row["expression"]} := by' in text
        assert row['expression'].startswith('AllToAllSourceFaithful.tensor ')


def test_original_add_left_branch_faithful_exchange(worlds, config, rank_code):
    text, detail = api().render(worlds, str(Path(config['pm_capture'])/'capture.pkl'), rank_code)
    assert [r['source_index'] for r in detail['reads']] == [113, 349, 585, 821]
    assert [r['output_tid'] for r in detail['reads']] == [302, 605, 908, 1211]
    assert all(r['params'] == [1, 2] for r in detail['reads'])
    assert all(r['raw_params'] == [2, 1] for r in detail['reads'])
    assert text.count('#print axioms') == 8
    assert 'AllToAllSourceFaithful.tensor' in text
    assert 'backwardAddRead_pm_' in text
    assert not detail['kernel_value_proved']


@pytest.fixture(scope='module')
def admitted(worlds, config, rank_code):
    from Verdict import graph_to_lean as compiler, runtime_backward_add_consumers as add
    _, prior = add.render(worlds)
    snapshot = compiler._load_chunk_source(str(Path(config['pm_capture'])/'capture.pkl'), rank_code)
    compiler.attach_collective_scopes(worlds[1][0], snapshot)
    return prior, snapshot


@pytest.mark.parametrize('fault', ['context', 'dimensions', 'peers', 'read-point', 'missing-contribution', 'duplicate-contribution'])
def test_reverse_residual_scope_rejects_corruption(worlds, admitted, monkeypatch, fault):
    import copy
    from dataclasses import replace
    prior, snapshot = admitted; view, cells, _, order, _ = worlds[1]
    row = next(r['add_read'] for r in prior['reads'] if r['world'] == 'pm')
    _, good = api()._read(view, cells, snapshot, order, prior, row)
    source, previous = copy.deepcopy(snapshot), copy.deepcopy(prior)
    node = view.nodes()[good['source_index']]; scope = view.collective_scopes[node]
    writer = next(w for w in source['writers'] if w['export_id'] == scope.source_writer)
    with monkeypatch.context() as m:
        if fault == 'context': writer['adapter']['backward_context']['status'] = 'missing'
        elif fault == 'dimensions': m.setitem(view.collective_scopes, node, replace(scope, params=(2, 1)))
        elif fault == 'peers': m.setitem(view.collective_scopes, node, replace(scope, input_tids=tuple(reversed(scope.input_tids))))
        elif fault == 'read-point': writer['adapter']['backward_context']['gradient_read_points'][0]['writer'] += '-wrong'
        else:
            other = next(r for r in previous['reads'] if r['world'] == 'pm' and r['add_read']['output_tids'][0] == good['input_tids'][1])
            if fault == 'missing-contribution': previous['reads'].remove(other)
            else: previous['reads'].append(copy.deepcopy(other))
        with pytest.raises(ValueError): api()._read(view, cells, source, order, previous, row)
    assert api()._read(view, cells, snapshot, order, prior, row)[1] == good
