"""Replicated FFN weight gradients use the original DP×TP SUM group."""
from pathlib import Path
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_wred_reads import admitted, api
from scripts.tests.test_runtime_backward_cotangent_reads import rank_code
from scripts.tests.test_runtime_backward_seed_reads import config


def selected(worlds):
    view, cells, _, order, _ = worlds[1]
    result = []
    for rank in range(view.W.runtime_ndevs):
        add = next(cells[i] for i in order['execution_to_source']
                   if cells[i].rank == rank and cells[i].opname.name == 'BW_add')
        matches = [i for i, c in enumerate(cells) if c.rank == rank
                   and c.opname.name == 'BW_linear' and c.inputs[0] == add.outputs[1]]
        assert len(matches) == 1
        result.append(matches[0])
    return result


def test_original_replicated_fc2_reducer_accepts_unique_dp_tp_coordinates(worlds, config, rank_code):
    text, detail = api().render(worlds, selected(worlds), str(Path(config['pm_capture'])/'capture.pkl'), rank_code)
    assert len(detail['reads']) == 4
    assert all(row['ranks'] == [0, 1, 2, 3] for row in detail['reads'])
    for row in detail['reads']:
        assert row['parameter_placement']['name'] == 'layers.1.ffn.fc2.weight'
        assert row['parameter_placement']['full_shape'] == [64, 256]
        assert row['reduce_op'] == 'sum' and row['nreplicas'] == 1
        coords = [(c['parameter_placement']['scale_unit'], c['parameter_placement']['plan_rank'])
                  for c in row['contributions']]
        assert coords == [(0, 0), (0, 1), (1, 0), (1, 1)]
    assert text.count('#print axioms') == 8
    assert all(detail[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.mark.parametrize('fault', ['duplicate-coordinate', 'bool-plan-rank', 'negative-plan-rank', 'distinct-wrong-plan-rank', 'different-slice'])
def test_replicated_reducer_still_requires_source_coordinate_and_parameter_identity(worlds, admitted, monkeypatch, fault):
    import copy
    view, cells, _, order, _ = worlds[1]
    indices = selected(worlds)
    _, good = api()._read(view, cells, admitted, order, indices[0], indices)
    snapshot = copy.deepcopy(admitted)
    nodes = [next(n for n, scope in view.wred_scopes.items()
                  if n.rank == c['parameter_ref'][1] and list(scope.parameter) == c['parameter_ref'])
             for c in good['contributions']]
    peer = snapshot.raw_writers[nodes[1]]['placement']
    if fault == 'duplicate-coordinate': peer['plan_rank'] = snapshot.raw_writers[nodes[0]]['placement']['plan_rank']
    elif fault == 'bool-plan-rank': peer['plan_rank'] = True
    elif fault == 'negative-plan-rank': peer['plan_rank'] = -1
    elif fault == 'distinct-wrong-plan-rank': peer['plan_rank'] = 9
    else: peer['indmap'][0] = [32, 64]
    with pytest.raises(ValueError, match='bw-wred'):
        api()._read(view, cells, snapshot, order, indices[0], indices)
    assert api()._read(view, cells, admitted, order, indices[0], indices)[1] == good
