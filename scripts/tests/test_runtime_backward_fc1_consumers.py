"""Original reverse FC1 path retains both communications and all LN outputs."""
import importlib
import importlib.util
import os
from pathlib import Path
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_fc1_consumers'), 'missing original FC1 continuation'
    return importlib.import_module('Verdict.runtime_backward_fc1_consumers')


@pytest.fixture(scope='module')
def paths():
    p = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    return str(p/'capture.pkl'), str(p/'code/_parallel_modules/genmodel/model/gpt/GPT/_')


def test_original_fc1_path_discovery(worlds):
    rows = api().discover(worlds)
    assert len(rows) == 5
    for row in rows:
        assert row['linear']['input_refs'][0] == row['grad_ref']
        assert row['layernorm']['input_refs'][0] == row['dx_ref']
        assert len(row['layernorm']['output_tids']) == 3
        if row['world'] == 'pm':
            assert row['before_op'] == 'AllGatherPrim'
            assert row['after_op'] == 'AllToAllPrim'
        else:
            assert row['before_index'] is None and row['after_index'] is None


def test_fc1_follows_original_fullref_not_adjacent_index(worlds, monkeypatch):
    from Verdict import runtime_backward_linear_reads as linear
    import copy
    api().discover(worlds)
    original = linear.render_read
    def corrupted(*args):
        text, row = original(*args); row = copy.deepcopy(row)
        row['input_tids'][0] += 10000
        return text, row
    monkeypatch.setattr(linear, 'render_read', corrupted)
    with pytest.raises(ValueError): api().discover(worlds)


def test_fc1_exports_same_generated_expressions_for_next_stage(worlds, paths):
    text, detail = api().render(worlds, *paths)
    for row in detail['reads']:
        for key in ('linear', 'layernorm'):
            values = row[key + '_expressions']
            assert len(values) == len(row[key]['output_tids'])
            for tid, value in zip(row[key]['output_tids'], values, strict=True):
                assert f't {tid} = {value} := by' in text
    # The consumer can reuse expressions without reverse-parsing proof text.
    assert len(detail['reads'][0]['layernorm_expressions']) == 3


def test_actual_fc1_chain_and_all_parameter_branches(worlds, paths):
    text, detail = api().render(worlds, *paths)
    assert len(detail['reads']) == 5
    assert text.count('#print axioms') == 33
    assert len(detail['collective_reads']) == 8
    assert 'allGatherPrimDimN 1' in text
    assert 'AllToAllSourceFaithful.tensor 2 0 2 1' in text
    assert all(len(r['layernorm']['theorems']) == 3 for r in detail['reads'])
    assert all(detail[k] is False for k in ('kernel_value_proved','proof_admissible','public_complete','torch_refinement'))


def test_existing_fc1_and_affine_parameter_reducers(worlds, paths):
    from Verdict import runtime_backward_wred_reads as wred
    from Verdict import runtime_backward_layernorm_wred as affine
    rows = [r for r in api().discover(worlds) if r['world'] == 'pm']
    _, dw = wred.render(worlds, [r['linear']['source_index'] for r in rows], *paths)
    _, ln = affine.render(worlds, [r['layernorm']['source_index'] for r in rows], *paths)
    assert len(dw['reads']) == 4 and len(ln['reads']) == 8
    for r in dw['reads']:
        assert r['ranks'] in ([0, 2], [1, 3])
        assert r['parameter_placement']['full_shape'] == [256, 64]
        assert len(r['contributions']) == 2
    for r in ln['reads']:
        assert r['ranks'] == [0, 1, 2, 3]
        assert len(r['contributions']) == 4
        assert r['role'] in ('dgamma', 'dbeta')


@pytest.mark.parametrize('fault', ['params', 'peer-order', 'input-tid', 'output-ref'])
def test_composition_binds_collective_dto_to_original_ports(worlds, paths, monkeypatch, fault):
    import copy
    from Verdict import runtime_backward_collective_reads as collective
    original = collective.render_read
    def corrupted(*args):
        text, row = original(*args); row = copy.deepcopy(row)
        if fault == 'params': row['params'][0] += 1
        elif fault == 'peer-order': row['predecessors'].reverse()
        elif fault == 'input-tid': row['input_tids'][0] += 1
        else: row['output_ref'][-1] += 1
        return text, row
    monkeypatch.setattr(collective, 'render_read', corrupted)
    with pytest.raises(ValueError, match='bw-fc1 original collective binding mismatch'):
        api().render(worlds, *paths)
