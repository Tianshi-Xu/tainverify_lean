"""Original dV-to-V-linear same-Store DAG, not cross-world equality."""
import importlib
import importlib.util
from pathlib import Path
import os

import pytest

from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    name = 'Verdict.runtime_backward_v_projection_consumers'
    assert importlib.util.find_spec(name), 'missing original V projection composition'
    return importlib.import_module(name)


def paths():
    base = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    return str(base / 'capture.pkl'), str(base / 'code/_parallel_modules/genmodel/model/gpt/GPT/_')


def test_original_v_projection_api_exists():
    assert callable(api().render)


def generator():
    path = Path(__file__).resolve().parents[2] / 'iroha-tasks/trainverify-backward/render_actual_v_projection.py'
    assert path.is_file(), 'missing V projection runtime receipt generator'
    spec = importlib.util.spec_from_file_location('actual_v_projection', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_generator_exists():
    assert callable(generator().generate)


@pytest.fixture(scope='module')
def rendered_output(tmp_path_factory):
    return tmp_path_factory.mktemp('v-projection-generated')


@pytest.fixture(scope='module')
def rendered(worlds, rendered_output):
    return generator().generate(worlds, Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']),
                                output=rendered_output)


def test_real_v_projection_path_both_linear_ports(worlds, rendered):
    text, detail = rendered
    assert [(r['world'], r['source_index']) for r in detail['linear_reads']] == [
        ('sm', 88), ('pm', 152), ('pm', 388), ('pm', 624), ('pm', 860)]
    assert len(detail['reads']) == 28
    assert text.count('#print axioms') == 33
    for row in detail['linear_reads']:
        w = next(w for w in worlds if w[-1] == row['world'])
        cell = w[1][row['source_index']]
        assert row['input_refs'] == [list(r) for r in cell.inputs]
        assert row['output_refs'] == [list(r) for r in cell.outputs]
        assert row['output_roles'] == ['input_gradient', 'parameter_gradient']
        assert cell._input_irs[2].is_param() is True
        assert len(row['composition_theorems']) == 2
        assert row['input_shapes'] == ([[2, 16, 64], [2, 16, 64], [64, 64]]
            if row['world'] == 'sm' else [[1, 16, 64], [1, 16, 32], [64, 32]])
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False


def test_fullref_discovery_is_not_source_adjacency(worlds):
    paths = api().discover(worlds)
    assert [p['source_indices'] for p in paths] == [
        [77, 82, 83, 88],
        [131, 132, 140, 141, 142, 143, 152],
        [367, 368, 376, 377, 378, 379, 388],
        [603, 604, 612, 613, 614, 615, 624],
        [839, 840, 848, 849, 850, 851, 860]]


def test_emitted_sources_and_shared_dag_are_path_only(worlds, rendered):
    text, detail = rendered
    rows = detail['reads']
    assert text.count('def backwardVValue_') == len(rows)
    assert 'backwardMatmulRead_sm_77_dy s t h' in text
    for i in (132, 368, 604, 840):
        assert f'backwardMatmulDVReduceScatter_pm_{i} s t h' in text
    assert 'SourceBWMatmulRead.' not in text
    assert 'SourceReduceScatterRead.' not in text
    for kind, law, count in [('transpose', 'SourceBWTransposeRead.', 5),
                             ('view', 'SourceBWViewRead.', 5),
                             ('collective', 'value_of_split', 8),
                             ('linear', 'SourceBWLinearRead.', 10)]:
        source = detail[kind + '_source']
        assert source.count(law) == count
        assert source.count('#print axioms') == count
        assert 'SourceReduceScatterRead.' not in source
        assert 'SourceBWMatmulRead.' not in source
    by_key = {(r['world'], r['source_index']): r for r in rows}
    for row in rows:
        if row['stage'] != 'BW_linear':
            assert row['output_roles'] == ['value_cotangent']
        for parent in row['parents']:
            upstream = by_key[parent['world'], parent['source_index']]
            assert rows.index(upstream) < rows.index(row)
            assert upstream['value_name'] + ' t' in row['value_body']
            assert upstream['value_body'] not in row['value_body']
            assert parent['theorem'] + ' s t h' in text
        if row['stage'] == 'BW_linear':
            _, x, weight = row['input_tids']
            assert row['value_body'].endswith(f'(t {x}) (t {weight})')
        if row['stage'] in ('AllGatherPrim', 'AllToAllPrim'):
            assert [p['output_tid'] for p in row['parents']] == row['input_tids']
            assert [p['output_ref'] for p in row['parents']] == row['input_refs']
            assert [p['output_ref'][1] for p in row['parents']] == row['ranks']
            assert row['local_index'] == row['ranks'].index(row['output_ref'][1])
    # Attaching fresh scopes must not repair/mutate the original caller view.
    for view, _, _, _, label in worlds:
        if label == 'pm':
            assert not getattr(view, 'collective_scopes', {})


def test_generator_writes_exact_modules_and_receipt_checked_dag(rendered, rendered_output):
    import json
    text, detail = rendered
    gen = generator()
    assert rendered_output != gen.OUT
    mapping = {'ActualBWVTransposeRead': 'transpose_source', 'ActualBWVViewRead': 'view_source',
               'ActualBWVCollectiveRead': 'collective_source', 'ActualBWVLinearRead': 'linear_source'}
    for module, field in mapping.items():
        emitted = (rendered_output / (module + '.lean')).read_text()
        assert detail[field] in emitted
        assert 'import TrainVerifyRuntimeWorldData\n' in emitted
    emitted = (rendered_output / 'ActualBWVProjectionDAG.lean').read_text()
    assert text in emitted
    for module in ['TrainVerifyRuntimeWorldData', 'ActualBWMatmulRead', 'ActualBWMatmulDVReduceScatter', *mapping]:
        assert f'import {module}\n' in emitted
    receipt = json.loads((rendered_output / 'ActualBWVProjectionDAG.json').read_text())
    assert receipt['paths'] == detail['paths']
    assert len(receipt['linear_reads']) == 5


@pytest.mark.parametrize('fault', ['version', 'owner', 'wrong-port', 'bool-version'])
def test_discovery_rejects_wrong_fullref_and_output_port(worlds, fault):
    from copy import copy
    view, original, snapshot, order, label = worlds[0]
    cells = list(original)
    cells[82] = copy(cells[82])
    cells[82].inputs = list(cells[82].inputs)
    ref = cells[82].inputs[0]
    if fault == 'version':
        cells[82].inputs[0] = ref._replace(v=ref.v + 1)
    elif fault == 'owner':
        cells[82].inputs[0] = ref._replace(rank=ref.rank + 1)
    elif fault == 'bool-version':
        cells[82].inputs[0] = ref._replace(v=bool(ref.v))
    else:
        cells[82].inputs[0] = cells[77].outputs[0]
    with pytest.raises(ValueError, match='bw-v-projection'):
        api().render([(view, cells, snapshot, order, label), worlds[1]], *paths())
    with pytest.raises(ValueError, match='bw-v-projection'):
        api()._consumer(view, original, order, 77, 0, 'BW_transpose')


@pytest.mark.parametrize('fault', ['source-signature', 'saved-weight-fullref'])
def test_original_source_and_saved_parameter_bindings_reject_tampering(worlds, rendered, monkeypatch, fault):
    from copy import copy
    from Verdict import runtime_backward_transpose_reads as transpose
    from Verdict import runtime_backward_linear_reads as linear
    view, original, snapshot, order, label = worlds[0]
    if fault == 'source-signature':
        row = next(r for r in rendered[1]['reads'] if r['world'] == 'sm' and r['source_index'] == 82)
        forward = original[row['source_contract']['fw_source_index']]
        monkeypatch.setattr(forward.ir, 'signature', 'torch.mul')
        with pytest.raises(ValueError, match='bw-transpose'):
            transpose.render_read(view, original, snapshot, 82, order, label)
    else:
        cells = list(original)
        cells[88] = copy(cells[88])
        cells[88].inputs = list(cells[88].inputs)
        cells[88].inputs[2] = cells[88].inputs[2]._replace(v=cells[88].inputs[2].v + 1)
        with pytest.raises(ValueError, match='bw-linear'):
            linear.render_read(view, cells, snapshot, 88, order, label)


@pytest.mark.parametrize('is_param', [False, 1])
def test_parameter_role_needs_literal_original_true(worlds, monkeypatch, is_param):
    cell = worlds[0][1][88]
    assert api()._parameter_role(cell) == 'parameter_gradient'
    monkeypatch.setattr(type(cell._input_irs[2]), 'is_param', lambda self: is_param)
    assert api()._parameter_role(cell) == 'weight_gradient'


@pytest.mark.parametrize('fault', ['peer-read', 'fullref', 'tid', 'peer-order', 'missing', 'future'])
def test_collective_dag_rejects_tampered_parent_certificates(rendered, fault):
    from copy import deepcopy
    rows = rendered[1]['reads']
    raw = deepcopy(next(r for r in rows if r['stage'] == 'AllToAllPrim'))
    values = {(r['world'], r['source_index']): deepcopy(r) for r in rows}
    assert api()._collective_parents(raw, values)
    key = ('pm', raw['predecessors'][0]['source_index'])
    parent = values[key]
    if fault == 'peer-read': parent['source_read']['params'].reverse()
    elif fault == 'fullref':
        parent['output_refs'] = [list(parent['output_refs'][0])]
        parent['output_refs'][0][4] += 1
    elif fault == 'tid': parent['output_tids'] = [parent['output_tids'][0] + 1]
    elif fault == 'peer-order': raw['predecessors'].reverse()
    elif fault == 'missing': del values[key]
    else: parent['execution_index'] = raw['execution_index'] + 1
    with pytest.raises(ValueError, match='bw-v-projection .* (peer|DAG)'):
        api()._collective_parents(raw, values)


def test_receipt_failure_preserves_existing_generated_artifact(worlds, rendered, rendered_output, monkeypatch):
    import json
    gen = generator()
    base = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
    receipt = json.loads((base / gen.RECEIPT).read_text())
    receipt['execution_order']['sm']['source_to_execution'].reverse()
    target = rendered_output / 'ActualBWVProjectionDAG.lean'
    before = target.read_bytes()
    monkeypatch.setattr(gen.json, 'loads', lambda _: receipt)
    def forbidden_render(*args):
        pytest.fail('render reached before runtime receipt validation')
    monkeypatch.setattr(gen, 'render', forbidden_render)
    with pytest.raises(ValueError, match='runtime receipt'):
        gen.generate(worlds, base, output=rendered_output)
    assert target.read_bytes() == before


@pytest.mark.parametrize('fault', ['fullref', 'tid', 'shape', 'order', 'inverse', 'duplicate', 'bool-version'])
def test_runtime_receipt_join_rejects_mismatched_worlds(worlds, fault):
    import json
    gen = generator()
    receipt = json.loads((Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / gen.RECEIPT).read_text())
    gen.validate_receipt(worlds, receipt)
    row = receipt['fullrefs']['pm'][0]
    if fault == 'fullref': row['ref'][3] += 1
    elif fault == 'tid': row['tid'] += 1
    elif fault == 'shape': row['shape'][0] += 1
    elif fault == 'order': receipt['execution_order']['pm']['execution_to_source'].reverse()
    elif fault == 'inverse': receipt['execution_order']['pm']['source_to_execution'].reverse()
    elif fault == 'duplicate': receipt['fullrefs']['pm'].append(row)
    else: row['ref'][4] = bool(row['ref'][4])
    with pytest.raises(ValueError, match='runtime receipt'):
        gen.validate_receipt(worlds, receipt)
