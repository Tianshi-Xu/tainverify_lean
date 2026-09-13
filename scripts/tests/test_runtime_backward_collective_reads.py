"""Original captured backward collectives, not seed/Add-specific compositions."""
import copy
import importlib
import importlib.util
import os
from pathlib import Path

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


@pytest.fixture(scope='module')
def admitted(worlds):
    from Verdict import graph_to_lean as compiler
    root = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    snapshot = compiler._load_chunk_source(str(root / 'capture.pkl'),
        str(root / 'code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    view, cells, _, order, label = worlds[1]
    compiler.attach_collective_scopes(view, snapshot)
    return view, cells, snapshot, order, label


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_collective_reads'), \
        'missing generic original backward collective source reader'
    return importlib.import_module('Verdict.runtime_backward_collective_reads').render_read


def test_real_gelu_to_allgather(admitted):
    from Verdict import runtime_backward_gelu_reads as gelu
    view, cells, snapshot, order, label = admitted
    text, row = api()(view, cells, snapshot, 116, order, label, gelu.render_read, 0)
    assert row['opname'] == 'AllGatherPrim'
    assert row['params'] == row['raw_params'] == [1]
    assert row['input_refs'] == [list(r) for r in cells[116].inputs]
    assert [p['source_index'] for p in row['predecessors']] == [115, 351]
    assert row['theorems'] == ['backwardCollective_pm_116_read']
    assert 'SourceAllGatherRead.allGather_value_of_split' in text
    assert 'allGatherPrimDimN 1 2 0' in text
    assert 'bw_gelu' not in text and 'bw_add' not in text
    assert text.count('#print axioms') == 1
    assert all(row[k] is False for k in
        ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.mark.parametrize('index', [116, 352, 588, 824, 118, 354, 590, 826])
def test_all_original_gelu_ag_and_fc1_aa_peers(admitted, index):
    from Verdict import runtime_backward_gelu_reads as gelu, runtime_backward_linear_reads as linear
    view, cells, snapshot, order, label = admitted
    ag = cells[index].opname.name == 'AllGatherPrim'
    reader = gelu.render_read if ag else linear.render_read
    text, row = api()(view, cells, snapshot, index, order, label, reader, 0)
    assert row['source_index'] == index
    assert row['execution_index'] == order['source_to_execution'][index]
    assert row['opname'] == ('AllGatherPrim' if ag else 'AllToAllPrim')
    assert row['params'] == ([1] if ag else [2, 1])
    assert row['raw_params'] == ([1] if ag else [1, 2])
    assert row['output_shape'] == ([1, 16, 256] if ag else [1, 8, 64])
    assert row['input_refs'] == [list(r) for r in cells[index].inputs]
    assert row['output_ref'] == list(cells[index].outputs[0])
    for ref, tid, predecessor in zip(row['input_refs'], row['input_tids'], row['predecessors'], strict=True):
        assert predecessor['output_refs'][0] == ref
        assert predecessor['output_tids'][0] == tid
        assert predecessor == reader(view, cells, snapshot, predecessor['source_index'], order, label)[1]
    assert row['theorems'] == [f'backwardCollective_pm_{index}_read']
    assert ('SourceAllGatherRead.allGather_value_of_split' if ag else
            'SourcePrimitiveRead.allToAll_value_of_split') in text
    assert 'bw_gelu' not in text and 'bw_linear' not in text and 'bw_add' not in text


@pytest.mark.parametrize('fault', ['peer-order', 'effective-raw', 'peer-readpoint', 'grad-fullref',
    'bool-version', 'generated-body', 'call', 'export', 'inverse', 'source-order', 'shape',
    'raw-kwargs', 'lowered-op', 'producer-port', 'producer-row', 'missing-authority', 'suffix'])
def test_fail_closed_at_new_collective_boundary(admitted, monkeypatch, fault):
    from dataclasses import replace
    from Verdict import runtime_backward_linear_reads as linear
    from verdict.operators.names import OpName
    view, original_cells, snapshot, order, label = admitted
    # Real cloned source authority must work before any adversarial mutation.
    clone = copy.copy(view)
    clone.collective_scopes = dict(view.collective_scopes)
    cells = list(original_cells)
    source = copy.deepcopy(snapshot)
    execution = copy.deepcopy(order)
    reader, port, index = linear.render_read, 0, 118
    good_text, good = api()(clone, cells, source, index, execution, label, reader, port)
    node = cells[index].node
    scope = clone.collective_scopes[node]
    wid = scope.source_writer
    writer = next(w for w in source['writers'] if w['export_id'] == wid)
    peer = next(w for w in source['writers'] if w['export_id'] == writer['adapter']['peer_writers'][1])
    ctx = peer['adapter']['backward_context']
    if fault == 'peer-order':
        clone.collective_scopes[node] = replace(scope, input_tids=tuple(reversed(scope.input_tids)))
    elif fault == 'effective-raw':
        clone.collective_scopes[node] = replace(scope, params=(1, 2))
    elif fault == 'peer-readpoint': ctx['gradient_read_points'][0]['writer'] += '-forged'
    elif fault == 'grad-fullref': ctx['output_gradient'][0]['source_tid'] += 1
    elif fault == 'bool-version': ctx['output_gradient'][0]['version'] = True
    elif fault == 'generated-body': source.raw_rank_sources['1'] += '\n# forged source body\n'
    elif fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'export': writer['export_id'] += '-forged'
    elif fault == 'inverse': execution['source_to_execution'][index] += 1
    elif fault == 'source-order': cells[index], cells[index+1] = cells[index+1], cells[index]
    elif fault == 'shape':
        original_shape = clone.tensor_shape
        monkeypatch.setattr(clone, 'tensor_shape', lambda t: (1, 8, 128)
                            if t.tid == good['output_tid'] else original_shape(t))
    elif fault == 'raw-kwargs':
        cell = object.__new__(type(cells[index]))
        for slot in cell.__slots__: setattr(cell, slot, getattr(cells[index], slot))
        cells[index] = cell
        cell.kwargs = dict(cell.kwargs, idim=2, odim=1)
    elif fault == 'lowered-op':
        original_op = clone.node_opname
        monkeypatch.setattr(clone, 'node_opname', lambda n: OpName.AllGatherPrim if n == node else original_op(n))
    elif fault == 'producer-port': port = 1
    elif fault == 'producer-row':
        real = reader
        from functools import wraps
        @wraps(real)
        def changed(*args):
            text, row = real(*args)
            row['input_tids'][0] += 1
            return text, row
        # Reach the actual row/port guard, not merely the callable identity gate.
        monkeypatch.setattr(linear, 'render_read', changed)
        reader = changed
    elif fault == 'missing-authority': source = dict(source)
    else:
        original_outputs = clone.node_outputs
        suffix = clone.nodes()[execution['execution_to_source'][-1]]
        target = clone.node_inputs(node)[0]
        monkeypatch.setattr(clone, 'node_outputs', lambda n: original_outputs(n) + [target]
                            if n == suffix else original_outputs(n))
    with pytest.raises(ValueError):
        api()(clone, cells, source, index, execution, label, reader, port)
    assert good_text and good['opname'] == 'AllToAllPrim'
