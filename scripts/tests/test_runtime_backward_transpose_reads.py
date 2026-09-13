"""Original capture authority plus position-sensitive real Torch/autograd oracle."""
import importlib
import importlib.util
from math import prod
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_transpose_reads'), 'missing original BW_transpose reader'
    return importlib.import_module('Verdict.runtime_backward_transpose_reads')


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            i = next(i for i in order['execution_to_source']
                     if cells[i].rank == rank and cells[i].opname.name == 'BW_transpose')
            yield view, cells, snapshot, i, order, label


def test_actual_transpose_source_read_and_real_autograd_values(worlds):
    import torch
    rows = []
    for args in selected(worlds):
        text, row = api().render_read(*args)
        rows.append(row)
        c = row['source_contract']; fw = args[1][c['fw_source_index']]
        assert c['input_roles'] == ['cotangent', 'saved_input']
        assert c['saved_inputs'] == [list(r) for r in fw.inputs]
        assert row['input_refs'] == [list(r) for r in args[1][args[3]].inputs]
        assert row['output_refs'] == [list(r) for r in args[1][args[3]].outputs]
        assert row['execution_index'] == args[4]['source_to_execution'][args[3]]
        assert row['operand_nonwrite_source_indices'] == args[4]['execution_to_source'][row['execution_index']:]
        g, saved = row['input_tids']; dx, = row['output_tids']
        d0, d1 = row['params']
        assert f't {dx} = transposeAxes {d0} {d1} (t {g})' in text
        assert 'SourceBWTransposeRead.bw_transpose_value_of_split' in text
        assert f'(h : {args[5]}DenoteWithInputs s = some t)' in text
        assert all(row[k] is False and c[k] is False for k in
                   ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
        fn = torch
        for part in fw.ir.signature.split('.')[1:]: fn = getattr(fn, part)
        kwargs = {k: v for k, v in fw.ir.kwargs.items() if k != '__consts'}
        # Original four-dimensional shape AND equal-length swapped axes: shape cannot reject identity.
        square = list(fw._input_irs[0].shape); square[d0] = square[d1] = 3
        for shape in (tuple(fw._input_irs[0].shape), tuple(square), (3, 3)):
            kw = kwargs if len(shape) > 2 else {'dim0': -2, 'dim1': -1}
            n = prod(shape)
            x = (torch.arange(n, dtype=torch.float64) + .25).reshape(shape).requires_grad_()
            y = fn(x, **kw)
            grad = (torch.arange(n, dtype=torch.float64) + 7.5).reshape(y.shape)
            out, = torch.autograd.grad(y, x, grad)
            expected = grad.transpose(**kw)
            torch.testing.assert_close(out, expected, rtol=0, atol=0)
            # Independent coordinate oracle, not a second transpose call.
            import itertools
            for idx in itertools.product(*(range(n) for n in shape)):
                src = list(idx); a, b = kw['dim0'], kw['dim1']; src[a], src[b] = src[b], src[a]
                assert out[idx] == grad[tuple(src)]
            assert torch.count_nonzero(out) == n and not torch.equal(out, x.detach())
            assert not torch.equal(out.flatten(), grad.flatten())
            if shape in (tuple(square), (3, 3)):
                assert out.shape == grad.shape and not torch.equal(out, grad)
    assert [(r['world'], r['source_index']) for r in rows] == [
        ('sm', 76), ('pm', 129), ('pm', 365), ('pm', 601), ('pm', 837)]


@pytest.mark.parametrize('fault', [
    'fw-signature', 'bw-signature', 'dims-range', 'dims-type', 'dims-bw-only', 'dims-wrong', 'dims-negative-range', 'unknown-kwarg',
    'saved-version', 'saved-output', 'ordered-inputs', 'coordinated-inputs',
    'gradient-metadata', 'saved-metadata', 'cotangent-initial', 'bool-version',
    'fw-lowered-op', 'bw-lowered-op', 'fw-params', 'bw-params',
    'writer-call', 'fw-writer-missing', 'source-suffix', 'output-suffix',
    'execution-order', 'execution-truncated', 'inverse-order',
])
def test_original_transpose_rejects_mutations(worlds, monkeypatch, fault):
    import copy
    from Verdict import graph_to_lean
    from verdict.operators.names import OpName
    for args in selected(worlds):
        view, cells, snapshot, i, order, label = args
        text, good = api().render_read(*args)
        cell = cells[i]; fw = cells[good['source_contract']['fw_source_index']]
        with monkeypatch.context() as m:
            if fault == 'fw-signature': m.setattr(fw.ir, 'signature', 'torch.sigmoid')
            elif fault == 'bw-signature': m.setattr(cell.ir, 'signature', 'torch.add')
            elif fault in ('dims-range', 'dims-type', 'dims-bw-only', 'dims-wrong', 'dims-negative-range', 'unknown-kwarg'):
                for obj in ((cell,) if fault == 'dims-bw-only' else (cell, fw)):
                    key = 'unknown' if fault == 'unknown-kwarg' else 'dim0'
                    value = {'dims-type': True, 'dims-wrong': 0, 'dims-negative-range': -5}.get(fault, 7)
                    m.setattr(obj, 'kwargs', dict(obj.kwargs, **{key: value}))
                    m.setitem(obj.ir.kwargs, key, value)
            elif fault in ('saved-version', 'bool-version'):
                m.setattr(cell, 'inputs', [cell.inputs[0], cell.inputs[1]._replace(
                    v=True if fault == 'bool-version' else cell.inputs[1].v + 1)])
            elif fault == 'saved-output':
                m.setattr(cell, 'inputs', [cell.inputs[0], fw.outputs[0]])
                m.setattr(cell, '_input_irs', [cell._input_irs[0], fw._output_irs[0]])
            elif fault in ('ordered-inputs', 'coordinated-inputs'):
                m.setattr(cell, 'inputs', list(reversed(cell.inputs)))
                if fault == 'coordinated-inputs': m.setattr(cell, '_input_irs', list(reversed(cell._input_irs)))
            elif fault in ('gradient-metadata', 'saved-metadata'):
                port = 0 if fault == 'gradient-metadata' else 1
                irs = list(cell._input_irs); irs[port] = copy.deepcopy(irs[port])
                irs[port]._valmap = type(irs[port]._valmap)((1, 3))
                m.setattr(cell, '_input_irs', irs)
            elif fault == 'cotangent-initial':
                m.setattr(cell, 'inputs', [cell.inputs[0]._replace(v=0), cell.inputs[1]])
            elif fault in ('fw-lowered-op', 'bw-lowered-op'):
                obj = fw if fault.startswith('fw') else cell
                m.setitem(view.source._node2opname, obj.node, OpName.FW_add)
            elif fault in ('fw-params', 'bw-params'):
                target = fw.node if fault.startswith('fw') else cell.node
                original = graph_to_lean._get_node_params
                m.setattr(graph_to_lean, '_get_node_params',
                          lambda v, n, **kw: [False] if n == target else original(v, n, **kw))
            elif fault == 'writer-call':
                row = next(w for w in snapshot['writers'] if w['export_id'] == good['bw_writer'])
                m.setitem(row['ref'], 'call_instance', row['ref']['call_instance'] + 1)
            elif fault == 'fw-writer-missing':
                m.setitem(snapshot, 'writers', [w for w in snapshot['writers'] if w['export_id'] != good['fw_writer']])
            elif fault in ('source-suffix', 'output-suffix'):
                later = cells[-1]
                m.setattr(later, 'outputs', [cell.inputs[1] if fault == 'source-suffix' else cell.outputs[0]])
            elif fault == 'execution-order':
                m.setitem(order, 'execution_to_source', list(reversed(order['execution_to_source'])))
            elif fault == 'execution-truncated':
                m.setitem(order, 'execution_to_source', order['execution_to_source'][:good['execution_index']+1])
            else:
                inv = list(order['source_to_execution']); inv[i] = inv[i] + 1
                m.setitem(order, 'source_to_execution', inv)
            with pytest.raises(ValueError): api().render_read(*args)
        assert api().render_read(*args) == (text, good)



def test_signed_axes_normalization_not_two_dimensional_assumption(worlds, monkeypatch):
    from trainverify.backward_transpose_authority import bind
    from Verdict.graph_to_lean import _get_node_params
    for view, cells, snapshot, i, order, label in selected(worlds):
        original = bind(cells, i); fw = cells[original['fw_source_index']]
        for dims in ((-3, -2), (2, 1)):
            with monkeypatch.context() as m:
                for obj in (fw, cells[i]):
                    for key, val in zip(('dim0', 'dim1'), dims):
                        m.setitem(obj.kwargs, key, val)
                        m.setitem(obj.ir.kwargs, key, val)
                c = bind(cells, i)
                assert c['source_dims'] == list(dims)
                assert c['params'] == [d % 4 for d in dims]
                assert _get_node_params(view, cells[i].node, num_parts=0) == c['params']


def test_lean_helper_and_joint_value_sensitive_witness_present():
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    helper = root / 'trainverify/denote/SourceBWTransposeRead.lean'
    witness = root / 'iroha-tasks/trainverify-backward/TransposeReadWitness.lean'
    assert helper.exists(), 'missing original transpose source helper'
    assert witness.exists(), 'missing joint successful transpose witness'
    h, w = helper.read_text(), witness.read_text()
    assert 'SourceValueRead.node_value_of_split' in h and 'applyNode_bw_transposeAxes_out' in h
    for name in ('caller_nonvacuous', 'run_success', 'seed_nonconstant', 'saved_nonconstant',
                 'not_identity', 'same_shape', 'pointwise_transpose'):
        assert name in w
    assert all(token not in h + w for token in ('sorry', 'axiom ', 'native_decide'))
