"""Fresh original captures; BW_view is inverse reshape, not a saved-value premise."""
import importlib
import importlib.util
from math import prod
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_view_reads'), 'missing original BW_view reader'
    return importlib.import_module('Verdict.runtime_backward_view_reads')


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            i = next(i for i in order['execution_to_source']
                     if cells[i].rank == rank and cells[i].opname.name == 'BW_view')
            yield view, cells, snapshot, i, order, label


def test_actual_view_original_read_and_float64_inverse_reshape(worlds):
    import torch
    rows = []
    for args in selected(worlds):
        text, row = api().render_read(*args)
        rows.append(row)
        c = row['source_contract']; fw = args[1][c['fw_source_index']]
        assert c['input_roles'] == ['cotangent', 'saved_input']
        assert c['output_roles'] == ['dx']
        assert c['saved_inputs'] == [list(r) for r in fw.inputs]
        assert row['input_refs'] == [list(r) for r in args[1][args[3]].inputs]
        assert row['output_refs'] == [list(r) for r in args[1][args[3]].outputs]
        assert row['execution_index'] == args[4]['source_to_execution'][args[3]]
        assert row['operand_nonwrite_source_indices'] == args[4]['execution_to_source'][row['execution_index']:]
        g, x = row['input_tids']; dx, = row['output_tids']
        assert f't {dx} = fw_view {c["target_shape"]} (t {g})' in text
        assert 'SourceBWViewRead.bw_view_value_of_split' in text
        assert f'(h : {args[5]}DenoteWithInputs s = some t)' in text
        assert len(row['theorems']) == 1
        assert all(row[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
        fn = torch
        for part in fw.ir.signature.split('.')[1:]: fn = getattr(fn, part)
        shape = tuple(fw._input_irs[0].shape); n = prod(shape)
        x = torch.linspace(-3.1, 7.3, n, dtype=torch.float64).reshape(shape).requires_grad_()
        y = fn(x, *fw.ir.kwargs['size'])
        g = torch.linspace(.2, 9.7, n, dtype=torch.float64).reshape(y.shape)
        dx, = torch.autograd.grad(y, x, g)
        torch.testing.assert_close(dx, g.reshape(x.shape), rtol=0, atol=0)
        assert tuple(dx.shape) == tuple(c['target_shape']) != tuple(g.shape)
        assert tuple(dx.shape) != tuple(g.reshape(y.shape).shape)  # saved OUTPUT is wrong
        assert torch.count_nonzero(dx) == n and dx.flatten()[0] != dx.flatten()[1]
        assert x.flatten()[0] != x.flatten()[1]
        assert not torch.equal(dx, x.detach())  # saved values are not derivative values
    assert [(r['world'], r['source_index']) for r in rows] == [('sm', 74), ('pm', 125), ('pm', 361), ('pm', 597), ('pm', 833)]


@pytest.mark.parametrize('fault', [
    'fw-signature', 'bw-signature', 'size-product', 'size-type', 'size-bw-only', 'unknown-kwarg',
    'saved-version', 'saved-output', 'ordered-inputs', 'coordinated-inputs',
    'gradient-metadata', 'saved-metadata', 'cotangent-initial', 'bool-version',
    'fw-lowered-op', 'bw-lowered-op', 'fw-params', 'bw-params',
    'writer-call', 'fw-writer-missing', 'source-suffix', 'output-suffix',
    'execution-order', 'execution-truncated', 'inverse-order',
])
def test_original_view_rejects_mutations(worlds, monkeypatch, fault):
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
            elif fault in ('size-product', 'size-type', 'size-bw-only', 'unknown-kwarg'):
                for obj in ((cell,) if fault == 'size-bw-only' else (cell, fw)):
                    key = 'unknown' if fault == 'unknown-kwarg' else 'size'
                    value = [True, 16, 32] if fault == 'size-type' else [7, 9]
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


def test_view_continuation_uses_original_linear_port(worlds):
    from Verdict import runtime_backward_linear_reads as linear
    rows = []
    for view, cells, snapshot, i, order, label in selected(worlds):
        ref = cells[i].inputs[0]
        li, = [j for j, c in enumerate(cells) if ref in c.outputs]
        _, lr = linear.render_read(view, cells, snapshot, li, order, label)
        expr = '(bw_linear ' + ' '.join(f'(t {tid})' for tid in lr['input_tids']) + ')'
        rows.append(dict(world=label, linear=lr, linear_expressions=[expr+'.1', expr+'.2'],
                         linear_theorems=lr['theorems']))
    text, detail = api().render_after_linear(worlds, rows)
    assert len(detail['reads']) == 5 and text.count('#print axioms') == 5
    assert detail['view_source'].count('#print axioms') == 5
    for row in detail['reads']:
        assert row['view_read']['input_refs'][0] == row['producer']['linear']['output_refs'][0]
        assert f't {row["view_read"]["output_tids"][0]} = {row["expression"]} := by' in text
    import copy
    bad = copy.deepcopy(rows)
    bad[0]['linear']['output_tids'][0] += 10000
    with pytest.raises(ValueError): api().render_after_linear(worlds, bad)


def test_lean_helper_and_joint_nonconstant_witness_present():
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    helper = root / 'trainverify/denote/SourceBWViewRead.lean'
    witness = root / 'iroha-tasks/trainverify-backward/ViewReadWitness.lean'
    assert helper.exists(), 'missing original view source helper'
    assert witness.exists(), 'missing joint successful view witness'
    h, w = helper.read_text(), witness.read_text()
    assert 'SourceValueRead.node_value_of_split' in h and 'applyNode_bw_view_out' in h
    for name in ('caller_nonvacuous', 'run_success', 'seed_nonconstant', 'saved_nonconstant',
                 'not_identity', 'not_saved_output', 'pointwise_reshape'):
        assert name in w
    assert all(token not in h + w for token in ('sorry', 'axiom ', 'native_decide'))
