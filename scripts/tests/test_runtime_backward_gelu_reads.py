"""Original BW_gelu source reads; trusted captures loaded in memory only."""
import importlib
import importlib.util
import math

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_gelu_reads'), 'missing original BW_gelu reader'
    return importlib.import_module('Verdict.runtime_backward_gelu_reads')


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            index = next(i for i in order['execution_to_source']
                         if cells[i].rank == rank and cells[i].opname.name == 'BW_gelu')
            yield view, cells, snapshot, index, order, label


def test_original_gelu_same_final_store_read_and_python_semantics(worlds):
    import torch
    rows = []
    for args in selected(worlds):
        text, row = api().render_read(*args)
        rows.append(row)
        contract = row['source_contract']
        assert contract['input_roles'] == ['cotangent', 'saved_input']
        assert contract['output_roles'] == ['dx']
        assert contract['approximate'] == 'none'
        assert row['input_refs'] == [list(r) for r in args[1][args[3]].inputs]
        assert row['operand_nonwrite_source_indices'] == args[4]['execution_to_source'][row['execution_index']:]
        assert row['execution_index'] == args[4]['source_to_execution'][args[3]]
        g, x = row['input_tids']; dx, = row['output_tids']
        assert f't {dx} = bw_gelu (t {g}) (t {x})' in text
        assert 'SourceBWGeluRead.bw_gelu_value_of_split' in text
        assert f'(h : {args[5]}DenoteWithInputs s = some t)' in text
        assert len(row['theorems']) == 1
        assert all(row[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
        # Invoke the AUTHENTICATED original Python signature and exact kwargs.
        fw = args[1][contract['fw_source_index']]
        module, name = fw.ir.signature.rsplit('.', 1)
        fn = getattr(importlib.import_module(module), name)
        x = torch.tensor([-3., -1., .5, 2.], dtype=torch.float64, requires_grad=True)
        g = torch.tensor([2., -.5, -2., 4.], dtype=torch.float64)
        y = fn(x, approximate=contract['approximate'])
        dx, = torch.autograd.grad(y, x, g)
        def deriv(z):
            return .5*(1+torch.erf(z/math.sqrt(2))) + z*torch.exp(-z**2/2)/math.sqrt(2*math.pi)
        torch.testing.assert_close(dx, g*deriv(x.detach()), rtol=1e-12, atol=1e-12)
        assert not torch.allclose(dx, g*deriv(y.detach()), rtol=1e-8, atol=1e-8)
        z = x.detach().requires_grad_()
        tanh_dx, = torch.autograd.grad(fn(z, approximate='tanh'), z, g)
        assert not torch.allclose(dx, tanh_dx, rtol=1e-8, atol=1e-8)
        assert not torch.allclose(dx, g)
    assert len(rows) == 5


@pytest.mark.parametrize('fault', [
    'fw-signature', 'bw-signature', 'approximate', 'approximate-type',
    'saved-version', 'saved-output', 'ordered-inputs', 'coordinated-inputs',
    'gradient-metadata', 'saved-metadata', 'cotangent-initial', 'bool-version',
    'fw-lowered-op', 'bw-lowered-op', 'fw-params', 'bw-params',
    'writer-call', 'fw-writer-missing', 'source-suffix', 'output-suffix',
    'execution-order', 'execution-truncated', 'inverse-order',
])
def test_original_gelu_rejects_mutations(worlds, monkeypatch, fault):
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
            elif fault in ('approximate', 'approximate-type'):
                for obj in (cell, fw):
                    value = 'tanh' if fault == 'approximate' else False
                    m.setattr(obj, 'kwargs', dict(obj.kwargs, approximate=value))
                    m.setitem(obj.ir.kwargs, 'approximate', value)
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


def test_lean_helper_and_nonconstant_successful_run_witness_are_present():
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    helper = root / 'trainverify/denote/SourceBWGeluRead.lean'
    witness = root / 'iroha-tasks/trainverify-backward/GeluReadWitness.lean'
    assert helper.exists(), 'missing independent same-final-Store helper'
    assert witness.exists(), 'missing nonconstant successful-run witness'
    h = helper.read_text(); w = witness.read_text()
    assert 'SourceValueRead.node_value_of_split' in h
    assert 'applyNode_bw_gelu_out' in h
    assert 't dx = bw_gelu (t grad) (t savedX)' in h
    assert 'geluDerivScalar' in w and 'bw_gelu_valAt' in w
    assert 'caller_nonvacuous' in w and 'run_success' in w
    assert 'seed_nonconstant' in w and 'saved_nonconstant' in w
    assert 'sorry' not in h + w and 'axiom ' not in h + w
