"""Original captures, no recapture; logical contiguous gradient, not storage refinement."""
import importlib
import importlib.util
from math import prod
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_contiguous_reads'), 'missing original BW_contiguous reader'
    return importlib.import_module('Verdict.runtime_backward_contiguous_reads')


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            i = next(i for i in order['execution_to_source']
                     if cells[i].rank == rank and cells[i].opname.name == 'BW_contiguous')
            yield view, cells, snapshot, i, order, label


def test_original_read_and_noncontiguous_float64_autograd(worlds):
    import torch
    rows = []
    for args in selected(worlds):
        text, row = api().render_read(*args)
        rows.append(row)
        c = row['source_contract']; cell = args[1][args[3]]
        fw = args[1][c['fw_source_index']]
        assert c['input_roles'] == ['cotangent', 'saved_input']
        assert c['output_roles'] == ['dx']
        assert c['saved_inputs'] == [list(r) for r in fw.inputs]
        assert row['input_refs'] == [list(r) for r in cell.inputs]
        assert row['output_refs'] == [list(r) for r in cell.outputs]
        assert c['fw_node'] == list(fw.node) and c['bw_node'] == list(cell.node)
        assert c['fw_signature'] == 'torch.Tensor.contiguous'
        assert c['bw_signature'] == 'torch.autograd.grad'
        assert c['fw_kwargs'] == c['bw_kwargs'] == {'__consts': []}
        assert row['params'] == []
        assert row['execution_index'] == args[4]['source_to_execution'][args[3]]
        assert row['operand_nonwrite_source_indices'] == args[4]['execution_to_source'][row['execution_index']:]
        gtid, xtid = row['input_tids']; dxid, = row['output_tids']
        assert f't {dxid} = t {gtid}' in text
        assert f't {dxid} = t {xtid}' not in text
        assert 'SourceBWContiguousRead.bw_contiguous_value_of_split' in text
        assert f'(h : {args[5]}DenoteWithInputs s = some t)' in text
        assert len(row['theorems']) == 1
        assert all(row[k] is False and c[k] is False for k in (
            'proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
        assert c['saved_value_premise'] is False
        assert c['derivative'] == 'cotangent'
        assert c['input_writer_source_indices'][0] == args[3] - 1
        producer = args[1][args[3]-1]
        assert producer.opname.name == ('BW_view' if args[5] == 'sm' else 'AllToAllPrim')
        fn = torch
        for part in fw.ir.signature.split('.')[1:]: fn = getattr(fn, part)
        shape = tuple(fw._input_irs[0].shape); n = prod(shape)
        base_shape = (*shape[:-2], shape[-1], shape[-2])
        leaf = torch.linspace(-3.1, 7.3, n, dtype=torch.float64).reshape(base_shape).requires_grad_()
        x = leaf.transpose(-1, -2)
        assert not x.is_contiguous()
        y = fn(x, **{k: v for k, v in fw.ir.kwargs.items() if k != '__consts'})
        assert y.is_contiguous() and y.data_ptr() != x.data_ptr()
        torch.testing.assert_close(y, x, rtol=0, atol=0)
        g = torch.linspace(.2, 9.7, n, dtype=torch.float64).reshape(shape)
        dx, = torch.autograd.grad(y, x, g)
        torch.testing.assert_close(dx, g, rtol=0, atol=0)
        assert tuple(dx.shape) == tuple(c['target_shape']) == tuple(c['cotangent_shape'])
        assert torch.count_nonzero(dx) == n and dx.flatten()[0] != dx.flatten()[1]
        assert x.flatten()[0] != x.flatten()[1]
        assert not torch.equal(dx, x.detach())
    assert [(r['world'], r['source_index']) for r in rows] == [('sm', 75), ('pm', 127), ('pm', 363), ('pm', 599), ('pm', 835)]


@pytest.mark.parametrize('fault', [
    'fw-signature', 'bw-signature', 'memory-format', 'unknown-kwarg',
    'saved-version', 'saved-output', 'ordered-inputs', 'coordinated-inputs',
    'gradient-metadata', 'saved-metadata', 'cotangent-initial', 'bool-version',
    'fw-lowered-op', 'bw-lowered-op', 'fw-params', 'bw-params',
    'writer-call', 'fw-writer-missing', 'source-suffix', 'output-suffix',
    'execution-order', 'execution-truncated', 'inverse-order',
    'source-owner', 'source-cid', 'collective-scope', 'input-writer-missing', 'shape-zero',
])
def test_original_contiguous_rejects_mutations(worlds, monkeypatch, fault):
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
            elif fault in ('memory-format', 'unknown-kwarg'):
                for obj in (cell, fw):
                    key = 'memory_format' if fault == 'memory-format' else 'unknown'
                    m.setattr(obj, 'kwargs', dict(obj.kwargs, **{key: 1}))
                    m.setitem(obj.ir.kwargs, key, 1)
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
            elif fault in ('source-owner', 'source-cid'):
                m.setattr(cell, 'node', cell.node._replace(**(
                    {'rank': cell.rank+1} if fault == 'source-owner' else {'cid': cell.node.cid+1})))
            elif fault == 'collective-scope':
                m.setattr(view, 'collective_scopes', {cell.node: (0, 1)}, raising=False)
            elif fault == 'input-writer-missing':
                j = good['source_contract']['input_writer_source_indices'][0]
                m.setattr(cells[j], 'outputs', [])
            elif fault == 'shape-zero':
                irs = list(cell._input_irs); irs[0] = copy.deepcopy(irs[0])
                m.setattr(irs[0], '_shape', (0,))
                m.setattr(cell, '_input_irs', irs)
            elif fault == 'execution-order':
                m.setitem(order, 'execution_to_source', list(reversed(order['execution_to_source'])))
            elif fault == 'execution-truncated':
                m.setitem(order, 'execution_to_source', order['execution_to_source'][:good['execution_index']+1])
            else:
                inv = list(order['source_to_execution']); inv[i] = inv[i] + 1
                m.setitem(order, 'source_to_execution', inv)
            with pytest.raises(ValueError): api().render_read(*args)
        assert api().render_read(*args) == (text, good)


def test_lean_helper_and_joint_nonconstant_witness_present():
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    helper = root / 'trainverify/denote/SourceBWContiguousRead.lean'
    witness = root / 'iroha-tasks/trainverify-backward/ContiguousReadWitness.lean'
    assert helper.exists(), 'missing original contiguous source helper'
    assert witness.exists(), 'missing joint successful contiguous witness'
    h, w = helper.read_text(), witness.read_text()
    assert 'SourceValueRead.node_value_of_split' in h and 'applyNode_bw_contiguous_out' in h
    for name in ('caller_nonvacuous', 'run_success', 'seed_nonconstant', 'saved_nonconstant',
                 'not_saved_input', 'pointwise_gradient'):
        assert name in w
    assert 'sourceNode dx [grad, savedX]' in h
    assert all(token not in h + w for token in ('sorry', 'axiom ', 'native_decide'))
