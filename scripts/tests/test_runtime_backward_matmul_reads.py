"""Original BW_matmul ports, saved primal authority and independent CPU oracle."""
import importlib
import importlib.util
import itertools
from math import prod
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_matmul_reads'), 'missing original BW_matmul reader'
    return importlib.import_module('Verdict.runtime_backward_matmul_reads')


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            i = next(i for i, c in enumerate(cells) if c.rank == rank and c.opname.name == 'BW_matmul')
            yield view, cells, snapshot, i, order, label


def oracle(g, x, y):
    """Independent scalar-index contractions: no matmul/transpose/einsum."""
    import torch
    dx, dy = torch.zeros_like(x), torch.zeros_like(y)
    n, k, m = x.shape[-2], x.shape[-1], y.shape[-1]
    for b in itertools.product(*(range(d) for d in x.shape[:-2])):
        for i, l in itertools.product(range(n), range(k)):
            dx[b + (i, l)] = sum(g[b + (i, j)].item() * y[b + (l, j)].item() for j in range(m))
        for l, j in itertools.product(range(k), range(m)):
            dy[b + (l, j)] = sum(x[b + (i, l)].item() * g[b + (i, j)].item() for i in range(n))
    return dx, dy


def check_cpu(fn, xs, ys):
    import torch
    # Distinct nonsymmetric operands, all batches different, exact small integers.
    x = (torch.arange(prod(xs), dtype=torch.float64) % 11 + 1).reshape(xs).requires_grad_()
    y = (torch.arange(prod(ys), dtype=torch.float64) % 13 + 2).reshape(ys).requires_grad_()
    z = fn(x, y)
    g = (torch.arange(z.numel(), dtype=torch.float64) % 7 + 3).reshape(z.shape)
    actual = torch.autograd.grad(z, (x, y), g)
    expected = oracle(g, x.detach(), y.detach())
    for a, e, saved in zip(actual, expected, (x, y), strict=True):
        torch.testing.assert_close(a, e, rtol=0, atol=0)
        assert torch.count_nonzero(a) == a.numel()
        assert a.unique().numel() > 1 and saved.unique().numel() > 1
        assert not torch.equal(a, saved)
    if actual[0].shape == actual[1].shape:
        assert not torch.equal(*actual)
        assert not torch.equal(actual[0], g @ y.detach())
        assert not torch.equal(actual[1], x.detach() @ g)


def test_original_matmul_two_ports_and_real_batched_derivatives(worlds):
    import torch
    rows = []
    for args in selected(worlds):
        text, row = api().render_read(*args)
        rows.append(row)
        cell = args[1][args[3]]; c = row['source_contract']; fw = args[1][c['fw_source_index']]
        assert c['input_roles'] == ['cotangent', 'saved_left', 'saved_right']
        assert c['output_roles'] == ['dx', 'dy']
        assert c['saved_inputs'] == [list(r) for r in fw.inputs] == [list(r) for r in cell.inputs[1:]]
        assert row['input_refs'] == [list(r) for r in cell.inputs]
        assert row['output_refs'] == [list(r) for r in cell.outputs]
        assert row['execution_index'] == args[4]['source_to_execution'][args[3]]
        assert row['operand_nonwrite_source_indices'] == args[4]['execution_to_source'][row['execution_index']:]
        assert len(row['theorems']) == 2
        for port, role in enumerate(('dx', 'dy'), 1):
            assert row['theorems'][port-1].endswith('_' + role)
            assert f'SourceBWMatmulRead.bw_matmul_{role}_value_of_split' in text
            assert f't {row["output_tids"][port-1]} = (bw_matmul ' in text
            assert f').{port} := by' in text
        assert 'dw' not in text.lower() and 'saved_weight' not in str(c)
        assert all(row[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
        assert c['batch_broadcast'] is False
        fn = torch
        for part in fw.ir.signature.split('.')[1:]: fn = getattr(fn, part)
        check_cpu(fn, tuple(fw._input_irs[0].shape), tuple(fw._input_irs[1].shape))
        producer, = [j for j, p in enumerate(args[1]) if cell.inputs[0] in p.outputs]
        assert producer == args[3] - 1
        assert args[1][producer].opname.name == ('BW_transpose' if args[5] == 'sm' else 'AllToAllPrim')
    assert [(r['world'], r['source_index']) for r in rows] == [('sm',77),('pm',131),('pm',367),('pm',603),('pm',839)]
    for xs, ys in [((1,2,2,2),(1,2,2,2)), ((2,3,2,4),(2,3,4,5)), ((3,2,5),(3,5,4))]:
        check_cpu(torch.matmul, xs, ys)


@pytest.mark.parametrize('fault', ['saved-x-version','saved-y-version','ports','saved-order',
    'saved-metadata','dy-valmap','fw-signature','bw-signature','fw-kwargs','bw-kwargs',
    'fw-op','bw-op','fw-params','bw-params','writer','fw-writer','suffix',
    'execution-truncated','inverse-order','left-valmap','g-valmap','dx-valmap','cloned-forward-ir','execution-reversed'])
def test_original_matmul_rejects_mutations(worlds, monkeypatch, fault):
    import copy
    from Verdict import graph_to_lean
    from verdict.operators.names import OpName
    for args in selected(worlds):
        view, cells, snapshot, i, order, label = args
        text, good = api().render_read(*args)
        cell = cells[i]; fw = cells[good['source_contract']['fw_source_index']]
        with monkeypatch.context() as m:
            if fault in ('saved-x-version','saved-y-version'):
                port = 1 if fault == 'saved-x-version' else 2
                refs = list(cell.inputs); refs[port] = refs[port]._replace(v=refs[port].v+1)
                m.setattr(cell, 'inputs', refs)
            elif fault == 'ports':
                m.setattr(cell, 'outputs', list(reversed(cell.outputs)))
                m.setattr(cell, '_output_irs', list(reversed(cell._output_irs)))
            elif fault == 'saved-order':
                m.setattr(cell, 'inputs', [cell.inputs[0], *reversed(cell.inputs[1:])])
                m.setattr(cell, '_input_irs', [cell._input_irs[0], *reversed(cell._input_irs[1:])])
            elif fault in ('saved-metadata', 'dy-valmap','left-valmap','g-valmap','dx-valmap'):
                attr, port = {'saved-metadata':('_input_irs',2), 'dy-valmap':('_output_irs',1),
                              'left-valmap':('_input_irs',1), 'g-valmap':('_input_irs',0),
                              'dx-valmap':('_output_irs',0)}[fault]
                irs = list(getattr(cell, attr)); irs[port] = copy.deepcopy(irs[port])
                irs[port]._valmap = type(irs[port]._valmap)((1, 3))
                m.setattr(cell, attr, irs)
            elif fault == 'cloned-forward-ir': m.setattr(fw, 'ir', copy.deepcopy(fw.ir))
            elif fault == 'execution-reversed': m.setitem(order, 'execution_to_source', list(reversed(order['execution_to_source'])))
            elif fault.endswith('signature'):
                m.setattr((fw if fault.startswith('fw') else cell).ir, 'signature', 'torch.add')
            elif fault.endswith('kwargs'):
                obj = fw if fault.startswith('fw') else cell
                m.setitem(obj.ir.kwargs, 'unexpected', True)
                m.setattr(obj, 'kwargs', dict(obj.kwargs, unexpected=True))
            elif fault.endswith('-op'):
                m.setitem(view.source._node2opname, (fw if fault.startswith('fw') else cell).node, OpName.FW_add)
            elif fault.endswith('-params'):
                target = (fw if fault.startswith('fw') else cell).node
                original = graph_to_lean._get_node_params
                m.setattr(graph_to_lean, '_get_node_params', lambda v,n,**kw: [False] if n==target else original(v,n,**kw))
            elif fault == 'writer':
                wr = next(w for w in snapshot['writers'] if w['export_id'] == good['bw_writer'])
                m.setitem(wr['ref'], 'call_instance', wr['ref']['call_instance']+1)
            elif fault == 'fw-writer':
                m.setitem(snapshot, 'writers', [w for w in snapshot['writers'] if w['export_id'] != good['fw_writer']])
            elif fault == 'suffix': m.setattr(cells[-1], 'outputs', [cell.outputs[1]])
            elif fault == 'execution-truncated': m.setitem(order, 'execution_to_source', order['execution_to_source'][:-1])
            else:
                inv = list(order['source_to_execution']); inv[i] += 1
                m.setitem(order, 'source_to_execution', inv)
            with pytest.raises(ValueError): api().render_read(*args)
        assert api().render_read(*args) == (text, good)


@pytest.mark.parametrize('g,x,y', [((2,), (2,), (2,)),
    ((2,3,5),(1,3,4),(2,4,5)), ((2,3,5),(2,3,4),(2,6,5)),
    ((2,3,6),(2,3,4),(2,4,5)), ((1,2,2),(True,2,2),(1,2,2))])
def test_domain_failclosed(g,x,y):
    from trainverify.backward_matmul_authority import validate_shapes
    with pytest.raises(ValueError): validate_shapes(g,x,y)


def test_exact_joint_witness_cpu_tables_and_saved_dependencies():
    import torch
    from pathlib import Path
    import ast
    import re
    shape = (1,2,2,2)
    x = torch.arange(1,9,dtype=torch.float64).reshape(shape).requires_grad_()
    y = torch.arange(11,19,dtype=torch.float64).reshape(shape).requires_grad_()
    g = torch.arange(3,11,dtype=torch.float64).reshape(shape)
    actual = torch.autograd.grad(torch.matmul(x,y), (x,y), g)
    expected = oracle(g,x.detach(),y.detach())
    witness = (Path(__file__).resolve().parents[2] / 'iroha-tasks/trainverify-backward/MatmulReadWitness.lean').read_text()
    for role, a, e in zip(('dx','dy'),actual,expected,strict=True):
        table = ast.literal_eval(re.search(r'def expected_'+role+r'.*?:= \((\[[^]]+\])', witness)[1])
        assert a.flatten().tolist() == e.flatten().tolist() == table
    # Changing X changes only dY; changing Y changes only dX.
    x_changed = oracle(g, x.detach()+3, y.detach())
    y_changed = oracle(g, x.detach(), y.detach()+5)
    assert torch.equal(x_changed[0],actual[0]) and not torch.equal(x_changed[1],actual[1])
    assert not torch.equal(y_changed[0],actual[0]) and torch.equal(y_changed[1],actual[1])
    # Accidental reuse of batch zero must change both derivatives of batch one.
    x0=x.detach().clone(); y0=y.detach().clone(); g0=g.clone()
    for t in (x0,y0,g0): t[:,1]=t[:,0]
    wrong=oracle(g0,x0,y0)
    assert all(not torch.equal(a[:,1],b[:,1]) for a,b in zip(actual,wrong,strict=True))


def test_lean_helper_and_joint_nonconstant_witness_present():
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    helper = root / 'trainverify/denote/SourceBWMatmulRead.lean'
    witness = root / 'iroha-tasks/trainverify-backward/MatmulReadWitness.lean'
    assert helper.exists(), 'missing original matmul source helper'
    assert witness.exists(), 'missing joint successful matmul witness'
    h, w = helper.read_text(), witness.read_text()
    assert 'SourceValueRead.node_value_of_split' in h
    assert 'applyNode_bw_matmul_fst_out' in h and 'applyNode_bw_matmul_snd_out' in h
    for name in ('caller_nonvacuous', 'run_success', 'seed_nonconstant', 'left_nonconstant',
                 'right_nonconstant', 'not_swapped', 'not_saved', 'not_missing_transpose'):
        assert name in w
    assert all(token not in h + w for token in ('sorry', 'axiom ', 'native_decide'))
