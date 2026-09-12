"""Original BW_div raw scalar authority and independent CPU64 autograd oracle."""
import importlib
import importlib.util
from math import prod

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_div_reads'), 'missing original BW_div reader'
    return importlib.import_module('Verdict.runtime_backward_div_reads')


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            i = next(i for i, c in enumerate(cells) if c.rank == rank and c.opname.name == 'BW_div')
            yield view, cells, snapshot, i, order, label


def oracle(g, divisor):
    return g / divisor


@pytest.mark.parametrize('value', [0, -1, 0.0, -4.0, 4.5, True, False,
    float('nan'), float('inf'), float('-inf'), '4', None, [4]])
def test_raw_divisor_domain_never_truncates_even_with_coordinated_metadata(worlds, monkeypatch, value):
    from trainverify.backward_div_authority import bind
    for _, cells, _, i, _, _ in selected(worlds):
        good = bind(cells, i); cell = cells[i]; fw = cells[good['fw_source_index']]
        with monkeypatch.context() as m:
            raw_input = fw.ir.inputs()[0]
            m.setattr(fw.ir, 'inputs', lambda: (raw_input, value))
            for obj in (cell, fw):
                m.setattr(obj, 'kwargs', dict(obj.kwargs, __consts=[value]))
                m.setitem(obj.ir.kwargs, '__consts', [value])
            with pytest.raises(ValueError, match='bw-div .*divisor'):
                bind(cells, i)
        assert bind(cells, i) == good


@pytest.mark.parametrize('kwargs', [
    {'rounding_mode': 'floor', '__consts': [4.0]},
    {'rounding_mode': 'trunc', '__consts': [4.0]},
    {'rounding_mode': False, '__consts': [4.0]},
    {'rounding_mode': None, '__consts': [4.0], 'out': None},
])
def test_raw_forward_backward_division_modes_failclosed(worlds, monkeypatch, kwargs):
    from trainverify.backward_div_authority import bind
    for _, cells, _, i, _, _ in selected(worlds):
        good = bind(cells, i); cell = cells[i]; fw = cells[good['fw_source_index']]
        with monkeypatch.context() as m:
            for obj in (cell, fw):
                m.setattr(obj, 'kwargs', dict(kwargs))
                for key in list(obj.ir.kwargs): m.delitem(obj.ir.kwargs, key)
                for key, value in kwargs.items(): m.setitem(obj.ir.kwargs, key, value)
            with pytest.raises(ValueError, match='bw-div'):
                bind(cells, i)
        assert bind(cells, i) == good


@pytest.mark.parametrize('target', ['fw-cell', 'bw-cell', 'fw-ir', 'bw-ir', 'raw-input'])
@pytest.mark.parametrize('value', [4, 8.0, [], [4.0, 4.0]])
def test_original_literal_not_const_metadata_or_lowered_integer(worlds, monkeypatch, target, value):
    from trainverify.backward_div_authority import bind
    for args in selected(worlds):
        _, cells, _, i, _, _ = args
        text, good = api().render_read(*args)
        cell = cells[i]; fw = cells[good['source_contract']['fw_source_index']]
        with monkeypatch.context() as m:
            if target == 'raw-input':
                raw_input = fw.ir.inputs()[0]
                m.setattr(fw.ir, 'inputs', lambda: (raw_input, value))
            else:
                obj = fw if target.startswith('fw') else cell
                obj = obj.ir if target.endswith('ir') else obj
                m.setitem(obj.kwargs, '__consts', value if type(value) is list else [value])
            with pytest.raises(ValueError, match='bw-div'):
                bind(cells, i)
            with pytest.raises(ValueError): api().render_read(*args)
        assert api().render_read(*args) == (text, good)


@pytest.mark.parametrize('fault', ['missing', 'extra', 'reversed', 'tensor'])
def test_raw_forward_argument_inventory_not_tensor_only_dto(worlds, monkeypatch, fault):
    from trainverify.backward_div_authority import bind
    for _, cells, _, i, _, _ in selected(worlds):
        good = bind(cells, i); fw = cells[good['fw_source_index']]
        raw = list(fw.ir.inputs())
        if fault == 'missing': raw.pop()
        elif fault == 'extra': raw.append(4.0)
        elif fault == 'reversed': raw.reverse()
        else: raw[1] = fw._input_irs[0]
        with monkeypatch.context() as m:
            m.setattr(fw.ir, 'inputs', lambda: tuple(raw))
            with pytest.raises(ValueError, match='bw-div'):
                bind(cells, i)
        assert bind(cells, i) == good


@pytest.mark.parametrize('value', [1, 4, 8.0])
@pytest.mark.parametrize('wrapped', [False, True])
def test_supported_raw_integral_scalars_preserve_literal_type(worlds, monkeypatch, value, wrapped):
    import torch
    from nnscaler.ir.cten import IRObject
    for args in selected(worlds):
        _, cells, _, i, _, _ = args
        text, good = api().render_read(*args)
        cell = cells[i]; fw = cells[good['source_contract']['fw_source_index']]
        raw_input = fw.ir.inputs()[0]
        arg = IRObject(value=value, is_constant=True) if wrapped else value
        with monkeypatch.context() as m:
            m.setattr(fw.ir, 'inputs', lambda: (raw_input, arg))
            for obj in (cell, fw):
                m.setitem(obj.kwargs, '__consts', [value])
                m.setitem(obj.ir.kwargs, '__consts', [value])
            _, row = api().render_read(*args)
            assert type(row['source_contract']['raw_divisor']) is type(value)
            assert row['source_contract']['raw_divisor'] == value
            assert row['params'] == [int(value)]
            x = torch.tensor([-3., 2., 7.], dtype=torch.float64, requires_grad=True)
            g = torch.tensor([2., -5., 11.], dtype=torch.float64)
            literal = arg.value if wrapped else arg
            actual, = torch.autograd.grad(torch.div(x, literal), (x,), g)
            torch.testing.assert_close(actual, oracle(g, value))
        assert api().render_read(*args) == (text, good)


@pytest.mark.parametrize('fault', ['dynamic', 'bool', 'fractional', 'tensor-value', 'tensor'])
def test_nonliteral_or_tensor_divisor_cannot_pose_as_raw_scalar(worlds, monkeypatch, fault):
    import torch
    from nnscaler.ir.cten import IRObject
    from trainverify.backward_div_authority import bind
    for _, cells, _, i, _, _ in selected(worlds):
        good = bind(cells, i); fw = cells[good['fw_source_index']]
        raw_input = fw.ir.inputs()[0]
        value = {'dynamic': 4.0, 'bool': True, 'fractional': 4.5,
                 'tensor-value': torch.tensor(4.0), 'tensor': raw_input}[fault]
        arg = value if fault == 'tensor' else IRObject(value=value, is_constant=fault != 'dynamic')
        with monkeypatch.context() as m:
            m.setattr(fw.ir, 'inputs', lambda: (raw_input, arg))
            with pytest.raises(ValueError, match='bw-div .*divisor'):
                bind(cells, i)
        assert bind(cells, i) == good


@pytest.mark.parametrize('shape', [(), (0,), (-1,), (True,), (2.0,), ('2',)])
def test_coordinated_original_shapes_require_positive_integer_dimensions(worlds, monkeypatch, shape):
    from trainverify.backward_div_authority import bind
    for _, cells, _, i, _, _ in selected(worlds):
        good = bind(cells, i); cell = cells[i]; fw = cells[good['fw_source_index']]
        with monkeypatch.context() as m:
            for t in original_tensors(cell, fw):
                m.setattr(t, '_shape', shape)
            with pytest.raises(ValueError, match='bw-div .*shape'):
                bind(cells, i)
        assert bind(cells, i) == good


def original_tensors(cell, fw):
    # Cover cloned expansion tensors and raw mirrors, including gradient edges.
    tensors = [*cell._input_irs, *cell._output_irs, *fw._input_irs, *fw._output_irs,
               *cell.ir.inputs(), *cell.ir.outputs(), fw.ir.inputs()[0], *fw.ir.outputs()]
    tensors += [t.grad for t in tensors if t.grad is not None]
    return list({id(t): t for t in tensors}.values())


@pytest.mark.parametrize('role', ['g', 'x', 'dx'])
def test_coordinated_same_identity_still_requires_g_x_dx_same_shape(worlds, monkeypatch, role):
    from trainverify.backward_div_authority import bind
    for _, cells, _, i, _, _ in selected(worlds):
        good = bind(cells, i); cell = cells[i]; fw = cells[good['fw_source_index']]
        target = {'g': cell._input_irs[0], 'x': cell._input_irs[1], 'dx': cell._output_irs[0]}[role]
        with monkeypatch.context() as m:
            for t in original_tensors(cell, fw):
                if t.tid == target.tid:
                    m.setattr(t, '_shape', (3,))
            with pytest.raises(ValueError, match='bw-div .*shape'):
                bind(cells, i)
        assert bind(cells, i) == good


def test_alternative_complete_dependency_order_keeps_source_identity(worlds):
    from Verdict import runtime_schedule
    view, cells, snapshot, original_order, label = next(w for w in worlds if w[-1] == 'pm')
    predecessors, _, _, _ = runtime_schedule._dependencies(view)
    pending = set(range(len(cells))); done = set(); schedule = []
    while pending:
        ready = [i for i in pending if predecessors[i] <= done]
        assert ready
        i = max(ready)
        pending.remove(i); done.add(i); schedule.append(i)
    order = runtime_schedule.validate(view, schedule)
    assert order['execution_to_source'] != original_order['execution_to_source']
    changed = False
    for args in selected([worlds[1]]):
        _, _, _, i, _, _ = args
        _, original = api().render_read(*args)
        text, row = api().render_read(view, cells, snapshot, i, order, label)
        changed |= row['execution_index'] != original['execution_index']
        for key in ('node', 'source_index', 'input_tids', 'output_tids', 'source_contract', 'bw_writer', 'fw_writer'):
            assert row[key] == original[key]
        k = schedule.index(i)
        assert row['operand_nonwrite_source_indices'] == schedule[k:]
        assert f'(pmInputRequests.take {k}) (pmInputRequests.drop {k+1}) pmNode_{i}' in text
    assert changed


def test_original_div_read_and_real_raw_forward_derivative(worlds):
    import torch
    from Verdict.graph_to_lean import _get_node_params
    rows = []
    for args in selected(worlds):
        text, row = api().render_read(*args)
        rows.append(row)
        view, cells, _, i, order, label = args
        cell = cells[i]; c = row['source_contract']; fw = cells[c['fw_source_index']]
        raw_divisor = fw.ir.inputs()[1]
        assert type(raw_divisor) is float and raw_divisor == 4.0
        assert type(c['raw_divisor']) is float and c['raw_divisor'] == raw_divisor
        assert type(c['divisor']) is int and c['divisor'] == 4
        assert c['input_roles'] == ['cotangent', 'saved_input']
        assert c['output_roles'] == ['dx']
        assert c['saved_inputs'] == [list(r) for r in fw.inputs] == [list(r) for r in cell.inputs[1:]]
        assert row['input_refs'] == [list(r) for r in cell.inputs]
        assert row['output_ref'] == list(cell.outputs[0])
        assert row['output_refs'] == [row['output_ref']]
        assert row['input_tids'] == [t.tid for t in view.node_inputs(cell.node)]
        assert row['output_tid'] == view.node_outputs(cell.node)[0].tid
        assert row['output_tids'] == [row['output_tid']]
        assert row['params'] == _get_node_params(view, cell.node, num_parts=0) == [4]
        assert row['execution_index'] == order['source_to_execution'][i]
        assert row['operand_nonwrite_source_indices'] == order['execution_to_source'][row['execution_index']:]
        assert len(row['theorems']) == 1
        assert 'SourceBWDivRead.bw_div_value_of_split' in text
        assert f't {row["output_tid"]} = bw_div (4 : Scalar) (t {row["input_tids"][0]})' in text
        for record in (row, c):
            assert all(record[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
        assert fw.ir.signature == 'torch.div'
        assert cell.ir.signature == 'torch.autograd.grad'
        assert c['fw_kwargs'] == c['bw_kwargs'] == {'rounding_mode': None, '__consts': [4.0]}
        shape = tuple(fw._input_irs[0].shape)
        assert shape == ((2,4,16,16) if label == 'sm' else (1,4,16,8))
        assert c['input_shapes'] == [list(shape), list(shape)] and c['output_shapes'] == [list(shape)]
        x = ((torch.arange(prod(shape), dtype=torch.float64) % 23 - 11) / 7).reshape(shape).requires_grad_()
        g = ((torch.arange(prod(shape), dtype=torch.float64) % 13 + 1) / 5).reshape(shape)
        fn = torch
        for part in fw.ir.signature.split('.')[1:]: fn = getattr(fn, part)
        bw = torch
        for part in cell.ir.signature.split('.')[1:]: bw = getattr(bw, part)
        y = fn(x, raw_divisor, **{k:v for k,v in fw.ir.kwargs.items() if k != '__consts'})
        actual, = bw(y, (x,), g)
        torch.testing.assert_close(actual, oracle(g, raw_divisor), rtol=1e-13, atol=1e-14)
        assert actual.unique().numel() > 1 and torch.count_nonzero(actual) == actual.numel()
        assert not torch.allclose(actual, g * raw_divisor)
        assert not torch.allclose(actual, g) and not torch.allclose(actual, x)
        x2 = (x.detach() * -3 + 5).requires_grad_()
        actual2, = bw(fn(x2, raw_divisor, rounding_mode=None), (x2,), g)
        torch.testing.assert_close(actual2, actual)
    assert [(r['world'], r['source_index'], r['source_contract']['fw_source_index']) for r in rows] == [
        ('sm',79,46), ('pm',135,77), ('pm',371,313), ('pm',607,549), ('pm',843,785)]


@pytest.mark.parametrize('fault', ['saved-version', 'saved-output', 'g-metadata', 'x-metadata',
    'dx-metadata', 'fw-signature', 'bw-signature', 'cloned-forward-ir', 'duplicate-mirror',
    'writer-missing', 'suffix-overwrite', 'kwargs-mismatch', 'raw-kwargs-mismatch',
    'input-order', 'output-arity', 'node-identity', 'initial-cotangent', 'bool-version',
    'bool-index', 'negative-index', 'fw-op', 'bw-op'])
def test_raw_source_identity_failclosed(worlds, monkeypatch, fault):
    import copy
    from trainverify.backward_div_authority import bind
    from verdict.operators.names import OpName
    for args in selected(worlds):
        _, cells, _, i, _, _ = args
        good = bind(cells, i); cell = cells[i]; fw = cells[good['fw_source_index']]
        changed_cells = cells; changed_index = i
        with monkeypatch.context() as m:
            if fault == 'saved-version':
                m.setattr(cell, 'inputs', [cell.inputs[0], cell.inputs[1]._replace(v=cell.inputs[1].v+1)])
            elif fault == 'saved-output':
                m.setattr(cell, 'inputs', [cell.inputs[0], fw.outputs[0]])
                m.setattr(cell, '_input_irs', [cell._input_irs[0], fw._output_irs[0]])
            elif fault.endswith('metadata'):
                attr, port = {'g-metadata':('_input_irs',0), 'x-metadata':('_input_irs',1), 'dx-metadata':('_output_irs',0)}[fault]
                irs = list(getattr(cell, attr)); irs[port] = copy.deepcopy(irs[port])
                irs[port]._valmap = type(irs[port]._valmap)((1,3))
                m.setattr(cell, attr, irs)
            elif fault.endswith('signature'):
                m.setattr((fw if fault.startswith('fw') else cell).ir, 'signature', 'torch.add')
            elif fault == 'cloned-forward-ir': m.setattr(fw, 'ir', copy.deepcopy(fw.ir))
            elif fault == 'duplicate-mirror': changed_cells = [*cells, fw]
            elif fault == 'writer-missing':
                producer, = [c for c in cells[:i] if cell.inputs[0] in c.outputs]
                m.setattr(producer, 'outputs', [])
            elif fault == 'suffix-overwrite': m.setattr(cells[-1], 'outputs', [cell.outputs[0]])
            elif fault == 'kwargs-mismatch': m.setattr(cell, 'kwargs', dict(cell.kwargs, rounding_mode="floor"))
            elif fault == 'raw-kwargs-mismatch': m.setitem(cell.ir.kwargs, 'rounding_mode', 'floor')
            elif fault == 'input-order': m.setattr(cell, 'inputs', list(reversed(cell.inputs)))
            elif fault == 'output-arity': m.setattr(cell, 'outputs', [])
            elif fault == 'node-identity': m.setattr(cell, 'node', cell.node._replace(cid=cell.node.cid+1))
            elif fault in ('initial-cotangent', 'bool-version'):
                m.setattr(cell, 'inputs', [cell.inputs[0]._replace(v=0 if fault == 'initial-cotangent' else True), cell.inputs[1]])
            elif fault == 'bool-index': changed_index = True
            elif fault == 'negative-index': changed_index = -1
            else: m.setattr(fw if fault == 'fw-op' else cell, 'opname', OpName.FW_add)
            with pytest.raises(ValueError, match='bw-div'):
                bind(changed_cells, changed_index)
        assert bind(cells, i) == good


@pytest.mark.parametrize('fault', ['fw-op', 'bw-op', 'fw-kwargs', 'bw-kwargs', 'fw-params', 'bw-params',
    'fw-input', 'bw-input', 'bw-output', 'fw-shape', 'bw-shape', 'scope', 'inventory', 'world',
    'writer', 'fw-writer', 'writer-export', 'writer-ports', 'truncated', 'reverse-valid-inverse',
    'inverse', 'duplicate-schedule', 'bool-schedule'])
def test_reader_join_and_complete_schedule_failclosed(worlds, monkeypatch, fault):
    from Verdict import graph_to_lean
    from verdict.operators.names import OpName
    for args in selected(worlds):
        view, cells, snapshot, i, order, label = args
        text, good = api().render_read(*args)
        cell = cells[i]; fw = cells[good['source_contract']['fw_source_index']]
        call_args = args
        with monkeypatch.context() as m:
            if fault.endswith('-op'):
                m.setitem(view.source._node2opname, (fw if fault.startswith('fw') else cell).node, OpName.FW_add)
            elif fault.endswith('-kwargs'):
                original = view.node_kwargs; target = (fw if fault.startswith('fw') else cell).node
                m.setattr(view, 'node_kwargs', lambda n: {'rounding_mode': 'floor'} if n == target else original(n))
            elif fault.endswith('-params'):
                original = graph_to_lean._get_node_params; target = (fw if fault.startswith('fw') else cell).node
                m.setattr(graph_to_lean, '_get_node_params', lambda v,n,**kw: [False] if n == target else original(v,n,**kw))
            elif fault in ('fw-input', 'bw-input', 'bw-output'):
                side = 'node_outputs' if fault == 'bw-output' else 'node_inputs'
                original = getattr(view, side); target = (fw if fault.startswith('fw') else cell).node
                m.setattr(view, side, lambda n: [view.node_inputs(fw.node)[0]] if n == target else original(n))
                if fault == 'fw-input':
                    m.setattr(view, side, lambda n: [view.node_outputs(fw.node)[0]] if n == target else original(n))
            elif fault.endswith('-shape'):
                original = view.tensor_shape
                target = view.node_outputs((fw if fault.startswith('fw') else cell).node)[0]
                m.setattr(view, 'tensor_shape', lambda t: (1,) if t == target else original(t))
            elif fault == 'scope': m.setattr(view, 'collective_scopes', {cell.node: [0]}, raising=False)
            elif fault == 'inventory': m.setattr(view, 'nodes', lambda: list(reversed([c.node for c in cells])))
            elif fault == 'world': call_args = (*args[:-1], 'pm' if label == 'sm' else 'sm')
            elif fault == 'writer':
                wr = next(w for w in snapshot['writers'] if w['export_id'] == good['bw_writer'])
                m.setitem(wr['ref'], 'call_instance', wr['ref']['call_instance']+1)
            elif fault == 'fw-writer': m.setitem(snapshot, 'writers', [w for w in snapshot['writers'] if w['export_id'] != good['fw_writer']])
            elif fault in ('writer-export', 'writer-ports'):
                wr = next(w for w in snapshot['writers'] if w['export_id'] == good['bw_writer'])
                m.setitem(wr, 'export_id' if fault == 'writer-export' else 'inputs', 'bad' if fault == 'writer-export' else list(reversed(wr['inputs'])))
            elif fault == 'inverse': m.setitem(order, 'source_to_execution', list(reversed(order['source_to_execution'])))
            else:
                schedule = list(order['execution_to_source'])
                if fault == 'truncated': schedule.pop()
                elif fault == 'duplicate-schedule': schedule[-1] = schedule[0]
                elif fault == 'bool-schedule': schedule[0] = False
                else:
                    schedule.reverse()
                    m.setitem(order, 'source_to_execution', [schedule.index(j) for j in range(len(cells))])
                m.setitem(order, 'execution_to_source', schedule)
            with pytest.raises(ValueError): api().render_read(*call_args)
        assert api().render_read(*args) == (text, good)


@pytest.mark.parametrize('port', [0, 1, 2])
def test_lowered_store_tid_cannot_be_overwritten_in_execution_suffix(worlds, monkeypatch, port):
    # Distinct rank fullrefs are legal to the schedule, but may not alias one
    # Store ID. Keep source ports intact and change only the lowered suffix ID.
    from Verdict import runtime_schedule
    args = next(a for a in selected(worlds) if a[5] == 'pm')
    view, cells, snapshot, i, order, label = args
    text, good = api().render_read(*args)
    watched = [*good['input_tids'], good['output_tid']][port]
    tail = next(c for c in reversed(cells) if c.outputs and c.rank != cells[i].rank)
    original_outs = view.node_outputs(tail.node)
    old = original_outs[0]; alias = old._replace(tid=watched)
    source_tensor = view.source_tensor; inventory = view.tensors()
    with monkeypatch.context() as m:
        m.setitem(view._node2outputs, tail.node, [alias, *original_outs[1:]])
        m.setattr(view, 'tensors', lambda: [*inventory, alias])
        m.setattr(view, 'source_tensor', lambda t: source_tensor(old) if t == alias else source_tensor(t))
        runtime_schedule.validate(view, order['execution_to_source'])
        with pytest.raises(ValueError, match='bw-div .*suffix'):
            api().render_read(*args)
    assert api().render_read(*args) == (text, good)
