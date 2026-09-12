"""Original reverse residual split: authenticate both derivatives before reads."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_add_reads'), 'missing original BW_add reader'
    return importlib.import_module('Verdict.runtime_backward_add_reads')


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            index = next(i for i in order['execution_to_source']
                         if cells[i].rank == rank and cells[i].opname.name == 'BW_add')
            yield view, cells, snapshot, index, order, label


def test_original_add_two_final_store_reads(worlds):
    rows = []
    for args in selected(worlds):
        text, row = api().render_read(*args)
        rows.append(row)
        assert row['source_contract']['input_roles'] == ['cotangent', 'saved_left', 'saved_right']
        assert row['source_contract']['output_roles'] == ['dleft', 'dright']
        assert len(row['theorems']) == 2
        assert all('bw_add_' + role + '_value_of_split' in text for role in ('dleft', 'dright'))
        assert '(bw_add2 ' in text and ').1' in text and ').2' in text
        assert row['operand_nonwrite_source_indices'] == args[4]['execution_to_source'][row['execution_index']:]
        assert all(row[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
    assert len(rows) == 5


@pytest.mark.parametrize('fault', ['broadcast-right', 'zero-dimension'])
def test_add_source_shape_domain_rejected_by_shape_gate(worlds, monkeypatch, fault):
    from trainverify.backward_add_authority import bind
    for _, cells, _, i, _, _ in selected(worlds):
        good = bind(cells, i)
        cell = cells[i]; fw = cells[good['fw_source_index']]
        irs = [*cell._input_irs, *cell._output_irs, *fw._input_irs, *fw._output_irs,
               *cell.ir.inputs(), *cell.ir.outputs(), *fw.ir.inputs(), *fw.ir.outputs()]
        irs += [ir.grad for ir in list(irs) if ir.grad is not None]
        right_ids = {fw._input_irs[1].tid, cell._output_irs[1].tid}
        with monkeypatch.context() as m:
            for ir in {id(ir): ir for ir in irs}.values():
                if fault == 'zero-dimension':
                    m.setattr(ir, '_shape', (0, *ir.shape[1:]))
                elif ir.tid in right_ids:
                    m.setattr(ir, '_shape', (*ir.shape[:-1], 1))
            with pytest.raises(ValueError, match='equal positive residual'):
                bind(cells, i)
        assert bind(cells, i) == good


@pytest.mark.parametrize('fault', ['signature', 'alpha', 'saved-version', 'saved-order',
    'gradient-order', 'coordinated-gradient-order', 'cotangent-metadata',
    'cotangent-initial', 'fw-lowered-op', 'params', 'writer-call', 'suffix'])
def test_original_add_rejects_source_mutations(worlds, monkeypatch, fault):
    import copy
    from verdict.operators.names import OpName
    for args in selected(worlds):
        view, cells, snapshot, i, order, label = args
        text, good = api().render_read(*args)
        cell = cells[i]
        fw = cells[good['source_contract']['fw_source_index']]
        with monkeypatch.context() as m:
            if fault == 'signature': m.setattr(fw.ir, 'signature', 'torch.sub')
            elif fault == 'alpha':
                for obj in (cell, fw):
                    m.setattr(obj, 'kwargs', dict(obj.kwargs, alpha=2))
                    m.setitem(obj.ir.kwargs, 'alpha', 2)
            elif fault == 'saved-version': m.setattr(cell, 'inputs', [cell.inputs[0], cell.inputs[1]._replace(v=cell.inputs[1].v + 1), cell.inputs[2]])
            elif fault == 'saved-order': m.setattr(cell, 'inputs', [cell.inputs[0], cell.inputs[2], cell.inputs[1]])
            elif fault in ('gradient-order', 'coordinated-gradient-order'):
                m.setattr(cell, 'outputs', list(reversed(cell.outputs)))
                if fault == 'coordinated-gradient-order': m.setattr(cell, '_output_irs', list(reversed(cell._output_irs)))
            elif fault == 'cotangent-metadata':
                ir = copy.deepcopy(cell._input_irs[0]); ir._valmap = type(ir._valmap)((1, 3))
                m.setattr(cell, '_input_irs', [ir, *cell._input_irs[1:]])
            elif fault == 'cotangent-initial': m.setattr(cell, 'inputs', [cell.inputs[0]._replace(v=0), *cell.inputs[1:]])
            elif fault == 'fw-lowered-op': m.setitem(view.source._node2opname, fw.node, OpName.FW_gelu)
            elif fault == 'params':
                from Verdict import graph_to_lean
                m.setattr(graph_to_lean, '_get_node_params', lambda *a, **k: [False])
            elif fault == 'writer-call':
                row = next(w for w in snapshot['writers'] if w['export_id'] == good['bw_writer'])
                m.setitem(row['ref'], 'call_instance', row['ref']['call_instance'] + 1)
            else:
                later = cells[order['execution_to_source'][-1]]
                m.setattr(later, 'outputs', [cell.inputs[1]])
            with pytest.raises(ValueError): api().render_read(*args)
        assert api().render_read(*args) == (text, good)
