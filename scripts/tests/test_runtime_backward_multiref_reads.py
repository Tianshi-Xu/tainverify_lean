"""Raw BW_multiref authority and SAME-final-Store ordered sum reads, real captures."""
import copy
import importlib
import importlib.util

import pytest

from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api(module, name):
    assert importlib.util.find_spec(module), f'missing original multiref boundary: {module}'
    return getattr(importlib.import_module(module), name)


def selected(worlds):
    for view, cells, snapshot, order, label in worlds:
        seen = set()
        for i, c in enumerate(cells):
            if c.opname.name == 'BW_multiref' and c.rank not in seen:
                seen.add(c.rank)
                yield view, cells, snapshot, i, order, label


def clone(cell):
    result = object.__new__(type(cell))
    for slot in cell.__slots__:
        setattr(result, slot, getattr(cell, slot))
    for field in ('inputs', 'outputs', '_input_irs', '_output_irs'):
        setattr(result, field, list(getattr(result, field)))
    return result


def test_raw_all_ordered_contributions_are_not_saved_primal_aliases(worlds):
    bind = api('trainverify.backward_multiref_authority', 'bind')
    for _, cells, _, i, _, label in selected(worlds):
        c = cells[i]; row = bind(cells, i)
        assert row['inputs'] == [list(r) for r in c.inputs]
        assert row['outputs'] == [list(r) for r in c.outputs]
        assert row['times'] == len(c.ir.mirror.outputs()) == len(c.ir.inputs())
        assert row['saved_inputs'] == []
        assert row['semantics'] == 'tensorSum; ordered gradient contributions'
        assert [r['ref'] for r in row['contributions']] == row['inputs']
        assert [r['port'] for r in row['contributions']] == list(range(row['times']))
        for r in row['contributions']:
            assert r['source_index'] < i
            assert r['value_relation_closed'] is False
            if label == 'pm':
                assert r['op'] == 'AllToAllPrim'
                assert 'AA' in r['obligation']
        assert row['proof_admissible'] is False


@pytest.mark.parametrize('fault', [
    'ordered-gradients', 'missing-contribution', 'saved-primal', 'signature',
    'times', 'bool-times', 'raw-grad-metadata', 'raw-input-grad', 'raw-order',
    'version', 'bool-version', 'initial', 'owner', 'cid', 'fw-version',
    'source-suffix-input', 'source-suffix-output', 'duplicate-input-writer'])
def test_raw_mutations_have_accepted_predecessors(worlds, monkeypatch, fault):
    bind = api('trainverify.backward_multiref_authority', 'bind')
    for _, original, _, i, _, _ in selected(worlds):
        good = bind(original, i)
        cells = list(original); c = cells[i] = clone(cells[i])
        fw_i = good['fw_source_index']; fw = cells[fw_i] = clone(cells[fw_i])
        assert bind(cells, i) == good
        with monkeypatch.context() as m:
            if fault == 'ordered-gradients': c.inputs.reverse(); c._input_irs.reverse()
            elif fault == 'missing-contribution': c.inputs.pop(); c._input_irs.pop()
            elif fault == 'saved-primal': c.inputs += fw.inputs; c._input_irs += fw._input_irs
            elif fault == 'signature': m.setattr(fw.ir, 'signature', 'torch.clone')
            elif fault in ('times', 'bool-times'):
                m.setitem(fw.ir.kwargs, 'times', 3 if fault == 'times' else True)
            elif fault in ('raw-grad-metadata', 'raw-input-grad'):
                t = (fw.ir.outputs() if fault == 'raw-grad-metadata' else fw.ir.inputs())[0]
                m.setattr(t, '_grad', None)
            elif fault == 'raw-order': m.setattr(c.ir, 'inputs', lambda: tuple(reversed(c._input_irs)))
            elif fault in ('version', 'bool-version', 'initial'):
                c.inputs[0] = c.inputs[0]._replace(v={'version': 99, 'bool-version': True, 'initial': 0}[fault])
            elif fault == 'owner': c.inputs[0] = c.inputs[0]._replace(rank=c.rank+1)
            elif fault == 'cid': c.node = c.node._replace(cid=c.node.cid+1)
            elif fault == 'fw-version': fw.outputs[0] = fw.outputs[0]._replace(v=99)
            elif fault.startswith('source-suffix'):
                suffix = clone(c); suffix.outputs = [c.inputs[0] if fault.endswith('input') else c.outputs[0]]
                cells.append(suffix)
            else:
                j = good['contributions'][0]['source_index']
                duplicate = clone(cells[j]); cells.insert(i, duplicate); i += 1
            with pytest.raises(ValueError, match='bw-multiref'):
                bind(cells, i)
        assert bind(original, good['source_index']) == good


def test_read_all_ranks_nonterminal_same_final_store_ordered_sum(worlds):
    render = api('Verdict.runtime_backward_multiref_reads', 'render_read')
    for view, cells, snapshot, i, order, label in selected(worlds):
        text, row = render(view, cells, snapshot, i, order, label)
        k = order['source_to_execution'][i]
        assert i < len(cells)-1 and k < len(cells)-1
        assert row['execution_index'] == k
        assert row['input_refs'] == [list(r) for r in cells[i].inputs]
        assert row['input_tids'] == [t.tid for t in view.node_inputs(cells[i].node)]
        assert row['operand_nonwrite_source_indices'] == order['execution_to_source'][k:]
        assert row['output_nonwrite_source_indices'] == order['execution_to_source'][k+1:]
        tids = '[' + ', '.join(map(str, row['input_tids'])) + ']'
        assert f'tensorSum ({tids}.map t)' in text
        assert f'{label}InputRequests.take {k}' in text
        assert f'{label}InputRequests.drop {k+1}' in text
        assert 'SourceBWMultirefRead.bw_multiref_value_of_split' in text
        assert 'alias' not in text and 'identity' not in text
        assert len(row['contribution_writers']) == len(cells[i].ir.inputs())
        assert row['lean_helper_verified'] is False
        assert all(row[x] is False for x in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.mark.parametrize('fault', ['call', 'export', 'rank', 'writer-order', 'writer-missing',
    'fw-writer-missing', 'duplicate', 'execution-order', 'inverse-order', 'params',
    'lowered-order', 'execution-suffix-input', 'execution-suffix-output'])
def test_renderer_translation_mutations_have_accepted_predecessors(worlds, monkeypatch, fault):
    from Verdict import graph_to_lean
    from trainverify.backward_multiref_authority import bind
    render = api('Verdict.runtime_backward_multiref_reads', 'render_read')
    for view, cells, snapshot, i, order, label in selected(worlds):
        _, good = render(view, cells, snapshot, i, order, label)
        source = copy.deepcopy(snapshot); execution = copy.deepcopy(order)
        row = next(w for w in source['writers'] if w['export_id'] == good['bw_writer'])
        with monkeypatch.context() as m:
            if fault == 'call': row['ref']['call_instance'] += 1
            elif fault == 'export': row['export_id'] = 'wrong'
            elif fault == 'rank': row['ref']['runtime_rank'] += 1
            elif fault == 'writer-order': row['inputs'].reverse()
            elif fault.endswith('writer-missing'):
                key = good['fw_writer'] if fault.startswith('fw') else good['contribution_writers'][0]
                source['writers'] = [w for w in source['writers'] if w['export_id'] != key]
            elif fault == 'duplicate': source['writers'].append(copy.deepcopy(row))
            elif fault == 'execution-order': execution['execution_to_source'].reverse()
            elif fault == 'inverse-order': execution['source_to_execution'][i] += 1
            elif fault == 'params': m.setattr(graph_to_lean, '_get_node_params', lambda *a, **k: [False])
            elif fault == 'lowered-order':
                original = view.node_inputs
                m.setattr(view, 'node_inputs', lambda n: list(reversed(original(n))) if n == cells[i].node else original(n))
            else:
                original = view.node_outputs
                suffix = cells[order['execution_to_source'][-1]].node
                tensor = (view.node_inputs if fault.endswith('input') else view.node_outputs)(cells[i].node)[0]
                m.setattr(view, 'node_outputs', lambda n: original(n) + [tensor] if n == suffix else original(n))
            bind(cells, i)
            with pytest.raises(ValueError): render(view, cells, source, i, execution, label)
        assert render(view, cells, snapshot, i, order, label)[1] == good
