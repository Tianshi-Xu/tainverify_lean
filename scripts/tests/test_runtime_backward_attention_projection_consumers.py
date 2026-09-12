"""Only the original Add.right -> AG -> attention projection -> first view."""
import importlib
import importlib.util
import os
from pathlib import Path

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_attention_projection_consumers'), 'missing attention projection consumer'
    return importlib.import_module('Verdict.runtime_backward_attention_projection_consumers')


@pytest.fixture(scope='module')
def result(worlds):
    p = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    module = api()
    original = module.residual_join_consumers.render
    calls = []
    def observed(*args):
        calls.append(args)
        return original(*args)  # instrument, never replace the real source result
    with pytest.MonkeyPatch.context() as m:
        m.setattr(module.residual_join_consumers, 'render', observed)
        rendered = module.render(worlds, str(p/'capture.pkl'), str(p/'code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    assert len(calls) == 1 and calls[0][0] is worlds
    return rendered


def test_actual_right_gather_linear_both_outputs_keep_left_stop_at_view(worlds, result):
    text, detail = result
    assert len(detail['reads']) == 5
    assert len(detail['collective_reads']) == 4
    assert [r['params'] for r in detail['collective_reads']] == [[2]] * 4
    assert [r['ranks'] for r in detail['collective_reads']] == [[0, 1], [0, 1], [2, 3], [2, 3]]
    assert detail['collective_source'].count('#print axioms') == 4
    assert detail['linear_source'].count('#print axioms') == 10
    assert text.count('#print axioms') == 14
    assert 'SourceBWViewRead' not in text
    assert 'SourceBWLinearRead.bw_linear_dx_value_of_split' in detail['linear_source']
    assert 'SourceBWLinearRead.bw_linear_dw_value_of_split' in detail['linear_source']
    assert [r['linear']['source_index'] for r in detail['reads']] == [73, 124, 360, 596, 832]
    for row in detail['reads']:
        world = next(w for w in worlds if w[-1] == row['world'])
        view, cells, _, order, label = world
        prior, lr, grad = row['prior'], row['linear'], row['gradient']
        ar = prior['add_read']
        assert lr['input_refs'][0] == grad['output_ref']
        assert lr['input_tids'][0] == grad['output_tid']
        assert lr['source_contract']['saved_inputs'] == lr['input_refs'][1:]
        assert row['retained']['output_ref'] == ar['output_refs'][0]
        assert row['retained']['expression'] == prior['add_expressions'][0]
        assert row['retained']['theorem'] == prior['add_theorems'][0]
        assert row['retained']['port'] == 0
        assert len(row['linear_expressions']) == len(row['linear_theorems']) == 2
        for tid, rhs, name in zip(lr['output_tids'], row['linear_expressions'], row['linear_theorems'], strict=True):
            assert f't {tid} = {rhs} := by' in text
            assert f'#print axioms {name}' in text
            assert grad['expression'] in rhs
        frontier = row['view_frontier']
        vc = cells[frontier['source_index']]
        assert vc.opname.name == 'BW_view'
        assert frontier['input_ref'] == lr['output_refs'][0] == list(vc.inputs[0])
        assert frontier['predecessor']['theorem'] == row['linear_theorems'][0]
        assert frontier['execution_index'] > lr['execution_index'] > grad['read']['execution_index']
        if label == 'pm':
            cr = grad['read']
            scope = view.collective_scopes[cells[cr['source_index']].node]
            assert cr['opname'] == 'AllGatherPrim' and cr['output_port'] == 1
            assert cr['params'] == list(scope.params)
            assert [b['output_ref'] for b in grad['contributions']] == cr['input_refs']
            assert [b['output_tid'] for b in grad['contributions']] == cr['input_tids']
            assert [b['read'] for b in grad['contributions']] == cr['predecessors']
            assert cr['ranks'] == list(scope.ranks)
            for b in grad['contributions']:
                assert b['port'] == 1 and b['expression'] in grad['expression']
                assert b['theorem'] + ' s t h' in text
        else:
            assert grad['output_ref'] == ar['output_refs'][1]
            assert grad['expression'] == prior['add_expressions'][1]
            assert grad['theorem'] == prior['add_theorems'][1]
        print(label, ar['source_index'], grad['source_index'], lr['source_index'], frontier['source_index'], grad['read'].get('params'), frontier['input_ref'])
    assert all(detail[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.fixture(scope='module')
def bound_worlds(worlds, result):
    from Verdict import graph_to_lean as compiler
    p = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    fresh = compiler._load_chunk_source(str(p/'capture.pkl'), str(p/'code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    return [(v, c, fresh if label == 'pm' else s, o, label) for v, c, s, o, label in worlds]


@pytest.mark.parametrize('fault', ['params', 'peer-order', 'local-index', 'port'])
def test_linear_rejects_changed_gather_binding(bound_worlds, result, fault):
    import copy
    row = next(r for r in result[1]['reads'] if r['world'] == 'pm')
    world = next(w for w in bound_worlds if w[-1] == 'pm')
    grad = copy.deepcopy(row['gradient'])
    if fault == 'params': grad['read']['params'] = [1]
    elif fault == 'peer-order': grad['read']['ranks'].reverse()
    elif fault == 'local-index': grad['read']['local_index'] = 1
    else: grad['read']['output_port'] = 0
    with pytest.raises(ValueError):
        api()._linear(world, row['linear']['source_index'], grad, row['prior'])


@pytest.mark.parametrize('fault', ['dims', 'ranks', 'missing-peer', 'duplicate-peer', 'right-port', 'saved-ref', 'ctx', 'source-failure'])
def test_narrow_gather_fresh_context_and_complete_peers(bound_worlds, result, monkeypatch, fault):
    import copy
    from dataclasses import replace
    row = next(r for r in result[1]['reads'] if r['world'] == 'pm')
    view, cells, snapshot, order, label = next(w for w in bound_worlds if w[-1] == 'pm')
    index = row['gradient']['source_index']
    node = cells[index].node
    prior = copy.deepcopy([r['prior'] for r in result[1]['reads']])
    peer = row['gradient']['read']['predecessors'][0]['source_index']
    selected = next(p for p in prior if p['world'] == 'pm' and p['add_read']['source_index'] == peer)
    source = snapshot
    if fault == 'dims':
        monkeypatch.setitem(view.collective_scopes, node, replace(view.collective_scopes[node], params=(1,)))
    elif fault == 'ranks':
        monkeypatch.setitem(view.collective_scopes, node, replace(view.collective_scopes[node], ranks=tuple(reversed(view.collective_scopes[node].ranks))))
    elif fault == 'missing-peer': prior.remove(selected)
    elif fault == 'duplicate-peer': prior.append(copy.deepcopy(selected))
    elif fault == 'right-port': selected['add_read']['output_refs'][1] = selected['add_read']['output_refs'][0]
    elif fault == 'saved-ref': selected['add_read']['input_refs'][1][-1] += 1
    elif fault == 'ctx':
        source = copy.deepcopy(snapshot)
        writer = next(w for w in source['writers'] if w['export_id'] == row['gradient']['read']['source_writer'])
        writer['adapter']['backward_context']['runtime']['backward']['kwargs']['dim'] = 1
    else:
        def unavailable(*args):
            raise ValueError('source unavailable')
        monkeypatch.setattr(api().compiler, '_load_chunk_source', unavailable)
    with pytest.raises(ValueError):
        api()._gather((view, cells, source, order, label), index, prior)


@pytest.mark.parametrize('fault', ['port', 'bool-port', 'version', 'tid', 'saved-order', 'output-order', 'writer', 'execution', 'left-ref', 'first-view'])
@pytest.mark.parametrize('label', ['sm', 'pm'])
def test_narrow_linear_rebinds_saved_weight_ports_and_boundary(bound_worlds, result, monkeypatch, fault, label):
    import copy
    row = next(r for r in result[1]['reads'] if r['world'] == label)
    view, cells, snapshot, order, label = next(w for w in bound_worlds if w[-1] == label)
    index = row['linear']['source_index']
    grad, prior = copy.deepcopy((row['gradient'], row['prior']))
    source, schedule = snapshot, order
    if fault == 'port': grad['port'] = 1 - grad['port']
    elif fault == 'bool-port': grad['port'] = True
    elif fault == 'version': grad['output_ref'][-1] += 1
    elif fault == 'tid': grad['output_tid'] += 1
    elif fault == 'saved-order':
        monkeypatch.setattr(cells[index], 'inputs', [cells[index].inputs[0], *reversed(cells[index].inputs[1:])])
    elif fault == 'output-order': monkeypatch.setattr(cells[index], 'outputs', list(reversed(cells[index].outputs)))
    elif fault == 'writer':
        source = copy.deepcopy(snapshot)
        writer = next(w for w in source['writers'] if w['export_id'] == row['linear']['bw_writer'])
        writer['ref']['call_instance'] += 1
    elif fault == 'execution':
        schedule = copy.deepcopy(order)
        schedule['source_to_execution'][index] += 1
    elif fault == 'left-ref': prior['add_read']['output_refs'][0][-1] += 1
    else:
        vc = cells[row['view_frontier']['source_index']]
        refs = copy.deepcopy(vc.inputs)
        refs[0] = tuple([*refs[0][:-1], refs[0][-1] + 1])
        monkeypatch.setattr(vc, 'inputs', refs)
    with pytest.raises(ValueError):
        api()._linear((view, cells, source, schedule, label), index, grad, prior)
