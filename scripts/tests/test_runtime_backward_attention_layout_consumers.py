"""Original attention layout chain; no cross-world gradient/refinement claim."""
import copy
import importlib
import importlib.util
import os
from pathlib import Path

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_attention_layout_consumers'), 'missing attention layout consumer'
    return importlib.import_module('Verdict.runtime_backward_attention_layout_consumers')


def test_module_exists():
    api()


@pytest.fixture(scope='module')
def result(worlds):
    module = api()
    root = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    original = module.projection.render
    calls = []
    def observed(*args):
        calls.append(args)
        return original(*args)
    with pytest.MonkeyPatch.context() as m:
        m.setattr(module.projection, 'render', observed)
        rendered = module.render(worlds, str(root/'capture.pkl'), str(root/'code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    assert len(calls) == 1 and calls[0][0] is worlds
    return rendered


def test_actual_complete_two_exchange_waves_stop_at_transpose(worlds, result):
    text, detail = result
    assert len(detail['reads']) == 5
    assert text.count('#print axioms') == 18
    for field, count in [('collective_source', 8), ('contiguous_source', 5), ('transpose_source', 5)]:
        assert detail[field].count('#print axioms') == count
    assert [r['view_read']['source_index'] for r in detail['reads']] == [74, 125, 361, 597, 833]
    assert [r['contiguous_read']['source_index'] for r in detail['reads']] == [75, 127, 363, 599, 835]
    assert [r['transpose_read']['source_index'] for r in detail['reads']] == [76, 129, 365, 601, 837]
    waves = [[], [], [], []]
    for row in detail['reads']:
        world = next(w for w in worlds if w[-1] == row['world'])
        view, cells, _, order, label = world
        prior = row['prior']
        assert row['view_read'] is prior['view_read']
        assert row['view_expression'] == prior['expression']
        assert row['view_theorems'] == prior['theorems']
        assert prior['producer']['retained']['port'] == 0
        assert prior['producer']['retained']['expression'] == prior['producer']['prior']['add_expressions'][0]
        assert len(prior['producer']['linear_expressions']) == 2
        lr = prior['producer']['linear']
        assert lr['input_refs'][1:] == lr['source_contract']['saved_inputs']
        stages = [('before', 'view_read', 'view_expression', 0), ('after', 'contiguous_read', 'contiguous_expression', 2)]
        for key, readkey, exprkey, wave in stages:
            branch = row[key]
            if label == 'sm':
                assert branch['read'] == row[readkey]
                assert branch['expression'] == row[exprkey]
                continue
            cr = branch['read']
            scope = view.collective_scopes[cells[cr['source_index']].node]
            assert cr['opname'] == 'AllToAllPrim' and cr['output_port'] == 0
            assert cr['params'] == list(scope.params)
            assert cr['ranks'] == list(scope.ranks)
            assert cr['local_index'] == scope.local_index
            assert [b['read'] for b in branch['contributions']] == cr['predecessors']
            assert [b['output_ref'] for b in branch['contributions']] == cr['input_refs']
            assert [b['output_tid'] for b in branch['contributions']] == cr['input_tids']
            expected = f'AllToAllSourceFaithful.tensor {len(cr["ranks"])} {cr["local_index"]} {cr["params"][0]} {cr["params"][1]}'
            assert branch['expression'].startswith(expected + ' [')
            for b in branch['contributions']:
                peer = next(r for r in detail['reads'] if r['world'] == label and r[readkey]['source_index'] == b['source_index'])
                assert b['expression'] == peer[exprkey]
                assert b['theorem'] + ' s t h' in text
                assert order['source_to_execution'][b['source_index']] < cr['execution_index']
            waves[wave].append(text.index('theorem ' + branch['theorem'] + ' '))
        for key, upstream, wave in [('contiguous', 'before', 1), ('transpose', 'after', 3)]:
            read = row[key + '_read']
            rhs = row[key + '_expression']
            theorem, = row[key + '_theorems']
            assert read['input_refs'][0] == row[upstream]['output_ref']
            assert read['input_tids'][0] == row[upstream]['output_tid']
            assert f't {read["output_tids"][0]} = {rhs} := by' in text
            assert row[upstream]['theorem'] + ' s t h' in text
            assert row[upstream]['read']['execution_index'] < read['execution_index']
            waves[wave].append(text.index('theorem ' + theorem + ' '))
        assert row['contiguous_expression'] == row['before']['expression']
        a, b = row['transpose_read']['params']
        assert row['transpose_expression'] == f'transposeAxes {a} {b} ({row["after"]["expression"]})'
    assert all(max(a) < min(b) for a, b in zip(waves, waves[1:]))
    assert all(detail[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))
    assert '(h : smDenoteWithInputs s = some t)' in text
    assert '(h : pmDenoteWithInputs s = some t)' in text
    assert 'BW_matmul' not in text and 'houtput' not in text


@pytest.fixture(scope='module')
def bound_worlds(worlds, result):
    from Verdict import graph_to_lean as compiler
    root = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    fresh = compiler._load_chunk_source(str(root/'capture.pkl'), str(root/'code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    return [(v, c, fresh if label == 'pm' else s, o, label) for v, c, s, o, label in worlds]


@pytest.mark.parametrize('stage', ['view', 'contiguous'])
@pytest.mark.parametrize('fault', ['missing-peer', 'port', 'ref', 'dims', 'ranks', 'local-index'])
def test_exchange_rejects_incomplete_or_changed_original_boundary(bound_worlds, result, monkeypatch, stage, fault):
    from dataclasses import replace
    row = next(r for r in result[1]['reads'] if r['world'] == 'pm')
    world = next(w for w in bound_worlds if w[-1] == 'pm')
    view, cells, snapshot, order, label = world
    key = 'before' if stage == 'view' else 'after'
    index = row[key]['source_index']
    peers = copy.deepcopy(row[key]['contributions'])
    if fault == 'missing-peer': peers.pop()
    elif fault == 'port': peers[0]['port'] = True
    elif fault == 'ref': peers[0]['output_ref'][-1] += 1
    else:
        node = cells[index].node
        scope = view.collective_scopes[node]
        changes = {'dims': {'params': tuple(reversed(scope.params))},
                   'ranks': {'ranks': tuple(reversed(scope.ranks))},
                   'local-index': {'local_index': len(scope.ranks)}}[fault]
        monkeypatch.setitem(view.collective_scopes, node, replace(scope, **changes))
    with pytest.raises(ValueError):
        api()._exchange(world, index, peers, stage)


@pytest.mark.parametrize('stage', ['contiguous', 'transpose'])
@pytest.mark.parametrize('fault', ['port', 'ref', 'tid', 'execution', 'params'])
def test_unary_rejects_changed_gradient_and_cannot_skip_second_aa(bound_worlds, result, stage, fault):
    row = next(r for r in result[1]['reads'] if r['world'] == 'pm')
    world = next(w for w in bound_worlds if w[-1] == 'pm')
    grad = copy.deepcopy(row['before' if stage == 'contiguous' else 'after'])
    if fault == 'port': grad['port'] = 1
    elif fault == 'ref': grad['output_ref'][-1] += 1
    elif fault == 'tid': grad['output_tid'] += 1
    elif fault == 'execution': grad['read']['execution_index'] += 1
    else: grad['read']['params'].reverse()
    with pytest.raises(ValueError):
        api()._unary(world, row[stage + '_read']['source_index'], grad, stage)


def test_transpose_rejects_direct_contiguous_bypass(bound_worlds, result):
    row = next(r for r in result[1]['reads'] if r['world'] == 'pm')
    world = next(w for w in bound_worlds if w[-1] == 'pm')
    grad = api()._branch(row['contiguous_read'], 0, row['contiguous_expression'], row['contiguous_theorems'][0], 'contiguous')
    with pytest.raises(ValueError):
        api()._unary(world, row['transpose_read']['source_index'], grad, 'transpose')
