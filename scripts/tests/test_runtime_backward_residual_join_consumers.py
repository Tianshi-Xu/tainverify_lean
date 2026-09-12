"""Bounded original residual join: actual capture, no downstream traversal."""
import importlib
import importlib.util
import os
from pathlib import Path

import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_residual_join_consumers'), 'missing original residual join consumer'
    return importlib.import_module('Verdict.runtime_backward_residual_join_consumers')


@pytest.fixture(scope='module')
def result(worlds):
    p = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    return api().render(worlds, str(p/'capture.pkl'), str(p/'code/_parallel_modules/genmodel/model/gpt/GPT/_'))


def test_actual_complete_ordered_joins_and_direct_add_outputs(worlds, result):
    text, detail = result
    assert len(detail['reads']) == 5
    assert len(detail['collective_reads']) == 4
    assert detail['collective_source'].count('#print axioms') == 4
    assert detail['add_source'].count('#print axioms') == 10
    assert text.count('#print axioms') == 19
    assert 'SourceBWMultirefRead' not in text  # reference the accepted root, never duplicate it
    for row in detail['reads']:
        world = next(w for w in worlds if w[-1] == row['world'])
        view, cells, _, order, label = world
        merge = row['merge_read']
        assert merge['input_refs'] == [list(r) for r in cells[merge['source_index']].inputs]
        assert [b['output_ref'] for b in row['branches']] == merge['input_refs']
        assert [b['output_tid'] for b in row['branches']] == merge['input_tids']
        assert row['join_expression'] == 'tensorSum [' + ', '.join('(' + b['expression'] + ')' for b in row['branches']) + ']'
        assert row['add_read']['input_refs'][0] == merge['output_refs'][0]
        assert row['add_read']['input_tids'][0] == merge['output_tids'][0]
        assert merge['execution_index'] < row['add_read']['execution_index']
        assert len(row['add_expressions']) == len(row['add_theorems']) == 2
        for tid, rhs in zip(row['add_read']['output_tids'], row['add_expressions'], strict=True):
            assert f't {tid} = {rhs} := by' in text
        if label == 'pm':
            assert row['main']['read']['opname'] == 'AllToAllPrim'
            assert row['main']['read']['params'] != row['main']['read']['raw_params']
            for peer in row['main']['contributions']:
                assert peer['expression'] in row['main']['expression']
        else:
            assert row['main']['kind'] == 'layernorm'
        print(label, merge['source_index'], merge['input_tids'], row['add_read']['source_index'])
    assert all(detail[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.fixture(scope='module')
def bound_worlds(worlds, result):
    from Verdict import graph_to_lean as compiler
    p = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']) / 'p2-r4'
    fresh = compiler._load_chunk_source(str(p/'capture.pkl'), str(p/'code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    return [(v, c, fresh if label == 'pm' else s, o, label) for v, c, s, o, label in worlds]


@pytest.mark.parametrize('fault', ['order', 'missing-main', 'missing-retained', 'duplicate', 'extra', 'port', 'bool-port', 'tid', 'version', 'writer'])
def test_narrow_join_rejects_incomplete_or_wrong_original_branches(bound_worlds, result, fault):
    import copy
    for original in result[1]['reads']:
        world = next(w for w in bound_worlds if w[-1] == original['world'])
        branches = copy.deepcopy(original['branches'])
        if fault == 'order': branches.reverse()
        elif fault == 'missing-main': branches = [b for b in branches if b['kind'].startswith('retained')]
        elif fault == 'missing-retained': branches = [b for b in branches if not b['kind'].startswith('retained')]
        elif fault == 'duplicate': branches[1] = copy.deepcopy(branches[0])
        elif fault == 'extra': branches.append(copy.deepcopy(branches[0]))
        elif fault == 'port': branches[0]['port'] = 1
        elif fault == 'bool-port': branches[0]['port'] = False
        elif fault == 'tid': branches[0]['output_tid'] += 1
        elif fault == 'version': branches[0]['output_ref'][-1] += 1
        else: branches[0]['source_index'] += 1
        with pytest.raises(ValueError, match='bw-residual-join'):
            api()._join(world, original['merge_read']['source_index'], branches)


@pytest.mark.parametrize('fault', ['source-order', 'missing-port', 'shape', 'writer', 'execution'])
def test_narrow_join_fresh_source_authority_not_previous_rows(bound_worlds, result, monkeypatch, fault):
    import copy
    for row in result[1]['reads']:
        v, cells, snapshot, order, label = next(w for w in bound_worlds if w[-1] == row['world'])
        index = row['merge_read']['source_index']
        cell = cells[index]
        source, schedule = copy.deepcopy(snapshot), copy.deepcopy(order)
        with monkeypatch.context() as m:
            if fault == 'source-order': m.setattr(cell, 'inputs', list(reversed(cell.inputs)))
            elif fault == 'missing-port': m.setattr(cell, 'inputs', list(cell.inputs[:-1]))
            elif fault == 'shape':
                irs = copy.deepcopy(cell._input_irs)
                irs[0]._shape = tuple(d + 1 for d in irs[0].shape)
                m.setattr(cell, '_input_irs', irs)
            elif fault == 'writer':
                writer = next(w for w in source['writers'] if w['export_id'] == row['merge_read']['bw_writer'])
                writer['ref']['call_instance'] += 1
            else: schedule['source_to_execution'][index] += 1
            with pytest.raises(ValueError):
                api()._join((v, cells, source, schedule, label), index, row['branches'])


@pytest.mark.parametrize('fault', ['cotangent-port', 'output-order'])
def test_direct_add_rebinds_both_original_ports(bound_worlds, result, monkeypatch, fault):
    for row in result[1]['reads']:
        world = next(w for w in bound_worlds if w[-1] == row['world'])
        cell = world[1][row['add_read']['source_index']]
        with monkeypatch.context() as m:
            if fault == 'cotangent-port':
                m.setattr(cell, 'inputs', [cell.inputs[1], cell.inputs[0], *cell.inputs[2:]])
            else:
                m.setattr(cell, 'outputs', list(reversed(cell.outputs)))
            with pytest.raises(ValueError):
                api()._join(world, row['merge_read']['source_index'], row['branches'])


@pytest.mark.parametrize('fault', ['dims', 'peer-order', 'missing-peer', 'wrong-ln-port'])
def test_narrow_main_rechecks_real_inverse_aa_and_all_ln_peers(bound_worlds, result, monkeypatch, fault):
    import copy
    from dataclasses import replace
    world = next(w for w in bound_worlds if w[-1] == 'pm')
    view, cells, _, _, _ = world
    mains = [r['main'] for r in result[1]['reads'] if r['world'] == 'pm']
    # These are accepted real upstream reads/RHSs from the single full render,
    # not synthesized capture rows or mocked renderers.
    peers = {b['source_index']: b for main in mains for b in main['contributions']}
    prior = [dict(world='pm', layernorm=copy.deepcopy(b['read']),
                  layernorm_expressions=[b['expression']], layernorm_consumers=[b['theorem']])
             for b in peers.values()]
    for main in mains:
        changed = copy.deepcopy(prior)
        node = cells[main['source_index']].node
        scope = view.collective_scopes[node]
        with monkeypatch.context() as m:
            if fault == 'dims':
                m.setitem(view.collective_scopes, node, replace(scope, params=tuple(reversed(scope.params))))
            elif fault == 'peer-order':
                m.setitem(view.collective_scopes, node, replace(scope, ranks=tuple(reversed(scope.ranks))))
            else:
                peer_index = main['contributions'][0]['source_index']
                if fault == 'missing-peer': changed = [p for p in changed if p['layernorm']['source_index'] != peer_index]
                else:
                    p = next(p for p in changed if p['layernorm']['source_index'] == peer_index)
                    p['layernorm']['output_refs'][0] = p['layernorm']['output_refs'][1]
            with pytest.raises(ValueError): api()._main(world, main['source_index'], changed)
