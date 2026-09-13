"""Canonical wiring and portable replay, not saved-capture/kernel acceptance."""
import copy
import importlib
import re

import pytest

from Verdict import runtime_world as world_api
from Verdict.runtime_binder_source import expand as expand_binders
from Verdict.runtime_read_source import expand as expand_reads
from scripts.tests import test_runtime_frontier_projection_entry as projection
from scripts.tests import test_runtime_frontier_post_transpose_entry as post


STAGE = 'frontier_middle_exchange_values'
PREDECESSOR = post.STAGE


def attachment(monkeypatch, **kwargs):
    monkeypatch.setattr(projection, 'STAGES', tuple(dict.fromkeys(
        (*projection.STAGES, PREDECESSOR, STAGE))))
    return projection.attachment(monkeypatch, **kwargs)


def test_middle_full_fragment_detail_six_original_objects_and_order(monkeypatch):
    result, calls, texts, details, six, _ = attachment(monkeypatch)
    selected = [(key, args) for key, args in calls if key in (PREDECESSOR, STAGE)]
    assert [key for key, _ in selected] == [PREDECESSOR, STAGE], 'middle exchange not attached after post-transpose'
    for key, args in selected:
        assert len(args) == 6 and all(a is b for a, b in zip(args, six, strict=True))
        assert result.receipt[key] is details[key]
        assert result.lean.count(texts[key]) == 1
    assert result.lean.index(texts[PREDECESSOR]) < result.lean.index(texts[STAGE])
    assert list(result.receipt).index(PREDECESSOR) < list(result.receipt).index(STAGE)
    assert all(result.receipt[flag] is False for flag in projection.FLAGS)
    assert all(result.receipt[STAGE][flag] is False for flag in projection.FLAGS)
    assert result.receipt['proof_bundle']['kernel_checked'] is False


# These adjacent helpers already belong to the accepted earlier pipeline.
HELPERS = ('denote.SourceRank4ReverseExchange', 'denote.SourceRank4MiddleExchange')
READ_HELPER = 'denote.SourcePrimitiveRead'


def test_middle_reuses_existing_exact_helper_inventory(monkeypatch):
    result, *_ = attachment(monkeypatch)
    imports = result.receipt['proof_bundle']['modules'][-1]['imports']
    assert [name for name in imports if name in HELPERS] == list(HELPERS)
    assert all(imports.count(name) == result.lean.count(f'import {name}\n') == 1
               for name in (*HELPERS, READ_HELPER))


@pytest.mark.parametrize('helper', HELPERS)
@pytest.mark.parametrize('fault', ('missing', 'duplicate', 'unknown', 'reordered'))
def test_incorrect_helper_inventory_rejects(monkeypatch, helper, fault):
    result, *_ = attachment(monkeypatch)
    line = f'import {helper}\n'
    replacement = {'missing': '', 'duplicate': line + line,
                   'unknown': 'import denote.UnapprovedMiddleExchangeHelper\n',
                   'reordered': ''}[fault]
    bad = result.lean.replace(line, replacement)
    if fault == 'reordered':
        bad += line
    with pytest.raises(ValueError, match='import membership mismatch'):
        world_api._proof_bundle(bad, result.supporting_sources)


def test_empty_stage_preserves_full_detail_without_appending_text(monkeypatch):
    detail = dict(reads=[], units=[], frontier_units=[dict(source='unchanged',
        facts_theorem='originalFullFacts', history=['original-source'])],
        retained_units=[], deferred_units=[], **dict.fromkeys(projection.FLAGS, False))
    result, _, texts, details, _, _ = attachment(monkeypatch, fragments={
        STAGE: ('-- zero-output stage must not be appended\n', detail)})
    assert result.receipt[STAGE] is detail
    assert texts[STAGE] not in result.lean
    assert result.receipt[PREDECESSOR] is details[PREDECESSOR]
    assert all(result.lean.count(f'import {name}\n') == 1 for name in HELPERS)


def test_no_initial_goals_keeps_entry_bytes_and_never_calls_stage(monkeypatch):
    result, calls, _, _, _, world = attachment(monkeypatch, bound=dict(relations=[]))
    assert result.lean == world.lean and calls == []
    assert 'proof_bundle' not in result.receipt


def test_no_input_feed_never_calls_stage_or_adds_helpers(monkeypatch):
    result, calls, texts, _, _, _ = attachment(monkeypatch, input_feed=False)
    assert calls == [] and texts[STAGE] not in result.lean
    assert all(name not in result.lean for name in HELPERS)


def test_middle_counts_toward_unchanged_strict_total_byte_cap(monkeypatch):
    from Verdict.graph_to_lean import GENERATED_LEAN_SOURCE_LIMIT
    result, *_ = attachment(monkeypatch)
    size = len(result.lean.encode()) + sum(len(t.encode()) for t in result.supporting_sources.values())
    assert size < GENERATED_LEAN_SOURCE_LIMIT == 2_500_000
    padded = result.lean + '-' * (GENERATED_LEAN_SOURCE_LIMIT - size - 1)
    world_api._proof_bundle(padded, result.supporting_sources)
    with pytest.raises(ValueError, match='2500000 bytes total'):
        world_api._proof_bundle(padded + '-', result.supporting_sources)


@pytest.fixture(scope='module')
def public_chain():
    """Real portable TP=3 chain; the handed-off fixture has a divisible head factor.

    This is not the actual TP=2 saved source: it emits six, not four, PM reads.
    Only subsequent attachment is replayed; generation uses real public renderers.
    """
    from scripts.tests.test_runtime_frontier_middle_exchange_values import prepared
    args = prepared()
    # Include the authentic earlier carry declaration, not just the QKV tail.
    earlier = tuple('frontier_' + name + '_values' for name in (
        'alias_exchange', 'layernorm', 'linear', 'gelu', 'next_linear',
        'sequence_hidden', 'add', 'next_alias_exchange', 'next_layernorm'))
    keys = (*earlier, projection.PREDECESSOR, *projection.STAGES, PREDECESSOR, STAGE)
    fragments = {}; calls = []
    with pytest.MonkeyPatch.context() as live:
        for key in keys:
            module = importlib.import_module('Verdict.runtime_' + key)
            original = module.render
            def render(*six, _key=key, _original=original):
                assert len(six) == 6 and all(a is b for a, b in zip(six, args, strict=True))
                calls.append(_key)
                pair = _original(*six)
                fragments[_key] = pair
                return pair
            live.setattr(module, 'render', render)
        importlib.import_module('Verdict.runtime_' + STAGE).render(*args)
    assert calls == list(reversed(keys))
    return args, fragments


def test_real_public_complete_fragment_detail_order_and_suffix_replay(monkeypatch, public_chain):
    args, fragments = public_chain
    snapshot = copy.deepcopy(fragments)
    result, *_ = attachment(monkeypatch, fragments=fragments)
    canonical = expand_binders(expand_reads(result.lean))
    positions = []
    for key, (text, detail) in fragments.items():
        assert result.receipt[key] is detail
        assert canonical.count(text) == 1
        positions.append(canonical.index(text))
        for row in (*detail['reads'], *detail['units']):
            name = row['theorem']
            assert len(re.findall(r'^theorem ' + re.escape(name) + r'(?=\s)', canonical, re.M)) == 1
            assert canonical.count(f'#print axioms {name}\n') == 1
        assert all(detail[flag] is False for flag in projection.FLAGS)
    assert positions == sorted(positions) and fragments == snapshot
    final = fragments[STAGE][1]
    closed = fragments[PREDECESSOR][1]
    assert len(final['frontier_units']) == len(closed['frontier_units']) == 8
    assert len(final['units']) == 2
    expected_reads = {tuple(step['node']) for row in final['units'] for step in row['local_steps']}
    assert len(final['reads']) == len(expected_reads)
    assert {tuple(row['node']) for row in final['reads']} == expected_reads
    assert len(final['reads']) == sum(len(row['ranks']) for row in final['units'])
    for row in final['reads']:
        assert row['world'] == 'pm' and row['op'] == 'AllToAllPrim'
        assert row['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][row['execution_index']:]
        step = next(s for unit in final['units'] for s in unit['local_steps'] if tuple(s['node']) == tuple(row['node']))
        assert row['params'] == [step['gather_axis'], step['split_axis']]
    assert all(result.receipt[flag] is False for flag in projection.FLAGS)
    assert result.receipt['proof_bundle']['kernel_checked'] is False
    assert all(result.lean.count(f'import {name}\n') == 1 for name in HELPERS)


def test_real_mixed_full_contracts_derive_from_source_and_keep_all_history(monkeypatch, public_chain):
    args, fragments = public_chain
    result, *_ = attachment(monkeypatch, fragments=fragments)
    canonical = expand_binders(expand_reads(result.lean))
    final = fragments[STAGE][1]; closed = fragments[PREDECESSOR][1]
    consumed = final['consumed_frontier_indices']
    assert consumed == [i for i, row in enumerate(final['frontier_units']) if any(row is u for u in final['units'])]
    retained = []; deferred = []; replicas = []; carries = []
    for i, (old, new) in enumerate(zip(closed['frontier_units'], final['frontier_units'], strict=True)):
        if i in consumed:
            assert new['input_frontier'] is old
            assert new['predecessor_facts'] == old['facts_theorem']
            assert new['source_step'] == old['source_step']
            assert new['sm_output_ref'] == old['sm_output_ref']
            assert new['input_refs'] == old['pm_output_refs']
            assert new['source_output_slot'] == old['source_output_slot']
            assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
            assert all(c['value_proved'] is False for c in new['downstream_consumers'])
        else:
            assert new is old  # complete Q/V/carry history, metadata and authority
            if old['source_step']['op'] == 'FW_multiref':
                retained.append(new); carries.append(new)
            elif old['layout'] == 'replicated_within_dp':
                retained.append(new); replicas.append(new)
                assert new['gather_axis'] is None and new['output_gather_axis'] is None
            else:
                deferred.append(new)
        global_port = next(p for p in new['source_step']['outputs']
                           if list(p['endpoint']['ref']) == new['sm_output_ref'])
        local_ports = [next(p for p in step['outputs'] if list(p['endpoint']['ref']) == ref)
                       for step, ref in zip(new['local_steps'], new['pm_output_refs'], strict=True)]
        global_shape = list(global_port['endpoint']['shape'])
        local_shape = list(local_ports[0]['endpoint']['shape'])
        assert new['global_shape'] == global_shape
        assert new['local_shape'] == local_shape
        assert all(list(p['endpoint']['shape']) == local_shape for p in local_ports)
        g = global_port['endpoint']['tid']
        tids = [p['endpoint']['tid'] for p in local_ports]
        assert g == new['sm_output_tid'] and tids == new['pm_output_tids']
        ys = '[' + ', '.join(f'q {tid}' for tid in tids) + ']'
        D, remainder = divmod(global_shape[0], local_shape[0])
        assert remainder == 0 and D == new['dimensions']['D']
        chunk = f'chunkPrimDimN 0 {D} {new["unit"]} (t {g})'
        if new['layout'] == 'replicated_within_dp':
            assert new['gather_axis'] is None
            value = f'∀ y ∈ {ys}, y = {chunk}'
        else:
            # Axis comes from the real peer partition, not a Q/K label or TID.
            axes = [axis for axis in range(len(local_shape))
                    if any(list(p['bounds'][axis]) != [0, p['parent_shape'][axis]] for p in local_ports)]
            assert axes == [new['gather_axis']]
            value = f'{chunk} = allGatherPrimDimN {axes[0]} {len(local_ports)} 0 {ys}'
        statement = canonical.split(f'theorem {new["facts_theorem"]} ', 1)[1].split(' := by', 1)[0]
        assert '(hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)' in statement
        assert '(hvalues : InitialParameterValues s p) :' in statement
        assert statement.endswith(f'    (t {g}).shape = {global_shape} ∧\n'
            f'    (∀ y ∈ {ys}, y.shape = {local_shape}) ∧\n    {value}')
    assert final['retained_units'] == retained
    assert final['deferred_units'] == deferred
    assert len(replicas) == len(carries) == len(deferred) == 2
