"""Canonical attachment tests, not whole-capture or kernel acceptance."""
import copy
import importlib
import re

import pytest

from Verdict import runtime_world as world_api
from Verdict.runtime_binder_source import expand as expand_binders
from Verdict.runtime_read_source import expand as expand_reads
from scripts.tests import test_runtime_frontier_projection_entry as projection


STAGE = 'frontier_post_transpose_values'
PREDECESSOR = projection.STAGES[-1]


def attachment(monkeypatch, **kwargs):
    # Discover the new boundary even before production attaches it (RED).
    monkeypatch.setattr(projection, 'STAGES', tuple(dict.fromkeys((*projection.STAGES, STAGE))))
    return projection.attachment(monkeypatch, **kwargs)


def test_post_transpose_full_fragment_detail_six_original_objects_and_order(monkeypatch):
    result, calls, texts, details, six, _ = attachment(monkeypatch)
    selected = [(key, args) for key, args in calls if key in (PREDECESSOR, STAGE)]
    assert [key for key, _ in selected] == [PREDECESSOR, STAGE], 'post-transpose not attached after projection transpose'
    for key, args in selected:
        assert len(args) == 6 and all(a is b for a, b in zip(args, six, strict=True))
        assert result.receipt[key] is details[key]
        assert result.lean.count(texts[key]) == 1
    assert result.lean.index(texts[PREDECESSOR]) < result.lean.index(texts[STAGE])
    assert list(result.receipt).index(PREDECESSOR) < list(result.receipt).index(STAGE)
    assert all(result.receipt[flag] is False for flag in projection.FLAGS)
    assert all(result.receipt[STAGE][flag] is False for flag in projection.FLAGS)
    assert result.receipt['proof_bundle']['kernel_checked'] is False


# Already imported by the accepted earlier pipeline: add no duplicate helpers.
HELPERS = ('denote.SourceAllGatherRead', 'denote.SourceLayoutRead',
           'denote.SourceTranspose23Unit')


def test_post_transpose_reuses_existing_exact_helper_inventory(monkeypatch):
    result, *_ = attachment(monkeypatch)
    imports = result.receipt['proof_bundle']['modules'][-1]['imports']
    for name in HELPERS:
        assert imports.count(name) == result.lean.count(f'import {name}\n') == 1
    assert [name for name in imports if name in HELPERS] == list(HELPERS)


@pytest.mark.parametrize('helper', HELPERS)
@pytest.mark.parametrize('fault', ('missing', 'duplicate', 'unknown', 'reordered'))
def test_partial_or_incorrect_helper_inventory_rejects(monkeypatch, helper, fault):
    result, *_ = attachment(monkeypatch)
    line = f'import {helper}\n'
    if fault == 'missing':
        bad = result.lean.replace(line, '')
    elif fault == 'duplicate':
        bad = result.lean.replace(line, line + line)
    elif fault == 'unknown':
        bad = result.lean.replace(line, 'import denote.UnapprovedPostTransposeHelper\n')
    else:
        bad = result.lean.replace(line, '') + line
    with pytest.raises(ValueError, match='import membership mismatch'):
        world_api._proof_bundle(bad, result.supporting_sources)


def test_zero_output_preserves_complete_carries_without_appending_text(monkeypatch):
    detail = dict(reads=[], units=[], frontier_units=[dict(source='unchanged',
        facts_theorem='originalFullFacts', history=['original-source'])],
        retained_units=[], deferred_units=[], **dict.fromkeys(projection.FLAGS, False))
    result, _, texts, details, _, _ = attachment(monkeypatch, fragments={
        STAGE: ('-- zero-output stage must not be appended\n', detail)})
    assert result.receipt[STAGE] is detail
    assert texts[STAGE] not in result.lean
    assert result.receipt[PREDECESSOR] is details[PREDECESSOR]
    # Even empty output does not drop the old pipeline's existing helper imports.
    assert all(result.lean.count(f'import {name}\n') == 1 for name in HELPERS)


def test_no_initial_goals_keeps_entry_bytes_and_never_calls_stage(monkeypatch):
    result, calls, _, _, _, world = attachment(monkeypatch, bound=dict(relations=[]))
    assert result.lean == world.lean and calls == []
    assert 'proof_bundle' not in result.receipt


def test_no_input_feed_never_calls_stage_or_adds_its_helpers(monkeypatch):
    result, calls, texts, _, _, _ = attachment(monkeypatch, input_feed=False)
    assert calls == [] and texts[STAGE] not in result.lean
    assert all(name not in result.lean for name in HELPERS)


def test_new_fragment_counts_toward_unchanged_strict_total_byte_cap(monkeypatch):
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
    """Real portable source/public chain once; no raw-capture/cache/kernel claim."""
    from scripts.tests.test_runtime_frontier_post_transpose_values import prepared
    args = prepared()
    keys = (projection.PREDECESSOR, *projection.STAGES, STAGE)
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


def test_real_public_complete_text_metadata_and_mixed_value_contract_replay(monkeypatch, public_chain):
    args, fragments = public_chain
    snapshot = copy.deepcopy(fragments)
    result, *_ = attachment(monkeypatch, fragments=fragments)
    canonical = expand_binders(expand_reads(result.lean))
    positions = []
    for key, (text, detail) in fragments.items():
        assert result.receipt[key] is detail
        assert canonical.count(text) == 1  # exact full source, not just fact names/counts
        positions.append(canonical.index(text))
        for row in (*detail['reads'], *detail['units']):
            name = row['theorem']
            assert len(re.findall(r'^theorem ' + re.escape(name) + r'(?=\s)', canonical, re.M)) == 1
        assert all(detail[flag] is False for flag in projection.FLAGS)
    assert positions == sorted(positions)
    assert fragments == snapshot
    text, final = fragments[STAGE]
    closed = fragments[PREDECESSOR][1]
    consumed = final['consumed_frontier_indices']
    assert consumed == [i for i, row in enumerate(final['frontier_units']) if any(row is u for u in final['units'])]
    expected_retained = []; expected_deferred = []; expected_reads = set()
    for i, (old, new) in enumerate(zip(closed['frontier_units'], final['frontier_units'], strict=True)):
        if i not in consumed:
            assert new is old
            target = expected_retained if old['source_step']['op'] == 'FW_multiref' else expected_deferred
            target.append(new)
            continue
        assert new['input_frontier'] is old
        assert new['predecessor_facts'] == old['facts_theorem']
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
        assert new['theorem'] == new['facts_theorem']
        for step, ref in zip(new['local_steps'], new['pm_output_refs'], strict=True):
            assert list(step['outputs'][0]['endpoint']['ref']) == ref
            expected_reads.add(('pm', tuple(step['node'])))
        if new['family'] == 'FW_transpose':
            expected_reads.add(('sm', tuple(new['source_step']['node'])))
            assert new['layout'] == 'sharded' and new['gather_axis'] == 2
        else:
            assert new['family'] == 'AllGatherPrim'
            assert new['layout'] == 'replicated_within_dp'
            assert new['gather_axis'] is None and new['output_gather_axis'] is None
            assert new['sm_output_ref'] == old['sm_output_ref']
            assert new['source_step'] == old['source_step']
        # Independently spell the full shape/local-shape/value statement for EVERY unit.
        ys = '[' + ', '.join(f'q {tid}' for tid in new['pm_output_tids']) + ']'
        chunk = f'chunkPrimDimN 0 {new["dimensions"]["D"]} {new["unit"]} (t {new["sm_output_tid"]})'
        value = (f'∀ y ∈ {ys}, y = {chunk}' if new['layout'] == 'replicated_within_dp'
                 else f'{chunk} = allGatherPrimDimN {new["gather_axis"]} {len(new["ranks"])} 0 {ys}')
        theorem = text.split(f'theorem {new["theorem"]} ', 1)[1].split(' := by', 1)[0]
        assert theorem.endswith(f'    (t {new["sm_output_tid"]}).shape = {new["global_shape"]} ∧\n'
            f'    (∀ y ∈ {ys}, y.shape = {new["local_shape"]}) ∧\n    {value}')
        assert all(c['value_proved'] is False for c in new['downstream_consumers'])
    assert final['retained_units'] == expected_retained and expected_retained
    assert final['deferred_units'] == expected_deferred and expected_deferred
    assert {('sm' if r['world'] == 'sm' else 'pm', tuple(r['node'])) for r in final['reads']} == expected_reads
    assert len(final['reads']) == len(expected_reads)
    for row in final['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
        if row['op'] == 'FW_transpose':
            assert row['source_kwargs'] == dict(dim0=-2, dim1=-1, __consts=[])
    assert all(result.receipt[flag] is False for flag in projection.FLAGS)
    assert all(result.lean.count(f'import {name}\n') == 1 for name in HELPERS)
