"""Executable attachment tests; mock wiring is not a raw-capture/kernel proof."""
import ast
import copy
import importlib
from pathlib import Path

import pytest

from Verdict import runtime_initial_relations as initial
from Verdict import runtime_world as world_api
from Verdict.runtime_prefix import SUPPORT_MODULE, SUPPORT_FILE, support_source


STAGES = tuple('frontier_' + name + '_values' for name in (
    'projection_exchange', 'input_linear', 'gathered_linear', 'gathered_exchange',
    'projection_view', 'head_exchange', 'projection_transpose'))
PREDECESSOR = 'frontier_sequence_alias_values'
FLAGS = ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')


def attachment(monkeypatch, *, fragments=None, bound=None, input_feed=True):
    """Mock stage boundaries only; run real attach, codecs and bundle inventory.

    The real-public test below instead wraps every renderer without replacing
    its authority or predecessor reconstruction. No capture caches are used.
    """
    sm, pm, lineages, validation, order, parameters = (object() for _ in range(6))
    if bound is None:
        bound = dict(relations=[dict(units=[dict(initial_goal=dict(kind='replicated',
            sm_tid=1, pm_tids=[2], sm_shape=[1]))])], **dict.fromkeys(FLAGS, False))
    monkeypatch.setattr(initial, 'bind', lambda *args: bound)
    calls = []; details = {}; texts = {}
    tree = ast.parse(Path(initial.__file__).read_text())
    modules = [n.module for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)
               and n.module and n.module.startswith('Verdict.runtime_')
               and any(a.name == 'render' for a in n.names)]
    modules = list(dict.fromkeys([*modules, *('Verdict.runtime_' + s for s in STAGES)]))
    for module_name in modules:
        key = module_name.removeprefix('Verdict.runtime_')
        text = '-- attachment-fragment:' + key + '\n'
        rows = [dict(unit=i // 4, slot=i % 4, facts_theorem=f'{key}_{i}',
                     provenance=dict(source=[i], parents=[i - 1])) for i in range(8)]
        detail = dict(reads=[dict(source=key)], units=rows[:3] + rows[4:7],
                      routes=[], frontier_units=rows, retained_units=[rows[3], rows[7]],
                      deferred_units=[], consumed_frontier_indices=[0, 1, 2, 4, 5, 6],
                      **dict.fromkeys(FLAGS, False))
        if fragments and key in fragments:
            text, detail = fragments[key]
        texts[key] = text; details[key] = detail
        def render(*args, _key=key, _text=text, _detail=detail):
            calls.append((_key, args))
            return _text, _detail
        monkeypatch.setattr(importlib.import_module(module_name), 'render', render)
    receipt = dict(execution_order=order, **dict.fromkeys(FLAGS, False))
    if input_feed:
        receipt['input_feed'] = {}
    # A stale caller receipt must never replace any renderer's fresh result.
    receipt.update({s: dict(stale=True) for s in STAGES})
    lean = ('import TrainVerifyRuntimeWorldData\nimport denote.SourceScopedPrefix\n'
            f'import {SUPPORT_MODULE}\n')
    support = {world_api.WORLD_DATA_FILE: 'import denote.SourceScopedEval\n',
               SUPPORT_FILE: support_source()}
    world = world_api.WorldDefinitions(lean, receipt, support)
    original = copy.deepcopy(receipt)
    original['execution_order'] = order
    result = initial.attach(world, sm, pm, parameters, lineages, validation)
    assert world.receipt == original
    assert result.supporting_sources is support
    return result, calls, texts, details, (sm, pm, lineages, validation, bound, order), world


def test_canonical_projection_fragments_same_six_order_and_complete_details(monkeypatch):
    result, calls, texts, details, six, _ = attachment(monkeypatch)
    selected = [(key, args) for key, args in calls if key in (PREDECESSOR, *STAGES)]
    assert [key for key, _ in selected] == [PREDECESSOR, *STAGES], 'canonical QKV attachment missing/out of order'
    positions = []
    for key, args in selected:
        assert len(args) == 6 and all(a is b for a, b in zip(args, six, strict=True))
        assert result.receipt[key] is details[key]  # includes every skip/classification/provenance field
        assert result.lean.count(texts[key]) == 1  # never append rebuilt ancestor text
        positions.append(result.lean.index(texts[key]))
        assert len(result.receipt[key]['frontier_units']) == 8
        assert all(result.receipt[key][flag] is False for flag in FLAGS)
    assert positions == sorted(positions)
    assert all(result.receipt[flag] is False for flag in FLAGS)
    assert result.receipt['proof_bundle']['kernel_checked'] is False


HELPERS = ('denote.SourceLinearInputUnit', 'denote.SourceReduceScatterRead')


def test_input_linear_helpers_in_canonical_closed_inventory(monkeypatch):
    result, *_ = attachment(monkeypatch)
    imports = result.receipt['proof_bundle']['modules'][-1]['imports']
    at = imports.index('denote.SourceLinearUnit') + 1
    assert imports[at:at + 2] == list(HELPERS), 'input-column/ReduceScatter helper imports missing'
    assert all(result.lean.count(f'import {name}\n') == 1 for name in HELPERS)


@pytest.mark.parametrize('fault', ['partial', 'duplicate', 'reordered', 'unknown'])
def test_helper_inventory_rejects_noncanonical_imports(monkeypatch, fault):
    result, *_ = attachment(monkeypatch)
    pair = ''.join(f'import {name}\n' for name in HELPERS)
    assert pair in result.lean
    replacement = {'partial': f'import {HELPERS[0]}\n', 'duplicate': pair + pair,
                   'reordered': ''.join(f'import {name}\n' for name in reversed(HELPERS)),
                   'unknown': pair + 'import denote.UnapprovedHelper\n'}[fault]
    with pytest.raises(ValueError, match='import membership mismatch'):
        world_api._proof_bundle(result.lean.replace(pair, replacement), result.supporting_sources)


def test_all_new_fragment_and_import_bytes_count_toward_strict_cap(monkeypatch):
    from Verdict.graph_to_lean import GENERATED_LEAN_SOURCE_LIMIT
    result, *_ = attachment(monkeypatch)
    size = len(result.lean.encode()) + sum(len(t.encode()) for t in result.supporting_sources.values())
    assert size < GENERATED_LEAN_SOURCE_LIMIT == 2_500_000
    # Entry and support bytes must both count; no optional import is free.
    padded = result.lean + '-' * (GENERATED_LEAN_SOURCE_LIMIT - size - 1)
    world_api._proof_bundle(padded, result.supporting_sources)
    with pytest.raises(ValueError, match='2500000 bytes total'):
        world_api._proof_bundle(padded + '-', result.supporting_sources)


def test_empty_projection_stages_keep_details_without_source_or_helpers(monkeypatch):
    fragments = {key: ('-- no new declarations\n', dict(reads=[], units=[],
        frontier_units=[dict(retained=key)], retained_units=[dict(retained=key)],
        deferred_units=[], **dict.fromkeys(FLAGS, False))) for key in STAGES}
    result, _, _, details, _, _ = attachment(monkeypatch, fragments=fragments)
    assert '-- no new declarations' not in result.lean
    assert all(name not in result.lean for name in HELPERS)
    assert all(result.receipt[key] is details[key] for key in STAGES)


def test_no_initial_goals_preserves_entry_bytes_and_skips_all_stages(monkeypatch):
    result, calls, _, _, _, world = attachment(monkeypatch, bound=dict(relations=[]))
    assert result.lean == world.lean and calls == []
    assert 'proof_bundle' not in result.receipt


def test_no_input_feed_does_not_enter_frontier_or_add_helpers(monkeypatch):
    result, calls, _, _, _, _ = attachment(monkeypatch, input_feed=False)
    assert calls == []
    assert all(name not in result.lean for name in HELPERS)


def test_real_public_projection_chain_and_attachment_replay(monkeypatch):
    """Real portable raw/lineage/public chain; replay is not whole-world/kernel.

    No renderer/predecessor authority is mocked during public generation.
    Only the later attachment harness replays those exact generated fragments.
    """
    from scripts.tests.test_runtime_frontier_projection_transpose_values import prepared
    from Verdict.runtime_binder_source import expand as expand_binders
    from Verdict.runtime_read_source import expand as expand_reads
    args = prepared(next_consumers=True)
    fragments = {}; calls = []
    with monkeypatch.context() as live:
        for key in (PREDECESSOR, *STAGES):
            module = importlib.import_module('Verdict.runtime_' + key)
            original = module.render
            def render(*six, _key=key, _original=original):
                assert len(six) == 6 and all(a is b for a, b in zip(six, args, strict=True))
                calls.append(_key)
                pair = _original(*six)
                fragments[_key] = pair
                return pair
            live.setattr(module, 'render', render)
        final_text, final = importlib.import_module('Verdict.runtime_' + STAGES[-1]).render(*args)
    assert calls == list(reversed((PREDECESSOR, *STAGES)))
    assert [len(final[k]) for k in ('reads', 'units', 'frontier_units', 'retained_units', 'deferred_units')] == [15, 6, 8, 2, 0]
    assert all(row['source_step']['op'] == 'FW_transpose' for row in final['units'])
    assert all(c['value_proved'] is False for r in final['units'] for c in r['downstream_consumers'])
    result, *_ = attachment(monkeypatch, fragments=fragments)
    canonical = expand_binders(expand_reads(result.lean))
    # Every actual stage read and newly emitted complete fact appears once.
    # Retained facts remain metadata, never spuriously emitted by this stage.
    for key in (PREDECESSOR, *STAGES):
        text, detail = fragments[key]
        assert result.receipt[key] is detail
        assert len(detail['frontier_units']) == 8
        for row in (*detail['reads'], *detail['units']):
            name = row['theorem']
            assert canonical.count(f'theorem {name} ') + canonical.count(f'theorem {name}\n') == 1
        assert all(detail[flag] is False for flag in FLAGS)
    assert final_text == fragments[STAGES[-1]][0]
    assert all(f'import {name}\n' in result.lean for name in HELPERS)
