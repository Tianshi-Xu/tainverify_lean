"""Canonical score wiring only; portable replay is not capture/kernel acceptance."""
import copy
import importlib
import re
from pathlib import Path

import pytest

from Verdict import runtime_initial_relations as initial
from Verdict import runtime_world as world_api
from Verdict.runtime_binder_source import expand as expand_binders
from Verdict.runtime_read_source import expand as expand_reads


HELPERS = ('denote.SourcePrimitiveRead', 'denote.SourceRank4Exchange',
           'denote.SourceMatmulRead', 'denote.SourceMatmulUnit')


@pytest.mark.parametrize('stage', ('frontier_score_matmul_values', 'frontier_score_exchange_values'))
@pytest.mark.parametrize('fault', ('text', 'detail', 'inputs', 'order'))
def test_attachment_mutants_are_killed(monkeypatch, stage, fault):
    """Mutate only the live attach function; never edit renderers or disk sources."""
    source = Path(initial.__file__).read_text()
    stem = stage.removesuffix('_values')
    begin = source.index(f'        from Verdict.runtime_{stage} import render')
    end = source.index(f"        result['{stage}'] = {stem}_detail", begin)
    end = source.index('\n', end) + 1
    block = source[begin:end]
    if fault == 'text':
        changed = block.replace(f"entry += '\\n' + {stem}_text", 'entry += \'\'')
    elif fault == 'detail':
        changed = block.replace(f"result['{stage}'] = {stem}_detail", f"result['{stage}'] = dict({stem}_detail)")
    elif fault == 'inputs':
        changed = block.replace('sm, pm, lineages, validation, bound,', 'pm, sm, lineages, validation, bound,')
    else:
        changed = ''
    assert changed != block
    source = source[:begin] + changed + source[end:]
    if fault == 'order':
        before = 'frontier_middle_exchange_values' if stage == 'frontier_score_matmul_values' else 'frontier_score_matmul_values'
        anchor = f'        from Verdict.runtime_{before} import render'
        source = source.replace(anchor, block + anchor, 1)
    scope = dict(initial.__dict__)
    exec(compile(source, initial.__file__, 'exec'), scope)
    from types import FunctionType
    monkeypatch.setattr(initial, 'attach', FunctionType(scope['attach'].__code__, initial.__dict__))
    tracer = test_public_matmul_attachment_tracer if stage == 'frontier_score_matmul_values' else test_public_exchange_attachment_tracer
    with pytest.raises(AssertionError):
        tracer(monkeypatch)


@pytest.mark.parametrize('helper', HELPERS)
@pytest.mark.parametrize('fault', ('missing', 'duplicate', 'unknown', 'reordered'))
def test_exact_existing_import_admission(monkeypatch, helper, fault):
    # Exercise the complete earlier inventory: the position helper depends on
    # PrimitiveRead. Without a route, PrimitiveRead is independently optional.
    result, *_ = attachment(monkeypatch, fragments={'embedding_route_values': (
        '-- authenticated-route attachment boundary\n', dict(reads=[{}], routes=[{}]))})
    imports = result.receipt['proof_bundle']['modules'][-1]['imports']
    assert imports.count(helper) == result.lean.count(f'import {helper}\n') == 1
    line = f'import {helper}\n'
    replacement = {'missing': '', 'duplicate': line + line,
                   'unknown': 'import denote.UnapprovedScoreHelper\n', 'reordered': ''}[fault]
    bad = result.lean.replace(line, replacement)
    if fault == 'reordered':
        bad += line
    with pytest.raises(ValueError, match='import membership mismatch'):
        world_api._proof_bundle(bad, result.supporting_sources)


@pytest.mark.parametrize('stage', ('frontier_score_matmul_values', 'frontier_score_exchange_values'))
def test_empty_stage_keeps_exact_detail_and_omits_text(monkeypatch, stage):
    detail = dict(reads=[], units=[], frontier_units=[dict(facts_theorem='carryFacts', history=['original'])],
                  retained_units=[], deferred_units=[], **dict.fromkeys(projection.FLAGS, False))
    result, _, texts, _, _, _ = attachment(monkeypatch, fragments={stage: ('-- no new score declarations\n', detail)})
    assert result.receipt[stage] is detail
    assert texts[stage] not in result.lean


def test_no_initial_goals_preserves_default_bytes(monkeypatch):
    result, calls, _, _, _, world = attachment(monkeypatch, bound=dict(relations=[]))
    assert result.lean == world.lean and calls == []
    assert 'proof_bundle' not in result.receipt


def test_no_input_feed_skips_score_stages(monkeypatch):
    result, calls, texts, _, _, _ = attachment(monkeypatch, input_feed=False)
    assert calls == []
    assert all(texts[key] not in result.lean for key in STAGES)


def test_unchanged_strict_total_cap(monkeypatch):
    from Verdict.graph_to_lean import GENERATED_LEAN_SOURCE_LIMIT
    result, *_ = attachment(monkeypatch)
    size = len(result.lean.encode()) + sum(len(t.encode()) for t in result.supporting_sources.values())
    assert size < GENERATED_LEAN_SOURCE_LIMIT == 2_500_000
    padded = result.lean + '-' * (GENERATED_LEAN_SOURCE_LIMIT - size - 1)
    world_api._proof_bundle(padded, result.supporting_sources)
    with pytest.raises(ValueError, match='2500000 bytes total'):
        world_api._proof_bundle(padded + '-', result.supporting_sources)


@pytest.mark.parametrize('stage', ('frontier_score_matmul_values', 'frontier_score_exchange_values'))
def test_source_rejection_propagates_without_publishing(monkeypatch, stage):
    original = initial.attach
    observed = []
    def fail(*six):
        observed.append(six)
        raise ValueError('source-bound score rejection')
    def attach(world, *args):
        receipt = copy.deepcopy(world.receipt)
        module = importlib.import_module('Verdict.runtime_' + stage)
        monkeypatch.setattr(module, 'render', fail)
        try:
            return original(world, *args)
        finally:
            assert list(world.receipt) == list(receipt)
            assert all(world.receipt[key] == receipt[key] for key in receipt if key != 'execution_order')
    monkeypatch.setattr(initial, 'attach', attach)
    with pytest.raises(ValueError, match='source-bound score rejection'):
        attachment(monkeypatch)
    assert len(observed) == 1 and len(observed[0]) == 6


@pytest.mark.parametrize('stage', ('frontier_alias_exchange_values',
                                 'frontier_next_alias_exchange_values',
                                 'frontier_score_matmul_values'))
def test_complete_predecessor_declaration_mutants_are_killed(monkeypatch, public_chain, stage):
    from dataclasses import replace
    original = initial.attach
    def attach(*args):
        result = original(*args)
        text = public_chain[1][stage][0]
        canonical = expand_binders(expand_reads(result.lean))
        assert canonical.count(text) == 1
        return replace(result, lean=canonical.replace(text, '', 1))
    monkeypatch.setattr(initial, 'attach', attach)
    with pytest.raises(AssertionError):
        test_real_public_complete_chain_replay(monkeypatch, public_chain)


@pytest.fixture(scope='module')
def public_chain():
    from scripts.tests.test_runtime_frontier_score_exchange_values import prepared
    args = prepared()
    earlier = tuple('frontier_' + name + '_values' for name in (
        'alias_exchange', 'layernorm', 'linear', 'gelu', 'next_linear',
        'sequence_hidden', 'add', 'next_alias_exchange', 'next_layernorm'))
    keys = (*earlier, projection.PREDECESSOR, *projection.STAGES,
            middle.PREDECESSOR, middle.STAGE, *STAGES)
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
        importlib.import_module('Verdict.runtime_' + EXCHANGE).render(*args)
    assert calls == list(reversed(keys))
    assert list(fragments) == list(keys)
    return args, fragments


def test_real_public_complete_chain_replay(monkeypatch, public_chain):
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
    before = fragments[middle.STAGE][1]
    matmul = fragments[MATMUL][1]; exchange = fragments[EXCHANGE][1]
    assert [len(d['frontier_units']) for d in (before, matmul, exchange)] == [8, 6, 6]
    assert [len(d['reads']) for d in (matmul, exchange)] == [7, 6]
    assert matmul['consumed_frontier_indices'] == [0, 1, 4, 5]
    assert exchange['consumed_frontier_indices'] == [0, 3]
    for u in range(2):
        left, right, v, carry = before['frontier_units'][4*u:4*u+4]
        score, v1, carry1 = matmul['frontier_units'][3*u:3*u+3]
        after, v2, carry2 = exchange['frontier_units'][3*u:3*u+3]
        assert score['input_frontiers'][0] is left and score['input_frontiers'][1] is right
        assert score['predecessors'] == [left['facts_theorem'], right['facts_theorem']]
        assert score['ordered_join']['frontier_indices'] == [4*u, 4*u+1]
        assert after['input_frontier'] is score
        assert after['predecessor_facts'] == score['facts_theorem']
        assert v2 is v1 is v and carry2 is carry1 is carry
        assert v['layout'] == 'replicated_within_dp' and v['gather_axis'] is None
        assert matmul['retained_units'][u] is exchange['retained_units'][u] is carry
        assert matmul['deferred_units'][u]['source_boundary'] is v
        assert exchange['deferred_units'][u]['source_boundary'] is v
        assert all(c['value_proved'] is False for c in after['downstream_consumers'])
        assert after['observed_consumer_ops'] == [['FW_div']]*4
        # Every surviving fact, including original residual carries, is declared.
        for row in (left, right, score, after, v, carry):
            name = row['facts_theorem']
            assert len(re.findall(r'^theorem ' + re.escape(name) + r'(?=\s)', canonical, re.M)) == 1
            assert canonical.count(f'#print axioms {name}\n') == 1
        for row in (score, after, v, carry):
            statement = canonical.split(f'theorem {row["facts_theorem"]} ', 1)[1].split(' := by', 1)[0]
            assert 'InitialParameterValues s p' in statement
            assert str(row['global_shape']) in statement and str(row['local_shape']) in statement
            assert '∀ ' in statement and '.shape =' in statement
            if row['layout'] == 'replicated_within_dp':
                assert 'allGatherPrimDimN' not in statement
    for key in STAGES:
        for read in fragments[key][1]['reads']:
            assert read['operand_nonwrite_source_indices'] == args[-1][read['world']]['execution_to_source'][read['execution_index']:]
        assert 'div_value_of_split' not in fragments[key][0]
    assert all(result.receipt[flag] is False for flag in projection.FLAGS)
    assert result.receipt['proof_bundle']['kernel_checked'] is False

from scripts.tests import test_runtime_frontier_projection_entry as projection
from scripts.tests import test_runtime_frontier_middle_exchange_entry as middle

MATMUL = 'frontier_score_matmul_values'
EXCHANGE = 'frontier_score_exchange_values'
STAGES = (MATMUL, EXCHANGE)


def attachment(monkeypatch, **kwargs):
    monkeypatch.setattr(projection, 'STAGES', tuple(dict.fromkeys(
        (*projection.STAGES, middle.PREDECESSOR, middle.STAGE, *STAGES))))
    return projection.attachment(monkeypatch, **kwargs)


def test_public_exchange_attachment_tracer(monkeypatch):
    result, calls, texts, details, six, _ = attachment(monkeypatch)
    selected = [(key, args) for key, args in calls if key in STAGES]
    assert [key for key, _ in selected] == list(STAGES), 'score exchange not attached'
    for key, args in selected:
        assert len(args) == 6 and all(a is b for a, b in zip(args, six, strict=True))
        assert result.receipt[key] is details[key]
        assert result.lean.count(texts[key]) == 1
    assert result.lean.index(texts[MATMUL]) < result.lean.index(texts[EXCHANGE])
    assert list(result.receipt).index(MATMUL) < list(result.receipt).index(EXCHANGE)
    assert all(result.receipt[EXCHANGE][flag] is False for flag in projection.FLAGS)


def test_public_matmul_attachment_tracer(monkeypatch):
    result, calls, texts, details, six, _ = attachment(monkeypatch)
    keys = (middle.STAGE, MATMUL)
    selected = [(key, args) for key, args in calls if key in keys]
    assert [key for key, _ in selected] == list(keys), 'score matmul not attached'
    for key, args in selected:
        assert len(args) == 6 and all(a is b for a, b in zip(args, six, strict=True))
        assert result.receipt[key] is details[key]
        assert result.lean.count(texts[key]) == 1
    assert result.lean.index(texts[keys[0]]) < result.lean.index(texts[keys[1]])
    assert list(result.receipt).index(keys[0]) < list(result.receipt).index(keys[1])
    assert all(result.receipt[flag] is False for flag in projection.FLAGS)
    assert all(result.receipt[MATMUL][flag] is False for flag in projection.FLAGS)
    assert result.receipt['proof_bundle']['kernel_checked'] is False
