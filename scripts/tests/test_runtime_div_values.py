"""First original division checkpoint; generated Lean is UNCOMPILED."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_matmul_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_matmul_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_div_values'), 'division renderer missing'
    return importlib.import_module('Verdict.runtime_div_values')


def fixture(D=2, tp=2, seqlen=2, branches=3, scalar=4.0):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen, branches)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        producers = [c for c in graph.cells if c.node.cid == (9000 if world == 's' else 9500)]
        for producer in producers:
            x = producer._output_irs[0]
            out = IR(9600, 'scaled.score', x.parent.shape, x.indmap)
            cell = NS(node=N(world, producer.rank, 0, 9600, 'FW_div'), rank=producer.rank,
                opname='FW_div', inputs=[producer.outputs[0]], outputs=[T(world, producer.rank, 0, 9600, 1)],
                kwargs={'rounding_mode': None, '__consts': [scalar]}, _input_irs=[copy.deepcopy(x)], _output_irs=[out])
            cell.ir = NS(signature='FW_div', inputs=lambda c=cell: c._input_irs,
                outputs=lambda c=cell: c._output_irs)
            for consumer in graph.cells:
                if consumer.rank != producer.rank: continue
                for j, ref in enumerate(consumer.inputs):
                    if ref == producer.outputs[0] and not consumer.opname.startswith('BW_'):
                        consumer.inputs[j] = cell.outputs[0]; consumer._input_irs[j] = copy.deepcopy(out)
                        if world == 'p':
                            for w in old['writers'] + old['adapter_source']:
                                if w['ref']['runtime_rank'] == consumer.rank and w['ref']['source_cid'] == consumer.node.cid:
                                    w['inputs'][j] = tref(cell.outputs[0])
            graph.cells.insert(graph.cells.index(producer)+1, cell)
            graph.shapes[cell.outputs[0]] = out.shape
            if world == 'p':
                rows.append(dict(ref=dict(world=world, runtime_rank=cell.rank, microbatch=0,
                    source_cid=9600, call_instance=0, op='FW_div', origin='fixture'),
                    source_irname='FW_div', inputs=[tref(t) for t in cell.inputs],
                    outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[]))
    def ordered(original):
        by_node = {(w['ref']['runtime_rank'], w['ref']['source_cid']): w for w in [*original, *rows]}
        return [by_node[(c.rank, c.node.cid)] for c in pm.cells]
    snapshot = build_snapshot(ordered(old['writers']))
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = ordered(old['adapter_source'])
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3, scalar=4.0):
    base = previous.previous.previous.previous.previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=fixture(D, tp, seqlen, branches, scalar)):
        return base.prepared(D, tp, seqlen)


def test_first_div_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'deferred_units', 'frontier_units')] == [5, 2, 2, 4]
    assert [r['world'] for r in detail['reads']] == ['sm', 'pm', 'pm', 'pm', 'pm']
    assert text.count('SourceDivRead.div_value_of_split') == 5
    assert text.count('TrainVerify.Denote.source_div_unit_output_reconstruct') == 2
    assert args[-1] == before
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None:
            assert new == old and new['layout'] == 'replicated_within_dp'
        else:
            assert 'slot' not in new
            assert new['predecessor'] == old['facts_theorem']
            assert new['sm_output_ref'] != old['sm_output_ref']
            assert new['global_shape'] == old['global_shape']
            assert new['local_shape'] == old['local_shape']
            assert new['gather_axis'] == 3 and new['scalar_nat'] == 4
            fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
            assert fragment.split(' := by')[0].count('(h') == 3
            assert old['facts_theorem']+' s p t q hs hp hvalues' in fragment
            assert 'List.map (fw_div' in fragment and 'predecessor.2.2' in fragment
    for r in detail['reads']:
        assert r['params'] == [4] and r['request'] == 'global'
        assert r['source_kwargs'] == {'rounding_mode': None, '__consts': [4.0]}
        assert type(r['source_kwargs']['__consts'][0]) is float
        assert r['operand_nonwrite_source_indices'] == args[-1][r['world']]['execution_to_source'][r['execution_index']:]
    assert all(not d['value_proved'] and d['first_consumers'] for d in detail['deferred_units'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :', '≠ 0'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def div_cells(args, label='pm'):
    return [c for c in args[3]._inputs[0 if label == 'sm' else 1] if c.opname == 'FW_div']


def set_kwargs(args, cell, kwargs, label='pm'):
    cell.kwargs = copy.deepcopy(kwargs)
    source = args[0 if label == 'sm' else 1]
    node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    source.source.node_kwargs(node).clear()
    source.source.node_kwargs(node).update(copy.deepcopy(kwargs))
    return source, node


@pytest.mark.parametrize('scalar', [0, -1, 1.25, True, float('nan'), float('inf'), -float('inf')])
def test_existing_admission_rejects_unsupported_not_new_guard(baseline, scalar):
    from Verdict.runtime_world import _ordinary
    from Verdict import graph_to_lean
    args, _ = copy.deepcopy(baseline)
    source, node = set_kwargs(args, div_cells(args)[0], {'__consts': [scalar]})
    # Coordinated raw+normalized kwargs survive the predecessor, which does
    # not apply _ordinary to this frontier. Existing _ordinary rejects them;
    # do not misreport this as a novel scalar admission restriction.
    with pytest.raises((ValueError, OverflowError)):
        _ordinary(source, node, graph_to_lean._get_node_params)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises((ValueError, OverflowError)): api().render(*args)


def test_independent_lossless_raw_to_actual_encoded_parameter(baseline):
    from Verdict import graph_to_lean
    from Verdict.runtime_world import _ordinary
    args, _ = copy.deepcopy(baseline)
    source = args[1]; cell = div_cells(args)[0]
    node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    assert predecessor.render(*args)[1]['frontier_units']
    getter = graph_to_lean._get_node_params
    # Isolate an incorrect normalized parameter without pretending the public
    # authority accepted it. _ordinary itself does not bind getter output to c.
    def corrupt(g, n, num_parts=0):
        return [5] if g is source and n == node else getter(g, n, num_parts)
    with patch.object(graph_to_lean, '_get_node_params', side_effect=corrupt):
        assert _ordinary(source, node, graph_to_lean._get_node_params) == ([5], None)
        with pytest.raises(ValueError, match='lossless.*binding'):
            api()._scalar(source, node)


@pytest.mark.parametrize('scalar', [True, -1, 0.5, float('nan'), float('inf'), -float('inf')])
def test_raw_losslessness_independent_of_normalized_params(baseline, scalar):
    args, _ = copy.deepcopy(baseline)
    # Direct new guard seam: no claim that unsupported source is invalid, or
    # that original _ordinary admitted fractions. Check before int conversion.
    with pytest.raises(ValueError, match='lossless'):
        api()._lossless_nat({'__consts': [scalar]})


@pytest.mark.parametrize('D,tp,seqlen,branches,scalar', [(3, 2, 6, 4, 3), (2, 3, 6, 5, 7.0), (3, 3, 9, 3, 1), (1, 2, 4, 2, 9)])
def test_dimension_scalar_and_full_frontier_variants(D, tp, seqlen, branches, scalar):
    args = prepared(D, tp, seqlen, branches, scalar)
    prior = predecessor.render(*args)[1]; text, detail = api().render(*args)
    ready = [u for u in prior['frontier_units'] if u['gather_axis'] == 3]
    unchanged = [u for u in prior['frontier_units'] if u not in ready]
    assert len(detail['units']) == len(ready) == D
    assert len(detail['reads']) == 1+sum(len(u['ranks']) for u in ready)
    assert len(detail['deferred_units']) == len(unchanged)
    assert len(detail['frontier_units']) == len(prior['frontier_units'])
    for u in detail['units']:
        assert u['global_shape'] == [D, 2*tp, seqlen, seqlen]
        assert u['local_shape'] == [1, 2*tp, seqlen, seqlen//tp]
        assert u['scalar_nat'] == scalar
        assert f"source_div_unit_output_reconstruct ({int(scalar)} : Scalar) {D} {tp} 1 {2*tp} {seqlen} {seqlen//tp}" in text
    for source, label in zip(args[:2], ('sm', 'pm'), strict=True):
        bw = {i for i, n in enumerate(source.nodes()) if source.node_opname(n).startswith('BW_')}
        assert bw and bw <= set(args[-1][label]['execution_to_source'])


@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['name', 'parent', 'bounds', 'batch', 'value', 'empty', 'absent'])
def test_paired_metadata_after_accepted_predecessor(baseline, field, fault):
    args, _ = copy.deepcopy(baseline); cell = div_cells(args)[0]
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
    ir = irs[0]
    if fault == 'absent': delattr(cell, field)
    elif fault == 'empty': setattr(cell, field, [])
    elif fault == 'name': ir.parent.name = 'other-logical-source'
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'value': ir.valmap = (1, 2)
    else:
        bounds = list(ir.indmap); j = 0 if fault == 'batch' else 3
        a, b = bounds[j]; bounds[j] = (a+1, b+1); ir.indmap = tuple(bounds)
    if fault in ('empty', 'absent'):
        with pytest.raises(ValueError): predecessor.render(*args)
    else:
        assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


def test_sm_pm_scalar_mismatch_after_accepted_predecessor(baseline):
    args, _ = copy.deepcopy(baseline)
    set_kwargs(args, div_cells(args)[0], {'__consts': [7.0]})
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='SM/PM scalar mismatch'): api().render(*args)


@pytest.mark.parametrize('fault', ['inputs', 'outputs', 'call', 'export'])
def test_source_writer_upstream_reject(baseline, fault):
    args, _ = copy.deepcopy(baseline); cell = div_cells(args)[0]
    w = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == cell.rank)
    if fault in ('inputs', 'outputs'): w[fault][0]['version'] += 1
    elif fault == 'call': w['ref']['call_instance'] += 1
    else: w['export_id'] = 'forged'
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['missing', 'unknown', 'mixed', 'duplicate'])
def test_new_discovery_guard_and_upstream_classification(baseline, fault):
    args, prior = copy.deepcopy(baseline); cells = div_cells(args)
    if fault == 'missing': args[3]._inputs[1].remove(cells[0])
    elif fault == 'duplicate':
        c = copy.deepcopy(cells[0]); c.node = N('p', c.rank, 0, 9700, 'FW_div')
        args[3]._inputs[1].append(c)
    else:
        for c in (cells if fault == 'unknown' else cells[:1]): c.opname = 'FW_unknown'
    # Raw inventory/opcodes are checked upstream; separately isolate discovery.
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('fault', ['rank-order', 'positions', 'layout', 'axis', 'duplicate'])
def test_independent_inventory_guard(baseline, fault):
    args, prior = copy.deepcopy(baseline); u = prior['frontier_units'][0]
    if fault == 'rank-order': u['ranks'].reverse()
    elif fault == 'positions': u['positions'] = [99]
    elif fault == 'layout': u['layout'] = 'replicated_within_dp'
    elif fault == 'axis': u['gather_axis'] = 1
    else: prior['frontier_units'].append(copy.deepcopy(u))
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('selected', [False, True])
def test_selected_and_entire_suffix_operand_nonwrite(baseline, selected):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index = _Index(args[1], args[3]._inputs[1])
    port = middle._output(index, prior['frontier_units'][0]['local_steps'][0])
    step, _ = api()._div(index, div_cells(args)[0], port)
    _, row = api()._read(args[1], 'pm', step, args[-1]['pm'])
    source = args[1]; node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if selected else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    assert source.nodes().index(target) in row['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[0]]
    if selected: step = replace(step, outputs=step.inputs)
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, 'pm', step, args[-1]['pm'])


def test_all_original_order_and_first_sm_read_dedup(baseline):
    args, prior = copy.deepcopy(baseline); prior['frontier_units'].reverse()
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['gather_axis'] for u in detail['frontier_units']] == [u['gather_axis'] for u in prior['frontier_units']]
    assert [r['world'] for r in detail['reads']].count('sm') == 1
    assert detail['reads'][0]['unit'] == prior['frontier_units'][1]['unit']
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None: assert new is old


def test_asymmetric_value_order_and_total_denote_zero_scope():
    from fractions import Fraction
    import numpy as np
    D, Tn, B, H, Q, C = 3, 3, 2, 4, 5, 7
    full = np.arange(D*B*H*Q*C*Tn).reshape(D*B, H, Q, C*Tn)
    for c in (0, 3, 7):
        # Exact rational replay of total Scalar division, NOT NumPy/Torch /0.
        div = np.vectorize(lambda x: Fraction(int(x), c) if c else Fraction(0), otypes=[object])
        for u in range(D):
            batch = full[u*B:(u+1)*B]
            xs = np.split(batch, Tn, axis=3); outputs = [div(x) for x in xs]
            assert all(y.shape == (B, H, Q, C) for y in outputs)
            assert np.array_equal(div(batch), np.concatenate(outputs, axis=3))
            if c: assert not np.array_equal(div(batch), np.concatenate(outputs[::-1], axis=3))


@pytest.mark.parametrize('kwargs', [{}, {'__consts': []}, {'__consts': [4, 4]},
    {'__consts': ['4']}, {'__consts': [4], 'extra': 1},
    {'__consts': [4], 'rounding_mode': 'floor'}, {'__consts': [4], 'rounding_mode': False}])
def test_exact_raw_kwargs_admission_after_accepted_predecessor(baseline, kwargs):
    args, _ = copy.deepcopy(baseline)
    set_kwargs(args, div_cells(args)[0], kwargs)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


def test_raw_integer_type_preserved_and_denote_only_zero(baseline):
    args, _ = copy.deepcopy(baseline)
    for label in ('sm', 'pm'):
        for cell in div_cells(args, label):
            set_kwargs(args, cell, {'rounding_mode': None, '__consts': [11]}, label)
    assert predecessor.render(*args)[1]['frontier_units']
    text, detail = api().render(*args)
    assert all(r['params'] == [11] and type(r['source_kwargs']['__consts'][0]) is int for r in detail['reads'])
    assert '(11 : Scalar)' in text
    assert api()._lossless_nat({'__consts': [0]}) == 0
    assert 'positive integral source admission' in detail['scalar_scope']


def test_coordinated_output_partition_swap_new_guard(baseline):
    args, _ = copy.deepcopy(baseline)
    for cell in div_cells(args):
        ir = copy.deepcopy(cell._output_irs[0]); cell._output_irs = [ir]
        lo, hi = ir.indmap[3]; width = hi-lo; j = (cell.rank % 2+1) % 2
        ir.indmap = (*ir.indmap[:3], (j*width, (j+1)*width))
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='input-derived output'): api().render(*args)


def test_deferred_original_port_correspondence(baseline):
    args, prior = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 9200)
    cell.inputs.reverse(); cell._input_irs.reverse()
    source = args[1]; node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    source._node2inputs[node].reverse()
    writer = next(w for w in source._collective_source['writers']
        if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == cell.rank)
    writer['inputs'].reverse()
    # Exact new-stage seam, not a public snapshot-acceptance claim.
    with pytest.raises(ValueError, match='deferred.*port'):
        api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('fault', ['owner', 'positions', 'execution-order', 'output-arity', 'input-arity'])
def test_original_authority_upstream_rejection(baseline, fault):
    args, prior = copy.deepcopy(baseline); cell = div_cells(args)[0]
    if fault in ('owner', 'positions'):
        unit = args[3]._inputs[3]['config']['units'][0]
        if fault == 'owner': unit['ranks'].reverse()
        else: unit['positions'] = [99]
    elif fault == 'execution-order': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'output-arity': cell.outputs.append(cell.outputs[0])
    else: cell.inputs.append(cell.inputs[0])
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
