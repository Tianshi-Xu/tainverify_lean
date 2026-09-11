"""Original softmax -> AA(1,2) portable source tracer; no kernel claim."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_softmax_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_softmax_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_softmax_exchange_values'), 'softmax exchange renderer missing'
    return importlib.import_module('Verdict.runtime_softmax_exchange_values')


def fixture(D=2, tp=2, seqlen=2):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    old = copy.deepcopy(authority[2]); rows, adapters, extra = [], [], []
    producers = [c for c in pm.cells if c.opname == 'FW_softmax']
    for producer in producers:
        x = producer._output_irs[0]
        ranks = list(range(producer.rank//tp*tp, (producer.rank//tp+1)*tp))
        peers = [next(p for p in producers if p.rank == r) for r in ranks]
        j = ranks.index(producer.rank); bounds = list(x.indmap)
        bounds[1] = (0, x.parent.shape[1]); width = x.parent.shape[2]//tp
        bounds[2] = (j*width, (j+1)*width)
        out = IR(9950, x.parent.name, x.parent.shape, tuple(bounds))
        kwargs = dict(ranks=ranks, idim=1, odim=2)
        cell = NS(node=N('p', producer.rank, 0, 9950, 'AllToAllPrim'), rank=producer.rank,
            opname='AllToAllPrim', inputs=[p.outputs[0] for p in peers],
            outputs=[T('p', producer.rank, 0, 9950, 1)], kwargs=kwargs,
            _input_irs=[copy.deepcopy(p._output_irs[0]) for p in peers], _output_irs=[out])
        cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs,
            outputs=lambda c=cell: c._output_irs)
        for consumer in pm.cells:
            if consumer.rank == producer.rank and not consumer.opname.startswith('BW_'):
                for i, ref in enumerate(consumer.inputs):
                    if ref == producer.outputs[0]:
                        consumer.inputs[i] = cell.outputs[0]; consumer._input_irs[i] = copy.deepcopy(out)
                        for w in old['writers'] + old['adapter_source']:
                            if w['ref']['runtime_rank'] == consumer.rank and w['ref']['source_cid'] == consumer.node.cid:
                                w['inputs'][i] = tref(cell.outputs[0])
        extra.append(cell); pm.shapes[cell.outputs[0]] = out.shape
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0, source_cid=9950,
            call_instance=0, op='AllToAllPrim', origin='fixture'), source_irname='AllToAllPrim',
            inputs=[tref(t) for t in cell.inputs], outputs=[tref(t) for t in cell.outputs],
            parameter_grad_tids=[], adapter_kwargs=copy.deepcopy(kwargs))
        rows.append(row); adapter = copy.deepcopy(row); adapter['inputs'] = [tref(producer.outputs[0])]
        adapter['primitive'] = dict(kind='AllToAllPrim', forward=True, kwargs=copy.deepcopy(kwargs),
            signature='nnscaler.runtime.adapter.all_to_all', generated_inputs=['normalized'], generated_outputs=['exchanged'])
        params = ', '.join(f'{k}={v!r}' for k, v in kwargs.items())
        old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace(
            '\ndef _train_step', '\n        exchanged = nnscaler.runtime.adapter.all_to_all(normalized, '+params+')\ndef _train_step')
        adapters.append(adapter)
    # Stable original dependency order, retaining all backward readers.
    def insert(items, additions, is_softmax):
        pending = [*items, *additions]; result = []
        def refs(item, key):
            values = item[key] if isinstance(item, dict) else getattr(item, key)
            return [tuple(v.values()) if isinstance(v, dict) else tuple(v) for v in values]
        while pending:
            produced = {ref for item in pending for ref in refs(item, 'outputs')}
            ready = next(item for item in pending if not produced.intersection(refs(item, 'inputs')))
            result.append(ready); pending.remove(ready)
        return result
    pm.cells[:] = insert(pm.cells, extra, lambda c: c.opname == 'FW_softmax')
    snapshot = build_snapshot(insert(old['writers'], rows, lambda w: w['ref']['op'] == 'FW_softmax'))
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    from trainverify.runtime_source_authority import writer_export_id
    by_writer = {writer_export_id(w['ref']): w for w in [*old['adapter_source'], *adapters]}
    snapshot['adapter_source'] = [by_writer[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2):
    base = previous.previous.previous.previous.previous.previous.previous.previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=fixture(D, tp, seqlen)):
        return base.prepared(D, tp, seqlen)


def test_first_softmax_exchange_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'deferred_units', 'frontier_units')] == [4, 2, 2, 4]
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    assert text.count('SourceRank4InnerExchange.axis1_output_facts') == 2
    assert args[-1] == before
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None:
            assert new == old and new['layout'] == 'replicated_within_dp'
        else:
            assert new['predecessor'] == old['facts_theorem']
            assert new['source_step'] == old['source_step'] and new['source_step']['op'] == 'FW_softmax'
            assert new['sm_output_ref'] == old['sm_output_ref'] and new['global_shape'] == old['global_shape']
            assert new['gather_axis'] == 2 and new['input_gather_axis'] == 1
            assert new['local_shape'] == [1, 4, 1, 2]
            fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
            assert fragment.split(' := by')[0].count('(h') == 3
            assert old['facts_theorem']+' s p t q hs hp hvalues' in fragment
    for r in detail['reads']:
        assert (r['world'], r['input_gather_axis'], r['gather_axis'], r['output_gather_axis'], r['params']) == ('pm', 1, 1, 2, [1, 2])
        assert r['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][r['execution_index']:]
    assert all(not d['value_proved'] for d in detail['deferred_units'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', 'fw_softmax', 'fw_matmul', '(hshape :', '(houtput :'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def seam(args, prior):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    index = _Index(args[1], args[3]._inputs[1])
    old = next(u for u in prior['frontier_units'] if u['gather_axis'] == 1)
    ports = [middle._output(index, d) for d in old['local_steps']]
    return index, old, ports, view._consumer(index, ports[0])


def test_parent_identity_after_fresh_predecessor_acceptance(baseline):
    args, prior = copy.deepcopy(baseline)
    _, _, _, cell = seam(args, prior)
    cell._input_irs = copy.deepcopy(cell._input_irs)
    cell._input_irs[0].parent.tid += 17
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent identity'):
        api().render(*args)


@pytest.mark.parametrize('mode', ['absent', 'local-only', 'all-peers'])
def test_optional_input_metadata_honest_coverage(baseline, mode):
    args, prior = copy.deepcopy(baseline)
    _, _, _, cell = seam(args, prior)
    if mode == 'absent': del cell._input_irs
    if mode == 'local-only': cell._input_irs = cell._input_irs[:1]
    assert predecessor.render(*args)[1]['frontier_units']
    _, detail = api().render(*args)
    row = detail['reads'][0]
    assert row['input_metadata'] == mode
    assert row['input_parent_identity'] == ('not-observed' if mode == 'absent' else mode)


@pytest.mark.parametrize('field,fault', [('_input_irs', 'name'), ('_input_irs', 'bounds'),
    ('_input_irs', 'value'), ('_output_irs', 'name'), ('_output_irs', 'bounds'),
    ('_output_irs', 'value')])
def test_paired_metadata_after_fresh_predecessor_acceptance(baseline, field, fault):
    args, prior = copy.deepcopy(baseline); _, _, _, cell = seam(args, prior)
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs); ir = irs[0]
    if fault == 'name': ir.parent.name = 'different-value'
    elif fault == 'value': ir.valmap = (1, 2)
    else:
        bounds = list(ir.indmap); lo, hi = bounds[2]; bounds[2] = (lo+1, hi+1); ir.indmap = tuple(bounds)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('kwargs', [dict(idim=2, odim=1), dict(idim=True, odim=2),
    dict(idim=1, odim=2, __consts=[1]), dict(idim=1, odim=2, extra=None)])
def test_raw_kwargs_private_boundary_guard(baseline, kwargs):
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    cell.kwargs = dict(ranks=old['ranks'], **kwargs)
    # The predecessor leaves these raw next-collective kwargs unproved.
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api()._boundary(index, cell, ports, old['ranks'], 0)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['owner', 'positions', 'order', 'call', 'export', 'fullref'])
def test_upstream_authority_seams(baseline, fault):
    args, prior = copy.deepcopy(baseline); _, _, _, cell = seam(args, prior)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault == 'owner': args[3]._inputs[3]['config']['units'][0]['ranks'].reverse()
    elif fault == 'positions': args[3]._inputs[3]['config']['units'][0]['positions'] = [99]
    elif fault == 'order': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'export': writer['export_id'] = 'different'
    else: writer['inputs'][0]['version'] += 1
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


def test_coherent_T3_geometry_and_partial_metadata():
    args = prepared(2, 3, 6); prior = predecessor.render(*args)[1]
    text, detail = api().render(*args)
    assert len(detail['reads']) == 6 and len(detail['units']) == 2
    assert [u['local_shape'] for u in detail['units']] == [[1, 6, 2, 6]]*2
    assert 'axis1_output_facts 2 0 3 1 2 2 6' in text
    _, _, _, cell = seam(args, prior); cell._input_irs = cell._input_irs[:2]
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='partial'): api().render(*args)


@pytest.mark.parametrize('where', ['selected', 'last'])
def test_complete_selected_and_bw_suffix_nonwrite(baseline, where):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    step, _ = api()._boundary(index, cell, ports, old['ranks'], 0)
    source = args[1]; _, row = api()._read(source, step, args[-1]['pm'])
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if where == 'selected' else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    assert source.nodes().index(target) in row['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[0]]
    if where == 'selected': step = replace(step, outputs=step.inputs[:1])
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, step, args[-1]['pm'])


def test_duplicate_crossunit_and_order_private_seams(baseline):
    args, prior = copy.deepcopy(baseline)
    prior['frontier_units'].reverse()
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['gather_axis'] for u in detail['frontier_units']] == [None, 2, None, 2]
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None: assert new is old
    prior['frontier_units'].append(copy.deepcopy(prior['frontier_units'][1]))
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_failclosed_malformed_original_arguments(baseline):
    args = list(copy.deepcopy(baseline[0])); args[3] = None
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('T', [0, False])
def test_private_unit_positive_T_before_division(baseline, T):
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict.runtime_lineage import _Index
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    step, _ = api()._boundary(index, cell, ports, old['ranks'], 0)
    g = middle._output(_Index(args[0], args[3]._inputs[0]), old['source_step'])
    old['dimensions']['T'] = T
    with pytest.raises(ValueError, match='positive'):
        api()._unit(old, g, ports, [step], {})


def test_none_input_metadata_upstream_seam_and_private_honesty(baseline):
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    cell._input_irs = None
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    _, coverage = api()._boundary(index, cell, ports, old['ranks'], 0)
    assert coverage['input_metadata'] == 'absent'
    assert coverage['input_parent_identity'] == 'not-observed'


def test_optional_output_metadata_and_crossunit_rejection(baseline):
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    del cell._output_irs
    assert predecessor.render(*args)[1]['frontier_units']
    _, detail = api().render(*args)
    assert detail['reads'][0]['output_metadata'] == 'absent'
    foreign = next(u for u in prior['frontier_units'] if u['gather_axis'] == 1 and u['unit'] != old['unit'])
    from Verdict import runtime_middle_exchange_values as middle
    foreign_ports = [middle._output(index, d) for d in foreign['local_steps']]
    with pytest.raises(ValueError): api()._boundary(index, cell, foreign_ports, old['ranks'], 0)


def test_asymmetric_inner_exchange_formula():
    import numpy as np
    D, T, B, S, H, C = 2, 3, 2, 5, 2, 7
    global_ = np.arange(B*D*S*T*H*T*C).reshape(B*D, S*T, H*T, C)
    for u in range(D):
        chunk = global_[u*B:(u+1)*B]
        xs = np.split(chunk, T, axis=1)
        outputs = [np.concatenate([np.split(x, T, axis=2)[j] for x in xs], axis=1) for j in range(T)]
        assert all(y.shape == (B, S*T, H, C) for y in outputs)
        assert np.array_equal(chunk, np.concatenate(outputs, axis=2))
        assert not np.array_equal(chunk, np.concatenate(outputs[::-1], axis=2))
