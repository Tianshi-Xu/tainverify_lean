"""First source last-axis softmax: portable authority tests, no kernel claim."""
import copy
import importlib
import importlib.util
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_div_exchange_values as previous
from Verdict import runtime_div_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_softmax_values'), 'softmax renderer missing'
    return importlib.import_module('Verdict.runtime_softmax_values')


def fixture(D=2, tp=2, seqlen=2, branches=3):
    sm, pm, authority = previous.fixture(D, tp, seqlen, branches)
    for graph in (sm, pm):
        for cell in graph.cells:
            if cell.opname != 'FW_softmax':
                continue
            cell.kwargs = dict(dim=-1, dtype=None, __consts=[])
            old = cell._output_irs[0]
            out = copy.deepcopy(cell._input_irs[0])
            out.tid = old.tid; out.parent.tid = old.parent.tid
            out.parent.name = 'attention.normalized'
            cell._output_irs = [out]
            graph.shapes[cell.outputs[0]] = out.shape
            for consumer in graph.cells:
                for j, ref in enumerate(consumer.inputs):
                    if ref == cell.outputs[0]:
                        consumer._input_irs[j] = copy.deepcopy(out)
    # Real BW_softmax saved-primal readers remain in the complete schedule.
    from types import SimpleNamespace as NS
    from scripts.tests.test_graph_to_lean_runtime_lineage import N, T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    snapshot = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        for forward in list(graph.cells):
            if forward.opname != 'FW_softmax': continue
            out = copy.deepcopy(forward._input_irs[0]); out.tid = 9901
            out.parent.tid = 9901; out.parent.name = 'score.gradient'
            cell = NS(node=N(world, forward.rank, 0, 9901, 'BW_softmax'), rank=forward.rank,
                opname='BW_softmax', inputs=[forward.outputs[0], forward.inputs[0]],
                outputs=[T(world, forward.rank, 0, 9901, 1)], kwargs=dict(dim=-1, dtype=None),
                _input_irs=[copy.deepcopy(forward._output_irs[0]), copy.deepcopy(forward._input_irs[0])],
                _output_irs=[out])
            cell.ir = NS(signature='BW_softmax', inputs=lambda c=cell: c._input_irs,
                outputs=lambda c=cell: c._output_irs)
            graph.cells.append(cell); graph.shapes[cell.outputs[0]] = out.shape
            if world == 'p':
                rows.append(dict(ref=dict(world=world, runtime_rank=cell.rank, microbatch=0,
                    source_cid=9901, call_instance=0, op='BW_softmax', origin='fixture'),
                    source_irname='BW_softmax', inputs=[tref(t) for t in cell.inputs],
                    outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[]))
    rebuilt = build_snapshot([*snapshot['writers'], *rows])
    rebuilt.update({k: snapshot[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    rebuilt['adapter_source'] = [*snapshot['adapter_source'], *copy.deepcopy(rows)]
    bind_reducers(rebuilt); bind_adapters(rebuilt)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), rebuilt, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3):
    base = previous.previous.previous.previous.previous.previous.previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=fixture(D, tp, seqlen, branches)):
        return base.prepared(D, tp, seqlen)


def test_first_softmax_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]
    before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'deferred_units', 'frontier_units')] == [5, 2, 2, 4]
    assert [r['world'] for r in detail['reads']] == ['sm', 'pm', 'pm', 'pm', 'pm']
    assert text.count('SourceSoftmaxRead.softmax_value_of_split') == 5
    assert text.count('TrainVerify.Denote.source_softmax_unit_output_reconstruct') == 2
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
            assert new['gather_axis'] == 1 and new['normalization_axis'] == 3
            assert new['source_step']['op'] == 'FW_softmax'
            assert all(s['op'] == 'FW_softmax' for s in new['local_steps'])
            fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
            assert fragment.split(' := by')[0].count('(h') == 3
            assert old['facts_theorem']+' s p t q hs hp hvalues' in fragment
            assert 'List.map fw_softmax' in fragment and 'predecessor.2.2' in fragment
    for r in detail['reads']:
        assert r['params'] == [] and r['request'] == 'global'
        assert r['normalization_axis'] == 3 and r['source_kwargs'] == dict(dim=-1, dtype=None, __consts=[])
        assert r['operand_nonwrite_source_indices'] == args[-1][r['world']]['execution_to_source'][r['execution_index']:]
    assert detail['reads'][0]['frontier_index'] == 0
    assert all(not d['value_proved'] and d['first_consumers'] for d in detail['deferred_units'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def softmax_cells(args, label='pm'):
    return [c for c in args[3]._inputs[0 if label == 'sm' else 1] if c.opname == 'FW_softmax']


def seam(args, prior, label='pm'):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    index = _Index(args[0 if label == 'sm' else 1], args[3]._inputs[0 if label == 'sm' else 1])
    old = next(u for u in prior['frontier_units'] if u['gather_axis'] == 1)
    descriptor = old['source_step'] if label == 'sm' else old['local_steps'][0]
    port = middle._output(index, descriptor)
    return index, old, port, softmax_cells(args, label)[0]


def test_nonempty_source_params_cannot_be_erased_by_normalization(baseline):
    from Verdict import graph_to_lean as compiler
    args, _ = copy.deepcopy(baseline)
    get_params = compiler._get_node_params
    # A nonempty extractor list can still have false Python truthiness.
    # This is returned by the extractor, not an invented raw kwarg schema.
    class FalseNonempty(list):
        def __bool__(self): return False
    def changed(source, node, num_parts=0):
        if source.node_opname(node) == 'FW_softmax': return FalseNonempty([3])
        return get_params(source, node, num_parts=num_parts)
    with patch.object(compiler, '_get_node_params', side_effect=changed):
        assert predecessor.render(*args)[1]['frontier_units']
        with pytest.raises(ValueError, match='empty params'):
            api().render(*args)


@pytest.mark.parametrize('label', ['sm', 'pm'])
def test_raw_producer_consumer_parent_identity_after_accepted_predecessor(baseline, label):
    args, _ = copy.deepcopy(baseline)
    cell = softmax_cells(args, label)[0]
    cell._input_irs = copy.deepcopy(cell._input_irs)
    cell._input_irs[0].parent.tid += 1
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent identity'):
        api().render(*args)


@pytest.mark.parametrize('peer', [0, 1])
@pytest.mark.parametrize('metadata', ['absent', 'none'])
@pytest.mark.parametrize('changed_parent', [False, True])
def test_optional_pm_producer_metadata_cannot_bypass_softmax_parent_check(
        baseline, peer, metadata, changed_parent):
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    args, prior = copy.deepcopy(baseline)
    index, old, _, _ = seam(args, prior)
    port = middle._output(index, old['local_steps'][peer])
    cell = view._consumer(index, port)
    assert port.endpoint.writer is not None
    producer = index.raw[port.endpoint.writer]
    cell._input_irs = copy.deepcopy(cell._input_irs)
    assert cell._input_irs[0].parent.tid == producer._output_irs[0].parent.tid
    if changed_parent:
        cell._input_irs[0].parent.tid += 12345
    if metadata == 'absent':
        del producer._output_irs
    else:
        producer._output_irs = None
    # Optional metadata remains legal upstream, even on a different TP peer.
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='complete original producer output metadata'):
        api().render(*args)


@pytest.mark.parametrize('metadata', [[], [None]], ids=['partial-arity', 'missing-entry'])
def test_incomplete_pm_producer_metadata_is_rejected_upstream(baseline, metadata):
    args, prior = copy.deepcopy(baseline)
    index, _, port, _ = seam(args, prior)
    assert port.endpoint.writer is not None
    index.raw[port.endpoint.writer]._output_irs = metadata
    with pytest.raises(ValueError):
        predecessor.render(*args)
    with pytest.raises(ValueError):
        api().render(*args)


@pytest.mark.parametrize('metadata', ['absent', 'empty'])
def test_missing_sm_producer_metadata_is_rejected_upstream(baseline, metadata):
    args, prior = copy.deepcopy(baseline)
    index, _, port, _ = seam(args, prior, 'sm')
    assert port.endpoint.writer is not None
    producer = index.raw[port.endpoint.writer]
    if metadata == 'absent':
        del producer._output_irs
    else:
        producer._output_irs = []
    # These are upstream raw-port/shape failures, not evidence for the new guard.
    with pytest.raises(ValueError, match='independent raw'):
        predecessor.render(*args)
    with pytest.raises(ValueError, match='independent raw'):
        api().render(*args)


def set_kwargs(args, label, cell, kwargs):
    source = args[0 if label == 'sm' else 1]
    node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    # Keep original source and independent raw kwargs coherent.
    source.node_kwargs(node).clear(); source.node_kwargs(node).update(copy.deepcopy(kwargs))
    cell.kwargs.clear(); cell.kwargs.update(copy.deepcopy(kwargs))


@pytest.mark.parametrize('D,tp,seqlen', [(3, 3, 9), (3, 2, 6), (1, 2, 4)])
def test_dimensions_order_and_equivalent_raw_axes(D, tp, seqlen):
    args = prepared(D, tp, seqlen)
    for label in ('sm', 'pm'):
        for j, cell in enumerate(softmax_cells(args, label)):
            set_kwargs(args, label, cell, dict(dim=3 if label == 'sm' or j % 2 else -1))
    prior = predecessor.render(*args)[1]
    text, detail = api().render(*args)
    assert len(detail['reads']) == 1+D*tp
    assert len(detail['units']) == D and len(detail['frontier_units']) == 2*D
    assert len(detail['deferred_units']) == D
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None: assert new == old
        else:
            assert new['global_shape'] == [D, 2*tp, seqlen, seqlen]
            assert new['local_shape'] == [1, 2, seqlen, seqlen]
            assert new['positions'] == old['positions'] and new['ranks'] == old['ranks']
    for r in detail['reads']:
        assert r['normalization_axis'] == 3
        assert r['source_kwargs']['dim'] in (-1, 3) and 'dtype' not in r['source_kwargs']
        source = args[0 if r['world'] == 'sm' else 1]
        bw = {i for i, n in enumerate(source.nodes()) if source.node_opname(n) == 'BW_softmax'}
        assert bw & set(r['operand_nonwrite_source_indices'])
        assert sorted(args[-1][r['world']]['execution_to_source']) == list(range(len(source.nodes())))
    assert text.count('SourceSoftmaxRead.softmax_value_of_split') == 1+D*tp


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('kwargs', [dict(dim=3.0), dict(dim=True), dict(dim=4), dict(dim=-5),
    dict(dim=0), dict(dim=-2), {}, dict(dim=-1, dtype='float32'),
    dict(dim=-1, __consts=[3]), dict(dim=-1, unexpected=None)])
def test_raw_schema_new_guard_after_accepted_predecessor(baseline, label, kwargs):
    args, _ = copy.deepcopy(baseline); cell = softmax_cells(args, label)[0]
    set_kwargs(args, label, cell, kwargs)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('rank', [1, 2, 3, 4, 5])
def test_axis_normalization_uses_actual_rank(baseline, rank):
    args, _ = copy.deepcopy(baseline); source = args[0]; cell = softmax_cells(args, 'sm')[0]
    node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    with patch.object(source, 'tensor_shape', return_value=(2,)*rank):
        for dim in (-1, rank-1):
            set_kwargs(args, 'sm', cell, dict(dim=dim))
            assert api()._axis(source, node) == rank-1
        for dim in (rank, -rank-1, True, float(rank-1)):
            set_kwargs(args, 'sm', cell, dict(dim=dim))
            with pytest.raises(ValueError): api()._axis(source, node)


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['name', 'parent', 'bounds', 'batch', 'value', 'shape', 'empty', 'absent'])
def test_paired_metadata_new_guard_or_explicit_upstream_rejection(baseline, label, field, fault):
    args, prior = copy.deepcopy(baseline); cell = softmax_cells(args, label)[0]
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs); ir = irs[0]
    if fault == 'absent': delattr(cell, field)
    elif fault == 'empty': setattr(cell, field, [])
    elif fault == 'name': ir.parent.name = 'unrelated'
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'shape': ir.shape = (*ir.shape[:-1], 99)
    else:
        bounds = list(ir.indmap); axis = 0 if fault == 'batch' else 1
        lo, hi = bounds[axis]; bounds[axis] = (lo+1, hi+1); ir.indmap = tuple(bounds)
    if fault in ('shape', 'empty', 'absent'):
        # Whole-source shape/arity authentication rejects these before this checkpoint.
        with pytest.raises(ValueError): predecessor.render(*args)
    else:
        assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('params', [[0], [3], (3,), [True], '3', {'ignored': 3}])
def test_source_extractor_exact_empty_params(baseline, params):
    from Verdict import graph_to_lean as compiler
    args, _ = copy.deepcopy(baseline); original = compiler._get_node_params
    def changed(source, node, num_parts=0):
        return params if source.node_opname(node) == 'FW_softmax' else original(source, node, num_parts=num_parts)
    with patch.object(compiler, '_get_node_params', side_effect=changed):
        assert predecessor.render(*args)[1]['frontier_units']
        with pytest.raises(ValueError, match='empty params'): api().render(*args)


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('where', ['selected', 'last', 'BW_softmax'])
def test_actual_input_selected_and_entire_bw_suffix_nonwrite(baseline, label, where):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index, _, port, cell = seam(args, prior, label)
    step, _ = api()._softmax(index, cell, port); source = index.view
    _, read = api()._read(source, label, step, args[-1][label])
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    if where == 'selected': target = node
    elif where == 'last': target = source.nodes()[args[-1][label]['execution_to_source'][-1]]
    else:
        target = next(n for n in source.nodes() if source.node_opname(n) == 'BW_softmax'
            and source.node_inputs(node)[0] in source.node_inputs(n))
    assert source.nodes().index(target) in read['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[0]]
    if where == 'selected': step = replace(step, outputs=step.inputs)
    with pytest.raises(ValueError, match='operand.*written'):
        api()._read(source, label, step, args[-1][label])


@pytest.mark.parametrize('fault', ['inputs', 'outputs', 'call', 'export', 'writer', 'owner', 'positions', 'order'])
def test_original_authority_upstream_rejection(baseline, fault):
    args, _ = copy.deepcopy(baseline); cell = softmax_cells(args)[0]
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault in ('inputs', 'outputs'): writer[fault][0]['version'] += 1
    elif fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'export': writer['export_id'] = 'forged'
    elif fault == 'writer': writer['source_irname'] = 'FW_unknown'
    elif fault == 'owner': args[3]._inputs[3]['config']['units'][0]['ranks'].reverse()
    elif fault == 'positions': args[3]._inputs[3]['config']['units'][0]['positions'] = [99]
    else: args[-1]['pm']['execution_to_source'].reverse()
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['missing', 'unknown', 'mixed', 'duplicate'])
def test_private_discovery_inventory_guards(baseline, fault):
    from scripts.tests.test_graph_to_lean_runtime_lineage import N
    args, prior = copy.deepcopy(baseline); cells = softmax_cells(args)
    if fault == 'missing': args[3]._inputs[1].remove(cells[0])
    elif fault == 'duplicate':
        cell = copy.deepcopy(cells[0]); cell.node = N('p', cell.rank, 0, 9999, cell.opname)
        args[3]._inputs[1].append(cell)
    else:
        for cell in (cells if fault == 'unknown' else cells[:1]): cell.opname = 'FW_unknown'
    # Explicit private discovery seam; no claim that a forged whole source is accepted.
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('field', ['inputs', 'outputs'])
def test_raw_arity_upstream_rejection_and_private_guard(baseline, field):
    args, prior = copy.deepcopy(baseline); cell = softmax_cells(args)[0]
    getattr(cell, field).append(getattr(cell, field)[0])
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'layout', 'duplicate'])
def test_private_frontier_owner_guards(baseline, fault):
    args, prior = copy.deepcopy(baseline); old = prior['frontier_units'][0]
    if fault == 'ranks': old['ranks'].reverse()
    elif fault == 'positions': old['positions'] = [99]
    elif fault == 'layout': old['layout'] = 'replicated_within_dp'
    else: prior['frontier_units'].append(copy.deepcopy(old))
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_reversed_frontier_sm_dedup_keeps_first_auth_annotation(baseline):
    args, prior = copy.deepcopy(baseline); prior['frontier_units'].reverse()
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['gather_axis'] for u in detail['frontier_units']] == [None, 1, None, 1]
    assert len([r for r in detail['reads'] if r['world'] == 'sm']) == 1
    smread = next(r for r in detail['reads'] if r['world'] == 'sm')
    assert smread['unit'] == prior['frontier_units'][1]['unit'] and smread['frontier_index'] == 1
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None: assert new is old


def test_deferred_original_port_correspondence(baseline):
    args, prior = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.opname == 'FW_matmul' and c.node.cid == 9200)
    cell.inputs.reverse(); cell._input_irs.reverse(); source = args[1]
    node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    source._node2inputs[node].reverse()
    writer = next(w for w in source._collective_source['writers']
        if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == cell.rank)
    writer['inputs'].reverse()
    with pytest.raises(ValueError, match='deferred.*port'):
        api()._render(args[0], args[1], args[3], args[-1], prior)


def test_complete_unsharded_normalization_guard(baseline):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index, _, producer, cell = seam(args, prior)
    # Same shape but a larger raw parent: normalized rows are incomplete.
    shape = (*producer.parent_shape[:-1], producer.parent_shape[-1]+1)
    producer = replace(producer, parent_shape=shape)
    for ir in (cell._input_irs[0], cell._output_irs[0]): ir.parent.shape = shape
    with pytest.raises(ValueError, match='complete normalization'):
        api()._softmax(index, cell, producer)


def test_global_request_not_invented_for_collective_scope(baseline):
    args, prior = copy.deepcopy(baseline); index, _, port, cell = seam(args, prior)
    node = next(n for n in index.view.nodes() if tuple(n) == tuple(cell.node))
    index.view.collective_scopes[node] = object()
    with pytest.raises(ValueError, match='global request'): api()._softmax(index, cell, port)


def test_asymmetric_position_sensitive_softmax_formula():
    # CPU formula replay only: neither runtime execution nor Lean refinement.
    import numpy as np
    D, T, B, H, Q, C = 3, 3, 2, 2, 5, 7
    grid = np.arange(D*B*H*T*Q*C).reshape(D*B, H*T, Q, C)
    x = np.sin(grid / 7) + np.cos(grid / 11)
    def softmax(a):
        ex = np.exp(a - a.max(axis=-1, keepdims=True))
        return ex / ex.sum(axis=-1, keepdims=True)
    full = softmax(x)
    for u in range(D):
        chunk = x[u*B:(u+1)*B]
        locals_ = [softmax(z) for z in np.split(chunk, T, axis=1)]
        assert all(z.shape == (B, H, Q, C) for z in locals_)
        assert np.array_equal(full[u*B:(u+1)*B], np.concatenate(locals_, axis=1))
        assert not np.allclose(full[u*B:(u+1)*B], np.concatenate(locals_[::-1], axis=1))


def test_deferred_requires_exact_replicated_none(baseline):
    args, prior = copy.deepcopy(baseline)
    old = next(u for u in prior['frontier_units'] if u['gather_axis'] is None)
    prior['frontier_units'] = [old]; old['dimensions']['T'] = 1
    for key in ('ranks', 'positions', 'local_steps', 'pm_output_refs', 'pm_output_tids'):
        old[key] = old[key][:1]
    owner = next(u for u in args[3]._inputs[3]['config']['units'] if u['unit'] == old['unit'])
    owner['ranks'] = old['ranks']; owner['positions'] = old['positions']
    old['layout'] = 'sharded'; old['gather_axis'] = 1
    with pytest.raises(ValueError, match='deferred.*replicated'):
        api()._render(args[0], args[1], args[3], args[-1], prior)


def test_raw_rank_owner_upstream_rejection_and_private_guard(baseline):
    args, prior = copy.deepcopy(baseline); softmax_cells(args)[0].rank = 1
    with pytest.raises(ValueError, match='raw node/owner identity'): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_private_adapter_asymmetric_geometry(baseline):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index, old, port, cell = seam(args, prior, 'sm')
    global_, _ = api()._softmax(index, cell, port)
    pi, _, _, _ = seam(args, prior)
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    locals_ = []
    for descriptor in old['local_steps']:
        p = middle._output(pi, descriptor)
        locals_.append(api()._softmax(pi, view._consumer(pi, p), p)[0])
    # Private emitter geometry oracle, not a new original-source/capture receipt.
    B, H, Q, C = 2, 3, 5, 7
    D, T = old['dimensions']['D'], old['dimensions']['T']
    whole, local = (B*D, H*T, Q, C), (B, H, Q, C)
    def shaped(step, j=None):
        shape = whole if j is None else local
        parent = whole if j is None else (B, *whole[1:])
        bounds = tuple((0, d) if j is None or a != 1 else (j*H, (j+1)*H)
            for a, d in enumerate(shape))
        def port_(p):
            return replace(p, endpoint=replace(p.endpoint, shape=shape), parent_shape=parent, bounds=bounds)
        return replace(step, inputs=tuple(map(port_, step.inputs)), outputs=tuple(map(port_, step.outputs)))
    global_ = shaped(global_); locals_ = [shaped(s, j) for j, s in enumerate(locals_)]
    old['dimensions']['B'] = B; old['local_shape'] = list(local); old['global_shape'] = list(whole)
    names = {s.node: 'originalRead_'+str(i) for i, s in enumerate([global_, *locals_])}
    proof, row = api()._unit(old, global_, locals_, names)
    text = '\n'.join(proof)
    assert row['global_shape'] == list(whole) and row['local_shape'] == list(local)
    assert f'source_softmax_unit_output_reconstruct {D} {T} {B} {H} {Q} {C}' in text
    assert text.count('(h') == 3
