"""Portable original-source AA tracer; no capture and no kernel claim."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_contiguous_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_contiguous_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_contiguous_exchange_values'), 'contiguous exchange renderer missing'
    return importlib.import_module('Verdict.runtime_contiguous_exchange_values')


def fixture(D=2, tp=2, seqlen=2):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D, tp, seqlen, consts=True)
    old = copy.deepcopy(authority[2]); rows, adapters = [], []
    producers = [c for c in pm.cells if c.opname == 'FW_contiguous']
    for producer in producers:
        x = producer._output_irs[0]
        ranks = list(range(producer.rank//tp*tp, (producer.rank//tp+1)*tp))
        peers = [next(p for p in producers if p.rank == r) for r in ranks]
        j = ranks.index(producer.rank); bounds = list(x.indmap)
        bounds[1] = (0, x.parent.shape[1]); width, rem = divmod(x.parent.shape[2], tp)
        assert rem == 0
        bounds[2] = (j*width, (j+1)*width)
        out = IR(19000, x.parent.name, x.parent.shape, tuple(bounds))
        kwargs = dict(ranks=ranks, idim=1, odim=2)
        cell = NS(node=N('p', producer.rank, 0, 19000, 'AllToAllPrim'), rank=producer.rank,
            opname='AllToAllPrim', inputs=[p.outputs[0] for p in peers],
            outputs=[T('p', producer.rank, 0, 19000, 1)], kwargs=kwargs,
            _input_irs=[copy.deepcopy(p._output_irs[0]) for p in peers], _output_irs=[out])
        cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs,
            outputs=lambda c=cell: c._output_irs)
        pm.cells.append(cell); pm.shapes[cell.outputs[0]] = out.shape
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0, source_cid=19000,
            call_instance=0, op='AllToAllPrim', origin='fixture'), source_irname=cell.node[-1],
            inputs=[tref(t) for t in cell.inputs], outputs=[tref(t) for t in cell.outputs],
            parameter_grad_tids=[], adapter_kwargs=copy.deepcopy(kwargs))
        rows.append(row); adapter = copy.deepcopy(row); adapter['inputs'] = [tref(producer.outputs[0])]
        adapter['primitive'] = dict(kind='AllToAllPrim', forward=True, kwargs=copy.deepcopy(kwargs),
            signature='nnscaler.runtime.adapter.all_to_all', generated_inputs=['contiguous'], generated_outputs=['exchanged'])
        params = ', '.join(f'{k}={v!r}' for k, v in kwargs.items())
        old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace(
            '\ndef _train_step', '\n        exchanged = nnscaler.runtime.adapter.all_to_all(contiguous, '+params+')\ndef _train_step')
        adapters.append(adapter)
    pm.cells.sort(key=lambda c: (c.rank, c.opname.startswith('BW_')))
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    by_writer = {writer_export_id(w['ref']): w for w in [*old['adapter_source'], *adapters]}
    snapshot['adapter_source'] = [by_writer[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2):
    f = fixture(D, tp, seqlen)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D, tp, seqlen)


def test_first_contiguous_exchange_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [4, 2, 2, 0]
    assert detail['consumed_frontier_indices'] == [0, 1]
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    assert text.count('SourceRank4InnerExchange.axis1_output_facts') == 2
    assert args[-1] == before
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        assert new['source_step'] == old['source_step'] and new['source_step']['op'] == 'FW_contiguous'
        assert new['sm_output_ref'] == old['sm_output_ref'] and new['global_shape'] == old['global_shape']
        assert new['gather_axis'] == 2 and new['input_gather_axis'] == 1
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
        assert new['facts_theorem'].startswith('contiguousExchangeUnitFacts_')
        fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert old['facts_theorem']+' s p t q hs hp hvalues' in fragment
    for r in detail['reads']:
        assert r['theorem'].startswith('contiguousExchangeRead_')
        assert (r['world'], r['params'], r['gather_axis'], r['split_axis']) == ('pm', [1, 2], 1, 2)
        assert r['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][r['execution_index']:]
        assert r['producer_metadata'] == 'all-peers'
    assert any(r['source_index'] != r['execution_index'] for r in detail['reads'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :', 'fw_matmul'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def seam(args, prior):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    index = _Index(args[1], args[3]._inputs[1]); old = prior['frontier_units'][0]
    ports = [middle._output(index, d) for d in old['local_steps']]
    return index, old, ports, view._consumer(index, ports[0])


@pytest.mark.parametrize('field,fault', [('_input_irs', 'parent'), ('_input_irs', 'bounds'),
    ('_input_irs', 'value'), ('_output_irs', 'parent'), ('_output_irs', 'bounds'),
    ('_output_irs', 'value'), ('_input_irs', 'bool-parent'), ('_output_irs', 'bool-shape')])
def test_metadata_after_fresh_predecessor_acceptance(baseline, field, fault):
    args, prior = copy.deepcopy(baseline); _, _, _, cell = seam(args, prior)
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs); ir = irs[0]
    if fault == 'parent':
        if field == '_input_irs': ir.parent.tid += 17
        else: ir.parent.name = 'different-value'
    elif fault == 'bool-parent': ir.parent.tid = True
    elif fault == 'bool-shape': ir.parent.shape = (True, *ir.parent.shape[1:])
    elif fault == 'value': ir.valmap = (1, 2)
    else:
        bounds = list(ir.indmap); lo, hi = bounds[2]; bounds[2] = (lo+1, hi+1); ir.indmap = tuple(bounds)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('kwargs', [dict(idim=2, odim=1), dict(idim=True, odim=2),
    dict(idim=1, odim=False), dict(idim=1, odim=2, __consts=[1]),
    dict(idim=1, odim=2, extra=None)])
def test_raw_kwargs_after_fresh_acceptance(baseline, kwargs):
    args, prior = copy.deepcopy(baseline); _, old, _, cell = seam(args, prior)
    cell.kwargs = dict(ranks=old['ranks'], **kwargs)
    assert predecessor.render(*args)[1]['frontier_units']
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


@pytest.mark.parametrize('field,value', [('params', (True, 2)), ('params', (2, 1)),
    ('params', (1,)), ('local_index', True), ('local_index', -1),
    ('local_index', 2), ('ranks', (1, 0)), ('input_tids', ())])
def test_scope_upstream_rejection_and_private_boundary(baseline, field, value):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    key = next(n for n in args[1].collective_scopes if tuple(n) == tuple(cell.node))
    args[1].collective_scopes[key] = replace(args[1].collective_scopes[key], **{field: value})
    # Fresh rebinding/typed-scope authentication rejects every mutated scope
    # upstream. Direct boundary rejection is additional private evidence only.
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._boundary(index, cell, ports, old['ranks'], 0)


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'cross-DP', 'duplicate', 'axis', 'bool-axis', 'cover'])
def test_private_frontier_not_caller_authority(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['frontier_units']
    old = prior['frontier_units'][0]
    if fault == 'ranks': old['ranks'].reverse()
    elif fault == 'positions': old['positions'] = [99]
    elif fault == 'cross-DP': old['local_steps'] = prior['frontier_units'][1]['local_steps']
    elif fault == 'duplicate': prior['frontier_units'].append(copy.deepcopy(old))
    elif fault == 'cover': old['local_steps'] = old['local_steps'][:1]
    else: old['gather_axis'] = True if fault == 'bool-axis' else 2
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('where', ['selected', 'last'])
def test_private_selected_and_entire_backward_suffix_nonwrite(baseline, where):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    step, _ = api()._boundary(index, cell, ports, old['ranks'], 0)
    source = args[1]; _, row = api()._read(source, step, args[-1]['pm'])
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if where == 'selected' else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    if where == 'last': assert source.node_opname(target).startswith('BW_')
    assert source.nodes().index(target) in row['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[0]]
    if where == 'selected': step = replace(step, outputs=step.inputs[:1])
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, step, args[-1]['pm'])


@pytest.mark.parametrize('fault', ['producer', 'sender-order', 'duplicate-sender', 'partial-sender', 'bool-rank', 'negative-index'])
def test_private_complete_original_sender_cover(baseline, fault):
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    ranks = old['ranks']; j = 0
    if fault == 'producer':
        cell._input_irs = cell._input_irs[:1]
        del index.raw[ports[1].endpoint.writer]._output_irs
    elif fault == 'sender-order': ports.reverse()
    elif fault == 'duplicate-sender': ports[1] = ports[0]
    elif fault == 'partial-sender': ports = ports[:1]
    elif fault == 'bool-rank': ranks[0] = False
    else: j = -1
    with pytest.raises(ValueError): api()._boundary(index, cell, ports, ranks, j)


def test_public_T3_nonsymmetric_and_ordered_frontier():
    args = prepared(2, 3, 9); prior = predecessor.render(*args)[1]
    text, detail = api().render(*args)
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [6, 2, 2, 0]
    for u in detail['units']:
        assert u['global_shape'] == [2, 9, 6, 6] and u['local_shape'] == [1, 9, 2, 6]
        assert u['dimensions'] == dict(D=2, T=3, B=1, S=3, H=2, C=6)
        assert 'allGatherPrimDimN 2 3 0' in text
    prior['frontier_units'].reverse()
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['unit'] for u in detail['units']] == [1, 0]
    index, old, ports, cell = seam(args, prior)
    cell._input_irs = cell._input_irs[:2]
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='partial'): api().render(*args)


def test_T1_private_geometry_only_upstream_fixture_unsupported(baseline):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    step, _ = api()._boundary(index, cell, ports, old['ranks'], 0)
    g = middle._output(_Index(args[0], args[3]._inputs[0]), old['source_step'])
    old['dimensions']['T'] = 1; old['ranks'] = old['ranks'][:1]; old['positions'] = old['positions'][:1]
    def whole(p):
        shape = p.parent_shape
        return replace(p, endpoint=replace(p.endpoint, shape=shape), bounds=tuple((0, d) for d in shape))
    p = whole(ports[0]); step = replace(step, inputs=(p,), outputs=(whole(step.outputs[0]),))
    proof, unit = api()._unit(old, g, [p], [step], {step.node: 'privateRead'})
    assert unit['dimensions']['T'] == 1 and 'allGatherPrimDimN 2 1 0' in '\n'.join(proof)
    with pytest.raises(StopIteration): prepared(2, 1, 2)
