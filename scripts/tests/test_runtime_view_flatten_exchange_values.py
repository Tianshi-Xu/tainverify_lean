"""Portable source rank-three exchange tests; no capture or kernel claim."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_view_flatten_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_view_flatten_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_view_flatten_exchange_values'), 'flatten exchange renderer missing'
    return importlib.import_module('Verdict.runtime_view_flatten_exchange_values')


def fixture(D=2, tp=2, seqlen=2):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    old = copy.deepcopy(authority[2]); rows, adapters = [], []
    producers = [c for c in pm.cells if c.opname == 'FW_view' and len(c._output_irs[0].shape) == 3
                 and c._output_irs[0].parent.name == 'new.flatten.result']
    for producer in producers:
        x = producer._output_irs[0]
        ranks = list(range(producer.rank//tp*tp, (producer.rank//tp+1)*tp))
        peers = [next(p for p in producers if p.rank == r) for r in ranks]
        j = ranks.index(producer.rank); bounds = list(x.indmap)
        bounds[2] = (0, x.parent.shape[2]); width, rem = divmod(x.parent.shape[1], tp)
        assert rem == 0
        bounds[1] = (j*width, (j+1)*width)
        out = IR(23000, x.parent.name, x.parent.shape, tuple(bounds))
        kwargs = dict(ranks=ranks, idim=2, odim=1)
        cell = NS(node=N('p', producer.rank, 0, 23000, 'AllToAllPrim'), rank=producer.rank,
            opname='AllToAllPrim', inputs=[p.outputs[0] for p in peers],
            outputs=[T('p', producer.rank, 0, 23000, 1)], kwargs=kwargs,
            _input_irs=[copy.deepcopy(p._output_irs[0]) for p in peers], _output_irs=[out])
        cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs,
            outputs=lambda c=cell: c._output_irs)
        pm.cells.append(cell); pm.shapes[cell.outputs[0]] = out.shape
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0, source_cid=23000,
            call_instance=0, op='AllToAllPrim', origin='fixture'), source_irname=cell.node[-1],
            inputs=[tref(t) for t in cell.inputs], outputs=[tref(t) for t in cell.outputs],
            parameter_grad_tids=[], adapter_kwargs=copy.deepcopy(kwargs))
        rows.append(row); adapter = copy.deepcopy(row); adapter['inputs'] = [tref(producer.outputs[0])]
        adapter['primitive'] = dict(kind='AllToAllPrim', forward=True, kwargs=copy.deepcopy(kwargs),
            signature='nnscaler.runtime.adapter.all_to_all', generated_inputs=['flattened'], generated_outputs=['hidden_exchanged'])
        params = ', '.join(f'{k}={v!r}' for k, v in kwargs.items())
        old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace(
            '\ndef _train_step', '\n        hidden_exchanged = nnscaler.runtime.adapter.all_to_all(flattened, '+params+')\ndef _train_step')
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


def test_flatten_exchange_source_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [4, 2, 2, 0]
    assert detail['consumed_frontier_indices'] == [0, 1] and args[-1] == before
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    assert text.count('SourceHiddenSequenceExchange.output_facts') == 2
    for old, new in zip(prior['frontier_units'], detail['units'], strict=True):
        assert new['source_step'] == old['source_step'] and new['source_step']['op'] == 'FW_view'
        assert new['sm_output_ref'] == old['sm_output_ref'] and new['global_shape'] == old['global_shape']
        assert new['layout'] == 'sharded' and new['gather_axis'] == 1 and new['input_gather_axis'] == 2
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions'] and 'slot' not in new
        B, ST, H = old['local_shape']; T = old['dimensions']['T']; D = old['dimensions']['D']
        assert new['dimensions'] == dict(D=D, T=T, B=B, S=ST//T, H=H)
        assert new['local_shape'] == [B, ST//T, H*T]
        assert new['facts_theorem'].startswith('viewFlattenExchangeUnitFacts_')
        fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert old['facts_theorem']+' s p t q hs hp hvalues' in fragment
        assert 'rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs' in fragment
        assert f'chunkPrimDimN 0 {D} {new["unit"]}' in fragment and f'allGatherPrimDimN 1 {T} 0' in fragment
    for row in detail['reads']:
        assert row['theorem'].startswith('viewFlattenExchangeRead_') and row['request'] == 'group'
        assert row['world'] == 'pm' and row['params'] == [2, 1]
        assert row['source_step']['outputs'][0]['endpoint']['ref'] == tuple(row['ref'])
        assert row['producer_metadata'] == 'all-peers'
        assert row['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][row['execution_index']:]
        assert f'pmNode_{row["source_index"]}' in text
    assert any(r['source_index'] != r['execution_index'] for r in detail['reads'])
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :', 'fw_matmul', 'fw_linear'):
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


@pytest.mark.parametrize('parent', [True, 123456])
def test_raw_input_parent_fresh_predecessor_accepts(baseline, parent):
    args, prior = copy.deepcopy(baseline); _, _, _, cell = seam(args, prior)
    cell._input_irs = copy.deepcopy(cell._input_irs)
    cell._input_irs[0].parent.tid = parent
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent identity'): api().render(*args)


@pytest.mark.parametrize('field,fault', [('_input_irs', 'bounds'), ('_input_irs', 'shape'),
    ('_input_irs', 'value'), ('_input_irs', 'name'), ('_output_irs', 'bounds'),
    ('_output_irs', 'shape'), ('_output_irs', 'value'), ('_output_irs', 'name'),
    ('_output_irs', 'bool-shape'), ('_output_irs', 'bool-parent'), ('_output_irs', 'missing')])
def test_metadata_fresh_predecessor_accepts(baseline, field, fault):
    args, prior = copy.deepcopy(baseline); _, _, _, cell = seam(args, prior)
    setattr(cell, field, copy.deepcopy(getattr(cell, field))); ir = getattr(cell, field)[0]
    if fault == 'bounds':
        bounds = list(ir.indmap); a, b = bounds[2]; bounds[2] = (a+1, b+1); ir.indmap = tuple(bounds)
    elif fault == 'shape': ir.parent.shape = (*ir.parent.shape[:2], ir.parent.shape[2]+1)
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'name': ir.parent.name = 'unrelated-value'
    elif fault == 'bool-shape': ir.parent.shape = (True, *ir.parent.shape[1:])
    elif fault == 'bool-parent': ir.parent.tid = True
    else: delattr(cell, field)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('kwargs', [dict(idim=1, odim=2), dict(idim=True, odim=1),
    dict(idim=2, odim=True), dict(idim=2.0, odim=1), dict(idim=5, odim=1),
    dict(idim=2, odim=-2), dict(idim=2, odim=1, __consts=False),
    dict(idim=2, odim=1, extra=None)])
def test_raw_kwargs_fresh_predecessor_accepts(baseline, kwargs):
    args, prior = copy.deepcopy(baseline); _, old, _, cell = seam(args, prior)
    cell.kwargs = dict(ranks=old['ranks'], **kwargs)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['owner', 'positions', 'order', 'call', 'export', 'fullref'])
def test_upstream_authority_attribution(baseline, fault):
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


@pytest.mark.parametrize('field,value', [('params', (True, 1)), ('params', (2, True)),
    ('params', (2.0, 1)), ('params', (5, 1)), ('params', (2, -2)), ('params', (1, 2)),
    ('params', (2,)), ('local_index', True), ('local_index', -1),
    ('local_index', 2), ('ranks', (1, 0)), ('input_tids', ())])
def test_scope_upstream_and_private_attribution(baseline, field, value):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    key = next(n for n in args[1].collective_scopes if tuple(n) == tuple(cell.node))
    args[1].collective_scopes[key] = replace(args[1].collective_scopes[key], **{field: value})
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._boundary(index, cell, ports, old['ranks'], 0)


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'cross-DP', 'duplicate', 'axis', 'bool-axis', 'cover'])
def test_private_frontier_not_public_authority(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['frontier_units']
    old = prior['frontier_units'][0]
    if fault == 'ranks': old['ranks'].reverse()
    elif fault == 'positions': old['positions'] = [99]
    elif fault == 'cross-DP': old['local_steps'] = prior['frontier_units'][1]['local_steps']
    elif fault == 'duplicate': prior['frontier_units'].append(copy.deepcopy(old))
    elif fault == 'cover': old['local_steps'] = old['local_steps'][:1]
    else: old['gather_axis'] = True if fault == 'bool-axis' else 1
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('where', ['selected', 'last'])
def test_private_selected_and_entire_BW_suffix(baseline, where):
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


@pytest.mark.parametrize('fault', ['producer', 'sender-order', 'duplicate-sender', 'partial-sender',
    'bool-rank', 'bool-index', 'negative-index', 'high-index', 'bool-bound', 'float-shape'])
def test_private_complete_producer_cover_and_integer_geometry(baseline, fault):
    from dataclasses import replace
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
    elif fault == 'bool-index': j = False
    elif fault == 'negative-index': j = -1
    elif fault == 'high-index': j = len(ranks)
    elif fault == 'bool-bound': ports[0] = replace(ports[0], bounds=((False, 1), *ports[0].bounds[1:]))
    else: ports[0] = replace(ports[0], parent_shape=(1.0, *ports[0].parent_shape[1:]))
    with pytest.raises(ValueError): api()._boundary(index, cell, ports, ranks, j)


@pytest.mark.parametrize('policy', ['absent', 'local-only'])
def test_public_consumer_metadata_policy_complete_producers(baseline, policy):
    args, prior = copy.deepcopy(baseline)
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    index = _Index(args[1], args[3]._inputs[1])
    for old in prior['frontier_units']:
        for j, desc in enumerate(old['local_steps']):
            cell = view._consumer(index, middle._output(index, desc))
            if policy == 'absent': del cell._input_irs
            else: cell._input_irs = cell._input_irs[j:j+1]
    assert predecessor.render(*args)[1]['frontier_units']
    _, detail = api().render(*args)
    assert all(r['input_metadata'] == policy and r['producer_metadata'] == 'all-peers' for r in detail['reads'])


def test_public_T3_nonsymmetric_order_and_partial_metadata():
    args = prepared(2, 3, 9); prior = predecessor.render(*args)[1]
    text, detail = api().render(*args)
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [6, 2, 2, 0]
    for unit in detail['units']:
        assert unit['global_shape'] == [2, 9, 36] and unit['local_shape'] == [1, 3, 36]
        assert unit['dimensions'] == dict(D=2, T=3, B=1, S=3, H=12)
    prior['frontier_units'].reverse()
    _, reversed_ = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['unit'] for u in reversed_['units']] == [1, 0]
    _, _, _, cell = seam(args, prior); cell._input_irs = cell._input_irs[:2]
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='partial'): api().render(*args)


def test_T1_public_fixture_honestly_unsupported():
    with pytest.raises(StopIteration): prepared(2, 1, 2)


def test_T1_private_geometry_not_public_support(baseline):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    args, prior = copy.deepcopy(baseline); index, old, ports, cell = seam(args, prior)
    step, _ = api()._boundary(index, cell, ports, old['ranks'], 0)
    g = middle._output(_Index(args[0], args[3]._inputs[0]), old['source_step'])
    old['dimensions']['T'] = 1; old['ranks'] = old['ranks'][:1]; old['positions'] = old['positions'][:1]
    old['pm_output_refs'] = old['pm_output_refs'][:1]
    old['local_shape'] = [1, *old['global_shape'][1:]]
    def whole(p):
        shape = p.parent_shape
        return replace(p, endpoint=replace(p.endpoint, shape=shape), bounds=tuple((0, d) for d in shape))
    p = whole(ports[0]); step = replace(step, inputs=(p,), outputs=(whole(step.outputs[0]),))
    proof, unit = api()._unit(old, g, [p], [step], {step.node: 'privateRead'})
    assert unit['dimensions']['T'] == 1 and 'allGatherPrimDimN 1 1 0' in '\n'.join(proof)
