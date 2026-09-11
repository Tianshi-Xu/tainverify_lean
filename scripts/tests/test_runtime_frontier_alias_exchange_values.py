"""Portable residual-frontier source tests; emitted Lean is not kernel evidence."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_attention_residual_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_attention_residual_values as residual


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_alias_exchange_values'), 'frontier alias exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_alias_exchange_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, branches=(0,)):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    old = copy.deepcopy(authority[2]); rows, adapters = [], []

    def append(graph, world, rank, cid, kind, refs, irs, outs, kwargs):
        cell = NS(node=N(world, rank, 0, cid, kind), rank=rank, opname=kind,
            inputs=refs, outputs=[T(world, rank, 0, ir.tid, 1) for ir in outs],
            kwargs=kwargs, _input_irs=copy.deepcopy(irs), _output_irs=outs)
        cell.ir = NS(signature=kind, inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
        at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')), len(graph.cells))
        graph.cells.insert(at, cell)
        graph.shapes.update({ref: ir.shape for ref, ir in zip(cell.outputs, outs, strict=True)})
        if world == 'p':
            row = dict(ref=dict(world=world, runtime_rank=rank, microbatch=0, source_cid=cid,
                call_instance=0, op=kind, origin='fixture'), source_irname=kind,
                inputs=[tref(r) for r in refs], outputs=[tref(r) for r in cell.outputs], parameter_grad_tids=[])
            rows.append(row); adapters.append(copy.deepcopy(row))
        return cell

    aliases = {}
    for world, graph in [('s', sm), ('p', pm)]:
        for producer in [c for c in graph.cells if c.node.cid == 26000]:
            x = producer._output_irs[0]
            outs = [IR(27001+k, x.parent.name, x.parent.shape, x.indmap) for k in range(2)]
            for k, ir in enumerate(outs): ir.parent.tid = 28001+k
            if reverse: outs.reverse()
            alias = append(graph, world, producer.rank, 27000, 'FW_multiref', producer.outputs,
                           [x], outs, dict(times=2, __consts=[]))
            aliases[world, producer.rank] = alias
    for rank in range(D*tp):
        ranks = list(range(rank//tp*tp, (rank//tp+1)*tp)); j = ranks.index(rank)
        for branch in branches:
            # Branch identity stays fixed while its original output slot may move.
            slot = next(k for k,ir in enumerate(aliases['p', rank]._output_irs) if ir.parent.tid == 28001+branch)
            peers = [aliases['p', r] for r in ranks]; x = peers[j]._output_irs[slot]
            bounds = ((0, 1), (j*(seqlen//tp), (j+1)*(seqlen//tp)), (0, 3*tp))
            out = IR(29000+branch, x.parent.name, x.parent.shape, bounds); out.parent.tid = x.parent.tid
            kw = dict(ranks=ranks, idim=2, odim=1)
            cell = append(pm, 'p', rank, 29000+branch, 'AllToAllPrim', [p.outputs[slot] for p in peers],
                [p._output_irs[slot] for p in peers], [out], kw)
            rows[-1]['adapter_kwargs'] = copy.deepcopy(kw)
            adapter = adapters[-1]; adapter['inputs'] = [tref(peers[j].outputs[slot])]
            adapter['primitive'] = dict(kind='AllToAllPrim', forward=True, kwargs=copy.deepcopy(kw),
                signature='nnscaler.runtime.adapter.all_to_all', generated_inputs=[f'alias_{branch}'],
                generated_outputs=[f'frontier_{branch}'])
            params = ', '.join(f'{k}={v!r}' for k,v in kw.items())
            old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                f'\n        frontier_{branch} = nnscaler.runtime.adapter.all_to_all(alias_{branch}, {params})\ndef _train_step')
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    by_writer = {writer_export_id(w['ref']): w for w in [*old['adapter_source'], *adapters]}
    snapshot['adapter_source'] = [by_writer[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, reverse=False, branches=(0,)):
    f = fixture(D, tp, seqlen, reverse, branches)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D, tp, seqlen)


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, residual.render(*args)[1]


def private(args, closed):
    return api()._render(args[0], args[1], args[3], args[-1], closed)


@pytest.mark.parametrize('cid,field', [(27000, '_input_irs'), (29000, '_input_irs'), (27000, '_output_irs')])
def test_original_edge_and_cross_world_branch_parent(baseline, cid, field):
    args, closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == cid)
    getattr(cell, field)[0].parent.tid += 999
    with pytest.raises(ValueError, match='parent'): private(args, closed)


@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['bool-shape', 'float-shape', 'bool-parent'])
def test_exchange_raw_types_before_conversion(baseline, field, fault):
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 29000)
    ir = getattr(cell, field)[0]
    if fault == 'bool-parent': ir.parent.tid = True
    else: ir.shape = ((True if fault == 'bool-shape' else float(ir.shape[0])), *ir.shape[1:])
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'typed raw reached lossy Port conversion'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('cid', [27000, 29000])
@pytest.mark.parametrize('fault', ['writer-call', 'writer-export', 'writer-refs', 'raw-op', 'raw-refs', 'raw-kwargs',
                                 'consts', 'extra-kw', 'scope-owner', 'scope-axes', 'scope-writer', 'scope-peers'])
def test_original_source_authority(baseline, cid, fault):
    from dataclasses import replace
    args, closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == cid)
    source = args[1]
    writer = next(w for w in source._collective_source['writers'] if w['ref']['source_cid'] == cid and w['ref']['runtime_rank'] == cell.rank)
    if fault == 'writer-call': writer['ref']['call_instance'] = True
    elif fault == 'writer-export': writer['export_id'] = 'wrong'
    elif fault == 'writer-refs': writer['inputs'][0]['version'] += 1
    elif fault == 'raw-op': cell.opname = 'FW_mul'
    elif fault == 'raw-refs': cell.inputs[0] = cell.inputs[0]._replace(v=2)
    elif fault == 'raw-kwargs': cell.kwargs['times' if cid == 27000 else 'idim'] = True
    elif fault in ('consts', 'extra-kw'):
        # Also change the lowered kwargs: validating raw/lowered equality alone
        # cannot authenticate semantics the old ordinary normalizer discards.
        node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
        cell.kwargs['__consts' if fault == 'consts' else 'extra'] = False
        source.source.cell(node).kwargs = dict(cell.kwargs)
    elif cid == 27000:
        # Multiref is ordinary and must not acquire a collective scope.
        node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
        source.collective_scopes[node] = next(iter(source.collective_scopes.values()))
    else:
        key, scope = next((k,s) for k,s in source.collective_scopes.items() if tuple(s.node) == tuple(cell.node))
        edits = {'scope-owner': dict(local_index=False), 'scope-axes': dict(params=(2, True)),
                 'scope-writer': dict(source_writer='wrong'), 'scope-peers': dict(input_tids=scope.input_tids[::-1])}
        source.collective_scopes[key] = replace(scope, **edits[fault])
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('fault', ['missing-unit', 'duplicate-unit', 'positions', 'ranks', 'bool-unit',
    'cross-DP', 'partial-locals', 'axis', 'global-shape', 'skip-facts', 'order-partial', 'order-duplicate', 'order-bool', 'order-reversed'])
def test_complete_frontier_and_schedule(baseline, fault):
    args, closed = copy.deepcopy(baseline); old = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop()
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(old))
    elif fault == 'positions': old['positions'] = [99]
    elif fault == 'ranks': old['ranks'].reverse()
    elif fault == 'bool-unit': old['unit'] = False
    elif fault == 'cross-DP': old['local_steps'] = closed['frontier_units'][1]['local_steps']
    elif fault == 'partial-locals': old['local_steps'].pop()
    elif fault == 'axis': old['gather_axis'] = True
    elif fault == 'global-shape': old['global_shape'][0] += 1
    elif fault == 'skip-facts':
        # Corrupt only the retained alias: it must not escape validation because
        # it has no exchange consumer.
        cell = next(c for c in args[3]._inputs[1] if c.node.cid == 27000)
        cell._output_irs[1].valmap = (False, 1)
    else:
        order = args[-1]['pm']['execution_to_source']
        if fault == 'order-partial': order.pop()
        elif fault == 'order-duplicate': order.append(order[-1])
        elif fault == 'order-bool': order[0] = False
        else: order.reverse()
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('D,tp,seqlen,reverse,branches', [(1,2,4,False,(0,)), (2,3,6,True,(0,)), (2,3,6,False,(0,1)), (3,2,4,True,())])
def test_general_dimensions_original_slots_and_all_branches(D, tp, seqlen, reverse, branches):
    args = prepared(D, tp, seqlen, reverse, branches)
    text, result = api().render(*args)
    assert len(result['alias_units']) == len(result['frontier_units']) == D*2
    assert len(result['exchange_units']) == D*len(branches)
    assert len(result['retained_units']) == D*(2-len(branches))
    assert result['deferred_units'] == []
    assert [r['slot'] for r in result['frontier_units']] == [0,1]*D
    assert [r['sm_output_ref'][3] for r in result['frontier_units']] == ([27002,27001] if reverse else [27001,27002])*D
    for row in result['frontier_units']:
        assert row['global_shape'] == [D,seqlen,3*tp]
        assert row['local_shape'] == ([1,seqlen//tp,3*tp] if row['gather_axis'] == 1 else [1,seqlen,3])
        assert len(row['local_steps']) == tp
        assert row['positions'] == [row['unit']]
    assert len({r['theorem'] for r in result['reads']}) == len(result['reads'])
    assert result['lean_bytes'] == len(text.encode())


@pytest.mark.parametrize('coverage', ['local-only', 'absent'])
def test_exchange_observation_coverage_is_not_fabricated(baseline, coverage):
    args, closed = copy.deepcopy(baseline)
    for cell in args[3]._inputs[1]:
        if cell.node.cid != 29000: continue
        if coverage == 'local-only': cell._input_irs = [cell._input_irs[cell.rank % 2]]
        else: del cell._input_irs; del cell._output_irs
    _, result = private(args, closed)
    assert {r['input_metadata'] for r in result['reads'] if r['op'] == 'AllToAllPrim'} == {coverage}


@pytest.mark.parametrize('cid,field', [(27000,'_input_irs'), (27000,'_output_irs'), (29000,'_input_irs'), (29000,'_output_irs')])
@pytest.mark.parametrize('fault', ['parent-shape', 'bounds', 'value'])
def test_all_raw_layout_types_precede_port_conversion(baseline, cid, field, fault):
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline)
    ir = getattr(next(c for c in args[3]._inputs[1] if c.node.cid == cid), field)[0]
    if fault == 'parent-shape': ir.parent.shape = (True, *ir.parent.shape[1:])
    elif fault == 'bounds': ir.indmap = ((False, ir.indmap[0][1]), *ir.indmap[1:])
    else: ir.valmap = (False, 1)
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'raw layout reached Port before typed checks'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('fault', ['all-opcodes', 'all-input-refs', 'output-parent'])
def test_bad_exchange_cannot_be_reclassified_as_deferred(baseline, fault):
    args, closed = copy.deepcopy(baseline)
    for cell in args[3]._inputs[1]:
        if cell.node.cid != 29000: continue
        if fault == 'all-opcodes': cell.opname = 'FW_mul'
        elif fault == 'all-input-refs': cell.inputs = [r._replace(v=2) for r in cell.inputs]
        else: cell._output_irs[0].parent.tid += 999
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('label,cid', [('sm',27000), ('pm',27000), ('pm',29000)])
def test_entire_BW_suffix_operand_nonwrite(baseline, label, cid):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_post_add_values as post
    from Verdict import runtime_embedding_route_values as primitive
    args, closed = copy.deepcopy(baseline); j = 0 if label == 'sm' else 1
    index = _Index(args[j], args[3]._inputs[j]); old = closed['frontier_units'][0]
    aliases = [api()._alias(index, d) for d in ([old['source_step']] if label == 'sm' else old['local_steps'])]
    step = aliases[0] if cid == 27000 else api()._exchange(index, aliases, 0, old['ranks'])[0][0]
    source = args[j]; order = args[-1][label]
    last = source.nodes()[order['execution_to_source'][-1]]
    assert source.node_opname(last).startswith('BW_')
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    source._node2outputs[last] = [source.node_inputs(node)[0]]
    with pytest.raises(ValueError, match='operand.*written'):
        (post if cid == 27000 else primitive)._read(source, label, step, order)


def test_exchange_frontier_consumers_are_not_stale_alias_consumers(baseline):
    args, closed = copy.deepcopy(baseline)
    _, result = private(args, closed)
    for row in result['exchange_units']:
        assert row['pm_consumers'] == []  # portable graph ends at exchange
        assert len(row['input_pm_consumers']) == row['dimensions']['T']


def test_exchange_read_source_kwargs_and_params(baseline):
    args, closed = copy.deepcopy(baseline)
    _, result = private(args, closed)
    for read in result['reads']:
        if read['op'] != 'AllToAllPrim': continue
        assert read['params'] == [2,1]
        assert read['source_kwargs'] == dict(ranks=read['ranks'], idim=2, odim=1)
        assert read['request'] == 'group'


def test_frontier_tracer():
    args = prepared()
    assert residual.render(*args)[1]['frontier_units']
    with patch.object(residual, 'render', wraps=residual.render) as fresh:
        text, result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args, args, strict=True))
    assert [len(result[k]) for k in ('reads', 'alias_units', 'exchange_units', 'frontier_units', 'retained_units', 'deferred_units')] == [9, 4, 2, 4, 2, 0]
    assert result['consumed_frontier_indices'] == [0, 1]
    assert text.count('SourceMultirefRead.multiref_value_of_split') == 5
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    assert text.count('SourceHiddenSequenceExchange.output_facts') == 2
    for row in result['frontier_units']:
        assert row['global_shape'] == [2, 2, 6]
        assert row['local_shape'] == ([1, 1, 6] if row['gather_axis'] == 1 else [1, 2, 3])
        assert row['facts_theorem'] == row['theorem']
        fragment = text.split('theorem '+row['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert '∀ y ∈' in fragment and '.shape = [2, 2, 6]' in fragment
        assert 'chunkPrimDimN 0 2' in fragment and f'allGatherPrimDimN {row["gather_axis"]} 2 0' in fragment
    assert len([r for r in result['reads'] if r['world'] == 'sm']) == 1
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert result[flag] is False
    for bad in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :', 'postAddAliasUnit_'):
        assert bad not in text
