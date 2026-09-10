"""Portable ORIGINAL source fixtures; no capture or kernel result is simulated."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_view_values as existing
from scripts.tests import test_runtime_view_frontier as backward
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_view_values as view
from Verdict import runtime_projection_values as projection


def api():
    assert importlib.util.find_spec('Verdict.runtime_projection_exchange_values'), 'projection exchange renderer missing'
    return importlib.import_module('Verdict.runtime_projection_exchange_values')


def exchange_fixture(D=2, tp=2, seqlen=2, branches=3, saved=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = existing.view_fixture(D, tp, seqlen, branches, deferred=True)
    # Widen the projection output channels, retaining head boundaries. This
    # makes channel splits legal for arbitrary T, including T=3, not just T=2.
    for graph in (sm, pm):
        for cell in graph.cells:
            for ir in (*cell._input_irs, *cell._output_irs):
                if not 300 <= ir.tid < 600:
                    continue
                shape, bounds = list(ir.parent.shape), list(ir.indmap)
                axis = 0 if ir.tid < 400 else len(shape)-1
                shape[axis] *= tp
                bounds[axis] = tuple(x*tp for x in bounds[axis])
                ir.parent.shape, ir.indmap = tuple(shape), tuple(bounds)
                ir.shape = tuple(b-a for a, b in bounds)
            if cell.opname == 'FW_view':
                cell.kwargs['size'] = list(cell._output_irs[0].shape)
            # Adapted collective references enumerate peers; raw IR is local.
            for ref in cell.inputs:
                ir = next((ir for ir in cell._input_irs if ir.tid == ref.tid), None)
                if ir is not None: graph.shapes[ref] = ir.shape
            for ref, ir in zip(cell.outputs, cell._output_irs, strict=True):
                graph.shapes[ref] = ir.shape
    old = copy.deepcopy(authority[2])
    for rank, source in old['rank_sources'].items():
        for cell in pm.cells:
            if cell.rank == int(rank) and cell.opname == 'FW_view':
                inp, out = cell.inputs[0].tid, cell.outputs[0].tid
                lines = source.splitlines()
                for i, line in enumerate(lines):
                    if f'view_{out} = projection_{inp}.view(' in line:
                        lines[i] = f'        view_{out} = projection_{inp}.view({", ".join(map(str, cell.kwargs["size"]))})'
                source = '\n'.join(lines)+'\n'
        old['rank_sources'][rank] = source
    added = []
    for producer in list(pm.cells):
        if producer.opname != 'FW_view': continue
        x = producer._output_irs[0]
        ranks = list(range(producer.rank//tp*tp, (producer.rank//tp+1)*tp))
        j = ranks.index(producer.rank)
        axis = next(d for d in (1, 2) if x.indmap[d] != (0, x.parent.shape[d]))
        bounds = list(x.indmap)
        bounds[axis] = (0, x.parent.shape[axis])
        width = x.parent.shape[3]//tp
        bounds[3] = (j*width, (j+1)*width)
        out = IR(x.tid+100, x.parent.name, x.parent.shape, tuple(bounds))
        kwargs = dict(ranks=ranks, idim=axis, odim=3)
        cell = NS(node=N('p', producer.rank, 0, producer.node.cid+200, 'AllToAllPrim'),
            rank=producer.rank, opname='AllToAllPrim',
            inputs=[T('p', r, 0, x.tid, 1) for r in ranks],
            outputs=[T('p', producer.rank, 0, out.tid, 1)],
            _input_irs=copy.deepcopy([x]), _output_irs=[out], kwargs=kwargs)
        cell.ir = NS(signature='AllToAllPrim', inputs=lambda c=cell: c._input_irs,
            outputs=lambda c=cell: c._output_irs)
        pm.cells.append(cell); added.append(cell)
        pm.shapes.update({ref: x.shape for ref in cell.inputs})
        pm.shapes[cell.outputs[0]] = out.shape
    rows, adapters = [], []
    for cell in added:
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0,
            source_cid=cell.node.cid, call_instance=0, op=cell.opname, origin='fixture'),
            source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
            outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[],
            adapter_kwargs=copy.deepcopy(cell.kwargs))
        adapter = copy.deepcopy(row)
        adapter['inputs'] = [tref(t) for t in cell.inputs if t.rank == cell.rank]
        adapter['primitive'] = dict(kind='AllToAllPrim', forward=True,
            kwargs=copy.deepcopy(cell.kwargs), signature='nnscaler.runtime.adapter.all_to_all',
            generated_inputs=[f'view_{cell.inputs[0].tid}'],
            generated_outputs=[f'exchange_{cell.outputs[0].tid}'])
        rows.append(row); adapters.append(adapter)
        key = str(cell.rank)
        line = f'        exchange_{cell.outputs[0].tid} = nnscaler.runtime.adapter.all_to_all(view_{cell.inputs[0].tid}, idim={cell.kwargs["idim"]}, odim=3, ranks={cell.kwargs["ranks"]})'
        old['rank_sources'][key] = old['rank_sources'][key].replace('\ndef _train_step', '\n'+line+'\ndef _train_step')
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *adapters]
    bind_reducers(snapshot); bind_adapters(snapshot)
    fixture = sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])
    if saved:
        with patch.object(existing, 'view_fixture', return_value=fixture):
            fixture = backward.saved_primal_fixture()
    return fixture


def prepared(D=2, tp=2, seqlen=2, branches=3, saved=False):
    fixture = exchange_fixture(D, tp, seqlen, branches, saved)
    with patch.object(existing.projection.norm.post.base, 'add_fixture', return_value=fixture):
        return existing.projection.norm.post.base.prepared(D, tp, seqlen)


def test_first_exchange_tracer_bullet():
    args = prepared()
    prior = view.render(*args)[1]
    assert len(prior['units']) == 4 and len(prior['deferred_units']) == 2
    text, detail = api().render(*args)
    assert len(detail['reads']) == 12
    assert len(detail['units']) == 6
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 12
    assert text.count('SourceRank4Exchange.axis1_output_facts') == 2
    assert text.count('SourceRank4Exchange.axis2_output_facts') == 2
    assert text.count('SourceHiddenSequenceExchange.output_facts') == 2
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False


@pytest.mark.parametrize('D,tp,seqlen,branches,saved', [
    (2, 2, 2, 3, True), (3, 2, 6, 4, False), (2, 3, 6, 5, False), (1, 2, 6, 1, False)])
def test_portable_full_checkpoint(D, tp, seqlen, branches, saved):
    args = prepared(D, tp, seqlen, branches, saved)
    predecessors = view.render(*args)[1]
    with patch.object(view, 'render', wraps=view.render) as fresh_view, patch.object(
            projection, 'render', wraps=projection.render) as fresh_projection:
        text, detail = api().render(*args)
        assert fresh_view.call_count == 1 and fresh_projection.call_count == 2
        assert all(call.args[-2] is args[-2] and call.args[-1] is args[-1]
                   for call in fresh_projection.call_args_list)
    assert len(detail['reads']) == D*tp*branches
    assert len(detail['units']) == D*branches
    assert detail['lean_bytes'] == len(text.encode())
    strong = {u['facts_theorem']: u for u in predecessors['units']}
    deferred = {u['predecessor'] for u in predecessors['deferred_units']}
    for unit in detail['units']:
        assert unit['global_shape'][0] == D*unit['local_shape'][0]
        if unit['predecessor'] in strong:
            assert unit['sm_output_ref'] == strong[unit['predecessor']]['sm_output_ref']
            assert unit['source_step']['op'] == 'FW_view'
            assert unit['gather_axis'] == 3
        else:
            assert unit['predecessor'] in deferred
            assert unit['source_step']['op'] == 'FW_linear'
            assert len(unit['global_shape']) == 3 and unit['gather_axis'] == 1
        assert f'have predecessor := {unit["predecessor"]} s p t q hs hp hvalues' in text
    for read in detail['reads']:
        suffix = args[-1]['pm']['execution_to_source'][read['execution_index']:]
        assert read['operand_nonwrite_source_indices'] == suffix
        assert read['input_metadata'] == 'local-only'
        assert read['output_metadata'] == 'present'
        assert read['params'] in ([1, 3], [2, 3], [2, 1])
        assert len(read['input_refs']) == tp and len(read['output_refs']) == 1
        assert read['source_writer'] and read['request'] == 'group'
    if saved:
        bw_indices = [i for i, n in enumerate(args[1].nodes()) if args[1].node_opname(n) == 'BW_view']
        assert bw_indices and set(bw_indices) <= set(args[-1]['pm']['execution_to_source'])
        assert any(set(bw_indices) & set(r['operand_nonwrite_source_indices']) for r in detail['reads'])
    for bad in ('sorry', 'admit', 'native_decide', '(hshape :', '(houtput :', 'fw_transpose'):
        assert bad not in text
    assert 'local view/transpose/downstream pending' in detail['deferred_stage']


def selected(args):
    from Verdict.runtime_lineage import _Index
    prior = view.render(*args)[1]
    index = _Index(args[1], args[3]._inputs[1])
    unit = prior['units'][0]
    ports = tuple(api()._output(index, d) for d in unit['local_steps'])
    cell = view._consumer(index, ports[0])
    return index, unit, ports, cell


@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['name', 'parent', 'bounds', 'value', 'tid', 'bool', 'missing', 'own-peer'])
def test_paired_metadata_rejected_after_fresh_view_acceptance(field, fault):
    args = prepared()
    index, unit, ports, cell = selected(args)
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
    ir = irs[0]
    if fault == 'name': ir.parent.name = 'other-full-source'
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'bounds': ir.indmap = (*ir.indmap[:-1], (1, ir.indmap[-1][1]+1))
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'tid': ir.tid += 9999
    elif fault == 'bool': ir.valmap = (False, 1)
    elif fault == 'missing': irs.clear()
    else:
        # Equal shapes/IDs still do not turn peer 1's layout into peer 0's.
        if field == '_input_irs':
            other = view._consumer(index, ports[1]); irs[0] = copy.deepcopy(other._input_irs[0])
        else:
            other = view._consumer(index, ports[1]); irs[0] = copy.deepcopy(other._output_irs[0])
    assert view.render(*args)[1]['units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['mixed', 'unknown', 'missing', 'ambiguous', 'version', 'owner'])
def test_frontier_unfiltered_after_predecessor(fault):
    args = prepared()
    views = view.render(*args)[1]; projections = projection.render(*args)[1]
    raw = args[3]._inputs[1]
    cell = next(c for c in raw if c.opname == 'AllToAllPrim' and c.node.cid >= 160)
    if fault == 'mixed': cell.opname = 'FW_view'
    elif fault == 'unknown': cell.opname = 'FW_contiguous'
    elif fault == 'missing': raw.remove(cell)
    elif fault == 'ambiguous': raw.append(copy.copy(cell))
    elif fault == 'version': cell.inputs[0] = cell.inputs[0]._replace(v=0)
    else: cell.rank += 1
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], views, projections)


@pytest.mark.parametrize('fault', ['source-writer', 'ranks', 'local-index', 'peers', 'kwargs', 'kwargs-bool', 'kwargs-unknown'])
def test_scope_and_kwargs_fail_closed_after_predecessor(fault):
    from dataclasses import replace
    args = prepared()
    index, unit, ports, cell = selected(args)
    pm = args[1]; node = next(n for n in pm.collective_scopes if tuple(n) == tuple(cell.node))
    if fault.startswith('kwargs'):
        update = {'kwargs': {'idim': 2}, 'kwargs-bool': {'idim': True}, 'kwargs-unknown': {'mystery': 1}}[fault]
        cell.kwargs.update(update); pm.node_kwargs(node).update(update)
    else:
        update = {'source-writer': {'source_writer': 'wrong'}, 'ranks': {'ranks': (1, 0)},
            'local-index': {'local_index': 1}, 'peers': {'input_tids': tuple(reversed(pm.collective_scopes[node].input_tids))}}[fault]
        pm.collective_scopes[node] = replace(pm.collective_scopes[node], **update)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('selected_writer', [True, False])
def test_all_operands_and_entire_suffix_nonwrites(selected_writer):
    from dataclasses import replace
    args = prepared(saved=True)
    index, unit, ports, cell = selected(args)
    step, _ = api()._boundary(index, cell, ports, unit['ranks'], 0)
    pm, order = args[1], args[-1]['pm']
    _, healthy = api()._read(pm, step, order)
    node = next(n for n in pm.nodes() if tuple(n) == step.node)
    target = node if selected_writer else pm.nodes()[order['execution_to_source'][-1]]
    assert pm.nodes().index(target) in healthy['operand_nonwrite_source_indices']
    pm._node2outputs[target] = [pm.node_inputs(node)[-1]]
    if selected_writer: step = replace(step, outputs=(step.inputs[-1],))
    with pytest.raises(ValueError, match='operand.*written'): api()._read(pm, step, order)


def test_coordinated_invalid_output_layout_not_derived_from_output():
    args = prepared()
    index, unit, ports, cell = selected(args)
    for p in ports:
        target = view._consumer(index, p)
        ir = target._output_irs[0]
        # Everybody agrees on a larger output parent, but the input parent does not.
        ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+2)
    assert view.render(*args)[1]['units']
    with pytest.raises(ValueError, match='paired original metadata'): api().render(*args)


@pytest.mark.parametrize('coverage', ['all-peers', 'absent'])
def test_reports_only_available_raw_metadata(coverage):
    args = prepared()
    index, unit, ports, cell = selected(args)
    if coverage == 'all-peers':
        cell._input_irs = [copy.deepcopy(view._consumer(index, p)._input_irs[0]) for p in ports]
    else:
        del cell._input_irs; del cell._output_irs
    assert view.render(*args)[1]['units']
    _, detail = api().render(*args)
    row = next(r for r in detail['reads'] if tuple(r['node']) == tuple(cell.node))
    assert row['input_metadata'] == coverage
    assert row['output_metadata'] == ('absent' if coverage == 'absent' else 'present')


def test_no_caller_output_assumptions_and_per_unit_input_equations():
    args = prepared()
    text, detail = api().render(*args)
    original = projection.render(*args)[1]['units']
    assert [(u['unit'], u['slot']) for u in detail['units']] == [(u['unit'], u['slot']) for u in original]
    for unit in detail['units']:
        fragment = text.split('theorem '+unit['theorem']+' ')[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        for step in unit['local_steps']:
            row = next(r for r in detail['reads'] if tuple(r['node']) == tuple(step['node']))
            assert row['theorem']+' p q hp' in fragment
        assert 'List.ofFn' in fragment and 'predecessor.2.2 outputs' in fragment


@pytest.mark.parametrize('fault', ['global-ref', 'local-ref', 'unit', 'ranks', 'missing', 'duplicate', 'extra'])
def test_route_fullref_join_and_complete_coverage(fault):
    args = prepared()
    views = view.render(*args)[1]; projections = projection.render(*args)[1]
    damaged = copy.deepcopy(views)
    deferred = damaged['deferred_units'][0]
    if fault == 'global-ref':
        ref = list(deferred['global_view']['inputs'][0]['endpoint']['ref']); ref[-1] += 1
        deferred['global_view']['inputs'][0]['endpoint']['ref'] = tuple(ref)
    elif fault == 'local-ref': deferred['boundaries'][0]['input_refs'][0][-1] += 1
    elif fault == 'unit': deferred['unit'] += 1
    elif fault == 'ranks': deferred['ranks'].reverse()
    elif fault == 'missing': damaged['deferred_units'].pop(0)
    elif fault == 'duplicate': damaged['deferred_units'].append(copy.deepcopy(deferred))
    else:
        extra = copy.deepcopy(deferred); extra['unit'] = 123
        damaged['deferred_units'].append(extra)
    with pytest.raises(ValueError, match='route|coverage'):
        api()._render(args[0], args[1], args[3], args[-1], damaged, projections)


def test_inherited_T3_channels_are_legitimately_nondivisible():
    from Verdict.runtime_lineage import _Index
    from Verdict.runtime_embedding_routes import Step
    args = existing.prepared(2, 3, 6, 3, deferred=True)
    prior = view.render(*args)[1]['units'][0]  # Fresh predecessor accepts C=2.
    si = _Index(args[0], args[3]._inputs[0]); pi = _Index(args[1], args[3]._inputs[1])
    global_ = api()._output(si, prior['source_step'])
    ports = tuple(api()._output(pi, d) for d in prior['local_steps'])
    assert ports[0].endpoint.shape[-1] == 2 and prior['dimensions']['T'] == 3
    # Negative contract probe only; these unbound steps cannot be emitted.
    steps = [Step(tuple(d['node']), 'AllToAllPrim', ports, (ports[j],),
        ranks=tuple(prior['ranks']), local_index=j, gather_axis=prior['gather_axis'], split_axis=3)
        for j, d in enumerate(prior['local_steps'])]
    with pytest.raises(ValueError, match='nondivisible actual channels'):
        api()._unit(prior, global_, ports, steps, {})


@pytest.mark.parametrize('fault', ['gap', 'nonzero-start', 'incomplete-cover', 'partial-split', 'nondivisible', 'other-axis'])
def test_independent_input_geometry_after_predecessor_acceptance(fault):
    from dataclasses import replace
    args = prepared()
    index, unit, ports, cell = selected(args)
    a, b = 1, 3
    changed = list(ports)
    if fault == 'incomplete-cover':
        for j, p in enumerate(changed):
            shape = list(p.parent_shape); shape[a] += 1
            changed[j] = replace(p, parent_shape=tuple(shape))
    elif fault == 'nondivisible':
        for j, p in enumerate(changed):
            shape, bounds, local = list(p.parent_shape), list(p.bounds), list(p.endpoint.shape)
            shape[b] += 1; bounds[b] = (0, shape[b]); local[b] += 1
            changed[j] = replace(p, parent_shape=tuple(shape), bounds=tuple(bounds),
                endpoint=replace(p.endpoint, shape=tuple(local)))
        node = next(n for n in args[1].collective_scopes if tuple(n) == tuple(cell.node))
        args[1].collective_scopes[node] = replace(args[1].collective_scopes[node], input_shape=changed[0].endpoint.shape)
    else:
        j = 1 if fault in ('gap', 'other-axis') else 0
        bounds = list(changed[j].bounds)
        axis = b if fault == 'partial-split' else (2 if fault == 'other-axis' else a)
        bounds[axis] = (bounds[axis][0]+1, bounds[axis][1])
        changed[j] = replace(changed[j], bounds=tuple(bounds))
    with pytest.raises(ValueError, match='partition|interval|cover|nondivisible'):
        api()._boundary(index, cell, tuple(changed), unit['ranks'], 0)


@pytest.mark.parametrize('field', ['global_shape', 'local_shape', 'dimensions'])
def test_full_contract_dimensions_cannot_be_inferred_from_output_alone(field):
    args = prepared()
    index, unit, ports, cell = selected(args)
    from Verdict.runtime_lineage import _Index
    global_ = api()._output(_Index(args[0], args[3]._inputs[0]), unit['source_step'])
    steps = [api()._boundary(index, view._consumer(index, p), ports, unit['ranks'], j)[0]
             for j, p in enumerate(ports)]
    changed = copy.deepcopy(unit)
    if field == 'dimensions': changed[field]['B'] += 1
    else: changed[field][-1] += 1
    with pytest.raises(ValueError, match='contract'):
        api()._unit(changed, global_, ports, steps, {})


def test_malformed_source_writer_rejected_even_by_original_boundary_guard():
    from dataclasses import replace
    args = prepared()
    index, unit, ports, cell = selected(args)
    node = next(n for n in args[1].collective_scopes if tuple(n) == tuple(cell.node))
    args[1].collective_scopes[node] = replace(args[1].collective_scopes[node], source_writer='arbitrary-nonempty')
    with pytest.raises(ValueError, match='writer'):
        api()._boundary(index, cell, ports, unit['ranks'], 0)
