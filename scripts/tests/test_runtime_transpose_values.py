"""Portable original-source first-transpose checkpoint (no kernel simulation)."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_projection_exchange_values as existing
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_projection_exchange_values as exchange
from Verdict import runtime_view_values as view


def api():
    assert importlib.util.find_spec('Verdict.runtime_transpose_values'), 'first transpose renderer missing'
    return importlib.import_module('Verdict.runtime_transpose_values')


def fixture(D=2, tp=2, seqlen=2, branches=3, saved=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = existing.exchange_fixture(D, tp, seqlen, branches, saved)
    added = []

    def append(graph, world, producer, out, opname, cid, kwargs):
        cell = NS(node=N(world, producer.rank, 0, cid, opname), rank=producer.rank,
            opname=opname, inputs=list(producer.outputs),
            outputs=[T(world, producer.rank, 0, out.tid, 1)],
            _input_irs=copy.deepcopy(producer._output_irs), _output_irs=[out], kwargs=kwargs)
        cell.ir = NS(signature=opname, inputs=lambda c=cell: c._input_irs,
            outputs=lambda c=cell: c._output_irs)
        graph.cells.append(cell); graph.shapes[cell.outputs[0]] = out.shape
        if world == 'p': added.append(cell)
        return cell

    for world, graph in [('s', sm), ('p', pm)]:
        producers = [c for c in graph.cells if (c.opname == 'FW_view' if world == 's'
            else c.opname == 'AllToAllPrim' and c._output_irs[0].tid >= 500)]
        for producer in producers:
            x = producer._output_irs[0]
            slot = x.tid % 100
            if len(x.shape) == 3:
                global_view = next(c for c in sm.cells if c.opname == 'FW_view' and c.outputs[0].tid == 500+slot)
                C = global_view._output_irs[0].parent.shape[3]
                out = IR(700+slot, global_view._output_irs[0].parent.name,
                    (*x.parent.shape[:2], x.parent.shape[2]//C, C),
                    (*x.indmap[:2], tuple(a//C for a in x.indmap[2]), (0, C)))
                producer = append(graph, world, producer, out, 'FW_view', 400+slot, dict(size=list(out.shape)))
                x = out
            shape, bounds = list(x.parent.shape), list(x.indmap)
            shape[1], shape[2] = shape[2], shape[1]
            bounds[1], bounds[2] = bounds[2], bounds[1]
            out = IR(800+slot, f'transpose.result{slot}', tuple(shape), tuple(bounds))
            first = append(graph, world, producer, out, 'FW_transpose', 500+slot, dict(dim0=1, dim1=2))
            if slot == 1:
                shape[2], shape[3] = shape[3], shape[2]
                bounds[2], bounds[3] = bounds[3], bounds[2]
                out = IR(900+slot, 'later.K.transpose', tuple(shape), tuple(bounds))
                append(graph, world, first, out, 'FW_transpose', 600+slot, dict(dim0=2, dim1=3))
    old = authority[2]
    rows = [dict(ref=dict(world='p', runtime_rank=c.rank, microbatch=0,
        source_cid=c.node.cid, call_instance=0, op=c.opname, origin='fixture'),
        source_irname=c.node.irname, inputs=[tref(t) for t in c.inputs],
        outputs=[tref(t) for t in c.outputs], parameter_grad_tids=[]) for c in added]
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *copy.deepcopy(rows)]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3, saved=False):
    data = fixture(D, tp, seqlen, branches, saved)
    base = existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=data):
        return base.prepared(D, tp, seqlen)


def test_first_transpose_tracer_bullet():
    args = prepared()
    prior = exchange.render(*args)[1]
    assert len(prior['reads']) == 12 and len(prior['units']) == 6
    text, detail = api().render(*args)
    assert len(detail['reads']) == 19
    assert len(detail['view_units']) == 2 and len(detail['units']) == 6
    assert text.count('SourceLayoutRead.view_value_of_split') == 4
    assert text.count('SourceLayoutRead.transposeAxes_value_of_split') == 15
    assert text.count('source_view_sequence_unit_output_reconstruct') == 2
    assert text.count('source_transpose12_inner_unit_output_reconstruct') == 4
    assert text.count('source_transpose12_sequence_unit_output_reconstruct') == 2
    assert [(u['unit'], u['slot']) for u in detail['units']] == [(u['unit'], u['slot']) for u in prior['units']]
    old = view.render(*args)[1]
    assert all('theorem '+r['theorem']+' ' not in text for r in old['reads'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False


@pytest.mark.parametrize('D,tp,seqlen,branches,saved', [
    (2, 2, 2, 3, True), (3, 2, 6, 4, False), (2, 3, 6, 5, False), (1, 2, 6, 1, False)])
def test_full_portable_checkpoint(D, tp, seqlen, branches, saved):
    args = prepared(D, tp, seqlen, branches, saved)
    before = copy.deepcopy(args[-1])
    with patch.object(exchange, 'render', wraps=exchange.render) as fresh, patch.object(
            view, 'render', wraps=view.render) as fresh_view:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and fresh_view.call_count == 2
    assert all(call.args[-2] is args[-2] and call.args[-1] is args[-1]
        for call in [*fresh.call_args_list, *fresh_view.call_args_list])
    assert args[-1] == before
    v = int(branches > 2)
    assert len(detail['reads']) == branches*(1+D*tp)+v*D*tp
    assert len(detail['view_units']) == v*D and len(detail['units']) == D*branches
    assert detail['lean_bytes'] == len(text.encode())
    assert 'later transpose/attention/downstream unproved' in detail['deferred_stage']
    for unit in [*detail['view_units'], *detail['units']]:
        fragment = text.split('theorem '+unit['theorem']+' ')[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert unit['predecessor']+' s p t q hs hp hvalues' in fragment
        assert 'predecessor.1 rfl predecessor.2.1 predecessor.2.2' in fragment
        assert unit['global_shape'][0] == D*unit['local_shape'][0]
        for step in unit['local_steps']:
            read = next(r for r in detail['reads'] if tuple(r['node']) == tuple(step['node']))
            assert read['theorem']+' p q hp' in fragment
        if unit in detail['units']:
            assert unit['axes'] == [1, 2]
            assert (unit['input_gather_axis'], unit['gather_axis']) in [(3, 3), (1, 2)]
    for read in detail['reads']:
        suffix = args[-1][read['world']]['execution_to_source'][read['execution_index']:]
        assert read['operand_nonwrite_source_indices'] == suffix
        assert read['source_step']['inputs'][0]['endpoint']['ref'] == tuple(read['input_refs'][0])
        assert read['request'] == 'global'
        assert f'{read["world"]}Node_{read["source_index"]}' in text
        assert read['output_refs'][0][3] < 900  # Later K transpose23 is downstream.
    if saved:
        for world, label in [(0, 'sm'), (1, 'pm')]:
            bw = {i for i, n in enumerate(args[world].nodes()) if args[world].node_opname(n).startswith('BW_')}
            assert bw <= set(args[-1][label]['execution_to_source'])
            assert bw
    for bad in ('sorry', 'admit', 'native_decide', '(hshape :', '(houtput :', 'axiom '):
        assert bad not in text


@pytest.mark.parametrize('world', [0, 1])
@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['name', 'parent', 'bounds', 'value', 'bool', 'tid', 'missing', 'joint-parent', 'joint-value'])
def test_metadata_after_fresh_predecessor_acceptance(world, field, fault):
    args = prepared()
    targets = [c for c in args[3]._inputs[world] if c.opname == 'FW_transpose' and c.node.cid < 600]
    if not fault.startswith('joint'):
        targets = targets[:1]
    for cell in targets:
        irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
        ir = irs[0]
        if fault == 'name': ir.parent.name = 'different-original-source'
        elif fault in ('parent', 'joint-parent'): ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
        elif fault == 'bounds': ir.indmap = (*ir.indmap[:-1], (1, ir.indmap[-1][1]+1))
        elif fault in ('value', 'joint-value'): ir.valmap = (1, 2)
        elif fault == 'bool': ir.valmap = (False, 1)
        elif fault == 'tid': ir.tid += 9999
        else: irs.clear()
    if fault != 'missing':
        assert exchange.render(*args)[1]['units']
    else:
        # Missing raw IR is already rejected by full-world predecessor replay.
        with pytest.raises(ValueError): exchange.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('world', [0, 1])
@pytest.mark.parametrize('fault', ['unknown', 'mixed', 'missing', 'ambiguous', 'version', 'owner',
    'kwargs', 'kwargs-bool', 'kwargs-float', 'kwargs-extra', 'kwargs-missing'])
def test_first_frontier_and_original_kwargs(world, fault):
    args = prepared()
    prior = exchange.render(*args)[1]; views = view.render(*args)[1]
    raw = args[3]._inputs[world]
    cell = next(c for c in raw if c.opname == 'FW_transpose' and c.node.cid == 500)
    if fault == 'unknown': cell.opname = 'FW_contiguous'
    elif fault == 'mixed': cell.opname = 'FW_view'
    elif fault == 'missing': raw.remove(cell)
    elif fault == 'ambiguous': raw.append(copy.copy(cell))
    elif fault == 'version': cell.inputs[0] = cell.inputs[0]._replace(v=0)
    elif fault == 'owner': cell.rank += 1
    else:
        changes = {'kwargs': {'dim1': 3}, 'kwargs-bool': {'dim0': True},
            'kwargs-float': {'dim0': 1.0}, 'kwargs-extra': {'unknown': 1}}
        if fault == 'kwargs-missing': cell.kwargs.pop('dim0')
        else: cell.kwargs.update(changes[fault])
        node = next(n for n in args[world].nodes() if tuple(n) == tuple(cell.node))
        kwargs = copy.deepcopy(cell.kwargs)
        args[world].node_kwargs(node).clear(); args[world].node_kwargs(node).update(kwargs)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior, views)


@pytest.mark.parametrize('world', [0, 1])
@pytest.mark.parametrize('selected', [True, False])
def test_selected_and_full_suffix_operand_nonwrites(world, selected):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    args = prepared(saved=True)
    exchange.render(*args)
    source, label = args[world], ('sm' if world == 0 else 'pm')
    index = _Index(source, args[3]._inputs[world])
    cell = next(c for c in index.raw.values() if c.opname == 'FW_transpose' and c.node.cid == 500)
    port = api().post._port(index, cell.inputs[0], cell._input_irs[0])
    step = api()._transpose(index, cell, port)
    _, healthy = api()._read(source, label, step, args[-1][label])
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if selected else source.nodes()[args[-1][label]['execution_to_source'][-1]]
    assert source.nodes().index(target) in healthy['operand_nonwrite_source_indices']
    source._node2outputs[target] = source.node_inputs(node)
    if selected: step = replace(step, outputs=step.inputs)
    with pytest.raises(ValueError, match='operand.*written'):
        api()._read(source, label, step, args[-1][label])


def test_read_layout_annotations_are_explicit():
    _, detail = api().render(*prepared())
    for read in detail['reads']:
        assert read['input_rank'] in (3, 4) and read['output_rank'] == 4
        assert read['input_shape'] == list(read['source_step']['inputs'][0]['endpoint']['shape'])
        assert read['output_shape'] == list(read['source_step']['outputs'][0]['endpoint']['shape'])


@pytest.mark.parametrize('fault', ['input-value', 'output-parent', 'output-bounds', 'output-value',
    'size-bool', 'size-wrong', 'unknown', 'missing', 'ambiguous'])
def test_needed_V_view_is_original_and_fail_closed(fault):
    args = prepared()
    prior = exchange.render(*args)[1]; views = view.render(*args)[1]
    raw = args[3]._inputs[1]
    cell = next(c for c in raw if c.opname == 'FW_view' and c.node.cid == 402)
    if fault == 'input-value': cell._input_irs[0].valmap = (1, 2)
    elif fault == 'output-parent':
        ir = cell._output_irs[0]; ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'output-bounds':
        ir = cell._output_irs[0]; ir.indmap = (*ir.indmap[:-1], (1, ir.indmap[-1][1]+1))
    elif fault == 'output-value': cell._output_irs[0].valmap = (1, 2)
    elif fault.startswith('size'):
        kwargs = copy.deepcopy(cell.kwargs)
        kwargs['size'][0] = True if fault == 'size-bool' else 99
        cell.kwargs = kwargs
        node = next(n for n in args[1].nodes() if tuple(n) == tuple(cell.node))
        args[1].node_kwargs(node).update(kwargs)
    elif fault == 'unknown': cell.opname = 'FW_contiguous'
    elif fault == 'missing': raw.remove(cell)
    else: raw.append(copy.copy(cell))
    if fault in ('input-value', 'output-parent', 'output-bounds', 'output-value'):
        assert exchange.render(*args)[1]['units']
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior, views)


@pytest.mark.parametrize('fault', ['parent', 'bounds', 'value'])
def test_joint_SM_PM_output_agreement_cannot_replace_axis_transport(fault):
    args = prepared()
    for raw in args[3]._inputs[:2]:
        for cell in raw:
            if cell.opname != 'FW_transpose' or cell.node.cid >= 600: continue
            ir = cell._output_irs[0]
            if fault == 'value': ir.valmap = (1, 2)
            else:
                ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
                if fault == 'bounds':
                    ir.indmap = (*ir.indmap[:-1], (1, ir.indmap[-1][1]+1))
    assert exchange.render(*args)[1]['units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['global-ref', 'source-node', 'output-value', 'missing', 'ambiguous'])
def test_existing_SM_V_read_is_matched_by_full_original_identity(fault):
    args = prepared()
    prior = exchange.render(*args)[1]; views = view.render(*args)[1]
    target = next(r for r in views['reads'] if r['world'] == 'sm' and r['output_refs'][0][3] == 502)
    if fault == 'global-ref':
        ep = target['source_step']['inputs'][0]['endpoint']
        ep['ref'] = (*ep['ref'][:-1], 123)
    elif fault == 'source-node': target['source_step']['node'] = ('s', 0, 0, 123, 'FW_view')
    elif fault == 'output-value': target['source_step']['outputs'][0]['value_part'] = (1, 2)
    elif fault == 'missing': views['reads'].remove(target)
    else: views['reads'].append(copy.deepcopy(target))
    with pytest.raises(ValueError, match='existing global view'):
        api()._render(args[0], args[1], args[3], args[-1], prior, views)


def test_original_interleaved_unit_and_declaration_order():
    args = prepared(saved=True)
    prior = exchange.render(*args)[1]['units']
    text, detail = api().render(*args)
    assert [(u['unit'], u['slot']) for u in detail['units']] == [(u['unit'], u['slot']) for u in prior]
    offsets = [text.index('theorem '+u['theorem']+' ') for u in detail['units']]
    assert offsets == sorted(offsets)
    for vu in detail['view_units']:
        vpos = text.index('theorem '+vu['theorem']+' ')
        for step in vu['local_steps']:
            read = next(r for r in detail['reads'] if tuple(r['node']) == tuple(step['node']))
            assert text.index('theorem '+read['theorem']+' ') < vpos
        unit = next(u for u in detail['units'] if u['predecessor'] == vu['theorem'])
        assert vpos < text.index('theorem '+unit['theorem']+' ')
    declarations = [line.split()[1] for line in text.splitlines() if line.startswith('theorem ')]
    assert len(declarations) == len(set(declarations))
