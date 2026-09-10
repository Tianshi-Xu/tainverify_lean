"""Portable first-view extension; predecessor fixtures remain untouched."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_projection_values as projection
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T


def api():
    assert importlib.util.find_spec('Verdict.runtime_view_values'), 'first view renderer missing'
    return importlib.import_module('Verdict.runtime_view_values').render


def view_fixture(D=2, tp=2, seqlen=2, branches=3, deferred=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    sm, pm, authority = projection.projection_fixture(D, tp, seqlen, branches)
    added = []
    for world, graph in [('s', sm), ('p', pm)]:
        for linear in list(graph.cells):
            if linear.opname != 'FW_linear':
                continue
            rank = linear.rank
            slot = linear.outputs[0].tid - 400
            x = linear._output_irs[0]
            if deferred and world == 'p' and slot == 2:
                opname = 'AllToAllPrim'
                ranks = list(range(rank//tp*tp, (rank//tp+1)*tp))
                ins = [T(world, r, 0, x.tid, 1) for r in ranks]
                # Original head shards -> sequence shards, prior to ANY view.
                bounds = (x.indmap[0], (rank%tp*seqlen//tp, (rank%tp+1)*seqlen//tp), (0, tp*4))
                out = IR(500+slot, x.parent.name, x.parent.shape, bounds)
                kwargs = dict(ranks=ranks, idim=2, odim=1)
            else:
                opname = 'FW_view'
                ins = linear.outputs
                C = 2
                bounds = (*x.indmap[:2], tuple(a//C for a in x.indmap[2]), (0, C))
                out = IR(500+slot, f'unflatten.result{slot}', (*x.parent.shape[:2], x.parent.shape[2]//C, C), bounds)
                kwargs = dict(size=list(out.shape))
            cell = NS(node=N(world, rank, 0, 60+slot, opname), rank=rank, opname=opname,
                inputs=ins, outputs=[T(world, rank, 0, out.tid, 1)],
                _input_irs=copy.deepcopy([x]), _output_irs=[out], kwargs=kwargs)
            cell.ir = NS(signature=opname, inputs=lambda c=cell: c._input_irs,
                         outputs=lambda c=cell: c._output_irs)
            graph.cells.append(cell)
            graph.shapes.update({r: x.shape for r in ins})
            graph.shapes[cell.outputs[0]] = out.shape
            if world == 'p': added.append(cell)
    old = authority[2]
    rows, adapters = [], []
    for cell in added:
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0,
            source_cid=cell.node.cid, call_instance=0, op=cell.opname, origin='fixture'),
            source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
            outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[])
        adapter = copy.deepcopy(row)
        if cell.opname == 'AllToAllPrim':
            row['adapter_kwargs'] = copy.deepcopy(cell.kwargs)
            adapter['inputs'] = [tref(t) for t in cell.inputs if t.rank == cell.rank]
            adapter['primitive'] = dict(kind=cell.node.irname, forward=True,
                kwargs=copy.deepcopy(cell.kwargs), signature='nnscaler.runtime.adapter.all_to_all',
                generated_inputs=[f'projection_{cell.inputs[0].tid}'],
                generated_outputs=[f'view_{cell.outputs[0].tid}'])
        rows.append(row); adapters.append(adapter)
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *adapters]
    for rank in range(D*tp):
        lines = []
        for cell in added:
            if cell.rank != rank: continue
            inp, out = cell.inputs[0].tid, cell.outputs[0].tid
            if cell.opname == 'FW_view':
                lines.append(f'        view_{out} = projection_{inp}.view({", ".join(map(str, cell.kwargs["size"]))})')
            else:
                lines.append(f'        view_{out} = nnscaler.runtime.adapter.all_to_all(projection_{inp}, idim=2, odim=1, ranks={cell.kwargs["ranks"]})')
        snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace(
            '\ndef _train_step', '\n'+'\n'.join(lines)+'\ndef _train_step')
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3, deferred=False):
    fixture = view_fixture(D, tp, seqlen, branches, deferred)
    with patch.object(projection.norm.post.base, 'add_fixture', return_value=fixture):
        return projection.norm.post.base.prepared(D, tp, seqlen)


@pytest.mark.parametrize('D,tp,seqlen,branches', [(2, 2, 2, 3), (3, 2, 4, 4), (2, 3, 6, 5), (1, 2, 6, 1)])
def test_all_original_immediate_views_and_strong_units(D, tp, seqlen, branches):
    from Verdict import runtime_projection_values as prior
    args = prepared(D, tp, seqlen, branches)
    with patch.object(prior, 'render', wraps=prior.render) as fresh:
        text, detail = api()(*args)
        assert fresh.call_count == 1
    assert len(detail['reads']) == branches*(1+D*tp)
    assert len(detail['units']) == D*branches
    assert detail['deferred_units'] == []
    assert text.count('SourceLayoutRead.view_value_of_split') == len(detail['reads'])
    assert text.count('source_view_sequence_unit_output_reconstruct') == D*sum(not(j%2 == 1 or j == 2) for j in range(branches))
    assert text.count('source_view_head_unit_output_reconstruct') == D*sum(j%2 == 1 or j == 2 for j in range(branches))
    assert 'projectionLinearUnitFacts_' in text
    for row in detail['reads']:
        assert row['op'] == 'FW_view'
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
        assert row['request'] == 'global'
        assert f'{row["world"]}Node_{row["source_index"]}' in text
    for row in detail['units']:
        assert row['ranks'] == list(range(row['unit']*tp, (row['unit']+1)*tp))
        assert row['global_shape'][-1] == row['local_shape'][-1] == 2
        assert f'have predecessor := {row["predecessor"]} s p t q hs hp hvalues' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for bad in ('sorry', 'admit', 'native_decide', '(hshape :', '(houtput :', 'transposeAxes_value', 'SourceAllToAllRead'):
        assert bad not in text
    assert detail['lean_bytes'] == len(text.encode())
    assert 'UNCOMPILED' in text
    assert api()(*args) == (text, detail)


@pytest.mark.parametrize('D,tp,seqlen', [(2, 2, 2), (3, 2, 4), (2, 3, 6)])
def test_original_alltoall_is_explicit_deferred_boundary(D, tp, seqlen):
    from Verdict import runtime_projection_values as prior
    args = prepared(D, tp, seqlen, deferred=True)
    _, predecessor = prior.render(*args)
    assert len(predecessor['units']) == 3*D
    text, detail = api()(*args)
    assert len(detail['reads']) == 3+2*D*tp
    assert len(detail['units']) == 2*D
    assert len(detail['deferred_units']) == D
    assert 'before-first-local-view' in detail['deferred_stage']
    for row in detail['deferred_units']:
        assert row['reason'] == 'original-authenticated-AllToAll-before-first-local-view'
        assert row['slot'] == 2
        assert len(row['boundaries']) == tp
        assert row['predecessor'] in {u['theorem'] for u in predecessor['units']}
        for boundary in row['boundaries']:
            assert boundary['source_writer']
            assert boundary['op'] == 'AllToAllPrim'
            assert boundary['params'] == [2, 1]
            assert boundary['input_metadata'] == 'local-only'
    assert 'SourceAllToAllRead' not in text
    assert all(r['op'] == 'FW_view' for r in detail['reads'])


@pytest.mark.parametrize('world', [0, 1])
@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['bounds', 'value', 'tid', 'name', 'parent', 'bool', 'missing'])
def test_raw_metadata_faults_reach_view_not_predecessor(world, field, fault):
    from Verdict import runtime_projection_values as prior
    args = prepared()
    cell = next(c for c in args[3]._inputs[world] if c.opname == 'FW_view')
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
    ir = irs[0]
    if fault == 'bounds': ir.indmap = (*ir.indmap[:-1], (1, ir.indmap[-1][1]+1))
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'tid': ir.tid += 9000
    elif fault == 'name': ir.parent.name = 'unrelated-source'
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'bool': ir.valmap = (False, 1)
    else: irs.clear()
    if fault != 'missing':
        # Full-world authentication accepts these independently retained metadata
        # mutations: rejection MUST come from the new source view guards.
        assert prior.render(*args)[1]['units']
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('fault', ['size', 'missing-size', 'unknown-kwargs', 'wrong-ref', 'rank', 'partial', 'ambiguous', 'schedule'])
def test_inventory_and_kwargs_faults(fault):
    args = prepared()
    cell = next(c for c in args[3]._inputs[1] if c.opname == 'FW_view')
    if fault == 'size': cell.kwargs['size'][-1] += 1
    elif fault == 'missing-size': cell.kwargs.pop('size')
    elif fault == 'unknown-kwargs': cell.kwargs['unknown'] = 1
    elif fault == 'wrong-ref': cell.inputs[0] = cell.inputs[0]._replace(v=0)
    elif fault == 'rank': cell.rank += 1
    elif fault == 'partial': args[3]._inputs[1].remove(cell)
    elif fault == 'ambiguous': args[3]._inputs[1].append(copy.copy(cell))
    else: args[-1]['pm']['execution_to_source'].reverse()
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('selected', [True, False])
def test_selected_and_entire_suffix_operand_nonwrites(selected):
    from dataclasses import replace
    from Verdict import runtime_view_values as view
    from Verdict import runtime_projection_values as prior
    from Verdict.runtime_lineage import _Index
    args = prepared()
    _, predecessor = prior.render(*args)
    pm, order = args[1], args[-1]['pm']
    index = _Index(pm, args[3]._inputs[1])
    port = view._output(index, predecessor['units'][0]['local_steps'][0])
    step = view._view(index, view._consumer(index, port), port)
    node = next(n for n in pm.nodes() if tuple(n) == step.node)
    target = node if selected else pm.nodes()[order['execution_to_source'][-1]]
    pm._node2outputs[target] = pm.node_inputs(node)
    if selected: step = replace(step, outputs=(step.inputs[0],))
    with pytest.raises(ValueError, match='operand.*written'):
        view._read(pm, 'pm', step, order)


def test_forward_consumer_ignores_saved_primal_backward_read_without_mutation():
    from Verdict import runtime_view_values as view
    ref = ('s', 0, 0, 10, 1)
    forward = NS(rank=0, opname='FW_view', inputs=[ref])
    backward = NS(rank=0, opname='BW_view', inputs=[('s', 0, 0, 20, 1), ref])
    raw = {'forward': forward, 'backward': backward}
    index = NS(raw=raw)
    port = NS(endpoint=NS(ref=ref))
    assert view._consumer(index, port) is forward
    assert index.raw == raw and index.raw['backward'] is backward


def test_T1_is_honestly_rejected_by_original_predecessor():
    with pytest.raises(ValueError, match='unsupported non-hidden embedding layout'):
        api()(*prepared(1, 1, 2, 1))


@pytest.mark.parametrize('fault', ['shift-sequence', 'shift-head', 'partial-inner', 'rank', 'target-product'])
def test_independent_output_metadata_rejects_predecessor_accepted_faults(fault):
    from Verdict import runtime_projection_values as prior
    args = prepared()
    cell = next(c for c in args[3]._inputs[1] if c.opname == 'FW_view' and c.rank == 0)
    ir = cell._output_irs[0]
    shape, bounds = list(ir.parent.shape), list(ir.indmap)
    if fault in ('shift-sequence', 'shift-head', 'partial-inner'):
        axis = {'shift-sequence': 1, 'shift-head': 2, 'partial-inner': 3}[fault]
        bounds[axis] = tuple(x+1 for x in bounds[axis]); shape[axis] += 1
    elif fault == 'rank':
        shape.append(1); bounds.append((0, 1))
    else: shape[2] *= 2
    ir.parent.shape, ir.indmap = tuple(shape), tuple(bounds)
    assert prior.render(*args)[1]['units']
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('fault', ['source-writer', 'ordered-ranks', 'local-index', 'peers', 'params', 'input-value', 'output-bounds', 'partial-irs'])
def test_deferred_boundary_authentication_faults(fault):
    from dataclasses import replace
    from Verdict import runtime_projection_values as prior
    args = prepared(deferred=True)
    pm = args[1]
    cell = next(c for c in args[3]._inputs[1] if c.opname == 'AllToAllPrim' and c.node.cid == 62)
    if fault in ('input-value', 'output-bounds', 'partial-irs'):
        if fault == 'input-value': cell._input_irs[0].valmap = (1, 2)
        elif fault == 'output-bounds':
            ir = cell._output_irs[0]; ir.indmap = (*ir.indmap[:2], (1, ir.parent.shape[2]+1))
        else: cell._input_irs.clear()
        assert prior.render(*args)[1]['units']
    else:
        node = next(n for n in pm.collective_scopes if tuple(n) == tuple(cell.node))
        changes = {'source-writer': dict(source_writer='wrong'), 'ordered-ranks': dict(ranks=(1, 0)),
            'local-index': dict(local_index=1), 'peers': dict(input_tids=(999, 998)), 'params': dict(params=(1, 2))}
        pm.collective_scopes[node] = replace(pm.collective_scopes[node], **changes[fault])
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('kind', ['mixed', 'unknown', 'missing', 'ambiguous'])
def test_frontier_inventory_is_not_filtered_by_supported_name(kind):
    from Verdict import runtime_view_values as view
    from Verdict import runtime_projection_values as prior
    args = prepared(deferred=True)
    _, predecessor = prior.render(*args)
    raw = args[3]._inputs[1]
    cell = next(c for c in raw if c.opname == 'AllToAllPrim' and c.node.cid == 62)
    if kind == 'mixed': cell.opname = 'FW_view'
    elif kind == 'unknown': cell.opname = 'FW_contiguous'
    elif kind == 'missing': raw.remove(cell)
    else: raw.append(copy.copy(cell))
    # Exercise frontier inventory independently of full-world replay to prove
    # unsupported consumers are not merely discarded by a whitelist.
    with pytest.raises(ValueError): view._render(args[0], args[1], args[3], args[-1], predecessor)


def test_normalized_original_kwargs_and_value_partition_preservation():
    from dataclasses import replace
    from Verdict import runtime_view_values as view
    from Verdict import runtime_projection_values as prior
    from Verdict.runtime_lineage import _Index
    args = prepared()
    _, predecessor = prior.render(*args)
    index = _Index(args[1], args[3]._inputs[1])
    port = view._output(index, predecessor['units'][0]['local_steps'][0])
    cell = view._consumer(index, port)
    for ir in (*cell._input_irs, *cell._output_irs): ir.valmap = (1, 2)
    cell.kwargs['size'][-1] = -1
    node = next(n for n in args[1].nodes() if tuple(n) == tuple(cell.node))
    # Fixture view kwargs retain the original mapping; update explicitly if
    # the fixture changes to return a separate mapping in the future.
    args[1].node_kwargs(node)['size'][-1] = -1
    step = view._view(index, cell, replace(port, value_part=(1, 2)))
    assert step.outputs[0].value_part == (1, 2)
    assert step.outputs[0].endpoint.shape[-1] == 2
