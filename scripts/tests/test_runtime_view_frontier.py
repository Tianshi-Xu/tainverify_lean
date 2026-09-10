"""Original backward saved-primal uses are not forward-view frontiers.

Only fixture construction is substituted; public predecessor authentication,
full execution schedules, and suffix liveness guards remain real.
"""
import copy
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_view_values as existing
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_projection_values as projection
from Verdict import runtime_view_values as view
from Verdict.runtime_lineage import _Index


def saved_primal_fixture():
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters

    sm, pm, authority = existing.view_fixture(deferred=True)
    rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        for forward in list(graph.cells):
            if forward.opname != 'FW_view':
                continue
            primal = forward._input_irs[0]
            out = IR(600 + forward.node.cid, 'view.input_grad', primal.parent.shape, primal.indmap)
            # Authentic BW_view argument order: gradient first, saved primal second.
            cell = NS(node=N(world, forward.rank, 0, 100 + forward.node.cid, 'BW_view'),
                rank=forward.rank, opname='BW_view',
                inputs=[forward.outputs[0], forward.inputs[0]],
                outputs=[T(world, forward.rank, 0, out.tid, 1)],
                _input_irs=copy.deepcopy([forward._output_irs[0], primal]),
                _output_irs=[out], kwargs={})
            cell.ir = NS(signature='BW_view', mirror=NS(cid=forward.node.cid), kwargs=cell.kwargs,
                inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
            graph.cells.append(cell)
            graph.shapes.update({r: ir.shape for r, ir in zip(cell.inputs, cell._input_irs)})
            graph.shapes[cell.outputs[0]] = out.shape
            if world == 'p':
                rows.append(dict(ref=dict(world=world, runtime_rank=cell.rank, microbatch=0,
                    source_cid=cell.node.cid, call_instance=0, op=cell.opname, origin='fixture'),
                    source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
                    outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[]))
    old = authority[2]
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *copy.deepcopy(rows)]
    bind_reducers(snapshot)
    bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared():
    fixture = saved_primal_fixture()
    with patch.object(existing.projection.norm.post.base, 'add_fixture', return_value=fixture):
        return existing.projection.norm.post.base.prepared(2, 2, 2)


def selected(args, world, predecessor):
    descriptor = (predecessor['units'][0]['source_step'] if world == 0
                  else predecessor['units'][0]['local_steps'][0])
    index = _Index(args[world], args[3]._inputs[world])
    port = view._output(index, descriptor)
    forward = next(c for c in index.raw.values() if c.opname == 'FW_view'
                   and tuple(c.inputs[0]) == port.endpoint.ref)
    backward = next(c for c in index.raw.values() if c.opname == 'BW_view'
                    and tuple(c.inputs[1]) == port.endpoint.ref)
    assert backward.inputs == [forward.outputs[0], forward.inputs[0]]
    assert backward.ir.mirror.cid == forward.node.cid
    return index, port, forward, backward


def test_public_saved_primal_frontier_preserves_authenticated_backward_execution():
    args = prepared()
    _, predecessor = projection.render(*args)  # Must succeed BEFORE the new renderer.
    assert len(predecessor['units']) == 6
    for world, label in [(0, 'sm'), (1, 'pm')]:
        raw = args[3]._inputs[world]
        forwards = [c for c in raw if c.opname == 'FW_view']
        backwards = [c for c in raw if c.opname == 'BW_view']
        assert len(backwards) == len(forwards)
        for forward in forwards:
            assert sum(c.inputs == [forward.outputs[0], forward.inputs[0]] for c in backwards) == 1
        nodes = args[world].nodes()
        assert all(nodes.index(c.node) in args[-1][label]['execution_to_source'] for c in backwards)
    text, detail = view.render(*args)
    assert len(detail['reads']) == 11
    assert len(detail['units']) == 4
    assert len(detail['deferred_units']) == 2
    assert all(row['slot'] == 2 for row in detail['deferred_units'])
    assert text.count('SourceLayoutRead.view_value_of_split') == 11
    for row in detail['reads']:
        world = 0 if row['world'] == 'sm' else 1
        suffix = args[-1][row['world']]['execution_to_source'][row['execution_index']:]
        assert row['operand_nonwrite_source_indices'] == suffix
        assert any(args[world].node_opname(args[world].nodes()[i]) == 'BW_view' for i in suffix)


@pytest.mark.parametrize('world', [0, 1], ids=['sm', 'pm'])
@pytest.mark.parametrize('fault', ['missing', 'unknown', 'second-forward'])
def test_forward_frontier_negatives_keep_backward_saved_primal(world, fault):
    args = prepared()
    _, predecessor = projection.render(*args)
    index, port, forward, backward = selected(args, world, predecessor)
    if fault == 'missing':
        del index.raw[tuple(forward.node)]
    elif fault == 'unknown':
        forward.opname = 'FW_contiguous'
    else:
        other = copy.copy(forward)
        other.node = other.node._replace(cid=other.node.cid + 1000)
        index.raw[tuple(other.node)] = other
    assert backward in index.raw.values()
    if fault == 'unknown':
        # Unknown forward operations must survive phase filtering, not vanish.
        assert view._consumer(index, port) is forward
        with pytest.raises(ValueError, match='opcode/arity'):
            view._view(index, forward, port)
    else:
        with pytest.raises(ValueError, match='consumer missing/ambiguous'):
            view._consumer(index, port)


@pytest.mark.parametrize('world', [0, 1], ids=['sm', 'pm'])
def test_backward_suffix_writer_still_blocks_operand_nonwrite(world):
    args = prepared()
    _, predecessor = projection.render(*args)
    index, port, forward, backward = selected(args, world, predecessor)
    # Directly select the known forward to isolate liveness from the RED frontier.
    step = view._view(index, forward, port)
    graph, label = args[world], ('sm', 'pm')[world]
    order = args[-1][label]
    _, healthy = view._read(graph, label, step, order)
    target = next(n for n in graph.nodes() if tuple(n) == tuple(backward.node))
    assert graph.nodes().index(target) in healthy['operand_nonwrite_source_indices']
    node = next(n for n in graph.nodes() if tuple(n) == step.node)
    graph._node2outputs[target] = [graph.node_inputs(node)[0]]
    with pytest.raises(ValueError, match='operand.*written'):
        view._read(graph, label, step, order)


def set_size(args, world, payload, missing=False):
    cell = next(c for c in args[3]._inputs[world] if c.opname == 'FW_view')
    node = next(n for n in args[world].nodes() if tuple(n) == tuple(cell.node))
    kwargs = {} if missing else {'size': copy.deepcopy(payload)}
    for target in (cell.kwargs, args[world].node_kwargs(node)):
        target.clear()
        target.update(copy.deepcopy(kwargs))
    assert cell.kwargs == args[world].node_kwargs(node)
    return cell


@pytest.mark.parametrize('world', [0, 1], ids=['sm', 'pm'])
@pytest.mark.parametrize('payload', [None, 'bad', [1, 2, 2], [True, 2, 2, 2],
    [1.0, 2, 2, 2], [0, 2, 2, 2], [-2, 2, 2, 2], [-1, -1, 2, 2],
    [1, 2, 2, 99], [-1, 3, 3, 3]],
    ids=['missing', 'string', 'arity', 'bool', 'float', 'zero', 'negative',
         'two-inferred', 'wrong-product', 'nondivisible-inferred'])
def test_coherent_invalid_size_is_rejected_after_predecessor_acceptance(world, payload):
    args = existing.prepared(deferred=True)
    set_size(args, world, payload, missing=payload is None)
    assert len(projection.render(*args)[1]['units']) == 6
    with pytest.raises(ValueError, match='view original (size kwargs|inferred size product)'):
        view.render(*args)


@pytest.mark.parametrize('world', [0, 1], ids=['sm', 'pm'])
@pytest.mark.parametrize('axis', [0, 1, 2, 3])
def test_full_public_render_accepts_one_inferred_size(world, axis):
    args = existing.prepared(deferred=True)
    cell = next(c for c in args[3]._inputs[world] if c.opname == 'FW_view')
    size = list(cell.kwargs['size'])
    size[axis] = -1
    set_size(args, world, size)
    assert len(projection.render(*args)[1]['units']) == 6
    text, detail = view.render(*args)
    assert len(detail['reads']) == 11
    assert len(detail['units']) == 4
    assert len(detail['deferred_units']) == 2
    assert text.count('SourceLayoutRead.view_value_of_split') == 11
