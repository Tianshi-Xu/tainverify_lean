"""Portable original-source matmul checkpoint; no capture or kernel claims."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_middle_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_middle_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_matmul_values'), 'matmul renderer missing'
    return importlib.import_module('Verdict.runtime_matmul_values')


def fixture(D=2, tp=2, seqlen=2, branches=3, saved=True, mutation=None):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen, branches, saved)
    old = copy.deepcopy(authority[2]); rows = []
    old['writers'] = [w for w in old['writers'] if w['ref']['op'] != 'FW_matmul']
    old['adapter_source'] = [w for w in old['adapter_source'] if w['ref']['op'] != 'FW_matmul']
    for world, graph in [('s', sm), ('p', pm)]:
        removed = [c for c in graph.cells if c.opname == 'FW_matmul']
        graph.cells[:] = [c for c in graph.cells if c not in removed]
        for c in removed:
            for ref in c.outputs: graph.shapes.pop(ref)
        for rank in range(D*tp if world == 'p' else 1):
            # Fixture topology only: renderer must join using fullrefs, not these tids.
            qtid, ktid = (800, 901) if world == 's' else (1000, 1201)
            q = next(c for c in graph.cells if c.rank == rank and c.outputs[0].tid == qtid)
            k = next(c for c in graph.cells if c.rank == rank and c.outputs[0].tid == ktid)

            def append(cid, kind, producers, shape, bounds, name):
                out = IR(cid, name, shape, bounds)
                cell = NS(node=N(world, rank, 0, cid, kind), rank=rank, opname=kind,
                    inputs=[p.outputs[0] for p in producers], outputs=[T(world, rank, 0, cid, 1)],
                    _input_irs=[copy.deepcopy(p._output_irs[0]) for p in producers],
                    _output_irs=[out], kwargs={})
                cell.ir = NS(signature=kind, inputs=lambda c=cell: c._input_irs,
                    outputs=lambda c=cell: c._output_irs)
                graph.cells.append(cell); graph.shapes[cell.outputs[0]] = out.shape
                if world == 'p':
                    rows.append(dict(ref=dict(world=world, runtime_rank=rank, microbatch=0,
                        source_cid=cid, call_instance=0, op=kind, origin='fixture'),
                        source_irname=kind, inputs=[tref(t) for t in cell.inputs],
                        outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[]))
                return cell

            x, y = q._output_irs[0], k._output_irs[0]
            z = append(9000, 'FW_matmul', [q, k], (*x.parent.shape[:3], y.parent.shape[3]),
                (*x.indmap[:3], y.indmap[3]), 'score.product')
            # Each remaining branch's other operand is outside this checkpoint.
            terminal = [c for c in graph.cells if c.rank == rank and c is not z
                and c.opname in ('FW_transpose', 'AllToAllPrim', 'AllGatherPrim')
                and not any(c.outputs[0] in d.inputs and not d.opname.startswith('BW_') for d in graph.cells)]
            for j, v in enumerate(terminal):
                a = append(9100+j, 'FW_softmax', [z], x.parent.shape, x.indmap, 'attention')
                vout = v._output_irs[0]
                append(9200+j, 'FW_matmul', [a, v], vout.parent.shape, vout.indmap, 'later.product')
    if mutation:
        mutation(pm)
        # Rebuild writer authority coherently from the changed original graph;
        # negatives below are not stale-snapshot/hash rejection tests.
        rows = [dict(ref=dict(world='p', runtime_rank=c.rank, microbatch=0,
            source_cid=c.node.cid, call_instance=0, op=c.opname, origin='fixture'),
            source_irname=c.node.irname, inputs=[tref(t) for t in c.inputs],
            outputs=[tref(t) for t in c.outputs], parameter_grad_tids=[])
            for c in pm.cells if c.node.cid >= 9000]
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*old['adapter_source'], *copy.deepcopy(rows)]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3, saved=True, mutation=None):
    base = previous.previous.previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=fixture(D, tp, seqlen, branches, saved, mutation)):
        return base.prepared(D, tp, seqlen)


def test_first_ready_tracer():
    args = prepared()
    prior = predecessor.render(*args)[1]
    before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'deferred_units', 'frontier_units')] == [5, 2, 2, 4]
    assert text.count('SourceMatmulRead.matmul_value_of_split') == 5
    assert text.count('TrainVerify.Denote.source_matmul_unit_output_reconstruct') == 2
    assert args[-1] == before
    assert [r['world'] for r in detail['reads']] == ['sm', 'pm', 'pm', 'pm', 'pm']
    for u in detail['units']:
        assert u['global_shape'] == [2, 4, 2, 2]
        assert u['local_shape'] == [1, 2, 2, 2]
        assert len(u['ordered_join']['frontier_indices']) == 2
        fragment = text.split('theorem '+u['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        for p in u['predecessors']: assert p+' s p t q hs hp hvalues' in fragment
    unchanged = [u for u in prior['frontier_units'] if u['gather_axis'] is None]
    assert [u for u in detail['frontier_units'] if u['gather_axis'] is None] == unchanged
    assert all(d['missing_operand_refs'] and not d['value_proved'] for d in detail['deferred_units'])
    assert detail['consumed_frontier_indices'] == [0, 1, 3, 4]
    assert 'UNCOMPILED' in text
    for f in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[f] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


@pytest.mark.parametrize('D,tp,seqlen,branches', [(3, 2, 6, 4), (2, 3, 6, 5), (1, 2, 2, 2)])
def test_variable_dimensions_branches(D, tp, seqlen, branches):
    args = prepared(D, tp, seqlen, branches)
    _, detail = api().render(*args)
    assert len(detail['reads']) == 1+D*tp
    assert len(detail['units']) == D
    assert len(detail['deferred_units']) == D*(branches-2)
    assert len(detail['frontier_units']) == D*(branches-1)
    for u in detail['units']:
        assert u['dimensions']['Q'] == seqlen
        assert u['dimensions']['M'] == seqlen
        assert u['dimensions']['K'] == 2*tp
    for read in detail['reads']:
        order = args[-1][read['world']]
        assert read['operand_nonwrite_source_indices'] == order['execution_to_source'][read['execution_index']:]
    for source, label in zip(args[:2], ('sm', 'pm'), strict=True):
        bw = {i for i, n in enumerate(source.nodes()) if source.node_opname(n).startswith('BW_')}
        assert bw and bw <= set(args[-1][label]['execution_to_source'])


def ready_cell(args):
    return next(c for c in args[3]._inputs[1] if c.opname == 'FW_matmul' and c.node.cid == 9000)


@pytest.mark.parametrize('fault', ['right-name', 'right-value', 'right-parent', 'right-bounds',
    'output-parent', 'output-bounds', 'output-value', 'coordinated-output-value'])
def test_new_guard_paired_metadata_after_fresh_middle(baseline, fault):
    args, _ = copy.deepcopy(baseline)
    selected = ready_cell(args)
    cells = [c for c in args[3]._inputs[1] if c.opname == 'FW_matmul' and c.node.cid == 9000] if fault.startswith('coordinated') else [selected]
    for cell in cells:
        field = '_input_irs' if fault.startswith('right') else '_output_irs'
        irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
        ir = irs[1 if field == '_input_irs' else 0]
        if fault.endswith('name'): ir.parent.name = 'wrong-logical-producer'
        elif fault.endswith('value'): ir.valmap = (1, 2)
        elif fault.endswith('parent'): ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
        else: ir.indmap = (ir.indmap[0], (1, ir.indmap[1][1]+1), *ir.indmap[2:])
    # These are NEW guard teeth, not an upstream rejection presented as one.
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['inputs', 'outputs', 'call', 'export'])
def test_writer_tampering_is_upstream_rejection(baseline, fault):
    args, _ = copy.deepcopy(baseline)
    cell = ready_cell(args)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault in ('inputs', 'outputs'): writer[fault][0]['version'] += 1
    elif fault == 'call': writer['ref']['call_instance'] += 1
    else: writer['export_id'] = 'forged-writer'
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['partial', 'missing-consumer', 'unknown'])
def test_upstream_partial_missing_unknown(baseline, fault):
    args, _ = copy.deepcopy(baseline)
    cell = ready_cell(args)
    if fault == 'partial': cell._input_irs = cell._input_irs[:1]
    elif fault == 'missing-consumer': args[3]._inputs[1].remove(cell)
    else: cell.opname = 'FW_unknown'
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('position', [0, 1])
@pytest.mark.parametrize('selected_writer', [False, True])
def test_nonwrites_cover_both_operands_and_selected_entire_suffix(baseline, position, selected_writer):
    from Verdict.runtime_lineage import _Index
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index = _Index(args[1], args[3]._inputs[1]); cell = ready_cell(args)
    operands = [predecessor._output(index, prior['frontier_units'][i]['local_steps'][0]) for i in (0, 1)]
    step = api()._matmul(index, cell, operands)
    _, row = api()._read(args[1], 'pm', step, args[-1]['pm'])
    source = args[1]; node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if selected_writer else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    assert source.nodes().index(target) in row['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[position]]
    if selected_writer: step = replace(step, outputs=(step.inputs[position],))
    with pytest.raises(ValueError, match='operand.*written'):
        api()._read(source, 'pm', step, args[-1]['pm'])


@pytest.mark.parametrize('fault', ['reversed-ports', 'wrong-pair', 'rank-order', 'mixed-DP', 'layout', 'duplicate'])
def test_join_guard_uses_fullrefs_not_shapes_or_slots(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['frontier_units']
    if fault in ('reversed-ports', 'wrong-pair'):
        from Verdict.runtime_lineage import _Index
        index = _Index(args[1], args[3]._inputs[1]); cell = ready_cell(args)
        operands = [predecessor._output(index, prior['frontier_units'][i]['local_steps'][0]) for i in (0, 1)]
        if fault == 'reversed-ports': operands.reverse()
        else: operands[1] = predecessor._output(index, prior['frontier_units'][2]['local_steps'][0])
        with pytest.raises(ValueError, match='ordered local ports'):
            api()._matmul(index, cell, operands)
        return
    if fault == 'rank-order': prior['frontier_units'][1]['ranks'].reverse()
    elif fault == 'mixed-DP': prior['frontier_units'][1]['unit'] = 1
    elif fault == 'layout': prior['frontier_units'][1]['layout'] = 'replicated_within_dp'
    else: prior['frontier_units'].append(copy.deepcopy(prior['frontier_units'][0]))
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_original_frontier_encounter_order_not_operand_order(baseline):
    args, prior = copy.deepcopy(baseline)
    old = prior['frontier_units']
    prior['frontier_units'] = [old[i] for i in (2, 1, 0, 5, 4, 3)]
    for u in prior['frontier_units']: u['slot'] = 777  # Not a join authority.
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['gather_axis'] for u in detail['frontier_units']] == [None, 1, None, 1]
    assert [u['ordered_join']['frontier_indices'] for u in detail['units']] == [[2, 1], [5, 4]]


@pytest.mark.parametrize('fault', ['reversed', 'wrong-pair'])
def test_coherent_actual_ordered_source_join_after_fresh_middle(fault):
    def mutation(graph):
        cell = next(c for c in graph.cells if c.node.cid == 9000 and c.rank == 0)
        if fault == 'reversed':
            cell.inputs.reverse(); cell._input_irs.reverse()
        else:
            # Same-shaped but different actual source operands, plus a distinct
            # legal first matmul consumer for K. No missing/unknown-op escape.
            other = copy.deepcopy(cell)
            other.node = N('p', 0, 0, 9800, 'FW_matmul')
            other.inputs = [cell.inputs[1]]*2
            other._input_irs = [copy.deepcopy(cell._input_irs[1]) for _ in range(2)]
            other.outputs = [T('p', 0, 0, 9800, 1)]
            ir = other._output_irs[0]; ir.tid = 9800; ir.parent.tid = 9800
            graph.cells.append(other); graph.shapes[other.outputs[0]] = ir.shape
            cell.inputs = [cell.inputs[0]]*2
            cell._input_irs = [copy.deepcopy(cell._input_irs[0]) for _ in range(2)]
    args = prepared(seqlen=4, mutation=mutation)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='ordered local ports|paired PM first consumer'):
        api().render(*args)


def test_deferred_local_operand_position_matches_global(baseline):
    args, prior = copy.deepcopy(baseline)
    # Existing middle checks each individual known port, but not the SM/PM
    # ordered port correspondence of a missing-other-operand boundary.
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 9200)
    cell.inputs.reverse(); cell._input_irs.reverse()
    source = args[1]; node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    source._node2inputs[node].reverse()
    writer = next(w for w in source._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    writer['inputs'].reverse()
    # Direct new-stage seam isolates the new order check from snapshot hashing.
    with pytest.raises(ValueError, match='deferred.*port'):
        api()._render(args[0], args[1], args[3], args[-1], prior)
