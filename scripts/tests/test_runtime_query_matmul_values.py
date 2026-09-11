"""Portable original-source query matmul tracer; no capture/kernel claim."""
import copy
import importlib
import importlib.util
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_softmax_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR
from Verdict import runtime_softmax_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_query_matmul_values'), 'query matmul renderer missing'
    return importlib.import_module('Verdict.runtime_query_matmul_values')


def fixture(D=2, tp=2, seqlen=2):
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    # Correct the portable next-boundary metadata from the two actual operands.
    # This is not an actual capture or a numerical equivalence claim.
    for graph in (sm, pm):
        for cell in graph.cells:
            if cell.opname != 'FW_matmul' or cell.node.cid == 9000:
                continue
            x, y = cell._input_irs
            old = cell._output_irs[0]
            out = IR(old.tid, old.parent.name, (*x.parent.shape[:3], y.parent.shape[3]),
                (*x.indmap[:3], y.indmap[3]))
            cell._output_irs = [out]; graph.shapes[cell.outputs[0]] = out.shape
            for consumer in graph.cells:
                for i, ref in enumerate(consumer.inputs):
                    if ref == cell.outputs[0]: consumer._input_irs[i] = copy.deepcopy(out)
    # Source order is deliberately not execution order; dependency sorting owns execution.
    sm.cells.sort(key=lambda c: c.opname.startswith('BW_'))
    pm.cells.sort(key=lambda c: (c.rank, c.opname.startswith('BW_')))
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), *authority[2:])


def prepared(D=2, tp=2, seqlen=2):
    base = previous.previous.previous.previous.previous.previous.previous.previous.previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=fixture(D, tp, seqlen)):
        return base.prepared(D, tp, seqlen)


def test_first_query_matmul_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'deferred_units', 'frontier_units')] == [5, 2, 0, 2]
    assert [r['world'] for r in detail['reads']] == ['sm', 'pm', 'pm', 'pm', 'pm']
    assert detail['consumed_frontier_indices'] == [0, 1, 2, 3]
    assert text.count('SourceMatmulRead.matmul_value_of_split') == 5
    assert text.count('TrainVerify.Denote.source_query_matmul_unit_output_reconstruct') == 2
    assert args[-1] == before
    assert [u['gather_axis'] for u in prior['frontier_units']] == [2, None, 2, None]
    for u in detail['units']:
        assert u['layout'] == 'sharded' and u['gather_axis'] == 2
        assert u['local_shape'] == [1, 4, 1, 4] and u['global_shape'] == [2, 4, 2, 4]
        assert u['ordered_join']['frontier_indices'] == [2*u['unit'], 2*u['unit']+1]
        assert len(u['predecessors']) == 2 and len(u['pm_output_refs']) == 2
        fragment = text.split('theorem '+u['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert 'left.1 right.1 rfl rfl left.2.1 right.2.2 left.2.2' in fragment
        assert 'List.zipWith fw_matmul' in fragment
    for r in detail['reads']:
        assert r['params'] == [] and r['request'] == 'global'
        assert r['operand_nonwrite_source_indices'] == args[-1][r['world']]['execution_to_source'][r['execution_index']:]
        assert r['theorem'].startswith('queryMatmulRead_')
        assert r['input_parent_identity'] == 'both-present'
    assert detail['reads'][0]['frontier_index'] == 0 and detail['reads'][0]['unit'] == 0
    assert any(r['source_index'] != r['execution_index'] for r in detail['reads'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def seam(args, prior, label='pm', peer=0):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    index = _Index(args[0 if label == 'sm' else 1], args[3]._inputs[0 if label == 'sm' else 1])
    operands = [middle._output(index, u['source_step'] if label == 'sm' else u['local_steps'][peer])
        for u in prior['frontier_units'][:2]]
    return index, view._consumer(index, operands[0]), operands


@pytest.mark.parametrize('label,operand', [('sm', 0), ('sm', 1), ('pm', 0), ('pm', 1)])
def test_raw_parent_guard_after_predecessor_acceptance(baseline, label, operand):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior, label)
    cell._input_irs = copy.deepcopy(cell._input_irs)
    cell._input_irs[operand].parent.tid += 37
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent identity'): api().render(*args)


@pytest.mark.parametrize('peer', [0, 1])
@pytest.mark.parametrize('metadata', ['absent', 'none'])
@pytest.mark.parametrize('changed_parent', [False, True])
def test_missing_producer_cannot_bypass_parent_guard(baseline, peer, metadata, changed_parent):
    args, prior = copy.deepcopy(baseline); index, cell, operands = seam(args, prior, peer=peer)
    producer = index.raw[operands[0].endpoint.writer]
    cell._input_irs = copy.deepcopy(cell._input_irs)
    if changed_parent: cell._input_irs[0].parent.tid += 37
    if metadata == 'absent': del producer._output_irs
    else: producer._output_irs = None
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='complete original producer output metadata'):
        api().render(*args)


@pytest.mark.parametrize('fault', ['left-name', 'left-value', 'output-parent', 'output-query-bounds', 'output-value', 'input-absent', 'output-absent'])
def test_paired_metadata_new_boundary_after_predecessor_accepts(baseline, fault):
    args, prior = copy.deepcopy(baseline); index, cell, ports = seam(args, prior)
    if fault == 'input-absent': del cell._input_irs
    elif fault == 'output-absent': del cell._output_irs
    else:
        field = '_input_irs' if fault.startswith('left') else '_output_irs'
        irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs); ir = irs[0]
        if fault.endswith('name'): ir.parent.name = 'wrong-source'
        elif fault.endswith('value'): ir.valmap = (1, 2)
        elif fault == 'output-parent': ir.parent.shape = (*ir.parent.shape[:2], ir.parent.shape[2]+1, ir.parent.shape[3])
        else:
            bounds = list(ir.indmap); bounds[2] = (1, 2); ir.indmap = tuple(bounds)
    if fault.endswith('absent'):
        # Ordinary missing port metadata is rejected upstream; only the private
        # boundary independently exercises the new mandatory-metadata guard.
        with pytest.raises(ValueError): predecessor.render(*args)
        with pytest.raises(ValueError): api()._matmul(index, cell, ports)
    else:
        assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'cross-DP', 'duplicate', 'unsupported-axis'])
def test_private_frontier_contract_rejection(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['frontier_units']
    if fault == 'ranks': prior['frontier_units'][1]['ranks'].reverse()
    elif fault == 'positions': prior['frontier_units'][1]['positions'] = ['not-the-owner-position']
    elif fault == 'cross-DP': prior['frontier_units'][1]['unit'] = 1
    elif fault == 'duplicate': prior['frontier_units'].append(copy.deepcopy(prior['frontier_units'][0]))
    else: prior['frontier_units'][0]['gather_axis'] = 1
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_private_missing_operand_deferral_and_reordered_frontier(baseline):
    args, prior = copy.deepcopy(baseline)
    old = prior['frontier_units']; prior['frontier_units'] = [old[1], old[0], old[3], old[2]]
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['ordered_join']['frontier_indices'] for u in detail['units']] == [[1, 0], [3, 2]]
    prior['frontier_units'] = [old[0], old[2], old[3]]
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [len(detail[k]) for k in ('units', 'deferred_units', 'frontier_units')] == [1, 1, 2]
    d = detail['deferred_units'][0]
    assert d['missing_operand_refs'] == [old[1]['sm_output_ref']] and not d['value_proved']
    assert detail['frontier_units'][0] is old[0]


@pytest.mark.parametrize('fault', ['swapped', 'cross-DP'])
def test_private_ordered_operand_identity(baseline, fault):
    from Verdict import runtime_middle_exchange_values as middle
    args, prior = copy.deepcopy(baseline); index, cell, ports = seam(args, prior)
    if fault == 'swapped': ports.reverse()
    else: ports[1] = middle._output(index, prior['frontier_units'][3]['local_steps'][0])
    with pytest.raises(ValueError, match='ordered local ports'): api()._matmul(index, cell, ports)


@pytest.mark.parametrize('operand', [0, 1])
@pytest.mark.parametrize('where', ['selected', 'last'])
def test_private_complete_both_operand_nonwrites(baseline, operand, where):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index, cell, ports = seam(args, prior)
    step = api()._matmul(index, cell, ports); source = args[1]
    _, read = api()._read(source, 'pm', step, args[-1]['pm'])
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if where == 'selected' else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    if where == 'last': assert source.node_opname(target).startswith('BW_')
    assert source.nodes().index(target) in read['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[operand]]
    if where == 'selected': step = replace(step, outputs=(ports[operand],))
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, 'pm', step, args[-1]['pm'])


@pytest.mark.parametrize('fault', ['call', 'export', 'fullref', 'owner', 'kwargs'])
def test_upstream_authority_rejections_are_not_new_guard_claims(baseline, fault):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'export': writer['export_id'] = 'wrong'
    elif fault == 'fullref': writer['inputs'][1]['version'] += 1
    elif fault == 'owner': args[3]._inputs[3]['config']['units'][0]['ranks'].reverse()
    else: cell.kwargs = {'__consts': [1]}
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('tp,seqlen', [(3, 9)])
def test_coherent_T3_public_source_geometry(tp, seqlen):
    args = prepared(2, tp, seqlen); text, detail = api().render(*args)
    assert len(detail['reads']) == 1+2*tp and len(detail['units']) == 2
    assert not detail['deferred_units']
    for u in detail['units']:
        assert u['dimensions'] == dict(D=2, T=tp, B=1, H=2*tp, Q=seqlen//tp, K=seqlen, M=2*tp)
        assert u['global_shape'] == [2, 2*tp, seqlen, 2*tp]
        assert u['local_shape'] == [1, 2*tp, seqlen//tp, 2*tp]


@pytest.mark.parametrize('bad', [0, False])
def test_private_unit_positive_geometry(baseline, bad):
    args, prior = copy.deepcopy(baseline); index, cell, ports = seam(args, prior)
    si, sc, sp = seam(args, prior, 'sm')
    global_ = api()._matmul(si, sc, sp); local = api()._matmul(index, cell, ports)
    left, right = prior['frontier_units'][:2]
    left['dimensions']['T'] = bad; right['dimensions']['T'] = bad
    with pytest.raises(ValueError, match='positive'):
        api()._unit(left, right, global_, [local], {}, {})



def test_T1_private_unit_geometry_not_upstream_fixture_claim(baseline):
    # The older projection-exchange fixture cannot construct T=1 (StopIteration).
    # This is deliberately a private unit-rendering test, not public authority.
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    si, sc, sp = seam(args, prior, 'sm'); pi, pc, pp = seam(args, prior)
    global_ = api()._matmul(si, sc, sp); local = api()._matmul(pi, pc, pp)
    left, right = prior['frontier_units'][:2]
    for old in (left, right):
        old['dimensions']['T'] = 1; old['ranks'] = old['ranks'][:1]; old['positions'] = old['positions'][:1]
    left['local_shape'] = [1, *left['global_shape'][1:]]
    out = local.outputs[0]; shape = (1, *global_.outputs[0].endpoint.shape[1:])
    out = replace(out, endpoint=replace(out.endpoint, shape=shape), bounds=tuple((0, d) for d in shape))
    local = replace(local, outputs=(out,))
    names = {global_.node: 'globalRead', local.node: 'localRead'}
    proof, unit = api()._unit(left, right, global_, [local], names, {})
    assert unit['dimensions']['T'] == 1 and unit['local_shape'] == list(shape)
    assert 'source_query_matmul_unit_output_reconstruct 2 1 1 4 2 2 4 0' in '\n'.join(proof)
