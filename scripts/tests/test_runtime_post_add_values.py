"""Portable extension of add fixtures; no fixture edits or Lean execution."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_add_values as base
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T


def api():
    assert importlib.util.find_spec('Verdict.runtime_post_add_values'), 'post-add renderer missing'
    return importlib.import_module('Verdict.runtime_post_add_values').render


def post_fixture(D=2, tp=2, seqlen=2, fault=None, exchange_slot=0):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    sm, pm, authority = base.add_fixture(D, tp, seqlen)
    added = []
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            add = next(c for c in graph.cells if c.rank == rank and c.node.cid == 15)
            original = add._output_irs[0]
            outs = [IR(tid, f'postadd.slot{slot}', original.parent.shape, original.indmap)
                    for slot, tid in enumerate((70, 71))]
            cell = NS(node=N(world, rank, 0, 17, 'FW_multiref'), rank=rank,
                opname='FW_multiref', inputs=list(add.outputs),
                outputs=[T(world, rank, 0, ir.tid, 1) for ir in outs],
                _input_irs=copy.deepcopy(add._output_irs), _output_irs=outs, kwargs={'times': 2})
            cell.ir = NS(signature='FW_multiref', inputs=lambda c=cell: c._input_irs,
                         outputs=lambda c=cell: c._output_irs)
            graph.cells.append(cell)
            graph.shapes.update({ref: ir.shape for ref, ir in zip(cell.outputs, outs)})
            if world == 'p':
                added.append(cell)
                ranks = list(range(rank//tp*tp, (rank//tp+1)*tp))
                bounds = ((0, 1), (rank%tp*(seqlen//tp), (rank%tp+1)*(seqlen//tp)), (0, tp*3))
                out = IR(72, outs[exchange_slot].parent.name, original.parent.shape, bounds)
                aa = NS(node=N(world, rank, 0, 18, 'AllToAllPrim'), rank=rank,
                    opname='AllToAllPrim', inputs=[T(world, r, 0, 70+exchange_slot, 1) for r in ranks],
                    outputs=[T(world, rank, 0, 72, 1)], _input_irs=[copy.deepcopy(outs[exchange_slot])],
                    _output_irs=[out], kwargs=dict(ranks=ranks, idim=2, odim=1))
                aa.ir = NS(signature='AllToAllPrim', inputs=lambda c=aa: c._input_irs,
                           outputs=lambda c=aa: c._output_irs)
                graph.cells.append(aa)
                graph.shapes[aa.outputs[0]] = out.shape
                added.append(aa)
    if fault:
        for graph in (sm, pm):
            for cell in list(graph.cells):
                if cell.node.cid == 17:
                    if fault == 'coherent-times': cell.kwargs['times'] = 1
                    elif fault == 'coherent-bool-times': cell.kwargs['times'] = True
                    elif fault == 'coherent-kwargs': cell.kwargs['unknown'] = 1
                    elif fault == 'coherent-consts': cell.kwargs['__consts'] = [1]
                    elif fault == 'missing-multiref':
                        cell.opname = 'FW_contiguous'
                        cell.node = cell.node._replace(irname='FW_contiguous')
                        cell.kwargs = {}
                    elif fault == 'duplicate-multiref':
                        duplicate = copy.copy(cell)
                        duplicate.node = cell.node._replace(cid=19)
                        duplicate.outputs = [ref._replace(tid=ref.tid+10) for ref in cell.outputs]
                        duplicate._output_irs = [IR(ir.tid+10, ir.parent.name, ir.parent.shape, ir.indmap)
                                                 for ir in cell._output_irs]
                        graph.cells.append(duplicate)
                        graph.shapes.update({ref: ir.shape for ref, ir in zip(duplicate.outputs, duplicate._output_irs)})
                        if graph is pm: added.append(duplicate)
                if fault == 'missing-AA' and cell.node.cid == 18:
                    graph.cells.remove(cell)
                    added.remove(cell)
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
                generated_inputs=[f'postadd_{70+exchange_slot}'], generated_outputs=['postadd_72'])
        rows.append(row); adapters.append(adapter)
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *adapters]
    for rank in range(D*tp):
        ranks = list(range(rank//tp*tp, (rank//tp+1)*tp))
        snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace(
            '\ndef _train_step', '\n        postadd_70, postadd_71 = multiref(added_60, times=2)\n'
            f'        postadd_72 = nnscaler.runtime.adapter.all_to_all(postadd_{70+exchange_slot}, idim=2, odim=1, ranks={ranks})\ndef _train_step')
    if fault == 'missing-AA':
        for rank, text in snapshot['rank_sources'].items():
            snapshot['rank_sources'][rank] = '\n'.join(line for line in text.splitlines() if 'postadd_72 =' not in line) + '\n'
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, fault=None, exchange_slot=0):
    fixture = post_fixture(D, tp, seqlen, fault, exchange_slot)
    with patch.object(base, 'add_fixture', return_value=fixture):
        return base.prepared(D, tp, seqlen)


@pytest.mark.parametrize('D,tp,seqlen', [(2, 2, 2), (3, 2, 2), (2, 3, 6)])
def test_all_original_alias_slots_and_exchange_reads(D, tp, seqlen):
    args = prepared(D, tp, seqlen)
    text, detail = api()(*args)
    assert len(detail['reads']) == 1 + 2*D*tp
    assert len(detail['units']) == 2*D
    aliases = [r for r in detail['reads'] if r['op'] == 'FW_multiref']
    assert len(aliases) == 1 + D*tp
    assert sum(len(r['output_tids']) for r in aliases) == 2*(1 + D*tp)
    assert text.count('SourceMultirefRead.multiref_value_of_split') == 1 + D*tp
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == D*tp
    assert '∀ output ∈' in text and 'addUnit_' in text and 'UNCOMPILED' in text
    assert {u['slot'] for u in detail['units']} == {0, 1}
    assert detail['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for bad in ('sorry', 'admit', 'native_decide', '(houtput :', '(hshape :'):
        assert bad not in text
    for read in detail['reads']:
        assert read['operand_nonwrite_source_indices'] == args[-1][read['world']]['execution_to_source'][read['execution_index']:]
    assert api()(*args) == (text, detail)



@pytest.mark.parametrize('fault', ['coherent-times', 'coherent-bool-times', 'coherent-kwargs',
    'coherent-consts', 'missing-multiref', 'duplicate-multiref', 'missing-AA'])
def test_coherent_invalid_graph_is_not_silently_skipped(fault):
    args = prepared(fault=fault)
    with pytest.raises(ValueError): api()(*args)


def test_matches_source_multiref_library_argument_order():
    args = prepared()
    text, detail = api()(*args)
    for row in detail['reads']:
        if row['op'] != 'FW_multiref':
            continue
        assert (f"{row['node'][1]} {row['input_tids'][0]} {row['output_tids']} "
                'output s t rfl ?_ rfl ?_ houtput h') in text


@pytest.mark.parametrize('operation', ['FW_multiref', 'AllToAllPrim'])
@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['name', 'bounds', 'value', 'tid', 'parent', 'boolean', 'partial'])
def test_independent_raw_metadata_is_checked(operation, field, fault):
    args = prepared()
    cell = next(c for c in args[3]._inputs[1] if c.opname == operation and c.rank == 1
                and c.node.cid in (17, 18))
    irs = copy.deepcopy(getattr(cell, field))
    setattr(cell, field, irs)
    ir = irs[0]
    if fault == 'name': ir.parent.name = 'wrong-source-parent'
    elif fault == 'bounds': ir.indmap = (*ir.indmap[:-1], (1, ir.parent.shape[-1]+1))
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'tid': ir.tid += 100
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'boolean': ir.valmap = (False, 1)
    else: irs.pop()
    with pytest.raises(ValueError):
        api()(*args)


@pytest.mark.parametrize('fault', ['arity', 'times', 'kwargs', 'consts', 'outputs-order', 'inputs-order',
    'slot', 'cross-unit', 'group', 'axes', 'scope-index', 'schedule', 'bound', 'validation'])
def test_mutated_source_authority_rejects(fault):
    from dataclasses import replace
    args = list(prepared())
    sm, pm, _, validation, bound, order = args
    raw = next(c for c in validation._inputs[1] if c.node.cid == 17 and c.rank == 0)
    aa = next(c for c in validation._inputs[1] if c.node.cid == 18 and c.rank == 0)
    if fault == 'arity': raw.inputs.append(raw.inputs[0]); raw._input_irs.append(raw._input_irs[0])
    elif fault == 'times': raw.kwargs['times'] = 1
    elif fault == 'kwargs': raw.kwargs['unexpected'] = 1
    elif fault == 'consts': raw.kwargs['__consts'] = [2]
    elif fault == 'outputs-order': raw.outputs.reverse(); raw._output_irs.reverse()
    elif fault == 'inputs-order': pm._node2inputs[aa.node].reverse()
    elif fault == 'slot': aa.inputs[-1] = aa.inputs[-1]._replace(tid=71)
    elif fault == 'cross-unit': aa.inputs[-1] = aa.inputs[-1]._replace(rank=3)
    elif fault == 'group': pm.collective_scopes[aa.node] = replace(pm.collective_scopes[aa.node], ranks=(2, 3))
    elif fault == 'axes': pm.collective_scopes[aa.node] = replace(pm.collective_scopes[aa.node], params=(1, 2))
    elif fault == 'scope-index': pm.collective_scopes[aa.node] = replace(pm.collective_scopes[aa.node], local_index=1)
    elif fault == 'schedule': order['pm']['execution_to_source'].reverse()
    elif fault == 'bound': bound['relations'][0]['units'][0]['initial_goal']['pm_tids'].reverse()
    else: args[3] = dict(validation)
    with pytest.raises(ValueError):
        api()(*args)


@pytest.mark.parametrize('selected', [True, False])
def test_multiref_full_nonwrite_guard(selected):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    from Verdict.runtime_post_add_values import _next, _read
    from Verdict.runtime_add_values import _ordinary_step
    args = prepared()
    _, pm, _, validation, _, order = args
    index = _Index(pm, validation._inputs[1])
    cell = next(c for c in validation._inputs[1] if c.node.cid == 15 and c.rank == 0)
    alias = _next(index, _ordinary_step(pm, index, cell).outputs[0])
    node = next(n for n in pm.nodes() if tuple(n) == alias.node)
    target = node if selected else pm.nodes()[order['pm']['execution_to_source'][-1]]
    operand = pm.node_inputs(node)[0]
    pm._node2outputs[target] = [operand]
    if selected:
        alias = replace(alias, outputs=(replace(alias.outputs[0], endpoint=alias.inputs[0].endpoint),))
    with pytest.raises(ValueError, match='operand.*written'):
        _read(pm, 'pm', alias, order['pm'])
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('selected', [True, False])
def test_exchange_nonwrites_include_remote_peer_and_selected_step(selected):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    from Verdict.runtime_post_add_values import _next, _exchange
    from Verdict.runtime_add_values import _ordinary_step
    from Verdict.runtime_embedding_route_values import _read
    args = prepared()
    _, pm, _, validation, _, order = args
    index = _Index(pm, validation._inputs[1])
    aliases = [_next(index, _ordinary_step(pm, index, next(c for c in validation._inputs[1]
               if c.node.cid == 15 and c.rank == r)).outputs[0]) for r in (0, 1)]
    _, steps, _ = _exchange(index, aliases, (0, 1))
    step = steps[0]
    node = next(n for n in pm.nodes() if tuple(n) == step.node)
    target = node if selected else pm.nodes()[order['pm']['execution_to_source'][-1]]
    operand = pm.node_inputs(node)[-1]  # remote sender must be protected too
    pm._node2outputs[target] = [operand]
    if selected:
        step = replace(step, outputs=(replace(step.outputs[0], endpoint=step.inputs[-1].endpoint),))
    with pytest.raises(ValueError, match='operand.*written'):
        _read(pm, 'pm', step, order['pm'])
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('fault', ['slot-mix', 'ambiguous-AA', 'cross-unit', 'peer-order'])
def test_exchange_selector_itself_rejects_mismatched_scopes(fault):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    from Verdict.runtime_post_add_values import _next, _exchange
    from Verdict.runtime_add_values import _ordinary_step
    args = prepared()
    _, pm, _, validation, _, _ = args
    index = _Index(pm, validation._inputs[1])
    aliases = [_next(index, _ordinary_step(pm, index, next(c for c in validation._inputs[1]
               if c.node.cid == 15 and c.rank == r)).outputs[0]) for r in (0, 1)]
    node = next(n for n in pm.collective_scopes if n.cid == 18 and n.rank == 1)
    scope = pm.collective_scopes[node]
    if fault == 'slot-mix':
        pm.collective_scopes[node] = replace(scope, input_tids=tuple(a.outputs[1].endpoint.tid for a in aliases))
    elif fault == 'ambiguous-AA':
        other = node._replace(cid=999)
        pm.collective_scopes[other] = replace(scope, node=other)
    elif fault == 'cross-unit': pm.collective_scopes[node] = replace(scope, ranks=(2, 3))
    else: pm.collective_scopes[node] = replace(scope, input_tids=tuple(reversed(scope.input_tids)))
    with pytest.raises(ValueError): _exchange(index, aliases, (0, 1))
    with pytest.raises(ValueError): api()(*args)


def test_exchange_activation_consumes_shared_add_facts():
    text, detail = api()(*prepared())
    assert len(detail['exchange_units']) == 2
    assert 'SourceHiddenSequenceExchange.output_facts' in text
    assert 'addUnitFacts_' in text
    assert detail['alltoall_activation_emitted'] is True
    assert detail['alltoall_activation_reconstruction'] is False
    for unit in detail['exchange_units']:
        assert f'theorem {unit["theorem"]} ' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False


@pytest.mark.parametrize('slot', [0, 1])
def test_strong_exchange_uses_the_coherent_source_selected_slot(slot):
    text, detail = api()(*prepared(exchange_slot=slot))
    for exchange in detail['exchange_units']:
        alias = next(u for u in detail['units'] if u['unit'] == exchange['unit'] and u['slot'] == slot)
        assert exchange['slot'] == slot
        assert exchange['sm_output_tid'] == alias['sm_output_tid']
        assert exchange['input_tids'] == alias['pm_output_tids']
        assert exchange['predecessor_value'] == alias['theorem']
        assert f'({alias["theorem"]} s p t q hs hp h) hy' in text


def test_absent_collective_ir_metadata_is_not_reported_as_complete():
    args = prepared()
    for cell in args[3]._inputs[1]:
        if cell.node.cid == 18:
            del cell._input_irs
            del cell._output_irs
    _, detail = api()(*args)
    assert all(r['input_metadata'] == r['output_metadata'] == 'absent' for r in detail['exchanges'])
