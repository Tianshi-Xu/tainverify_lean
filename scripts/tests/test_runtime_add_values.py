"""Portable original-source add fixtures; emitted Lean is explicitly UNCOMPILED."""
import copy
import importlib
import importlib.util
from dataclasses import replace
from types import SimpleNamespace as NS

import pytest

from Verdict.runtime_initial_relations import bind
from Verdict.runtime_lineage import Role, _Index
from Verdict.runtime_schedule import build
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_runtime_embedding_routes import adapter_fixture, discover


def api():
    assert importlib.util.find_spec('Verdict.runtime_add_values'), 'source add renderer missing'
    return importlib.import_module('Verdict.runtime_add_values').render


def add_fixture(D=2, tp=2, seqlen=2, fault=None):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    sm, pm, authority = adapter_fixture(D, tp, seqlen)
    added = []
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            left = next(c for c in graph.cells if c.rank == rank and c.node.cid == 9)
            right = next(c for c in graph.cells if c.rank == rank and c.node.cid == (13 if world == 's' else 14))
            b = D if world == 's' else 1
            lane = rank % tp
            out = IR(60, 'embedding.add', (b, seqlen, tp*3),
                None if world == 's' else ((0, b), (0, seqlen), (lane*3, (lane+1)*3)))
            inputs = [left.outputs[0], right.outputs[0]]
            irs = [left._output_irs[0], right._output_irs[0]]
            if world == 'p' and rank == 0:
                if fault == 'order': inputs.reverse(); irs.reverse()
                if fault == 'port': inputs[1] = inputs[0]; irs[1] = irs[0]
                if fault == 'cross-unit':
                    other = next(c for c in graph.cells if c.rank == tp and c.node.cid == 14)
                    inputs[1] = other.outputs[0]; irs[1] = other._output_irs[0]
            kw = {'alpha': 2} if fault == 'alpha' else {'alpha': 1, '__consts': []}
            if fault == 'kwargs': kw['unknown'] = 1
            if fault == 'consts': kw['__consts'] = [1]
            cell = NS(node=N(world, rank, 0, 15, 'FW_add'), rank=rank, opname='FW_add',
                inputs=inputs, outputs=[T(world, rank, 0, 60, 1)],
                _input_irs=irs, _output_irs=[out], kwargs=kw)
            cell.ir = NS(signature='FW_add', mirror=NS(cid=115),
                inputs=lambda cell=cell: cell._input_irs, outputs=lambda cell=cell: cell._output_irs)
            graph.cells.append(cell)
            graph.shapes[cell.outputs[0]] = out.shape
            if world == 'p': added.append(cell)
            if fault in ('duplicate', 'later'):
                duplicate = copy.copy(cell)
                duplicate.node = cell.node._replace(cid=16)
                duplicate.outputs = [cell.outputs[0]._replace(tid=61)]
                if fault == 'later':
                    duplicate.inputs = [cell.outputs[0], cell.inputs[0]]
                    duplicate._input_irs = [cell._output_irs[0], cell._input_irs[0]]
                duplicate._output_irs = [IR(61, 'embedding.add.duplicate', out.parent.shape, out.indmap)]
                duplicate.ir = NS(signature='FW_add', mirror=NS(cid=116),
                    inputs=lambda duplicate=duplicate: duplicate._input_irs,
                    outputs=lambda duplicate=duplicate: duplicate._output_irs)
                graph.cells.append(duplicate)
                graph.shapes[duplicate.outputs[0]] = out.shape
                if world == 'p': added.append(duplicate)
    old = authority[2]
    rows = [dict(ref=dict(world='p', runtime_rank=c.rank, microbatch=0, source_cid=c.node.cid,
        call_instance=0, op=c.opname, origin='fixture'), source_irname=c.node.irname,
        inputs=[tref(t) for t in c.inputs], outputs=[tref(t) for t in c.outputs], parameter_grad_tids=[])
        for c in added]
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *copy.deepcopy(rows)]
    for rank in range(D*tp):
        snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace(
            '\ndef _train_step', '\n        added_60 = torch.add(embedding_30, position_emb_52)\ndef _train_step')
    bind_reducers(snapshot)
    bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, fault=None):
    sm, pm, authority = add_fixture(D, tp, seqlen, fault)
    sm, pm, lineages, validation, _ = discover(sm, pm, authority)
    bindings = []
    for world, view, raw in [('sm', sm, authority[0]), ('pm', pm, authority[1])]:
        index = _Index(view, raw)
        for lineage in lineages:
            if lineage.role != Role.PARAMETER: continue
            endpoints = [lineage.target] if world == 'sm' else [p.endpoint for u in lineage.units for p in u.pieces]
            for ep in endpoints:
                meta = index.meta[ep.ref]
                bindings.append(dict(world=world, rank=ep.ref[1], ref=list(ep.ref), tid=ep.tid,
                    sm_ref=list(lineage.target.ref), logical_name=meta[0], parent_tid=ep.ref[3],
                    full_shape=list(meta[1]), bounds=[list(b) for b in meta[2]], value_part=list(meta[3]),
                    shape=list(ep.shape), runtime_name=f'weight_{ep.ref[3]}'))
    parameters = dict(status='current-run-parameter-values-validated', bindings=bindings,
        proof_admissible=False, kernel_value_proved=False, torch_refinement=False)
    bound = bind(sm, pm, parameters, lineages, validation)
    return sm, pm, lineages, validation, bound, {'sm': build(sm), 'pm': build(pm)}


@pytest.mark.parametrize('D,tp,seqlen', [(2, 2, 2), (3, 2, 2), (2, 3, 6)])
def test_source_add_reads_and_units(D, tp, seqlen):
    args = prepared(D, tp, seqlen)
    text, detail = api()(*args)
    assert len(detail['reads']) == 1 + D*tp
    assert len(detail['units']) == D
    assert text.count('SourceAddRead.add_value_of_split') == 1 + D*tp
    assert text.count('TrainVerify.Denote.source_add_unit_output_facts') == D
    for unit in detail['units']:
        assert f'theorem {unit["theorem"]} ' in text
        assert f'({unit["facts_theorem"]} s p t q hs hp h).2.2' in text
    assert detail['lean_bytes'] == len(text.encode())
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for phrase in ('embeddingUnitFacts_', 'embeddingPositionUnitFacts_', 'List.get_mem',
        'List.zipWith elemwiseAdd', 'a.1 b.1', 'a.2.2 b.2.2', '∀ row ∈'):
        assert phrase in text
    # Shapes and parameter projections remain in the shared predecessor facts,
    # not duplicated in each consumer's proof.
    assert 'fw_embedding_shape' not in text
    assert 'initialParameterValues_final s p t q hs hp h' not in text
    for bad in ('sorry', 'admit', 'native_decide', '(hshape :', '(houtput :'):
        assert bad not in text
    for row in detail['reads']:
        assert row['op'] == 'FW_add'
        assert row['input_refs'] == [list(p['endpoint']['ref']) for p in row['source_step']['inputs']]
    for row in detail['units']:
        assert row['ranks'] == list(range(row['unit']*tp, (row['unit']+1)*tp))
        assert row['dimensions'] == dict(D=D, T=tp, B=1, S=seqlen, H=3)
    assert api()(*args) == (text, detail)


@pytest.mark.parametrize('fault', ['order', 'port', 'cross-unit', 'alpha', 'kwargs', 'consts', 'duplicate'])
def test_source_authenticated_wrong_add_rejects(fault):
    args = prepared(fault=fault)
    with pytest.raises(ValueError):
        api()(*args)


@pytest.mark.parametrize('fault', ['group', 'schedule', 'raw-order', 'raw-version', 'raw-bool',
    'bound-status', 'bound-goal', 'bound-duplicate', 'bound-spec', 'bound-parent',
    'bound-shape', 'positions', 'plain-validation'])
def test_live_authority_and_same_bound_rejects(fault):
    sm, pm, lineages, validation, bound, order = prepared()
    if fault == 'group':
        n = next(iter(pm.collective_scopes))
        pm.collective_scopes[n] = replace(pm.collective_scopes[n], ranks=(2, 3))
    elif fault == 'schedule': order['pm']['execution_to_source'].reverse()
    elif fault.startswith('raw-'):
        cell = next(c for c in validation._inputs[1] if c.node.cid == 15)
        if fault == 'raw-order': cell.inputs.reverse()
        elif fault == 'raw-version': cell.inputs[0] = cell.inputs[0]._replace(v=7)
        else: cell.inputs[0] = cell.inputs[0]._replace(rank=False)
    elif fault == 'bound-status': bound['status'] = 'saved-receipt'
    elif fault == 'bound-goal': bound['relations'][0]['units'][0]['initial_goal']['pm_tids'].reverse()
    elif fault == 'bound-duplicate': bound['relations'].append(copy.deepcopy(bound['relations'][0]))
    elif fault == 'bound-spec': bound['relations'][0]['units'][0]['unit'] = 1
    elif fault == 'bound-parent': bound['relations'][0]['units'][0]['bindings'][0]['parent_tid'] += 1
    elif fault == 'bound-shape': bound['relations'][0]['units'][0]['initial_goal']['sm_shape'][1] += 1
    elif fault == 'positions':
        first = lineages[0]
        lineages = (replace(first, units=(replace(first.units[0], positions=(1,)), *first.units[1:])), *lineages[1:])
    else: validation = dict(validation)
    with pytest.raises(ValueError):
        api()(sm, pm, lineages, validation, bound, order)


@pytest.mark.parametrize('world', ['sm', 'pm'])
@pytest.mark.parametrize('fault', ['output-bounds', 'output-value-part', 'input-left', 'input-right'])
def test_pointwise_source_layout_must_match_predecessors(world, fault):
    args = prepared()
    raw = args[3]._inputs[0 if world == 'sm' else 1]
    cell = next(c for c in raw if c.node.cid == 15 and c.rank == 0)
    if fault.startswith('input-'):
        port = 0 if fault == 'input-left' else 1
        cell._input_irs = list(cell._input_irs)
        cell._input_irs[port] = copy.deepcopy(cell._input_irs[port])
        cell._input_irs[port].parent.name = 'mismatched-predecessor'
    else:
        cell._output_irs = copy.deepcopy(cell._output_irs)
        ir = cell._output_irs[0]
        if fault == 'output-value-part':
            ir.valmap = (1, 2)
        else:
            a, b = ir.indmap[-1]
            ir.indmap = (*ir.indmap[:-1], (b, b + b-a))
            if world == 'sm':
                ir.parent.shape = (*ir.parent.shape[:-1], 2 * ir.parent.shape[-1])
    with pytest.raises(ValueError, match='layout|metadata'):
        api()(*args)


def test_add_units_export_reusable_shape_and_value_facts():
    text, detail = api()(*prepared())
    for unit in detail['units']:
        facts = unit['facts_theorem']
        assert f'theorem {facts} ' in text
        assert f'({facts} s p t q hs hp h).2.2' in text
    assert 'source_add_unit_output_facts' in text
    assert '.shape = ' in text


def test_same_bound_flatten_order_is_the_projection_order():
    args = prepared(3, 2)
    bound = args[4]
    bound['relations'].reverse()
    for row in bound['relations']: row['units'].reverse()
    text, detail = api()(*args)
    assert [[p['spec_index'] for p in u['predecessors']] for u in detail['units']] == [[5, 2], [4, 1], [3, 0]]
    for u in detail['units']:
        header = (f'theorem {u["theorem"]} (s p t q : Store)\n'
            '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)\n'
            '    (h : InitialParameterValues s p) :')
        assert header in text
    from Verdict import runtime_embedding_units, runtime_embedding_position_units
    direct, _ = runtime_embedding_units.render(*args[:3], bound)
    position, _ = runtime_embedding_position_units.render(*args[:5])
    assert ':= hrels.2.2.2.2.2\n' in direct
    assert ':= hrels.2.2.1\n' in position
    assert 'embeddingUnitFacts_' in text and 'embeddingPositionUnitFacts_' in text


@pytest.mark.parametrize('selected', [True, False])
def test_complete_operand_nonwrite_guard_includes_selected_and_suffix(selected):
    from Verdict.runtime_add_values import _ordinary_step, _read
    sm, pm, lineages, validation, bound, order = prepared()
    cell = next(c for c in validation._inputs[1] if c.node.cid == 15 and c.rank == 0)
    step = _ordinary_step(pm, _Index(pm, validation._inputs[1]), cell)
    node = next(n for n in pm.nodes() if tuple(n) == step.node)
    target = node if selected else pm.nodes()[order['pm']['execution_to_source'][-1]]
    operand = pm.node_inputs(node)[0]
    pm._node2outputs[target] = [operand]
    if selected:
        # Match the read's supplied step so this test reaches its nonwrite check.
        # Public render separately rejects this forged source/output identity.
        step = replace(step, outputs=(replace(step.outputs[0], endpoint=replace(
            step.outputs[0].endpoint, ref=tuple(pm.source_tensor(operand)), tid=operand.tid)),))
    with pytest.raises(ValueError, match='operand.*written'):
        _read(pm, 'pm', step, order['pm'])
    with pytest.raises(ValueError):
        api()(sm, pm, lineages, validation, bound, order)


def test_unrelated_later_add_is_not_a_closed_predecessor():
    args = prepared(fault='later')
    text, detail = api()(*args)
    assert len(detail['reads']) == 5 and len(detail['units']) == 2
    assert all(r['node'][3] == 15 for r in detail['reads'])
    assert all(r['ref'][3] == 60 for r in detail['reads'])
    assert all(r['node'][3] != 16 for r in detail['reads'])
