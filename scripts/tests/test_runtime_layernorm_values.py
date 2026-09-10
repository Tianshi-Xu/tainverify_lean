"""Portable LayerNorm extension of post_fixture; no Lean or capture dependency."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_post_add_values as post
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T


def api():
    assert importlib.util.find_spec('Verdict.runtime_layernorm_values'), 'layernorm renderer missing'
    return importlib.import_module('Verdict.runtime_layernorm_values').render


def layernorm_fixture(D=2, tp=2, seqlen=2, fault=None, slot=0, swap=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    sm, pm, authority = post.post_fixture(D, tp, seqlen, exchange_slot=slot)
    added = []
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            producer = next(c for c in graph.cells if c.rank == rank and c.node.cid == (17 if world == 's' else 18))
            pos = slot if world == 's' else 0
            activation = producer._output_irs[pos]
            params = [IR(80, 'norm.gamma', (tp*3,), param=True), IR(81, 'norm.beta', (tp*3,), param=True)]
            if swap: params.reverse()
            if fault == 'tied': params[1] = params[0]
            ins = [producer.outputs[pos], *(T(world, rank, -1, p.tid, 0) for p in params)]
            out = IR(82, 'norm.output', activation.parent.shape, activation.indmap)
            kw = dict(normalized_shape=[tp*3], eps=1e-5)
            if fault == 'eps': kw['eps'] = 1e-4
            elif fault == 'norm': kw['normalized_shape'] = [tp*3, tp*3]
            elif fault == 'bool': kw['normalized_shape'] = [True]
            elif fault == 'kwargs': kw['unknown'] = 1
            elif fault == 'consts': kw['__consts'] = [1]
            if fault == 'role-mix' and world == 'p' and rank == 1:
                ins[1], ins[2] = ins[2], ins[1]; params.reverse()
            if fault == 'slot' and world == 's':
                ins[0] = producer.outputs[1-slot]
                activation = producer._output_irs[1-slot]
            cell = NS(node=N(world, rank, 0, 20, 'FW_layernorm'), rank=rank, opname='FW_layernorm',
                inputs=ins, outputs=[T(world, rank, 0, 82, 1)],
                _input_irs=[copy.deepcopy(activation), *params], _output_irs=[out], kwargs=kw)
            cell.ir = NS(signature='FW_layernorm', inputs=lambda c=cell: c._input_irs,
                outputs=lambda c=cell: c._output_irs)
            graph.cells.append(cell)
            graph.shapes.update({r: ir.shape for r, ir in zip(cell.inputs + cell.outputs, cell._input_irs + cell._output_irs)})
            if world == 'p': added.append(cell)
    old = authority[2]
    rows = [dict(ref=dict(world='p', runtime_rank=c.rank, microbatch=0, source_cid=c.node.cid,
        call_instance=0, op=c.opname, origin='fixture'), source_irname=c.node.irname,
        inputs=[tref(t) for t in c.inputs], outputs=[tref(t) for t in c.outputs], parameter_grad_tids=[])
        for c in added]
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *copy.deepcopy(rows)]
    for rank in range(D*tp):
        cell = next(c for c in added if c.rank == rank)
        names = {80: 'gamma_80', 81: 'beta_81'}
        gamma, beta = cell.inputs[1:]
        snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace(
            '\ndef _train_step', '\n        norm_82 = torch.nn.functional.layer_norm(postadd_72, normalized_shape=['
            + str(tp*3) + f'], weight=self.{names[gamma.tid]}, bias=self.{names[beta.tid]}, eps=1e-5)\ndef _train_step')
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, **kw):
    fixture = layernorm_fixture(D, tp, seqlen, **kw)
    with patch.object(post.base, 'add_fixture', return_value=fixture):
        return post.base.prepared(D, tp, seqlen)


@pytest.mark.parametrize('D,tp,seqlen', [(2, 2, 2), (3, 2, 2), (2, 3, 6)])
def test_reads_and_strong_units(D, tp, seqlen):
    args = prepared(D, tp, seqlen)
    text, detail = api()(*args)
    assert len(detail['reads']) == 1 + D*tp
    assert len(detail['units']) == D
    assert text.count('SourceLayernormRead.layernorm_value_of_split') == 1 + D*tp
    assert text.count('TrainVerify.Denote.source_layernorm_unit_output_reconstruct') == D
    assert 'postAddExchangeFacts_' in text
    assert 'initialParameterValues_final s p t q hs hp h' in text
    assert 'RelationCompiler.ReplicatedRel' in text and 'replica_values' in text
    assert 'List.Forall₂.cons' in text
    assert detail['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for bad in ('sorry', 'admit', 'native_decide', '(hshape :', '(houtput :'):
        assert bad not in text
    for row in detail['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
    assert api()(*args) == (text, detail)


@pytest.mark.parametrize('fault', ['eps', 'norm', 'bool', 'kwargs', 'consts', 'role-mix', 'slot'])
def test_coherent_invalid_source_rejects(fault):
    args = prepared(fault=fault)
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('slot', [0, 1])
@pytest.mark.parametrize('swap', [False, True])
def test_coherent_source_slots_and_parameter_role_binding(slot, swap):
    text, detail = api()(*prepared(slot=slot, swap=swap))
    for unit in detail['units']:
        gamma, beta = unit['parameters']
        assert gamma['role'] == 'gamma' and beta['role'] == 'beta'
        assert gamma['sm_ref'][3] == (81 if swap else 80)
        assert beta['sm_ref'][3] == (80 if swap else 81)
        assert gamma['spec_index'] != beta['spec_index']
        assert unit['source_step']['inputs'][0]['endpoint']['ref'][3] == 70+slot
    assert 'gammaRel.replica_values' in text and 'betaRel.replica_values' in text


@pytest.mark.parametrize('world', [0, 1])
@pytest.mark.parametrize('port', [0, 1, 2, 3])
@pytest.mark.parametrize('fault', ['bounds', 'value', 'tid', 'parent', 'bool', 'missing'])
def test_raw_full_metadata(world, port, fault):
    args = prepared()
    cell = next(c for c in args[3]._inputs[world] if c.node.cid == 20 and c.rank == 0)
    field = '_input_irs' if port < 3 else '_output_irs'
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
    ir = irs[port if port < 3 else 0]
    if fault == 'bounds': ir.indmap = (*ir.indmap[:-1], (1, ir.parent.shape[-1]+1))
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'tid': ir.tid += 100
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'bool': ir.valmap = (False, 1)
    else: irs.pop()
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('role', ['gamma', 'beta'])
@pytest.mark.parametrize('fault', ['ref', 'sm_ref', 'tid', 'rank', 'world', 'logical_name',
    'parent_tid', 'full_shape', 'bounds', 'value_part', 'shape', 'missing', 'order', 'goal', 'unit'])
def test_each_parameter_bound_role_is_checked(role, fault):
    args = prepared()
    row = next(r for r in args[4]['relations'] if r['sm_binding']['logical_name'] == 'norm.'+role)
    bu = row['units'][0]
    binding = bu['bindings'][0]
    if fault in ('ref', 'sm_ref'): binding[fault][3] += 1
    elif fault in ('tid', 'rank', 'parent_tid'): binding[fault] += 1
    elif fault in ('world', 'logical_name'): binding[fault] = 'wrong'
    elif fault in ('full_shape', 'shape'): binding[fault][0] += 1
    elif fault == 'bounds': binding[fault][0][0] = 1
    elif fault == 'value_part': binding[fault] = [1, 2]
    elif fault == 'missing': bu['bindings'].pop()
    elif fault == 'order': bu['bindings'].reverse()
    elif fault == 'goal': bu['initial_goal']['pm_tids'].reverse()
    else: bu['unit'] = 1
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('fault', ['spec-order', 'unit-order', 'parameter-role', 'raw-ref',
    'raw-port-order', 'source-kwargs', 'rank', 'scope-order', 'positions', 'schedule', 'missing', 'ambiguous'])
def test_source_inventory_and_order_mutations(fault):
    from dataclasses import replace
    args = list(prepared())
    sm, pm, lineages, validation, bound, order = args
    cell = next(c for c in validation._inputs[1] if c.node.cid == 20 and c.rank == 0)
    if fault == 'spec-order': bound['relations'].reverse()
    elif fault == 'unit-order': bound['relations'][-1]['units'].reverse()
    elif fault == 'parameter-role': args[2] = (*lineages[:-1], replace(lineages[-1], role='batch-activation'))
    elif fault == 'raw-ref': cell.inputs[1] = cell.inputs[1]._replace(rank=2)
    elif fault == 'raw-port-order': cell.inputs[1:] = reversed(cell.inputs[1:]); cell._input_irs[1:] = reversed(cell._input_irs[1:])
    elif fault == 'source-kwargs': cell.kwargs['eps'] = 1e-3
    elif fault == 'rank': cell.rank = 1
    elif fault == 'scope-order':
        node = next(n for n in pm.collective_scopes if n.cid == 18)
        pm.collective_scopes[node] = replace(pm.collective_scopes[node], ranks=(1, 0))
    elif fault == 'positions': validation._inputs[3]['config']['units'][0]['positions'] = [1]
    elif fault == 'schedule': order['pm']['execution_to_source'].reverse()
    elif fault == 'missing': validation._inputs[1].remove(cell)
    else: validation._inputs[1].append(copy.copy(cell))
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('operand', [0, 1, 2])
@pytest.mark.parametrize('selected', [True, False])
def test_all_operands_selected_and_suffix_nonwrite(operand, selected):
    from dataclasses import replace
    from Verdict.runtime_layernorm_values import _next, _read
    from Verdict.runtime_lineage import _Index
    from Verdict.runtime_post_add_values import _port
    args = prepared()
    _, pm, _, validation, _, order = args
    index = _Index(pm, validation._inputs[1])
    cell = next(c for c in validation._inputs[1] if c.node.cid == 20 and c.rank == 0)
    step = _next(index, _port(index, cell.inputs[0], cell._input_irs[0]))
    node = next(n for n in pm.nodes() if tuple(n) == step.node)
    target = node if selected else pm.nodes()[order['pm']['execution_to_source'][-1]]
    value = pm.node_inputs(node)[operand]
    pm._node2outputs[target] = [value]
    if selected: step = replace(step, outputs=(replace(step.outputs[0], endpoint=step.inputs[operand].endpoint),))
    with pytest.raises(ValueError, match='operand.*written'): _read(pm, 'pm', step, order['pm'])
    with pytest.raises(ValueError): api()(*args)


def test_coherent_shared_parameter_can_fill_both_roles():
    text, detail = api()(*prepared(fault='tied'))
    for unit in detail['units']:
        gamma, beta = unit['parameters']
        assert gamma['sm_ref'] == beta['sm_ref']
        assert gamma['spec_index'] == beta['spec_index']
        assert gamma['pm_refs'] == beta['pm_refs']
    assert 'congrArg₂ (fun g b => fw_layernorm' in text


def test_source_read_law_argument_order_and_scope():
    text, detail = api()(*prepared())
    for row in detail['reads']:
        x, gamma, beta = row['input_tids']
        assert f"{row['node'][1]} {x} {gamma} {beta} {row['output_tid']} s t rfl ?_ rfl ?_ ?_ ?_ h" in text
        assert row['request'] == 'global' and row['params'] == []


@pytest.mark.parametrize('mode', ['default', 'swapped', 'tied'])
def test_parameter_role_positive_fixtures_bind_generated_call_operands(mode):
    _, _, authority = layernorm_fixture(swap=mode == 'swapped', fault='tied' if mode == 'tied' else None)
    names = {80: 'gamma_80', 81: 'beta_81'}
    for cell in authority[1]:
        if cell.node.cid != 20:
            continue
        code = authority[2]['rank_sources'][str(cell.rank)]
        gamma, beta = cell.inputs[1:]
        assert f'weight=self.{names[gamma.tid]}, bias=self.{names[beta.tid]}' in code


@pytest.mark.parametrize('fault', ['parent-identity', 'role-payloads'])
def test_coordinated_bindings_reach_new_parameter_authority_guard(fault):
    from Verdict import runtime_layernorm_values as layernorm
    from Verdict import runtime_post_add_values as predecessor
    args = prepared()
    rows = {r['sm_binding']['logical_name']: r for r in args[4]['relations']}
    gamma, beta = rows['norm.gamma'], rows['norm.beta']
    if fault == 'parent-identity':
        for row in (gamma, beta):
            row['sm_binding']['parent_tid'] += 100
            for unit in row['units']:
                for binding in unit['bindings']:
                    binding['parent_tid'] += 100
    else:
        gamma['sm_binding'], beta['sm_binding'] = beta['sm_binding'], gamma['sm_binding']
        for gu, bu in zip(gamma['units'], beta['units'], strict=True):
            gu['bindings'], bu['bindings'] = bu['bindings'], gu['bindings']
    _, prior = predecessor.render(*args)
    assert len(prior['exchange_units']) == 2
    with pytest.raises(ValueError, match='layernorm original parameter binding mismatch'):
        layernorm.render(*args)
    with patch.object(layernorm, '_binding', lambda *args: None):
        _, mutant = layernorm.render(*args)
        assert len(mutant['units']) == 2


def test_fresh_post_renderer_is_called_and_annotations_are_not_claimed():
    from Verdict import runtime_post_add_values
    args = prepared()
    with patch.object(runtime_post_add_values, 'render', wraps=runtime_post_add_values.render) as fresh:
        expected = api()(*args)
        assert fresh.call_count == 1
    for row in args[4]['relations'][-2:]:
        row['sm_binding']['runtime_name'] = 'not-a-consumed-field'
        row['sm_binding']['extra'] = 'not-authority'
        for unit in row['units']:
            for binding in unit['bindings']:
                binding['runtime_name'] = 'not-a-consumed-field'
                binding['extra'] = 'not-authority'
    assert api()(*args) == expected
