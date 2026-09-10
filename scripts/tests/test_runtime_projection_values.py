"""Portable projection extension: never modifies the predecessor fixture."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_layernorm_values as norm
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T


def api():
    assert importlib.util.find_spec('Verdict.runtime_projection_values'), 'projection renderer missing'
    return importlib.import_module('Verdict.runtime_projection_values').render


def projection_fixture(D=2, tp=2, seqlen=2, branches=3):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    sm, pm, authority = norm.layernorm_fixture(D, tp, seqlen)
    added = []
    def append(graph, world, rank, cid, opname, ins, inirs, outirs, kwargs):
        cell = NS(node=N(world, rank, 0, cid, opname), rank=rank, opname=opname,
            inputs=ins, outputs=[T(world, rank, 0, ir.tid, 1) for ir in outirs],
            _input_irs=copy.deepcopy(inirs), _output_irs=outirs, kwargs=kwargs)
        cell.ir = NS(signature=opname, inputs=lambda c=cell: c._input_irs,
                     outputs=lambda c=cell: c._output_irs)
        graph.cells.append(cell)
        graph.shapes.update({r: ir.shape for r, ir in zip(ins, inirs)})
        graph.shapes.update({r: ir.shape for r, ir in zip(cell.outputs, outirs)})
        if world == 'p': added.append(cell)
        return cell
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            producer = next(c for c in graph.cells if c.rank == rank and c.opname == 'FW_layernorm')
            original = producer._output_irs[0]
            alias = append(graph, world, rank, 25, 'FW_multiref', producer.outputs,
                producer._output_irs, [IR(100+j, f'projection.branch{j}', original.parent.shape,
                original.indmap) for j in range(branches)], dict(times=branches))
            for slot in range(branches):
                inp, ir = alias.outputs[slot], alias._output_irs[slot]
                sharded = slot % 2 == 1 or slot == 2
                if world == 'p' and sharded:
                    ranks = list(range(rank//tp*tp, (rank//tp+1)*tp))
                    gathered = IR(200+slot, ir.parent.name, ir.parent.shape)
                    ag = append(graph, world, rank, 30+slot*2, 'AllGatherPrim',
                        [T(world, r, 0, ir.tid, 1) for r in ranks], [ir], [gathered],
                        dict(ranks=ranks, dim=1))
                    # Adapted refs enumerate peers; retained raw IR is LOCAL.
                    graph.shapes.update({r: ir.shape for r in ag.inputs})
                    inp, ir = ag.outputs[0], gathered
                width, hidden = tp*4, tp*3
                wb = ((rank%tp*4, (rank%tp+1)*4), (0, hidden)) if world == 'p' and sharded else None
                weight = IR(300+slot, f'projection.weight{slot}', (width, hidden), wb, True)
                out = IR(400+slot, f'projection.result{slot}',
                    (*ir.parent.shape[:2], width), (*ir.indmap[:2], weight.indmap[0]))
                append(graph, world, rank, 31+slot*2, 'FW_linear',
                    [inp, T(world, rank, -1, weight.tid, 0)], [ir, weight], [out], dict(bias=None))
    old = authority[2]
    rows, adapters = [], []
    for cell in added:
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0,
            source_cid=cell.node.cid, call_instance=0, op=cell.opname, origin='fixture'),
            source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
            outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[])
        adapter = copy.deepcopy(row)
        if cell.opname == 'AllGatherPrim':
            row['adapter_kwargs'] = copy.deepcopy(cell.kwargs)
            adapter['inputs'] = [tref(t) for t in cell.inputs if t.rank == cell.rank]
            slot = cell.outputs[0].tid-200
            adapter['primitive'] = dict(kind=cell.node.irname, forward=True,
                kwargs=copy.deepcopy(cell.kwargs), signature='nnscaler.runtime.adapter.all_gather',
                generated_inputs=[f'projection_{100+slot}'], generated_outputs=[f'projection_{200+slot}'])
        rows.append(row); adapters.append(adapter)
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *adapters]
    for rank in range(D*tp):
        lines = ['        '+', '.join(f'projection_{100+j}' for j in range(branches))
                 + f' = multiref(norm_82, times={branches})']
        for cell in added:
            if cell.rank != rank or cell.opname == 'FW_multiref': continue
            out = cell.outputs[0].tid
            if cell.opname == 'AllGatherPrim':
                lines.append(f'        projection_{out} = nnscaler.runtime.adapter.all_gather(projection_{cell.inputs[0].tid}, dim=1, ranks={cell.kwargs["ranks"]})')
            else:
                lines.append(f'        projection_{out} = torch.nn.functional.linear(projection_{cell.inputs[0].tid}, self.weight_{cell.inputs[1].tid}, bias=None)')
        snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace(
            '\ndef _train_step', '\n'+'\n'.join(lines)+'\ndef _train_step')
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3):
    with patch.object(norm.post.base, 'add_fixture', return_value=projection_fixture(D, tp, seqlen, branches)):
        return norm.post.base.prepared(D, tp, seqlen)


@pytest.mark.parametrize('D,tp,seqlen,branches', [(2, 2, 2, 3), (3, 2, 2, 4), (2, 3, 6, 3), (1, 2, 2, 1)])
def test_original_reads_and_strong_units(D, tp, seqlen, branches):
    args = prepared(D, tp, seqlen, branches)
    text, detail = api()(*args)
    aliases = [r for r in detail['reads'] if r['op'] == 'FW_multiref']
    linears = [r for r in detail['reads'] if r['op'] == 'FW_linear']
    gathers = [r for r in detail['reads'] if r['op'] == 'AllGatherPrim']
    shard_slots = sum(j % 2 == 1 or j == 2 for j in range(branches))
    assert len(aliases) == 1+D*tp
    assert sum(len(r['output_tids']) for r in aliases) == branches*(1+D*tp)
    assert len(linears) == branches*(1+D*tp)
    assert len(gathers) == shard_slots*D*tp
    assert len(detail['units']) == D*branches
    assert text.count('source_linear_sequence_unit_output_reconstruct') == D*(branches-shard_slots)
    assert text.count('source_linear_weight_unit_output_reconstruct') == D*shard_slots
    assert 'layernormUnitFacts_' in text and 'initialParameterValues_final s p t q hs hp h' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for bad in ('sorry', 'admit', 'native_decide', '(hshape :', '(houtput :'):
        assert bad not in text
    assert detail['lean_bytes'] == len(text.encode())
    for row in detail['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
    assert api()(*args) == (text, detail)



def test_T1_is_blocked_by_unmodified_predecessor():
    # Honest inherited limitation; the projection renderer must not bypass it.
    with pytest.raises(ValueError, match='unsupported non-hidden embedding layout'):
        api()(*prepared(1, 1, 2, 1))


@pytest.mark.parametrize('world', [0, 1])
@pytest.mark.parametrize('opname,field,port', [('FW_multiref', '_input_irs', 0),
    ('FW_multiref', '_output_irs', 2), ('FW_linear', '_input_irs', 0),
    ('FW_linear', '_input_irs', 1), ('FW_linear', '_output_irs', 0)])
@pytest.mark.parametrize('fault', ['bounds', 'value', 'tid', 'parent', 'bool', 'missing'])
def test_all_ordinary_original_ports(world, opname, field, port, fault):
    args = prepared()
    cell = next(c for c in args[3]._inputs[world] if c.opname == opname and c.node.cid >= 25 and c.rank == 0)
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
    ir = irs[port]
    if fault == 'bounds': ir.indmap = (*ir.indmap[:-1], (1, ir.parent.shape[-1]+1))
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'tid': ir.tid += 10
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'bool': ir.valmap = (False, 1)
    else: irs.pop()
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['value', 'bounds', 'tid', 'name', 'empty', 'wrong-local'])
def test_allgather_available_original_IR(field, fault):
    args = prepared()
    cell = next(c for c in args[3]._inputs[1] if c.opname == 'AllGatherPrim' and c.rank == 1)
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs)
    if fault == 'value': irs[0].valmap = (1, 2)
    elif fault == 'bounds': irs[0].indmap = ((0, 1), (0, 1), (0, 6))
    elif fault == 'tid': irs[0].tid += 10
    elif fault == 'name': irs[0].parent.name = 'wrong'
    elif fault == 'empty': irs.clear()
    else:
        other = next(c for c in args[3]._inputs[1] if c.opname == 'AllGatherPrim' and c.rank == 0)
        irs[0] = copy.deepcopy(getattr(other, field)[0])
        if field == '_output_irs': irs[0].valmap = (1, 2)
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('fault', ['spec-order', 'unit-order', 'role', 'slot', 'fullref', 'weight-order',
    'kwargs', 'missing', 'ambiguous', 'schedule', 'group', 'local-index', 'axis', 'source-writer', 'peers'])
def test_inventory_order_and_source_faults(fault):
    from dataclasses import replace
    args = list(prepared())
    sm, pm, lineages, validation, bound, order = args
    cell = next(c for c in validation._inputs[1] if c.opname == 'FW_linear' and c.rank == 0)
    if fault == 'spec-order': bound['relations'].reverse()
    elif fault == 'unit-order': bound['relations'][-1]['units'].reverse()
    elif fault == 'role': args[2] = (*lineages[:-1], replace(lineages[-1], role='batch-activation'))
    elif fault == 'slot': cell.inputs[0] = cell.inputs[0]._replace(tid=101)
    elif fault == 'fullref': cell.inputs[1] = cell.inputs[1]._replace(rank=2)
    elif fault == 'weight-order': bound['relations'][-1]['units'][0]['bindings'].reverse()
    elif fault == 'kwargs': cell.kwargs['unknown'] = 1
    elif fault == 'missing': validation._inputs[1].remove(cell)
    elif fault == 'ambiguous': validation._inputs[1].append(copy.copy(cell))
    elif fault == 'schedule': order['pm']['execution_to_source'].reverse()
    else:
        node = next(n for n, s in pm.collective_scopes.items() if s.op == 'AllGatherPrim')
        scope = pm.collective_scopes[node]
        changes = {'group': dict(ranks=(2, 3)), 'local-index': dict(local_index=1),
            'axis': dict(params=(2,)), 'source-writer': dict(source_writer='wrong'),
            'peers': dict(input_tids=tuple(reversed(scope.input_tids)))}
        pm.collective_scopes[node] = replace(scope, **changes[fault])
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('fault', ['ref', 'sm_ref', 'tid', 'rank', 'world', 'logical_name',
    'parent_tid', 'full_shape', 'bounds', 'value_part', 'shape', 'missing', 'goal', 'unit'])
@pytest.mark.parametrize('slot', [0, 1, 2])
def test_every_weight_bound_field(slot, fault):
    args = prepared()
    row = next(r for r in args[4]['relations'] if r['sm_binding']['logical_name'] == f'projection.weight{slot}')
    bu = row['units'][0]; binding = bu['bindings'][0]
    if fault in ('ref', 'sm_ref'): binding[fault][3] += 1
    elif fault in ('tid', 'rank', 'parent_tid'): binding[fault] += 1
    elif fault in ('world', 'logical_name'): binding[fault] = 'wrong'
    elif fault in ('full_shape', 'shape'): binding[fault][0] += 1
    elif fault == 'bounds': binding[fault][0][0] += 1
    elif fault == 'value_part': binding[fault] = [1, 2]
    elif fault == 'missing': bu['bindings'].pop()
    elif fault == 'goal': bu['initial_goal']['pm_tids'].reverse()
    else: bu['unit'] = 1
    with pytest.raises(ValueError): api()(*args)


@pytest.mark.parametrize('opname,operand', [('FW_linear', 0), ('FW_linear', 1),
    ('AllGatherPrim', 0), ('AllGatherPrim', 1), ('FW_multiref', 0)])
@pytest.mark.parametrize('selected', [True, False])
def test_selected_and_full_suffix_operand_nonwrites(opname, operand, selected):
    from dataclasses import replace
    from Verdict import runtime_projection_values as renderer
    from Verdict.runtime_lineage import _Index
    args = prepared()
    sm, pm, _, validation, _, order = args
    si, pi = _Index(sm, validation._inputs[0]), _Index(pm, validation._inputs[1])
    _, prior = norm.api()(*args)
    aliases = [renderer._alias(pi, d) for d in prior['units'][0]['local_steps']]
    if opname == 'FW_multiref': step = aliases[0]
    elif opname == 'FW_linear': step = renderer._linear(pi, aliases[0].outputs[0])
    else:
        ports = tuple(a.outputs[1] for a in aliases)
        cell = renderer._consumer(pi, ports[0], ('AllGatherPrim',))
        step, _ = renderer._gather(pi, cell, ports, (0, 1), 0)
    node = next(n for n in pm.nodes() if tuple(n) == step.node)
    target = node if selected else pm.nodes()[order['pm']['execution_to_source'][-1]]
    value = pm.node_inputs(node)[operand]
    pm._node2outputs[target] = [value]
    if selected: step = replace(step, outputs=(replace(step.outputs[0], endpoint=step.inputs[operand].endpoint),))
    with pytest.raises(ValueError, match='operand.*written'):
        renderer._read(pm, 'pm', step, order['pm'])


def test_fresh_predecessor_and_coverage_states():
    from Verdict import runtime_layernorm_values as renderer
    args = prepared()
    with patch.object(renderer, 'render', wraps=renderer.render) as fresh:
        _, detail = api()(*args)
        assert fresh.call_count == 1
    assert {r['input_metadata'] for r in detail['exchanges']} == {'local-only'}
    for cell in args[3]._inputs[1]:
        if cell.opname != 'AllGatherPrim': continue
        # Peer source ports, not _Index.meta, remain authority for absent IR.
        del cell._input_irs; del cell._output_irs
    _, detail = api()(*args)
    assert {r['input_metadata'] for r in detail['exchanges']} == {'absent'}


def test_all_peer_metadata_and_no_extra_public_alias_wrappers():
    args = prepared()
    raw = args[3]._inputs[1]
    for cell in raw:
        if cell.opname != 'AllGatherPrim': continue
        cell._input_irs = [copy.deepcopy(next(c for c in raw if c.node.cid == 25 and c.rank == ref.rank)
            ._output_irs[ref.tid-100]) for ref in cell.inputs]
    text, detail = api()(*args)
    assert {r['input_metadata'] for r in detail['exchanges']} == {'all-peers'}
    assert len(detail['units']) == 6
    assert len(detail['reads']) == 28
    assert text.count('theorem ') == len(detail['reads'])+len(detail['units'])
    assert 'projectionAliasUnit' not in text


def test_live_canonical_weight_identity_guard_is_not_predecessor_theatre():
    from Verdict import runtime_projection_values as renderer
    from Verdict import runtime_layernorm_values as predecessor
    args = prepared()
    for row in args[4]['relations']:
        if not row['sm_binding']['logical_name'].startswith('projection.weight'): continue
        row['sm_binding']['parent_tid'] += 1000
        for unit in row['units']:
            for binding in unit['bindings']: binding['parent_tid'] += 1000
    _, prior = predecessor.render(*args)
    assert len(prior['units']) == 2
    with pytest.raises(ValueError, match='original parameter binding mismatch'):
        renderer.render(*args)


def test_T1_weight_gather_does_not_emit_invalid_replicated_relation_fields():
    # The full API currently fails earlier in the unchanged embedding dependency.
    # This direct emitter guard prevents invalid Lean if that dependency expands.
    from Verdict import runtime_projection_values as renderer
    from Verdict import runtime_layernorm_values as predecessor
    from Verdict.runtime_lineage import _Index
    args = prepared()
    _, prior = predecessor.render(*args)
    unit = copy.deepcopy(prior['units'][0]); unit['dimensions']['T'] = 1
    pi = _Index(args[1], args[3]._inputs[1]); si = _Index(args[0], args[3]._inputs[0])
    ga = renderer._alias(si, unit['source_step'])
    aliases = [renderer._alias(pi, unit['local_steps'][0])]
    global_ = renderer._linear(si, ga.outputs[0])
    local = renderer._linear(pi, aliases[0].outputs[0])
    parameter = dict(kind='replicated', pm_shape=[8, 6], sm_shape=[8, 6], spec_index=0,
        sm_tid=global_.inputs[1].endpoint.tid, pm_tids=[local.inputs[1].endpoint.tid])
    names = {ga.node: 'globalAliasRead', aliases[0].node: 'localAliasRead',
        global_.node: 'globalLinearRead', local.node: 'localLinearRead'}
    with pytest.raises(ValueError, match='single-rank gathered'):
        renderer._unit(unit, 0, ga, aliases, global_, [local], [local], parameter, names, 1)
