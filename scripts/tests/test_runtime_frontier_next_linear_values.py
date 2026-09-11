"""Fresh GELU -> next direct linear: portable source tests, local B=1 only.

No capture/kernel evidence. Private shared-consumer probes below are explicitly
narrow guard tests, never substitutes for the public fresh-source tracer.
"""
import copy
import importlib
import importlib.util
import re
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_gelu_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_gelu_values as predecessor
from Verdict import runtime_frontier_linear_values as consumer


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_next_linear_values'), 'next linear renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_next_linear_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, I=11, O=7,
            weight_tid=81001, first_weight_tid=51001, output_tid=81003,
            gelu_tid=71003, skip_kind=None, copies=1, omit_rank=None):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D=D, tp=tp, seqlen=seqlen, reverse=reverse,
        O=I, weight_tid=first_weight_tid, gelu_tid=gelu_tid, skip_kind=skip_kind)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        for producer in [c for c in graph.cells if c.opname == 'FW_gelu']:
            if world == 'p' and producer.rank == omit_rank:
                continue
            for j in range(copies):
                x = producer._output_irs[0]; rank = producer.rank
                w = IR(weight_tid, 'independent.copied.matrix', (O, x.shape[-1]), param=True)
                y = IR(output_tid+j*10, 'next.direct.output', (*x.parent.shape[:2], O), (*x.indmap[:2], (0, O)))
                cell = NS(node=N(world, rank, 0, 81000+j*10, 'FW_linear'), rank=rank, opname='FW_linear',
                    inputs=[producer.outputs[0], T(world, rank, -1, w.tid, 0)],
                    outputs=[T(world, rank, 0, y.tid, 1)], kwargs=dict(bias=None, __consts=[]),
                    _input_irs=[copy.deepcopy(x), w], _output_irs=[y])
                cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
                at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')), len(graph.cells))
                graph.cells.insert(at, cell)
                graph.shapes.update({r: ir.shape for r,ir in zip(cell.inputs+cell.outputs, cell._input_irs+cell._output_irs, strict=True)})
                if world == 'p':
                    rows.append(dict(ref=dict(world=world, runtime_rank=rank, microbatch=0, source_cid=cell.node.cid,
                        call_instance=0, op=cell.opname, origin='fixture'), source_irname=cell.opname,
                        inputs=[tref(r) for r in cell.inputs], outputs=[tref(r) for r in cell.outputs], parameter_grad_tids=[]))
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                        f'\n        projected = torch.nn.functional.linear(activated, self.param_{weight_tid}, bias=None)\ndef _train_step')
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    adapters = {writer_export_id(w['ref']): w for w in [*old['adapter_source'], *copy.deepcopy(rows)]}
    snapshot['adapter_source'] = [adapters[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    # Reuse the complete predecessor's validation and canonical parameter inventory.
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D=kwargs.get('D', 2), tp=kwargs.get('tp', 2), seqlen=kwargs.get('seqlen', 2))


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def test_public_fresh_gelu_to_next_linear_tracer(baseline):
    args, _ = copy.deepcopy(baseline)
    renderer = api(); receipts = []
    real_fresh = predecessor.render
    def fresh(*six):
        answer = real_fresh(*six)
        receipts.append(answer[1])
        return answer
    with patch.object(predecessor, 'render', side_effect=fresh) as refresh, \
            patch.object(consumer, 'render', wraps=consumer.render) as earlier, \
            patch.object(consumer, '_render', wraps=consumer._render) as shared:
        text, result = renderer.render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args, args, strict=True))
    # The old public linear runs ONLY inside fresh GELU (to derive its FC1 input).
    assert earlier.call_count == 1 and shared.call_count == 2
    assert all(a is b for a,b in zip(shared.call_args.args[:6], args, strict=True))
    assert shared.call_args.args[6] is receipts[0]
    closed = receipts[0]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [5,2,4,2,0]
    assert result['consumed_frontier_indices'] == [0,2]
    assert result['retained_units'] == closed['retained_units']
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    assert text.count('SourceLinearRead.linear_value_of_split') == 5
    assert text.count('source_linear_sequence_unit_output_reconstruct') == 2
    assert 'initialParameterValues_final s p t q hs hp hvalues' in text
    assert 'frontierGeluUnitFacts_' in text
    for row in result['units']:
        assert row['dimensions'] == dict(D=2,T=2,B=1,S=1,H=7)
        assert row['input_shape'] == [2,2,11] and row['input_width'] == 11
        assert row['global_shape'] == [2,2,7] and row['local_shape'] == [1,1,7]
        assert row['parameters'][0]['sm_shape'] == [7,11]
        assert row['parameters'][0]['sm_ref'][3] == 81001
        assert row['source_step']['op'] == 'FW_linear' and row['source_output_slot'] == 0
        assert row['facts_theorem'] == row['theorem']
        assert row['predecessor'] == row['predecessor_facts'] == closed['frontier_units'][row['frontier_index']]['facts_theorem']
        fragment = text.split('theorem '+row['facts_theorem']+' ',1)[1].split('#print axioms')[0]
        assert '.shape = [2, 2, 7] ∧' in fragment and '∀ y ∈' in fragment
        assert '.shape = [1, 1, 7]' in fragment
        assert 'chunkPrimDimN 0 2' in fragment and 'allGatherPrimDimN 1 2 0' in fragment
    old_text, _ = consumer.render(*args)
    declarations = lambda src: set(re.findall(r'^theorem (\w+)', src, re.M))
    assert declarations(text) and declarations(text).isdisjoint(declarations(old_text))
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'):
        assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :','globalAlias','alias_'):
        assert bad not in text


def test_public_normalizes_final_consumer_structural_exception(baseline):
    # Deliberate seam fault injection AFTER the real fresh GELU run, not a fake receipt.
    args, _ = copy.deepcopy(baseline)
    real = consumer._render
    def malformed(*values):
        if values[-1]['frontier_units'][0].get('family') == 'FW_gelu':
            raise AttributeError('malformed next matrix parent')
        return real(*values)
    with patch.object(consumer, '_render', side_effect=malformed):
        with pytest.raises(ValueError, match='malformed frontier-next-linear original source') as error:
            api().render(*args)
    assert isinstance(error.value.__cause__, AttributeError)


def test_public_no_next_linear_defers_gelu_not_old_layernorm():
    args = previous.prepared()
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert result['frontier_units'] == closed['frontier_units']
    assert len(result['deferred_units']) == len(result['retained_units']) == 2
    assert not result['reads'] and not result['units']
    assert all(r['family'] == 'FW_gelu' for r in result['deferred_units'])


@pytest.mark.parametrize('fault', ['ref','parent_tid','rank','bounds','value_part','full_shape','sm_ref','order','goal'])
def test_shared_complete_new_weight_binding(baseline, fault):
    args, closed = copy.deepcopy(baseline); cell, _ = selected(args)
    row = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == cell._input_irs[1].tid)
    unit = row['units'][0]; binding = unit['bindings'][0]
    if fault in ('ref','sm_ref'): binding[fault][3] += 1
    elif fault in ('rank','parent_tid'): binding[fault] += 1
    elif fault == 'bounds': binding[fault][0][0] = 1
    elif fault == 'value_part': binding[fault] = [1,2]
    elif fault == 'full_shape': binding[fault][0] += 1
    elif fault == 'order': unit['bindings'].reverse()
    else: unit['initial_goal']['kind'] = 'sharded'
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('fault', ['float-shape','float-bounds','bool-value','missing','param','grad'])
def test_shared_every_new_weight_occurrence(baseline, fault):
    # Private raw-inventory fault probe only: no invented receipt or public graph claim.
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline); cell, _ = selected(args)
    other = copy.deepcopy(cell)
    other.node = other.node._replace(cid=99000,irname='BW_probe'); other.opname = 'BW_probe'
    other.inputs = [cell.inputs[1]]; ir = copy.deepcopy(cell._input_irs[1]); other._input_irs = [ir]
    other.outputs = []; other._output_irs = []
    args[3]._inputs[1].append(other)
    if fault == 'float-shape': ir.shape = (float(ir.shape[0]),ir.shape[1])
    elif fault == 'float-bounds': ir.indmap = ((0.0,ir.shape[0]),ir.indmap[1])
    elif fault == 'bool-value': ir.valmap = (False,1)
    elif fault == 'missing': other._input_irs = []
    elif fault == 'param': ir.param = 1
    else: ir.is_grad = lambda: True
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'malformed occurrence reached lossy Port'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)


def private(args, closed):
    """Explicit shared-consumer guard probe on a REAL fresh baseline receipt."""
    return consumer._render(*args, closed)


def selected(args, world=1):
    cell = next(c for c in args[3]._inputs[world] if c.node.cid == 81000 and c.rank == 0)
    node = next(n for n in args[world].nodes() if tuple(n) == tuple(cell.node))
    return cell, node


@pytest.mark.parametrize('D,tp,S,reverse,I,O,weight,first_weight,gelu,out', [
    (1,3,6,False,13,5,91001,61001,91003,92003),
    (3,2,8,True,17,1,101001,62001,101003,102003)])
def test_public_new_dimensions_identities_and_upstream_output_reorder(D,tp,S,reverse,I,O,weight,first_weight,gelu,out):
    args = prepared(D=D,tp=tp,seqlen=S,reverse=reverse,I=I,O=O,
        weight_tid=weight,first_weight_tid=first_weight,gelu_tid=gelu,output_tid=out)
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert len(result['reads']) == 1+D*tp and len(result['units']) == D
    assert result['consumed_frontier_indices'] == list(range(1 if reverse else 0,2*D,2))
    for i, old in enumerate(closed['frontier_units']):
        if i not in result['consumed_frontier_indices']:
            assert result['frontier_units'][i] == old
    for row in result['units']:
        assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S//tp,H=O)
        assert row['global_shape'] == [D,S,O] and row['local_shape'] == [1,S//tp,O]
        assert row['input_width'] == I and row['input_shape'] == [D,S,I]
        assert row['parameters'][0]['sm_ref'][3] == weight
        assert row['parameters'][0]['sm_shape'] == [O,I]
        assert row['sm_output_ref'][3] == out
        assert row['source_step']['inputs'][0]['endpoint']['ref'][3] == gelu
        assert row['predecessor'] == row['predecessor_facts']
        assert row['predecessor_facts'].startswith('frontierGeluUnitFacts_')
    assert result['retained_units'] == closed['retained_units'] and not result['deferred_units']


def test_public_ordered_add_skips_retained():
    args = prepared(skip_kind='FW_add', reverse=True)
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert result['frontier_units'][::2] == closed['frontier_units'][::2]
    assert result['retained_units'] == closed['retained_units']
    assert len(result['retained_units']) == 2 and not result['deferred_units']


@pytest.mark.parametrize('options', [dict(copies=2),dict(omit_rank=0)])
def test_public_partial_or_fanout_fails_closed(options):
    # Missing the only rank-weight occurrence may fail in canonical inventory first.
    with pytest.raises(ValueError, match='fan-out|partial|incomplete initial parameter rank inventory'):
        api().render(*prepared(**options))


@pytest.mark.parametrize('fault', ['bias','matrix-bool'])
def test_public_rejects_next_consumer_mutation_and_caller_receipt(baseline, fault):
    args, _ = copy.deepcopy(baseline); cell, node = selected(args)
    if fault == 'bias':
        cell.kwargs['bias'] = False
        args[1].source.cell(node).kwargs = dict(cell.kwargs)
    else:
        cell._input_irs[1].shape = (True, cell._input_irs[1].shape[1])
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(TypeError): api().render(*args, {'frontier_units': []})


@pytest.mark.parametrize('fault', ['raw-op','raw-ref','rank','node','writer-export','writer-call',
    'writer-ref','missing-writer','output-writer','bias','extra','consts','scope'])
def test_shared_original_source_writer_and_kwargs(baseline, fault):
    args, closed = copy.deepcopy(baseline); cell, node = selected(args); view = args[1]
    writer = next(w for w in view._collective_source['writers']
        if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == 0)
    if fault == 'raw-op': cell.opname = 'FW_mul'
    elif fault == 'raw-ref': cell.inputs[0] = cell.inputs[0]._replace(v=2)
    elif fault == 'rank': cell.rank = False
    elif fault == 'node': cell.node = cell.node._replace(rank=False)
    elif fault == 'writer-export': writer['export_id'] = 'wrong'
    elif fault == 'writer-call': writer['ref']['call_instance'] = True
    elif fault == 'writer-ref': writer['inputs'][1]['version'] += 1
    elif fault == 'missing-writer': view._collective_source['writers'].remove(writer)
    elif fault == 'output-writer': view._node2outputs[node] = list(view.node_inputs(node))
    elif fault == 'scope': view.collective_scopes[node] = next(iter(view.collective_scopes.values()))
    else:
        key, value = {'bias':('bias',False),'extra':('epsilon',1),'consts':('__consts',False)}[fault]
        cell.kwargs[key] = value; view.source.cell(node).kwargs = dict(cell.kwargs)
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('world', [0,1])
@pytest.mark.parametrize('fault', ['shape-bool','shape-float','parent-bool','parent-shape','bounds','value','missing','param','grad'])
def test_shared_raw_matrix_rejected_before_port_coercion(baseline, world, fault):
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline); cell, _ = selected(args, world); ir = cell._input_irs[1]
    if fault == 'shape-bool': ir.shape = (True, ir.shape[1])
    elif fault == 'shape-float': ir.shape = (float(ir.shape[0]), ir.shape[1])
    elif fault == 'parent-bool': ir.parent.tid = True
    elif fault == 'parent-shape': ir.parent.shape = (float(ir.parent.shape[0]), ir.parent.shape[1])
    elif fault == 'bounds': ir.indmap = ((0.0,ir.shape[0]), ir.indmap[1])
    elif fault == 'value': ir.valmap = (False,1)
    elif fault == 'missing': cell._input_irs.pop()
    elif fault == 'param': ir.param = 1
    else: ir.is_grad = lambda: True
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'malformed raw matrix reached lossy Port'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('role', ['input','weight','output'])
def test_shared_coherent_binding_cannot_override_source_parent(baseline, role):
    args, closed = copy.deepcopy(baseline); cell, _ = selected(args)
    ir = cell._output_irs[0] if role == 'output' else cell._input_irs[role == 'weight']
    ir.parent.tid += 999
    if role == 'weight':
        binding = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == ir.tid)
        binding['units'][0]['bindings'][0]['parent_tid'] = ir.parent.tid
    with pytest.raises(ValueError, match='parent'): private(args, closed)


@pytest.mark.parametrize('fault', ['missing-unit','duplicate-unit','ranks','positions','dimensions','slot',
    'order-partial','order-bool','order-reverse','spec-order','unit-order'])
def test_shared_full_frontier_bounds_and_schedule(baseline, fault):
    args, closed = copy.deepcopy(baseline); row = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop(2)
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'positions': row['positions'] = [99]
    elif fault == 'dimensions': row['dimensions']['H'] += 1
    elif fault == 'slot': row['source_output_slot'] = True
    elif fault == 'spec-order': args[4]['relations'].reverse()
    elif fault == 'unit-order': args[4]['relations'][-1]['units'].reverse()
    else:
        order = args[-1]['pm']['execution_to_source']
        if fault == 'order-partial': order.pop()
        elif fault == 'order-bool': order[0] = False
        else: order.reverse()
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('world', [0,1])
@pytest.mark.parametrize('operand', [0,1])
def test_shared_selected_and_every_bw_suffix_operand_nonwrite(baseline, world, operand):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_output_projection_values as direct
    args, closed = copy.deepcopy(baseline); view = args[world]
    index = _Index(view,args[3]._inputs[world]); old = closed['frontier_units'][0]
    descriptor = old['source_step'] if world == 0 else old['local_steps'][0]
    ref = old['sm_output_ref'] if world == 0 else old['pm_output_refs'][0]
    step = consumer._linear(index, consumer.predecessor._output(index,descriptor,ref))
    label = 'sm' if world == 0 else 'pm'
    direct._read(view,label,step,args[-1][label])
    node = next(n for n in view.nodes() if tuple(n) == step.node)
    bw = [n for n in view.nodes() if view.node_opname(n).startswith('BW_')]
    assert bw
    for target in [node,*bw]:
        copied = copy.deepcopy(view)
        copied._node2outputs[target] = [copied.node_inputs(node)[operand]]
        with pytest.raises(ValueError): direct._read(copied,label,step,args[-1][label])
