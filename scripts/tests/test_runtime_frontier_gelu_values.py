"""Portable exact GELU source graphs: no capture/kernel or public B>1 claim."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_linear_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_linear_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_gelu_values'), 'frontier GELU renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_gelu_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, O=11, weight_tid=51001,
            skip_kind=None, copies=1, omit_rank=None, gelu_tid=71003):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D, tp, seqlen, reverse, O, weight_tid, skip_kind)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        for producer in [c for c in graph.cells if c.node.cid == 51000]:
            if world == 'p' and producer.rank == omit_rank:
                continue
            for j in range(copies):
                x = producer._output_irs[0]; rank = producer.rank
                y = IR(gelu_tid+j*10, 'exact.activation', x.parent.shape, x.indmap)
                cell = NS(node=N(world, rank, 0, 71000+j*10, 'FW_gelu'), rank=rank, opname='FW_gelu',
                    inputs=[producer.outputs[0]], outputs=[T(world, rank, 0, y.tid, 1)],
                    kwargs=dict(approximate='none', __consts=[]),
                    _input_irs=[copy.deepcopy(x)], _output_irs=[y])
                cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
                at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')), len(graph.cells))
                graph.cells.insert(at, cell)
                graph.shapes.update({r: ir.shape for r,ir in zip(cell.inputs+cell.outputs, cell._input_irs+cell._output_irs, strict=True)})
                if world == 'p':
                    rows.append(dict(ref=dict(world=world, runtime_rank=rank, microbatch=0, source_cid=71000+j*10,
                        call_instance=0, op=cell.opname, origin='fixture'), source_irname=cell.opname,
                        inputs=[tref(r) for r in cell.inputs], outputs=[tref(r) for r in cell.outputs], parameter_grad_tids=[]))
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                        "\n        activated = torch.nn.functional.gelu(expanded, approximate='none')\ndef _train_step")
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    adapters = {writer_export_id(w['ref']): w for w in [*old['adapter_source'], *copy.deepcopy(rows)]}
    snapshot['adapter_source'] = [adapters[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous.previous, 'fixture', return_value=f):
        return previous.previous.prepared(kwargs.get('D', 2), kwargs.get('tp', 2), kwargs.get('seqlen', 2))


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def test_public_fresh_exact_gelu_tracer(baseline):
    args, closed = copy.deepcopy(baseline)
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args, args, strict=True))
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [5,2,4,2,0]
    assert result['consumed_frontier_indices'] == [0,2]
    assert result['retained_units'] == closed['retained_units']
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    assert text.count('SourceGeluRead.gelu_value_of_split') == 5
    assert text.count('source_gelu_unit_output_reconstruct') == 2
    assert 'frontierLinearUnitFacts_' in text
    for row in result['units']:
        assert row['dimensions'] == dict(D=2,T=2,B=1,S=1,H=11)
        assert row['global_shape'] == [2,2,11] and row['local_shape'] == [1,1,11]
        assert row['source_step']['op'] == 'FW_gelu' and row['source_output_slot'] == 0
        assert row['facts_theorem'] == row['theorem']
        assert row.get('predecessor') == row['predecessor_facts'] == closed['frontier_units'][row['frontier_index']]['facts_theorem']
        fragment = text.split('theorem '+row['facts_theorem']+' ',1)[1].split('#print axioms')[0]
        assert '∀ y ∈' in fragment and '.shape = [2, 2, 11] ∧' in fragment
        assert 'chunkPrimDimN 0 2' in fragment and 'allGatherPrimDimN 1 2 0' in fragment
        assert 'parameters' not in row or row['parameters'] == []
    for row in result['reads']:
        assert row['params'] == []
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'):
        assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :','gamma','beta','weightRel'):
        assert bad not in text


def private(args, closed):
    return api()._render(*args, closed)


def selected(args, world=1):
    cell = next(c for c in args[3]._inputs[world] if c.node.cid == 71000 and c.rank == 0)
    node = next(n for n in args[world].nodes() if tuple(n) == tuple(cell.node))
    return cell, node


@pytest.mark.parametrize('fault', ['missing','none','bool','tanh','unknown','extra','const-bool','const-tuple','const-values',
    'collective_scopes','chunk_scopes','wred_scopes'])
def test_exact_original_kwargs_and_scope(baseline, fault):
    args, closed = copy.deepcopy(baseline); cell, node = selected(args)
    if fault.endswith('_scopes'):
        scopes = getattr(args[1], fault, {})
        scopes[node] = next(iter(args[1].collective_scopes.values()))
        setattr(args[1], fault, scopes)
    else:
        if fault == 'missing': cell.kwargs.pop('approximate')
        elif fault == 'extra': cell.kwargs['epsilon'] = 1
        elif fault.startswith('const-'): cell.kwargs['__consts'] = {'const-bool':False,'const-tuple':(),'const-values':['none']}[fault]
        else: cell.kwargs['approximate'] = {'none':None,'bool':False,'tanh':'tanh','unknown':'unknown'}[fault]
        args[1].source.cell(node).kwargs = dict(cell.kwargs)
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('role', ['input','output'])
def test_cross_world_parent_identity(baseline, role):
    args, closed = copy.deepcopy(baseline); cell, _ = selected(args)
    ir = cell._input_irs[0] if role == 'input' else cell._output_irs[0]
    ir.parent.tid += 999
    with pytest.raises(ValueError, match='parent'): private(args, closed)


@pytest.mark.parametrize('raw', [[1],False,(),[False]])
def test_empty_original_node_params_required(baseline, raw):
    from Verdict import graph_to_lean as compiler
    args, closed = copy.deepcopy(baseline)
    original = compiler._get_node_params
    def changed(view, node, *a, **kw):
        return raw if node.cid == 71000 else original(view, node, *a, **kw)
    with patch.object(compiler, '_get_node_params', side_effect=changed):
        with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('D,tp,S,reverse,H,tid', [(1,2,4,False,5,81003),(2,3,6,True,17,91003),(3,2,4,True,1,101003)])
def test_public_dimensions_identity_and_order(D,tp,S,reverse,H,tid):
    args = prepared(D=D,tp=tp,seqlen=S,reverse=reverse,O=H,gelu_tid=tid)
    _, result = api().render(*args)
    assert len(result['reads']) == 1+D*tp and len(result['units']) == D
    assert result['consumed_frontier_indices'] == list(range(1 if reverse else 0,2*D,2))
    for row in result['units']:
        assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S//tp,H=H)
        assert row['global_shape'] == [D,S,H] and row['local_shape'] == [1,S//tp,H]
        assert row['sm_output_ref'][3] == tid
        assert row['predecessor_facts'].startswith('frontierLinearUnitFacts_')


@pytest.mark.parametrize('kind', ['FW_add','FW_mul','FW_layernorm'])
def test_public_hidden_skip_full_facts(kind):
    args = prepared(skip_kind=kind)
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    assert len(result['units']) == 2
    assert len(result['retained_units']) == (2 if kind == 'FW_add' else 0)
    assert len(result['deferred_units']) == (0 if kind == 'FW_add' else 2)


def test_public_missing_gelu_explicit_deferral():
    args = previous.prepared()
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert result['frontier_units'] == closed['frontier_units']
    assert len(result['deferred_units']) == len(result['retained_units']) == 2
    assert not result['reads'] and not result['units']


@pytest.mark.parametrize('options', [dict(copies=2),dict(omit_rank=0)])
def test_public_fanout_partial_fail_closed(options):
    args = prepared(**options)
    with pytest.raises(ValueError, match='partial|fan-out'): api().render(*args)


@pytest.mark.parametrize('fault', ['raw-op','raw-ref','rank','node','writer-export','writer-call','writer-ref','missing-writer','output-writer'])
def test_original_identity(baseline, fault):
    args, closed = copy.deepcopy(baseline); cell, node = selected(args)
    writer = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == 71000 and w['ref']['runtime_rank'] == 0)
    if fault == 'raw-op': cell.opname = 'FW_mul'
    elif fault == 'raw-ref': cell.inputs[0] = cell.inputs[0]._replace(v=2)
    elif fault == 'rank': cell.rank = False
    elif fault == 'node': cell.node = cell.node._replace(rank=False)
    elif fault == 'writer-export': writer['export_id'] = 'wrong'
    elif fault == 'writer-call': writer['ref']['call_instance'] = True
    elif fault == 'writer-ref': writer['inputs'][0]['version'] += 1
    elif fault == 'missing-writer': args[1]._collective_source['writers'].remove(writer)
    else: args[1]._node2outputs[node] = args[1].node_inputs(node)
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('world', [0,1])
@pytest.mark.parametrize('port', ['input','output'])
@pytest.mark.parametrize('fault', ['shape-bool','shape-float','parent-bool','parent-shape','bounds','value','missing','rank-two'])
def test_raw_types_before_port_coercion(baseline, world, port, fault):
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline); cell, _ = selected(args, world)
    irs = getattr(cell, '_'+port+'_irs'); ir = irs[0]
    if fault == 'shape-bool': ir.shape = (True, *ir.shape[1:])
    elif fault == 'shape-float': ir.shape = (float(ir.shape[0]), *ir.shape[1:])
    elif fault == 'parent-bool': ir.parent.tid = True
    elif fault == 'parent-shape': ir.parent.shape = (float(ir.parent.shape[0]), *ir.parent.shape[1:])
    elif fault == 'bounds': ir.indmap = ((float(ir.indmap[0][0]),ir.indmap[0][1]), *ir.indmap[1:])
    elif fault == 'value': ir.valmap = (False,1)
    elif fault == 'rank-two': ir.shape = ir.shape[:2]
    else: irs.pop()
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'invalid typed raw metadata reached lossy Port'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('fault', ['missing-unit','duplicate-unit','positions','ranks','unit-bool','axis','dimensions',
    'slot','tid','local-tids','local-step','order-partial','order-bool','order-reverse','spec-order','unit-order'])
def test_complete_frontier_and_canonical_order(baseline, fault):
    args, closed = copy.deepcopy(baseline); row = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop(2)
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault == 'positions': row['positions'] = [99]
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'unit-bool': row['unit'] = False
    elif fault == 'axis': row['gather_axis'] = True
    elif fault == 'dimensions': row['dimensions']['H'] += 1
    elif fault == 'slot': row['source_output_slot'] = 1
    elif fault == 'tid': row['sm_output_tid'] += 1
    elif fault == 'local-tids': row['pm_output_tids'].reverse()
    elif fault == 'local-step': row['local_steps'].pop()
    elif fault == 'spec-order': args[4]['relations'].reverse()
    elif fault == 'unit-order': args[4]['relations'][-1]['units'].reverse()
    else:
        order = args[-1]['pm']['execution_to_source']
        if fault == 'order-partial': order.pop()
        elif fault == 'order-bool': order[0] = False
        else: order.reverse()
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('world', [0,1])
def test_selected_and_every_BW_suffix_input_nonwrite(baseline, world):
    from Verdict.runtime_lineage import _Index
    args, closed = copy.deepcopy(baseline)
    index = _Index(args[world], args[3]._inputs[world]); old = closed['frontier_units'][0]
    desc = old['source_step'] if world == 0 else old['local_steps'][0]
    ref = old['sm_output_ref'] if world == 0 else old['pm_output_refs'][0]
    step = api()._next(index, api().frontier._output(index, desc, ref))
    label = 'sm' if world == 0 else 'pm'; view = args[world]
    _, row = api()._read(view,label,step,args[-1][label])
    node = next(n for n in view.nodes() if tuple(n) == step.node)
    bw = [n for n in view.nodes() if view.node_opname(n).startswith('BW_')]
    assert bw and all(view.nodes().index(n) in row['operand_nonwrite_source_indices'] for n in bw)
    for target in [node,*bw]:
        copied = copy.deepcopy(view)
        copied._node2outputs[target] = list(copied.node_inputs(node))
        with pytest.raises(ValueError): api()._read(copied,label,step,args[-1][label])


def test_public_rejects_raw_approximate_and_fake_receipt(baseline):
    args, _ = copy.deepcopy(baseline); cell, node = selected(args)
    cell.kwargs['approximate'] = 'tanh'; args[1].source.cell(node).kwargs = dict(cell.kwargs)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(TypeError): api().render(*args, {'frontier_units': []})
