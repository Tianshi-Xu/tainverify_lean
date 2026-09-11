"""Portable direct-linear frontier tests; not capture or kernel evidence."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_layernorm_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_layernorm_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_linear_values'), 'frontier linear renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_linear_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, O=11, weight_tid=51001, skip_kind=None,
            copies=1, omit_rank=None):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D, tp, seqlen, reverse, skip_kind=skip_kind)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        for producer in [c for c in graph.cells if c.node.cid == 31000]:
            if world == 'p' and producer.rank == omit_rank:
                continue
            for copy_index in range(copies):
                x = producer._output_irs[0]; rank = producer.rank
                w = IR(weight_tid, 'arbitrary.matrix.identity', (O, x.shape[-1]), param=True)
                y = IR(51003+copy_index*10, 'direct.expanded', (*x.parent.shape[:2], O), (*x.indmap[:2], (0, O)))
                ins = [producer.outputs[0], T(world, rank, -1, w.tid, 0)]
                cell = NS(node=N(world, rank, 0, 51000+copy_index*10, 'FW_linear'), rank=rank, opname='FW_linear',
                    inputs=ins, outputs=[T(world, rank, 0, y.tid, 1)], kwargs=dict(bias=None),
                    _input_irs=[copy.deepcopy(x), w], _output_irs=[y])
                cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
                at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')), len(graph.cells))
                graph.cells.insert(at, cell)
                graph.shapes.update({r: ir.shape for r,ir in zip(cell.inputs+cell.outputs, cell._input_irs+cell._output_irs, strict=True)})
                if world == 'p':
                    rows.append(dict(ref=dict(world=world, runtime_rank=rank, microbatch=0, source_cid=51000+copy_index*10,
                        call_instance=0, op=cell.opname, origin='fixture'), source_irname=cell.opname,
                        inputs=[tref(r) for r in ins], outputs=[tref(r) for r in cell.outputs], parameter_grad_tids=[]))
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                        f'\n        expanded = torch.nn.functional.linear(normalized, self.param_{weight_tid}, bias=None)\ndef _train_step')
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    adapters = {writer_export_id(w['ref']): w for w in [*old['adapter_source'], *copy.deepcopy(rows)]}
    snapshot['adapter_source'] = [adapters[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(kwargs.get('D', 2), kwargs.get('tp', 2), kwargs.get('seqlen', 2))


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def test_public_fresh_direct_linear_tracer(baseline):
    args, closed = copy.deepcopy(baseline)
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args, args, strict=True))
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [5,2,4,2,0]
    assert result['consumed_frontier_indices'] == [0,2]
    assert result['retained_units'] == closed['retained_units']
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    assert text.count('SourceLinearRead.linear_value_of_split') == 5
    assert text.count('source_linear_sequence_unit_output_reconstruct') == 2
    assert 'initialParameterValues_final s p t q hs hp hvalues' in text
    assert 'frontierLayernormUnitFacts_' in text
    assert 'outputProjectionRead_' not in text and 'outputProjectionUnitFacts_' not in text
    for row in result['units']:
        assert row['dimensions'] == dict(D=2,T=2,B=1,S=1,H=11)
        assert row['input_shape'] == [2,2,6] and row['input_width'] == 6
        assert row['global_shape'] == [2,2,11] and row['local_shape'] == [1,1,11]
        assert row['parameters'][0]['sm_shape'] == [11,6]
        assert row['source_step']['op'] == 'FW_linear' and row['source_output_slot'] == 0
        assert row['facts_theorem'] == row['theorem']
        fragment = text.split('theorem '+row['facts_theorem']+' ',1)[1].split('#print axioms')[0]
        assert '∀ y ∈' in fragment and '.shape = [2, 2, 11] ∧' in fragment
        assert 'chunkPrimDimN 0 2' in fragment and 'allGatherPrimDimN 1 2 0' in fragment
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'):
        assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :','globalAlias','alias_'):
        assert bad not in text


@pytest.mark.parametrize('D,tp,S,reverse,O,weight', [(1,2,4,False,5,61001), (2,3,6,True,17,62001), (3,2,4,True,1,63001)])
def test_public_dimensions_and_nondefault_identity(D,tp,S,reverse,O,weight):
    args = prepared(D=D,tp=tp,seqlen=S,reverse=reverse,O=O,weight_tid=weight)
    _, result = api().render(*args)
    assert len(result['reads']) == 1+D*tp and len(result['units']) == D
    assert result['consumed_frontier_indices'] == list(range(1 if reverse else 0,2*D,2))
    for row in result['units']:
        assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S//tp,H=O)
        assert row['global_shape'] == [D,S,O] and row['input_width'] == 3*tp
        assert row['parameters'][0]['sm_ref'][3] == weight


@pytest.mark.parametrize('kind', ['FW_add','FW_mul','FW_layernorm'])
def test_public_hidden_skip_facts_preserved(kind):
    args = prepared(skip_kind=kind)
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    assert len(result['units']) == 2
    assert len(result['retained_units']) == (2 if kind == 'FW_add' else 0)
    assert len(result['deferred_units']) == (0 if kind == 'FW_add' else 2)


def test_public_no_linear_explicit_deferral():
    args = previous.prepared()
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert result['frontier_units'] == closed['frontier_units']
    assert len(result['deferred_units']) == len(result['retained_units']) == 2
    assert not result['reads'] and not result['units']


@pytest.mark.parametrize('options', [dict(copies=2),dict(omit_rank=0)])
def test_public_fanout_and_partial_cover_fail_closed(options):
    # Missing a rank's only weight occurrence is rejected even earlier by the
    # canonical initial-parameter inventory; do not fabricate a closed receipt.
    with pytest.raises(ValueError, match='fan-out|incomplete initial parameter rank inventory'):
        args = prepared(**options)
        api().render(*args)


@pytest.mark.parametrize('fault', ['raw-op','raw-ref','rank','node','writer-export','writer-call','writer-ref',
    'extra','bias','consts','scope','missing-writer'])
def test_original_linear_authority(baseline, fault):
    args, closed = copy.deepcopy(baseline); source = args[1]
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 51000 and c.rank == 0)
    writer = next(w for w in source._collective_source['writers'] if w['ref']['source_cid'] == 51000 and w['ref']['runtime_rank'] == 0)
    if fault == 'raw-op': cell.opname = 'FW_mul'
    elif fault == 'raw-ref': cell.inputs[0] = cell.inputs[0]._replace(v=2)
    elif fault == 'rank': cell.rank = False
    elif fault == 'node': cell.node = cell.node._replace(rank=False)
    elif fault == 'writer-export': writer['export_id'] = 'wrong'
    elif fault == 'writer-call': writer['ref']['call_instance'] = True
    elif fault == 'writer-ref': writer['inputs'][1]['version'] += 1
    elif fault == 'missing-writer': source._collective_source['writers'].remove(writer)
    else:
        node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
        if fault == 'scope': source.collective_scopes[node] = next(iter(source.collective_scopes.values()))
        else:
            key, value = {'extra': ('unsupported_semantics',1),'bias': ('bias',False),'consts': ('__consts',False)}[fault]
            cell.kwargs[key] = value; source.source.cell(node).kwargs = dict(cell.kwargs)
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('fault', ['ref','parent_tid','rank','bounds','value_part','full_shape','sm_ref','order','goal'])
def test_complete_weight_binding(baseline, fault):
    args, closed = copy.deepcopy(baseline)
    row = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == 51001)
    bu = row['units'][0]; b = bu['bindings'][0]
    if fault in ('ref','sm_ref'): b[fault][3] += 1
    elif fault in ('rank','parent_tid'): b[fault] += 1
    elif fault == 'bounds': b[fault][0][0] = 1
    elif fault == 'value_part': b[fault] = [1,2]
    elif fault == 'full_shape': b[fault][0] += 1
    elif fault == 'order': bu['bindings'].reverse()
    else: bu['initial_goal']['kind'] = 'sharded'
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('world', [0,1])
@pytest.mark.parametrize('operand', [0,1])
@pytest.mark.parametrize('selected', [False,True])
def test_selected_node_and_whole_BW_suffix_nonwrite(baseline,world,operand,selected):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_output_projection_values as direct
    args, closed = copy.deepcopy(baseline); source = args[world]
    index = _Index(source,args[3]._inputs[world]); old = closed['frontier_units'][0]
    descriptor = old['source_step'] if world == 0 else old['local_steps'][0]
    ref = old['sm_output_ref'] if world == 0 else old['pm_output_refs'][0]
    step = api()._linear(index,predecessor._output(index,descriptor,ref))
    label = 'sm' if world == 0 else 'pm'
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if selected else source.nodes()[args[-1][label]['execution_to_source'][-1]]
    if not selected: assert source.node_opname(target).startswith('BW_')
    source._node2outputs[target] = [source.node_inputs(node)[operand]]
    with pytest.raises(ValueError): direct._read(source,label,step,args[-1][label])


def private(args, closed):
    return api()._render(*args, closed)


@pytest.mark.parametrize('world', [0,1])
@pytest.mark.parametrize('port', [0,1,2])
@pytest.mark.parametrize('fault', ['shape-bool','shape-float','parent-bool','parent-shape','bounds','value','missing'])
def test_raw_types_before_port_coercion(baseline, world, port, fault):
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[world] if c.node.cid == 51000 and c.rank == 0)
    irs = cell._input_irs if port < 2 else cell._output_irs
    ir = irs[port if port < 2 else 0]
    if fault == 'shape-bool': ir.shape = (True, *ir.shape[1:])
    elif fault == 'shape-float': ir.shape = (float(ir.shape[0]), *ir.shape[1:])
    elif fault == 'parent-bool': ir.parent.tid = True
    elif fault == 'parent-shape': ir.parent.shape = (float(ir.parent.shape[0]), *ir.parent.shape[1:])
    elif fault == 'bounds': ir.indmap = ((float(ir.indmap[0][0]),ir.indmap[0][1]), *ir.indmap[1:])
    elif fault == 'value': ir.valmap = (False,1)
    else: irs.pop()
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'typed raw metadata reached lossy Port'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('role', ['input','output','weight'])
def test_cross_world_parent_identity(baseline, role):
    args, closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 51000 and c.rank == 0)
    ir = cell._output_irs[0] if role == 'output' else cell._input_irs[role == 'weight']
    ir.parent.tid += 999
    if role == 'weight':
        row = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == 51001)
        row['units'][0]['bindings'][0]['parent_tid'] = ir.parent.tid
    with pytest.raises(ValueError, match='parent'): private(args, closed)


@pytest.mark.parametrize('fault', ['missing-unit','duplicate-unit','positions','ranks','unit-bool','axis',
    'dimensions','slot','order-partial','order-bool','order-reverse','spec-order','unit-order'])
def test_complete_frontier_and_canonical_order(baseline, fault):
    args, closed = copy.deepcopy(baseline); row = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop(2)
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault == 'positions': row['positions'] = [99]
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'unit-bool': row['unit'] = False
    elif fault == 'axis': row['gather_axis'] = True
    elif fault == 'dimensions': row['dimensions']['D'] = 3
    elif fault == 'slot': row['source_output_slot'] = 1
    elif fault == 'spec-order': args[4]['relations'].reverse()
    elif fault == 'unit-order': args[4]['relations'][-1]['units'].reverse()
    else:
        order = args[-1]['pm']['execution_to_source']
        if fault == 'order-partial': order.pop()
        elif fault == 'order-bool': order[0] = False
        else: order.reverse()
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('fault', ['float-shape','float-bounds','bool-value','missing','param','grad'])
def test_every_weight_occurrence_before_binding(baseline, fault):
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline)
    selected = next(c for c in args[3]._inputs[1] if c.node.cid == 51000 and c.rank == 0)
    other = copy.deepcopy(selected); other.node = other.node._replace(cid=99000,irname='BW_probe'); other.opname = 'BW_probe'
    other.inputs = [selected.inputs[1]]; ir = copy.deepcopy(selected._input_irs[1]); other._input_irs = [ir]
    other.outputs = []; other._output_irs = []
    args[3]._inputs[1].append(other)
    if fault == 'float-shape': ir.shape = (float(ir.shape[0]), ir.shape[1])
    elif fault == 'float-bounds': ir.indmap = ((0.0,ir.shape[0]),ir.indmap[1])
    elif fault == 'bool-value': ir.valmap = (False,1)
    elif fault == 'missing': other._input_irs = []
    elif fault == 'param': ir.param = 1
    else: ir.is_grad = lambda: True
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'invalid occurrence reached Port'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)
