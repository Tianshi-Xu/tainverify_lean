"""Fresh source frontier -> LN candidates; portable tests are not kernel evidence."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_alias_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_alias_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_layernorm_values'), 'frontier layernorm renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_layernorm_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, swap=False, skip_kind=None):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D, tp, seqlen, reverse)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            producer = next(c for c in graph.cells if c.rank == rank and c.node.cid == (27000 if world == 's' else 29000))
            slot = next(i for i, ir in enumerate(producer._output_irs) if ir.parent.tid == 28001)
            x = producer._output_irs[slot]
            params = [IR(31001, 'frontier.gamma', (3*tp,), param=True), IR(31002, 'frontier.beta', (3*tp,), param=True)]
            if swap: params.reverse()
            ins = [producer.outputs[slot], *(T(world, rank, -1, p.tid, 0) for p in params)]
            out = IR(31003, 'frontier.normalized', x.parent.shape, x.indmap)
            cell = NS(node=N(world, rank, 0, 31000, 'FW_layernorm'), rank=rank, opname='FW_layernorm',
                inputs=ins, outputs=[T(world, rank, 0, out.tid, 1)], kwargs=dict(normalized_shape=[3*tp], eps=1e-5),
                _input_irs=[copy.deepcopy(x), *params], _output_irs=[out])
            cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
            at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')), len(graph.cells))
            graph.cells.insert(at, cell)
            graph.shapes.update({r: ir.shape for r, ir in zip(cell.inputs+cell.outputs, cell._input_irs+cell._output_irs, strict=True)})
            if world == 'p':
                rows.append(dict(ref=dict(world=world, runtime_rank=rank, microbatch=0, source_cid=31000,
                    call_instance=0, op=cell.opname, origin='fixture'), source_irname=cell.opname,
                    inputs=[tref(r) for r in ins], outputs=[tref(r) for r in cell.outputs], parameter_grad_tids=[]))
                old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                    '\n        normalized = torch.nn.functional.layer_norm(frontier_0, normalized_shape=['+str(3*tp)
                    +f'], weight=self.param_{params[0].tid}, bias=self.param_{params[1].tid}, eps=1e-5)\ndef _train_step')
    fanout = skip_kind == 'fanout'
    if fanout: skip_kind = 'FW_add'
    if skip_kind:
        for world, graph in [('s',sm),('p',pm)]:
            for alias in [c for c in graph.cells if c.node.cid == 27000]:
                slot = next(i for i,ir in enumerate(alias._output_irs) if ir.parent.tid == 28002)
                x = alias._output_irs[slot]; ref = alias.outputs[slot]
                main = next(c for c in graph.cells if c.rank == alias.rank and c.node.cid == 31000)
                if fanout: x, ref = main._input_irs[0], main.inputs[0]
                irs = [x,*main._input_irs[1:]] if skip_kind == 'FW_layernorm' else [x,x]
                refs = [ref,*main.inputs[1:]] if skip_kind == 'FW_layernorm' else [ref,ref]
                out = IR(41001,'skip.consumer',x.parent.shape,x.indmap)
                kw = dict(main.kwargs) if skip_kind == 'FW_layernorm' else (dict(alpha=1) if skip_kind == 'FW_add' else {})
                c = NS(node=N(world,alias.rank,0,41000,skip_kind),rank=alias.rank,opname=skip_kind,
                    inputs=refs,outputs=[T(world,alias.rank,0,out.tid,1)],kwargs=kw,
                    _input_irs=copy.deepcopy(irs),_output_irs=[out])
                c.ir = NS(signature=skip_kind,inputs=lambda c=c:c._input_irs,outputs=lambda c=c:c._output_irs)
                at = next((i for i,b in enumerate(graph.cells) if b.rank == c.rank and b.opname.startswith('BW_')),len(graph.cells))
                graph.cells.insert(at,c); graph.shapes[c.outputs[0]] = out.shape
                if world == 'p':
                    rows.append(dict(ref=dict(world=world,runtime_rank=c.rank,microbatch=0,source_cid=41000,
                        call_instance=0,op=skip_kind,origin='fixture'),source_irname=skip_kind,
                        inputs=[tref(r) for r in refs],outputs=[tref(r) for r in c.outputs],parameter_grad_tids=[]))
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    adapters = {writer_export_id(w['ref']): w for w in [*old['adapter_source'], *copy.deepcopy(rows)]}
    snapshot['adapter_source'] = [adapters[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, reverse=False, swap=False, skip_kind=None):
    f = fixture(D, tp, seqlen, reverse, swap, skip_kind)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D, tp, seqlen)


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def test_public_six_input_fresh_tracer(baseline):
    args, closed = copy.deepcopy(baseline)
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args, args, strict=True))
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [5,2,4,2,0]
    assert result['consumed_frontier_indices'] == [0,2]
    assert result['retained_units'] == closed['retained_units']
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    assert text.count('SourceLayernormRead.layernorm_value_of_split') == 5
    assert text.count('source_layernorm_unit_output_reconstruct') == 2
    assert 'initialParameterValues_final s p t q hs hp h' in text
    assert 'frontierExchangeFacts_' in text
    assert 'layernormUnitFacts_' not in text and 'layernormRead_' not in text
    for row in result['units']:
        assert row['global_shape'] == [2,2,6] and row['local_shape'] == [1,1,6]
        assert row['layout'] == 'sharded' and row['gather_axis'] == 1
        assert row['source_step']['op'] == 'FW_layernorm'
        assert row['sm_output_ref'] == list(row['source_step']['outputs'][0]['endpoint']['ref'])
        assert row['pm_output_refs'] == [list(s['outputs'][0]['endpoint']['ref']) for s in row['local_steps']]
        assert row['facts_theorem'] == row['theorem']
        fragment = text.split('theorem '+row['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert '∀ y ∈' in fragment and '.shape = [2, 2, 6]' in fragment
        assert 'chunkPrimDimN 0 2' in fragment and 'allGatherPrimDimN 1 2 0' in fragment
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'):
        assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'):
        assert bad not in text


def private(args, closed):
    # Only negative seam tests bypass expensive fresh upstream reconstruction.
    return api()._render(*args, closed)


@pytest.mark.parametrize('D,tp,seqlen,reverse,swap', [(1,2,4,False,False), (2,3,6,True,True), (3,2,4,True,False)])
def test_public_dimensions_alias_slots_and_parameter_roles(D, tp, seqlen, reverse, swap):
    args = prepared(D,tp,seqlen,reverse,swap)
    text, result = api().render(*args)
    assert len(result['reads']) == 1+D*tp and len(result['units']) == D
    assert len(result['frontier_units']) == 2*D and len(result['retained_units']) == D
    assert result['consumed_frontier_indices'] == list(range(1 if reverse else 0, 2*D, 2))
    for row in result['units']:
        assert row['global_shape'] == [D,seqlen,3*tp]
        assert row['local_shape'] == [1,seqlen//tp,3*tp]
        assert row['parameters'][0]['sm_ref'][3] == (31002 if swap else 31001)
        assert row['parameters'][1]['sm_ref'][3] == (31001 if swap else 31002)
        assert row['parameters'][0]['spec_index'] != row['parameters'][1]['spec_index']
    assert 'frontierLayernormUnitFacts_' in text


@pytest.mark.parametrize('world', [0,1])
@pytest.mark.parametrize('port', [0,1,2,3])
@pytest.mark.parametrize('fault', ['shape-bool','shape-float','parent-bool','parent-shape','bounds','value','missing'])
def test_typed_raw_ports_before_lossy_conversion(baseline, world, port, fault):
    from Verdict import runtime_post_add_values as post
    args, closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[world] if c.node.cid == 31000 and c.rank == 0)
    irs = cell._input_irs if port < 3 else cell._output_irs
    ir = irs[port if port < 3 else 0]
    if fault == 'shape-bool': ir.shape = (True, *ir.shape[1:])
    elif fault == 'shape-float': ir.shape = (float(ir.shape[0]), *ir.shape[1:])
    elif fault == 'parent-bool': ir.parent.tid = True
    elif fault == 'parent-shape': ir.parent.shape = (float(ir.parent.shape[0]), *ir.parent.shape[1:])
    elif fault == 'bounds': ir.indmap = ((float(ir.indmap[0][0]), ir.indmap[0][1]), *ir.indmap[1:])
    elif fault == 'value': ir.valmap = (False,1)
    else: irs.pop()
    convert = post._port
    def checked(index, ref, raw):
        assert raw is not ir, 'typed metadata reached lossy Port conversion'
        return convert(index, ref, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('fault', ['input-parent','output-parent','raw-op','raw-refs','rank','node',
    'writer-export','writer-call','writer-refs','extra','eps','norm','consts','scope'])
def test_public_original_identity(baseline, fault):
    args, _ = copy.deepcopy(baseline); source = args[1]
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 31000 and c.rank == 0)
    writer = next(w for w in source._collective_source['writers'] if w['ref']['source_cid'] == 31000 and w['ref']['runtime_rank'] == 0)
    if fault == 'input-parent': cell._input_irs[0].parent.tid += 100
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 100
    elif fault == 'raw-op': cell.opname = 'FW_mul'
    elif fault == 'raw-refs': cell.inputs[0] = cell.inputs[0]._replace(v=2)
    elif fault == 'rank': cell.rank = False
    elif fault == 'node': cell.node = cell.node._replace(rank=False)
    elif fault == 'writer-export': writer['export_id'] = 'wrong'
    elif fault == 'writer-call': writer['ref']['call_instance'] = True
    elif fault == 'writer-refs': writer['inputs'][1]['version'] += 1
    else:
        node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
        if fault == 'scope': source.collective_scopes[node] = next(iter(source.collective_scopes.values()))
        else:
            key, value = {'extra': ('semantic_extra',1), 'eps': ('eps',1e-4), 'norm': ('normalized_shape',[True]), 'consts': ('__consts',False)}[fault]
            cell.kwargs[key] = value
            source.source.cell(node).kwargs = dict(cell.kwargs)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['missing-unit','duplicate-unit','partial-locals','positions','ranks','unit-bool',
    'axis','dimensions','global-shape','skip-shape','slot','order-partial','order-bool','order-reverse'])
def test_complete_frontier_contract(baseline, fault):
    args, closed = copy.deepcopy(baseline); row = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop(2)
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault == 'partial-locals': row['local_steps'].pop()
    elif fault == 'positions': row['positions'] = [99]
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'unit-bool': row['unit'] = False
    elif fault == 'axis': row['gather_axis'] = True
    elif fault == 'dimensions': row['dimensions']['D'] = 3
    elif fault == 'global-shape': row['global_shape'][0] += 1
    elif fault == 'skip-shape': closed['frontier_units'][1]['local_shape'][0] += 1
    elif fault == 'slot': row['source_output_slot'] = 1
    else:
        order = args[-1]['pm']['execution_to_source']
        if fault == 'order-partial': order.pop()
        elif fault == 'order-bool': order[0] = False
        else: order.reverse()
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('role', [31001,31002])
@pytest.mark.parametrize('fault', ['ref','parent_tid','rank','bounds','value_part','full_shape','sm_ref','order','spec-order','unit-order'])
def test_parameter_bindings_from_same_canonical_specs(baseline, role, fault):
    args, closed = copy.deepcopy(baseline)
    row = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == role)
    bu = row['units'][0]; b = bu['bindings'][0]
    if fault in ('ref','sm_ref'): b[fault][3] += 1
    elif fault in ('rank','parent_tid'): b[fault] += 1
    elif fault == 'bounds': b[fault][0][0] = 1
    elif fault == 'value_part': b[fault] = [1,2]
    elif fault == 'full_shape': b[fault][0] += 1
    elif fault == 'order': bu['bindings'].reverse()
    elif fault == 'spec-order': args[4]['relations'].reverse()
    else: row['units'].reverse()
    with pytest.raises(ValueError): private(args, closed)


@pytest.mark.parametrize('world', [0,1])
@pytest.mark.parametrize('operand', [0,1,2])
def test_selected_node_and_entire_BW_suffix_nonwrite(baseline, world, operand):
    from Verdict import runtime_layernorm_values as ln
    from Verdict.runtime_lineage import _Index
    args, closed = copy.deepcopy(baseline); source = args[world]
    index = _Index(source, args[3]._inputs[world]); old = closed['frontier_units'][0]
    descriptor = old['source_step'] if world == 0 else old['local_steps'][0]
    ref = old['sm_output_ref'] if world == 0 else old['pm_output_refs'][0]
    activation = api()._output(index, descriptor, ref)
    step = ln._next(index, activation); label = 'sm' if world == 0 else 'pm'
    last = source.nodes()[args[-1][label]['execution_to_source'][-1]]
    assert source.node_opname(last).startswith('BW_')
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    source._node2outputs[last] = [source.node_inputs(node)[operand]]
    with pytest.raises(ValueError, match='operand.*written'): ln._read(source,label,step,args[-1][label])


@pytest.mark.parametrize('kind', ['FW_layernorm','FW_mul','FW_add'])
def test_public_hidden_frontier_consumer_is_not_layout_dispatch(kind):
    args = prepared(skip_kind=kind)
    _, closed = predecessor.render(*args)
    _, result = api().render(*args)
    assert len(result['units']) == 2
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    if kind == 'FW_add':
        assert result['retained_units'] == closed['retained_units']
        assert result['deferred_units'] == []
    else:
        assert result['retained_units'] == []
        assert len(result['deferred_units']) == 2
        assert all(r['reason'] for r in result['deferred_units'])


def test_public_sequence_boundary_without_ln_is_explicitly_deferred():
    args = previous.prepared()
    _, result = api().render(*args)
    assert not result['units'] and not result['reads']
    assert len(result['deferred_units']) == len(result['retained_units']) == 2
    assert len(result['frontier_units']) == 4


def test_public_ln_fanout_fails_closed():
    args = prepared(skip_kind='fanout')
    with pytest.raises(ValueError, match='fan-out'): api().render(*args)


@pytest.mark.parametrize('role', [1,2])
def test_coherent_parameter_binding_cannot_reidentify_parent(baseline, role):
    args, closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 31000 and c.rank == 0)
    ir = cell._input_irs[role]; ir.parent.tid += 999
    row = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == ir.tid)
    row['units'][0]['bindings'][0]['parent_tid'] = ir.parent.tid
    with pytest.raises(ValueError, match='parent'): private(args, closed)
