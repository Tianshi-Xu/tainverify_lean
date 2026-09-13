"""Portable public rank-changing projection-view candidates, not a kernel gate."""
import copy
import importlib
import importlib.util
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_gathered_exchange_values as previous
from Verdict import runtime_frontier_gathered_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_projection_view_values'), 'projection view renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_projection_view_values')


def fixture(successors=False, successor_metadata="local-only", **kwargs):
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR
    sm, pm, authority = previous.fixture(**kwargs)
    alias = kwargs.get('alias_tid', 271003)
    for world, graph in [('s', sm), ('p', pm)]:
        for slot, cid in enumerate([alias+(9000 if world == 's' else 10000), alias+8001, alias+8002]):
            for cell in [c for c in graph.cells if c.node.cid == cid and c.opname == 'FW_view']:
                x = cell._input_irs[0]
                C = 3
                lo, hi = x.indmap[2]
                y = IR(cell.outputs[0].tid, f'projection.heads.{slot}',
                       (*x.parent.shape[:2], x.parent.shape[2]//C, C),
                       (*x.indmap[:2], (lo//C, hi//C), (0, C)))
                y.parent.tid = alias+12000+slot  # intentional new parent, shared SM/PM
                cell._output_irs = [y]
                cell.ir.signature = 'torch.Tensor.view'
                cell.kwargs = dict(size=list(y.shape))
                graph.shapes[cell.outputs[0]] = y.shape
    # Original runtime generated calls describe the same rank-changing view.
    snapshot = copy.deepcopy(authority[2])
    for rank, text in snapshot['rank_sources'].items():
        for cell in pm.cells:
            if cell.rank != int(rank) or cell.opname != 'FW_view': continue
            cid = cell.node.cid
            variable = 'next_q_view' if cid == alias+10000 else ('next_view_1' if cid == alias+8001 else 'next_view_2' if cid == alias+8002 else None)
            if variable:
                lines = text.splitlines()
                for i, line in enumerate(lines):
                    if line.strip().startswith(variable+' = '):
                        lines[i] = line[:line.index('.view(')]+'.view('+', '.join(map(str,cell._output_irs[0].shape))+')'
                text = '\n'.join(lines)+'\n'
        snapshot['rank_sources'][rank] = text
    if successors:
        _successors(sm, pm, snapshot, alias, kwargs.get('tp', 2))
        if successor_metadata == 'all-peers':
            for cell in pm.cells:
                if cell.opname == 'AllToAllPrim' and alias+13000 <= cell.node.cid <= alias+13002:
                    cell._input_irs = [copy.deepcopy(next(ir for c in pm.cells for ref,ir in
                        zip(c.outputs,c._output_irs,strict=True) if ref == r)) for r in cell.inputs]
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def _successors(sm, pm, snapshot, alias, tp):
    from types import SimpleNamespace as NS
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    rows = []; adapters = []
    for world, graph in [('s',sm), ('p',pm)]:
        for slot,cid in enumerate([alias+(9000 if world == 's' else 10000),alias+8001,alias+8002]):
            for producer in [c for c in graph.cells if c.node.cid == cid and c.opname == 'FW_view']:
                x = producer._output_irs[0]; rank = producer.rank
                if world == 's':
                    shape = list(x.parent.shape); shape[1],shape[2] = shape[2],shape[1]
                    y = IR(alias+13000+slot, f'transposed.{slot}', tuple(shape))
                    refs = producer.outputs[:]; kind = 'FW_transpose'; kw = dict(dim0=1,dim1=2)
                else:
                    ranks = list(range(rank//tp*tp,(rank//tp+1)*tp)); j = rank%tp
                    a,b = [(1,2),(1,3),(2,1)][slot]
                    bounds = list(x.indmap); bounds[a] = (0,x.parent.shape[a])
                    assert x.parent.shape[b]%tp == 0
                    width = x.parent.shape[b]//tp; bounds[b] = (j*width,(j+1)*width)
                    y = IR(alias+13000+slot,x.parent.name,x.parent.shape,tuple(bounds)); y.parent.tid=x.parent.tid
                    refs = [producer.outputs[0]._replace(rank=r) for r in ranks]
                    kind = 'AllToAllPrim'; kw = dict(ranks=ranks,idim=a,odim=b)
                cell = NS(node=N(world,rank,0,y.tid,kind),rank=rank,opname=kind,inputs=refs,
                    outputs=[T(world,rank,0,y.tid,1)],kwargs=kw,_input_irs=[copy.deepcopy(x)],_output_irs=[y])
                cell.ir = NS(signature='torch.Tensor.transpose' if world == 's' else 'nnscaler.runtime.adapter.all_to_all',
                             inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
                graph.cells.insert(graph.cells.index(producer)+1,cell); graph.shapes[cell.outputs[0]]=y.shape
                if world == 'p':
                    row = dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=y.tid,
                        call_instance=0,op=kind,origin='fixture'),source_irname=kind,
                        inputs=[tref(r) for r in refs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[],adapter_kwargs=kw.copy())
                    rows.append(row); adapter=copy.deepcopy(row); adapter['inputs']=[tref(producer.outputs[0])]
                    variable = 'next_q_view' if slot == 0 else f'next_view_{slot}'
                    adapter['primitive']=dict(kind=kind,forward=True,kwargs=kw.copy(),signature=cell.ir.signature,
                        generated_inputs=[variable],generated_outputs=[f'head_exchange_{slot}'])
                    adapters.append(adapter)
                    snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace('\ndef _train_step',
                        f'\n        head_exchange_{slot} = nnscaler.runtime.adapter.all_to_all({variable}, ranks={ranks}, idim={a}, odim={b})\ndef _train_step')
    fresh=build_snapshot([*snapshot['writers'],*rows]); fresh.update({k:snapshot[k] for k in ('source','runtime_ndevs','rank_sources')})
    by_id={writer_export_id(w['ref']):w for w in [*snapshot['adapter_source'],*adapters]}
    fresh['adapter_source']=[by_id[writer_export_id(w['ref'])] for w in fresh['writers']]
    bind_reducers(fresh); bind_adapters(fresh); snapshot.clear(); snapshot.update(fresh)


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(**kwargs)


def test_public_projection_view_tracer():
    args = prepared(); subject = api(); observed = []; original = predecessor.render
    def fresh(*six):
        result = original(*six); observed.append(result); return result
    with patch.object(predecessor, 'render', side_effect=fresh) as refresh:
        text, result = subject.render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed = observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [15,6,8,2,0]
    assert result['consumed_frontier_indices'] == [0,1,2,4,5,6]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in result['consumed_frontier_indices']: assert new is old
        else:
            assert new['predecessor_facts'] == old['facts_theorem']
            assert new['input_frontier'] is old
            assert new['global_shape'] == [2,2,2,3]
            assert new['local_shape'] == ([1,1,2,3] if i%4 != 2 else [1,2,1,3])
            assert new['source_output_slot'] == 0
            assert new['gather_axis'] == old['gather_axis']
            assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
            assert new['dimensions'] == dict(D=2,T=2,**dict(zip(('B','S','H','C'),new['local_shape'])) )
            assert f'have predecessor := {old["facts_theorem"]} ' in text
    assert result['retained_units'] == closed['retained_units']
    assert text.count('source_view_sequence_unit_output_reconstruct') == 4
    assert text.count('source_view_head_unit_output_reconstruct') == 2
    assert text.count('SourceLayoutRead.view_value_of_split') == 15
    for row in result['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'): assert bad not in text
    with pytest.raises(TypeError): subject.render(*args,closed)


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def transport(args, closed):
    with patch.object(predecessor, 'render', return_value=('',closed)) as fresh:
        result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    return result


def selected(args, world='pm', slot=0, rank=3):
    cid = 271003 + ((9000 if world == 'sm' else 10000) if slot == 0 else 8000+slot)
    return next(c for c in args[3]._inputs[0 if world == 'sm' else 1]
                if c.node.cid == cid and (world == 'sm' or c.rank == rank))


@pytest.mark.parametrize('world', ['sm','pm'])
@pytest.mark.parametrize('fault', ['signature','missing-signature','missing-ir','input-shape-bool',
    'input-shape-float','output-shape-bool','output-shape-float','parent-shape-bool','parent-shape-float',
    'output-rank','input-rank','bounds-bool','bounds-float','bounds-negative','bounds-overrun',
    'value-bool','value-float','value-partial','input-parent','output-parent','input-tid','output-tid',
    'param-type','grad-type','size-bool','size-float','size-missing','size-zero','size-product',
    'size-two-inferred','size-invalid-inferred','kwargs-extra','input-arity','output-arity','output-missing'])
def test_raw_view_authority(baseline, world, fault):
    args,closed = copy.deepcopy(baseline); cell = selected(args,world)
    x = cell._input_irs[0]; y = cell._output_irs[0]
    if fault == 'signature': cell.ir.signature = 'torch.reshape'
    elif fault == 'missing-signature': del cell.ir.signature
    elif fault == 'missing-ir': cell.ir = None
    elif fault.startswith('input-shape-'): x.shape = (True if fault.endswith('bool') else float(x.shape[0]), *x.shape[1:])
    elif fault.startswith('output-shape-'): y.shape = (True if fault.endswith('bool') else float(y.shape[0]), *y.shape[1:])
    elif fault.startswith('parent-shape-'): y.parent.shape = (True if fault.endswith('bool') else float(y.parent.shape[0]), *y.parent.shape[1:])
    elif fault == 'output-rank': y.shape = y.shape[:3]
    elif fault == 'input-rank': x.shape = (*x.shape,1)
    elif fault.startswith('bounds-'):
        lo = {'bounds-bool':False,'bounds-float':0.0,'bounds-negative':-1,'bounds-overrun':0}[fault]
        hi = y.parent.shape[0]+1 if fault == 'bounds-overrun' else y.indmap[0][1]
        y.indmap = ((lo,hi),*y.indmap[1:])
    elif fault.startswith('value-'): y.valmap = {'value-bool':(False,1),'value-float':(0.0,1),'value-partial':(0,2)}[fault]
    elif fault == 'input-parent': x.parent.tid += 1
    elif fault == 'output-parent': y.parent.tid += 1
    elif fault == 'input-tid': x.tid += 1
    elif fault == 'output-tid': y.tid += 1
    elif fault == 'param-type': y.param = 0
    elif fault == 'grad-type': y.is_grad = lambda: 0
    elif fault == 'size-missing': del cell.kwargs['size']
    elif fault.startswith('size-'):
        if fault == 'size-two-inferred': cell.kwargs['size'][:2] = [-1,-1]
        else: cell.kwargs['size'][0] = {'size-bool':True,'size-float':1.0,'size-zero':0,'size-product':3,'size-invalid-inferred':-2}[fault]
    elif fault == 'kwargs-extra': cell.kwargs['shape'] = [1]
    elif fault == 'input-arity': cell._input_irs *= 2
    elif fault == 'output-arity': cell._output_irs *= 2
    else: cell._output_irs = None
    with pytest.raises(ValueError): transport(args,closed)


def test_legal_inferred_size(baseline):
    args,closed = copy.deepcopy(baseline)
    for world,graph in [('sm',args[0]),('pm',args[1])]:
        for slot in range(3):
            for rank in ([0] if world == 'sm' else range(4)):
                cell = selected(args,world,slot,rank)
                cell.kwargs['size'][-1] = -1
                graph.node_kwargs(cell.node)['size'][-1] = -1
    text,result = transport(args,closed)
    assert len(result['reads']) == 15 and 'source_view_head_unit_output_reconstruct' in text


@pytest.mark.parametrize('fault', ['drop-q','drop-k','drop-v','drop-skip','reverse','ranks','dp',
    'dimensions','axis','source-slot','alias-slot','source-input','source-output','local-input','local-output',
    'partials','parameters','forged-q-gathers','facts','schedule','inverse','view-bw','linear-bw','gather-bw','partial-bw','exchange-bw'])
def test_mixed_frontier_provenance(baseline,fault):
    args,closed = copy.deepcopy(baseline); rows = closed['frontier_units']; row = rows[5]
    if fault.startswith('drop-'):
        slot = {'drop-q':0,'drop-k':1,'drop-v':2,'drop-skip':3}[fault]
        closed['frontier_units'] = [r for i,r in enumerate(rows) if i%4 != slot]
    elif fault == 'reverse': rows.reverse()
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'dp': row['unit'] = False
    elif fault == 'dimensions': row['dimensions']['H'] = 6.0
    elif fault == 'axis': row['gather_axis'] = 2
    elif fault == 'source-slot': row['source_output_slot'] = True
    elif fault == 'alias-slot': row['predecessor_source_output_slot'] = 2
    elif fault == 'source-input': row['source_step']['inputs'] = ()
    elif fault == 'source-output': row['source_step']['outputs'] = ()
    elif fault == 'local-input': row['local_steps'][0]['inputs'] = ()
    elif fault == 'local-output': row['local_steps'][0]['outputs'] = ()
    elif fault == 'partials': row['partial_steps'].pop()
    elif fault == 'parameters': row['parameters'][0]['pm_tids'].reverse()
    elif fault == 'forged-q-gathers': rows[4]['gather_steps'] = []
    elif fault == 'facts': row['facts_theorem'] = row['theorem'] = 'value_only'
    elif fault in ('schedule','inverse'):
        args[-1]['pm']['execution_to_source' if fault == 'schedule' else 'source_to_execution'].reverse()
    else:
        if fault == 'view-bw': cell = selected(args)
        elif fault == 'exchange-bw': cell = previous.selected(args)
        else: cell = previous.previous.selected(args,kind='AllGatherPrim' if fault == 'gather-bw' else 'FW_linear',slot=1 if fault == 'partial-bw' else 0)
        backward = next(n for n in reversed(args[1].nodes()) if args[1].node_opname(n).startswith('BW_'))
        args[1]._node2outputs[backward] = [args[1].node_inputs(cell.node)[0]]
    with pytest.raises(ValueError): transport(args,closed)


@pytest.fixture(scope='module')
def downstream():
    args = prepared(D=1,tp=3,seqlen=3,metadata='all-peers',successors=True)
    return args, predecessor.render(*args)[1]


def test_public_rank4_successors_not_consumed(downstream):
    args,_ = downstream
    text,result = api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units')] == [12,3,4,1]
    for row,axes in zip(result['units'],[(1,2),(1,3),(2,1)],strict=True):
        assert row['observed_consumer_ops'] == [['FW_transpose'],*([['AllToAllPrim']*3]*3)]
        assert len(row['sm_consumers']) == 1 and len(row['pm_consumers']) == 3
        actual = row['downstream_consumers']
        assert len(actual) == 4
        assert all((c['source_kwargs']['idim'],c['source_kwargs']['odim']) == axes for c in actual if c['op']=='AllToAllPrim')
    assert 'transpose_value_of_split' not in text and 'AllToAllSourceFaithful' not in text


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['input-bool','input-float','input-parent','input-tid','input-bounds','input-value',
    'input-absent','input-extra','input-ref','output-bool','output-tid'])
def test_rank4_successor_edges(downstream,world,fault):
    args,closed=copy.deepcopy(downstream)
    cell = next(c for c in args[3]._inputs[0 if world=='sm' else 1] if c.node.cid==284003)
    if fault == 'input-bool': cell._input_irs[0].shape=(True,*cell._input_irs[0].shape[1:])
    elif fault == 'input-float': cell._input_irs[0].shape=(1.0,*cell._input_irs[0].shape[1:])
    elif fault == 'input-parent': cell._input_irs[0].parent.tid+=1
    elif fault == 'input-tid': cell._input_irs[0].tid+=1
    elif fault == 'input-bounds': cell._input_irs[0].indmap=((0.0,1),*cell._input_irs[0].indmap[1:])
    elif fault == 'input-value': cell._input_irs[0].valmap=(0.0,1)
    elif fault == 'input-absent': cell._input_irs=None
    elif fault == 'input-extra': cell._input_irs*=2
    elif fault == 'input-ref': cell.inputs[0]=cell.inputs[0]._replace(mb=1)
    elif fault == 'output-bool': cell._output_irs[0].shape=(True,*cell._output_irs[0].shape[1:])
    else: cell._output_irs[0].tid+=1
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['coherent-drop-skip','coherent-drop-k','coherent-order','coherent-axis',
    'peer-parent','peer-head-factor','raw-ref','raw-writer','local-head-factor'])
def test_coherent_frontier_and_partition_mutants(baseline,fault):
    args,closed = copy.deepcopy(baseline)
    if fault.startswith('coherent-drop-') or fault == 'coherent-order':
        rows = closed['frontier_units']
        if fault == 'coherent-order':
            rows[0],rows[3] = rows[3],rows[0]; rows[4],rows[7] = rows[7],rows[4]
        else:
            slot = 3 if fault.endswith('skip') else 1
            rows = [r for i,r in enumerate(rows) if i%4 != slot]
        closed['frontier_units'] = rows
        closed['units'] = [r for r in rows if all(s['op']=='AllToAllPrim' for s in r['local_steps'])]
        closed['consumed_frontier_indices'] = [i for i,r in enumerate(rows) if r in closed['units']]
        for i,r in enumerate(rows): r['frontier_index']=i
        closed['retained_units'] = [r for r in rows if r['source_step']['op']=='FW_multiref']
        closed['deferred_units'] = [r for r in rows if all(s['op']=='ReduceScatterPrim' for s in r['local_steps'])]
    elif fault == 'coherent-axis':
        row=closed['frontier_units'][4]; row['gather_axis']=2; row['local_shape']=[1,2,3]
        row['dimensions'].update(S=2,H=3)
    else:
        cell=selected(args,rank=2)
        if fault == 'peer-parent': cell._output_irs[0].parent.tid+=1
        elif fault in ('peer-head-factor','local-head-factor'):
            if fault == 'local-head-factor': cell=selected(args,slot=1)
            y=cell._output_irs[0]
            y.parent.shape=(*y.parent.shape[:2],1,6)
            y.indmap=(*y.indmap[:2],(0,1),(0,6)); y.shape=(*y.shape[:2],1,6)
            cell.kwargs['size']=list(y.shape)
        elif fault == 'raw-ref': cell.inputs[0]=cell.inputs[0]._replace(rank=3)
        else: cell.outputs[0]=cell.outputs[0]._replace(v=2)
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('units', [(0,), (1,), (0, 1)])
@pytest.mark.parametrize('fault', ['omit', 'replace'])
def test_independent_carry_inventory(baseline, units, fault):
    from dataclasses import asdict
    from Verdict.runtime_lineage import _Index
    args, closed = copy.deepcopy(baseline)
    subject = api()
    indices = [_Index(v, raw) for v, raw in zip(args[:2], args[3]._inputs[:2], strict=True)]
    rows = []
    for row in closed['frontier_units']:
        if row['source_step']['op'] == 'FW_multiref' and row['unit'] in units:
            if fault == 'omit':
                continue
            # Substitute a real earlier residual skip, with its complete original
            # producer/ports. A self-consistent receipt is not the current carry.
            steps = []; slot = 1
            for index, rank in [(indices[0], 0), *[(indices[1], r) for r in row['ranks']]]:
                cell = next(c for c in index.raw.values() if c.node[3] == 27000 and c.rank == rank)
                port = subject.gathered._producer(index, cell.outputs[slot])
                step, actual_slot = subject._alias_producer(index, port, row['ranks'])
                assert actual_slot == slot
                steps.append(step)
            g = steps[0].outputs[slot]; ps = [s.outputs[slot] for s in steps[1:]]
            row.update(source_step=asdict(steps[0]), local_steps=[asdict(s) for s in steps[1:]],
                source_output_slot=slot, slot=slot, sm_output_tid=g.endpoint.tid,
                sm_output_ref=list(g.endpoint.ref), pm_output_tids=[p.endpoint.tid for p in ps],
                pm_output_refs=[list(p.endpoint.ref) for p in ps])
        rows.append(row)
    closed['frontier_units'] = rows
    for i, row in enumerate(rows): row['frontier_index'] = i
    closed['units'] = [r for r in rows if all(s['op'] == 'AllToAllPrim' for s in r['local_steps'])]
    closed['consumed_frontier_indices'] = [r['frontier_index'] for r in closed['units']]
    closed['retained_units'] = [r for r in rows if r['source_step']['op'] == 'FW_multiref']
    closed['deferred_units'] = [r for r in rows if all(s['op'] == 'ReduceScatterPrim' for s in r['local_steps'])]
    with pytest.raises(ValueError):
        transport(args, closed)


def test_public_allpeer_successor_metadata_and_reversal():
    args = prepared(D=1,tp=3,seqlen=3,successors=True,successor_metadata='all-peers')
    cells = [c for c in args[3]._inputs[1] if c.opname=='AllToAllPrim' and 284003 <= c.node.cid <= 284005]
    assert len(cells)==9 and all(len(c._input_irs)==3 for c in cells)
    observed=[]; original=predecessor.render
    def fresh(*six):
        result=original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh):
        _,result=api().render(*args)
    assert len(result['reads'])==12 and len(result['units'])==3
    closed=observed[0][1]
    cells[0]._input_irs.reverse()
    with pytest.raises(ValueError,match='producer/consumer'):
        transport(args,closed)
