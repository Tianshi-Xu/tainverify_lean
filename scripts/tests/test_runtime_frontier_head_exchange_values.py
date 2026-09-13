"""Portable head-exchange source candidates; actual/kernel gates belong to parent."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_projection_view_values as previous
from Verdict import runtime_frontier_projection_view_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_head_exchange_values'), 'head exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_head_exchange_values')


def fixture(**kwargs):
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    original = previous._successors
    def successors(sm, pm, snapshot, alias, tp):
        # K splits channels, so choose a divisible channel factor independently
        # of Q/V (which split heads/sequence). No production admission is relaxed.
        for graph in (sm, pm):
            for cell in graph.cells:
                if cell.opname != 'FW_view' or cell.node.cid != alias+8001: continue
                x = cell._input_irs[0]; C = tp
                y = IR(cell.outputs[0].tid, 'projection.heads.1',
                    (*x.parent.shape[:2], x.parent.shape[2]//C, C),
                    (*x.indmap[:2], (x.indmap[2][0]//C,x.indmap[2][1]//C), (0,C)))
                y.parent.tid = alias+12001
                cell._output_irs = [y]; cell.kwargs = dict(size=list(y.shape))
                graph.shapes[cell.outputs[0]] = y.shape
                if graph is pm:
                    text = snapshot['rank_sources'][str(cell.rank)]
                    lines = text.splitlines()
                    for i,line in enumerate(lines):
                        if line.strip().startswith('next_view_1 = '):
                            lines[i] = line[:line.index('.view(')]+'.view('+', '.join(map(str,y.shape))+')'
                    snapshot['rank_sources'][str(cell.rank)] = '\n'.join(lines)+'\n'
        original(sm, pm, snapshot, alias, tp)
        signature = 'nnscaler.runtime.adapter.nn.alltoall_alltoall'
        for cell in pm.cells:
            if cell.opname == 'AllToAllPrim' and alias+13000 <= cell.node.cid <= alias+13002:
                cell.ir.signature = signature
        for row in snapshot['adapter_source']:
            if alias+13000 <= row['ref']['source_cid'] <= alias+13002:
                row['primitive']['signature'] = signature
        for rank, text in snapshot['rank_sources'].items():
            snapshot['rank_sources'][rank] = '\n'.join(
                line.replace('nnscaler.runtime.adapter.all_to_all', signature)
                if line.strip().startswith('head_exchange_') else line for line in text.splitlines())+'\n'
        for cell in sm.cells:
            if cell.opname == 'FW_transpose': cell.ir.signature = 'torch.transpose'
        rows = []
        for producer in list(pm.cells):
            if producer.opname != 'AllToAllPrim' or not alias+13000 <= producer.node.cid <= alias+13002: continue
            slot = producer.node.cid-alias-13000
            x = producer._output_irs[0]; shape = list(x.parent.shape); bounds = list(x.indmap)
            shape[1],shape[2] = shape[2],shape[1]; bounds[1],bounds[2] = bounds[2],bounds[1]
            y = IR(alias+14000+slot, f'transposed.{slot}', tuple(shape), tuple(bounds))
            cell = NS(node=N('p',producer.rank,0,y.tid,'FW_transpose'),rank=producer.rank,opname='FW_transpose',
                inputs=producer.outputs[:],outputs=[T('p',producer.rank,0,y.tid,1)],kwargs=dict(dim0=1,dim1=2),
                _input_irs=[copy.deepcopy(x)],_output_irs=[y])
            cell.ir = NS(signature='torch.transpose',inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
            pm.cells.insert(pm.cells.index(producer)+1,cell); pm.shapes[cell.outputs[0]] = y.shape
            rows.append(dict(ref=dict(world='p',runtime_rank=cell.rank,microbatch=0,source_cid=y.tid,
                call_instance=0,op=cell.opname,origin='fixture'),source_irname=cell.opname,
                inputs=[tref(r) for r in cell.inputs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[]))
            snapshot['rank_sources'][str(cell.rank)] = snapshot['rank_sources'][str(cell.rank)].replace('\ndef _train_step',
                f'\n        head_transpose_{slot} = head_exchange_{slot}.transpose(1, 2)\ndef _train_step')
        fresh = build_snapshot([*snapshot['writers'],*rows])
        fresh.update({k:snapshot[k] for k in ('source','runtime_ndevs','rank_sources')})
        by_id = {writer_export_id(w['ref']):w for w in [*snapshot['adapter_source'],*rows]}
        fresh['adapter_source'] = [by_id[writer_export_id(w['ref'])] for w in fresh['writers']]
        bind_reducers(fresh); bind_adapters(fresh); snapshot.clear(); snapshot.update(fresh)
    with patch.object(previous, '_successors', side_effect=successors):
        return previous.fixture(successors=True, **kwargs)


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(**kwargs)


def test_public_head_exchange_tracer():
    subject = api(); args = prepared(); observed = []; original = predecessor.render
    def fresh(*six):
        result = original(*six); observed.append(result); return result
    with patch.object(predecessor, 'render', side_effect=fresh) as refresh:
        text, result = subject.render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed = observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [12,6,8,2,0]
    assert result['consumed_frontier_indices'] == [0,1,2,4,5,6]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in result['consumed_frontier_indices']:
            assert new is old
            continue
        assert new['input_frontier'] is old and new['predecessor_facts'] == old['facts_theorem']
        assert new['source_step'] == old['source_step'] and new['global_shape'] == old['global_shape']
        assert new['source_output_slot'] == 0 and new['pm_output_slots'] == [0,0]
        assert new['gather_axis'] == [2,3,1][i%4]
        assert new['local_shape'] == [[1,2,1,3],[1,2,3,1],[1,1,2,3]][i%4]
        assert new['dimensions'] == dict(D=2,T=2,**dict(zip(('B','S','H','C'),new['local_shape'])))
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
        assert new['observed_consumer_ops'] == [['FW_transpose']]*3
        assert len(new['sm_consumers']) == 1 and len(new['pm_consumers']) == 2
        assert len(new['downstream_consumers']) == 3
        assert f'have predecessor := {old["facts_theorem"]} ' in text
    for law in ('SourceRank4InnerExchange.axis1_output_facts','SourceRank4Exchange.axis1_output_facts',
                'SourceRank4MiddleExchange.axis2_output_facts'):
        assert text.count(law) == 2
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 12
    assert 'softmax_value_of_split' not in text and 'transpose_value_of_split' not in text
    for row in result['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][row['execution_index']:]
        assert len(row['input_refs']) == 2 and row['input_metadata'] == 'local-only'
        assert row['producer_metadata'] == 'all-peers' and row['input_parent_identity'] == 'local-only'
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


def selected(args, slot=0, rank=3, kind='AllToAllPrim', world='pm', alias=271003):
    offset = 13000 if kind == 'AllToAllPrim' or world == 'sm' else 14000
    return next(c for c in args[3]._inputs[0 if world == 'sm' else 1]
        if c.node.cid == alias+offset+slot and (world == 'sm' or c.rank == rank))


@pytest.mark.parametrize('slot', [0,1,2])
@pytest.mark.parametrize('fault', ['input-absent','input-extra','input-parent','input-shape-bool','input-shape-float',
    'input-value-bool','input-value-float','input-value-partial','output-absent','output-extra','output-parent',
    'output-shape-bool','output-shape-float','output-value-bool','output-value-float','output-value-partial',
    'output-bounds','output-rank','input-ref','output-ref','peer-parent','peer-shape-bool',
    'scope-local-bool','scope-rank-position','scope-ranks','scope-axis','scope-shape','scope-writer',
    'raw-axis-bool','raw-axis-float','raw-ranks','raw-kwargs','writer-call','writer-inputs','signature'])
def test_original_exchange_authority(baseline, slot, fault):
    from dataclasses import replace
    args, closed = copy.deepcopy(baseline); cell = selected(args,slot)
    if fault in ('input-absent','output-absent'):
        setattr(cell, '_'+fault.split('-')[0]+'_irs', None)
    elif fault in ('input-extra','output-extra'):
        getattr(cell, '_'+fault.split('-')[0]+'_irs').extend(copy.deepcopy(getattr(cell, '_'+fault.split('-')[0]+'_irs'))*2)
    elif fault.startswith(('input-shape-','output-shape-')):
        ir = getattr(cell, '_'+fault.split('-')[0]+'_irs')[0]
        ir.shape = (True if fault.endswith('bool') else float(ir.shape[0]), *ir.shape[1:])
    elif fault.startswith(('input-value-','output-value-')):
        getattr(cell, '_'+fault.split('-')[0]+'_irs')[0].valmap = {
            'bool':(False,1),'float':(0.0,1),'partial':(0,2)}[fault.split('-')[-1]]
    elif fault in ('input-parent','output-parent'):
        getattr(cell, '_'+fault.split('-')[0]+'_irs')[0].parent.tid += 1
    elif fault == 'output-bounds': cell._output_irs[0].indmap = ((0.0,1),*cell._output_irs[0].indmap[1:])
    elif fault == 'output-rank': cell._output_irs[0].shape = cell._output_irs[0].shape[:3]
    elif fault == 'input-ref': cell.inputs[0] = cell.inputs[0]._replace(mb=1)
    elif fault == 'output-ref': cell.outputs[0] = cell.outputs[0]._replace(v=2)
    elif fault.startswith('peer-'):
        peer = previous.selected(args,slot=slot,rank=2)
        if fault == 'peer-parent': peer._output_irs[0].parent.tid += 1
        else: peer._output_irs[0].shape = (True,*peer._output_irs[0].shape[1:])
    elif fault.startswith('scope-'):
        scope = args[1].collective_scopes[cell.node]
        changes = {'scope-local-bool':dict(local_index=True),'scope-rank-position':dict(local_index=3),
            'scope-ranks':dict(ranks=(1,3)), 'scope-axis':dict(params=(1,2) if slot else (1,3)),
            'scope-shape':dict(input_shape=(1,1,1,6)),'scope-writer':dict(source_writer='forged')}
        args[1].collective_scopes[cell.node] = replace(scope,**changes[fault])
    elif fault == 'raw-axis-bool': cell.kwargs['idim'] = True
    elif fault == 'raw-axis-float': cell.kwargs['odim'] = float(cell.kwargs['odim'])
    elif fault == 'raw-ranks': cell.kwargs['ranks'].reverse()
    elif fault == 'raw-kwargs': cell.kwargs['extra'] = 0
    elif fault == 'signature': cell.ir.signature = 'nnscaler.runtime.adapter.all_gather'
    else:
        writer = next(w for w in args[1]._collective_source['writers']
            if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
        if fault == 'writer-call': writer['ref']['call_instance'] += 1
        else: writer['inputs'].reverse()
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('world', ['sm','pm'])
@pytest.mark.parametrize('fault', ['signature','missing-ir','input-arity','output-arity','input-parent','output-parent',
    'parent-shape-float','shape-bool','bounds-float','value-partial'])
def test_incoming_view_original_authority(baseline, world, fault):
    args,closed = copy.deepcopy(baseline); cell = previous.selected(args,world)
    if fault == 'signature': cell.ir.signature = 'torch.reshape'
    elif fault == 'missing-ir': cell.ir = None
    elif fault == 'input-arity': cell._input_irs *= 2
    elif fault == 'output-arity': cell._output_irs *= 2
    elif fault == 'input-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 1
    elif fault == 'parent-shape-float': cell._output_irs[0].parent.shape = (1.0,*cell._output_irs[0].parent.shape[1:])
    elif fault == 'shape-bool': cell._output_irs[0].shape = (True,*cell._output_irs[0].shape[1:])
    elif fault == 'bounds-float': cell._output_irs[0].indmap = ((0.0,1),*cell._output_irs[0].indmap[1:])
    else: cell._output_irs[0].valmap = (0,2)
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault', ['source-input','source-output','local-input','local-output','history',
    'input-frontier','facts','source-slot','dimensions','ranks','positions','unit','axis',
    'coherent-drop-q','coherent-drop-k','coherent-drop-v','coherent-drop-skip','coherent-order','coherent-drop-dp',
    'schedule','inverse','view-bw','exchange-bw','remote-peer-bw','earlier-exchange-bw'])
def test_frontier_history_inventory_and_suffix(baseline, fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][4]
    if fault.startswith('source-') and fault != 'source-slot': row['source_step'][fault.split('-')[1]+'s'] = ()
    elif fault.startswith('local-'): row['local_steps'][0][fault.split('-')[1]+'s'] = ()
    elif fault == 'history': row['producer_history']['local_steps'] = []
    elif fault == 'input-frontier': row['input_frontier'] = copy.deepcopy(closed['frontier_units'][5]['input_frontier'])
    elif fault == 'facts': row['facts_theorem'] = row['theorem'] = 'value_only'
    elif fault == 'source-slot': row['source_output_slot'] = True
    elif fault == 'dimensions': row['dimensions']['C'] = 3.0
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'positions': row['positions'] = [0]
    elif fault == 'unit': row['unit'] = True
    elif fault == 'axis': row['gather_axis'] = 2
    elif fault.startswith('coherent-'):
        rows = closed['frontier_units']
        if fault == 'coherent-order': rows[0],rows[1] = rows[1],rows[0]
        elif fault == 'coherent-drop-dp': rows = rows[:4]
        else:
            slot = {'q':0,'k':1,'v':2,'skip':3}[fault.split('-')[-1]]
            rows = [r for i,r in enumerate(rows) if i%4 != slot]
        reclassify(closed,rows)
    elif fault in ('schedule','inverse'):
        args[-1]['pm']['execution_to_source' if fault == 'schedule' else 'source_to_execution'].reverse()
    else:
        if fault == 'view-bw': cell = previous.selected(args)
        elif fault == 'earlier-exchange-bw': cell = previous.previous.selected(args)
        else: cell = selected(args)
        backward = next(n for n in reversed(args[1].nodes()) if args[1].node_opname(n).startswith('BW_'))
        # Remote logical peer is also a read, not just receiver-local metadata.
        peer = 0 if fault == 'remote-peer-bw' else -1
        args[1]._node2outputs[backward] = [args[1].node_inputs(cell.node)[peer]]
    with pytest.raises(ValueError): transport(args,closed)


def reclassify(closed, rows):
    closed['frontier_units'] = rows
    for i,row in enumerate(rows):
        row['frontier_index'] = i
        if 'input_frontier' in row: row['input_frontier']['frontier_index'] = i
    closed['units'] = [r for r in rows if r['source_step']['op']=='FW_view']
    closed['retained_units'] = [r for r in rows if r['source_step']['op']=='FW_multiref']
    closed['consumed_frontier_indices'] = [r['frontier_index'] for r in closed['units']]
    closed['deferred_units'] = []


@pytest.mark.parametrize('units', [(0,), (1,), (0,1)])
def test_earlier_real_skip_substitution(baseline, units):
    from dataclasses import asdict
    from Verdict.runtime_lineage import _Index
    args,closed = copy.deepcopy(baseline)
    si,pi = [_Index(v,raw) for v,raw in zip(args[:2],args[3]._inputs[:2],strict=True)]
    for row in closed['retained_units']:
        if row['unit'] not in units: continue
        steps = []; slot = 1
        for index,rank in [(si,0),*[(pi,r) for r in row['ranks']]]:
            cell = next(c for c in index.raw.values() if c.node[3]==27000 and c.rank==rank)
            port = predecessor.gathered._producer(index,cell.outputs[slot])
            step,actual_slot = predecessor._alias_producer(index,port,row['ranks'])
            assert actual_slot == slot
            steps.append(step)
        g = steps[0].outputs[slot]; ps = [s.outputs[slot] for s in steps[1:]]
        row.update(source_step=asdict(steps[0]),local_steps=[asdict(s) for s in steps[1:]],source_output_slot=slot,slot=slot,
            sm_output_tid=g.endpoint.tid,sm_output_ref=list(g.endpoint.ref),
            pm_output_tids=[p.endpoint.tid for p in ps],pm_output_refs=[list(p.endpoint.ref) for p in ps])
    reclassify(closed,closed['frontier_units'])
    with pytest.raises(ValueError,match='inventory' if len(units)==2 else 'DP frontier cover'):
        transport(args,closed)


@pytest.mark.parametrize('world', ['sm','pm'])
@pytest.mark.parametrize('fault', ['input-absent','input-extra','input-parent','input-ref','input-bool',
    'output-parent-shape','output-absent','output-value','output-bounds'])
def test_unconsumed_rank4_transpose_edges(baseline, world, fault):
    args,closed = copy.deepcopy(baseline); cell = selected(args,world=world,kind='FW_transpose')
    assert cell.ir.signature == 'torch.transpose'
    if fault == 'input-absent': cell._input_irs = None
    elif fault == 'input-extra': cell._input_irs *= 2
    elif fault == 'input-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'input-ref': cell.inputs[0] = cell.inputs[0]._replace(mb=1)
    elif fault == 'input-bool': cell._input_irs[0].shape = (True,*cell._input_irs[0].shape[1:])
    elif fault == 'output-parent-shape': cell._output_irs[0].parent.shape = (1.0,*cell._output_irs[0].parent.shape[1:])
    elif fault == 'output-absent': cell._output_irs = None
    elif fault == 'output-value': cell._output_irs[0].valmap = (0.0,1)
    else: cell._output_irs[0].indmap = ((0,True),*cell._output_irs[0].indmap[1:])
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('metadata', ['local-only','all-peers'])
def test_dynamic_three_peer_public_and_reversal(metadata):
    args = prepared(D=1,tp=3,seqlen=3,alias_tid=390019,successor_metadata=metadata)
    observed=[]; original=predecessor.render
    def fresh(*six):
        result=original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh:
        text,result=api().render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units')] == [9,3,4,1]
    assert [r['gather_axis'] for r in result['units']] == [2,3,1]
    assert all(r['input_metadata']==metadata and len(r['input_refs'])==3 for r in result['reads'])
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split')==9
    for slot in range(3):
        badargs,closed=copy.deepcopy((args,observed[0][1]))
        cell=selected(badargs,slot=slot,rank=2,alias=390019)
        if metadata=='all-peers': cell._input_irs.reverse()
        else: cell._input_irs=copy.deepcopy(selected(badargs,slot=slot,rank=0,alias=390019)._input_irs)
        with pytest.raises(ValueError): transport(badargs,closed)
