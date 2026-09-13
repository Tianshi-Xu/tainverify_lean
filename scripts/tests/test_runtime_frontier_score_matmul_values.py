"""Portable original ordered score frontier; no capture/kernel claims."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_middle_exchange_values as previous
from Verdict import runtime_frontier_middle_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_score_matmul_values'), 'score matmul renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_score_matmul_values')


def fixture(**kwargs):
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    kwargs = dict({'D': 2, 'tp': 3, 'seqlen': 3}, **kwargs)
    sm, pm, authority = previous.fixture(**kwargs)
    alias = kwargs.get('alias_tid', 271003); tp = kwargs['tp']
    snapshot = copy.deepcopy(authority[2]); rows = []; adapters = []
    for graph, world in ((sm, 's'), (pm, 'p')):
        scores = [c for c in graph.cells if c.node.cid == alias+16000]
        for score in scores:
            x, k = score._input_irs
            shape = (*x.parent.shape[:3], k.parent.shape[3])
            bounds = (*x.indmap[:3], k.indmap[3])
            y = IR(score.outputs[0].tid, 'scores', shape, bounds)
            score._output_irs = [y]; graph.shapes[score.outputs[0]] = y.shape
        for score in scores:
            rank = score.rank; x = score._output_irs[0]
            shape = x.parent.shape; bounds = list(x.indmap)
            kind = 'FW_div'; sig = 'torch.div'; kw = dict(rounding_mode=None, __consts=[4.0])
            refs = score.outputs[:]; ins = [copy.deepcopy(x)]
            if world == 'p':
                ranks = list(range(rank//tp*tp, (rank//tp+1)*tp))
                kind = 'AllToAllPrim'; sig = 'nnscaler.runtime.adapter.nn.alltoall_alltoall'
                kw = dict(idim=1, odim=3, ranks=ranks)
                width = shape[3]//tp; assert width*tp == shape[3]
                bounds[1] = (0, shape[1]); bounds[3] = (rank%tp*width, (rank%tp+1)*width)
                refs = [score.outputs[0]._replace(rank=r) for r in ranks]
                if kwargs.get('metadata', 'local-only') == 'all-peers':
                    ins = [copy.deepcopy(next(c._output_irs[0] for c in scores if c.rank == r)) for r in ranks]
            y = IR(alias+18000, 'scores' if world=='p' else 'scaled_scores', shape, tuple(bounds))
            if world == 'p': y.parent.tid = x.parent.tid
            c = NS(node=N(world, rank, 0, y.tid, kind), rank=rank, opname=kind,
                inputs=refs, outputs=[T(world, rank, 0, y.tid, 1)], kwargs=kw, _input_irs=ins, _output_irs=[y])
            c.ir = NS(signature=sig, inputs=lambda c=c: c._input_irs, outputs=lambda c=c: c._output_irs)
            graph.cells.insert(graph.cells.index(score)+1, c); graph.shapes[c.outputs[0]] = y.shape
            # The V operand's first matmul requires a genuine, unavailable next-
            # stage result. No probability value or producer is assumed by proofs.
            v = next(c for c in graph.cells if c.rank==rank and c.node.cid==alias+(16002 if world=='s' else 17002))
            v.inputs = [c.outputs[0], v.inputs[-1]]
            v._input_irs = [copy.deepcopy(y), v._input_irs[-1]]
            graph.cells.remove(v)
            writers = [p for p in graph.cells if any(ref in p.outputs for ref in v.inputs)]
            graph.cells.insert(max(graph.cells.index(p) for p in writers)+1, v)
            if world == 's': continue
            row = dict(ref=dict(world=world, runtime_rank=rank, microbatch=0, source_cid=y.tid,
                call_instance=0, op=kind, origin='fixture'), source_irname=kind,
                inputs=[tref(r) for r in refs], outputs=[tref(r) for r in c.outputs], parameter_grad_tids=[], adapter_kwargs=kw.copy())
            adapter = copy.deepcopy(row); adapter['inputs'] = [tref(score.outputs[0])]
            adapter['primitive'] = dict(kind=kind, forward=True, kwargs=kw.copy(), signature=sig,
                generated_inputs=['projection_next_0'], generated_outputs=['after_score'])
            rows.append(row); adapters.append(adapter)
            for inventory in ('writers', 'adapter_source'):
                w = next(w for w in snapshot[inventory] if w['ref']['runtime_rank']==rank and w['ref']['source_cid']==v.node.cid)
                w['inputs'] = [tref(r) for r in v.inputs]
                snapshot[inventory].remove(w)
                # New next-stage writer is inserted before the V consumer below.
                (rows if inventory=='writers' else adapters).append(w)
            lines = [line for line in snapshot['rank_sources'][str(rank)].splitlines()
                     if not line.strip().startswith('after_post_2 =')]
            text = '\n'.join(lines)+'\n'
            snapshot['rank_sources'][str(rank)] = text.replace('\ndef _train_step',
                f'\n        after_score = {sig}(projection_next_0, idim=1, odim=3, ranks={ranks})'
                '\n        after_post_2 = torch.matmul(after_score, projection_next_2)\ndef _train_step')
    fresh = build_snapshot([*snapshot['writers'], *rows])
    fresh.update({k: snapshot[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    byid = {writer_export_id(w['ref']): w for w in [*snapshot['adapter_source'], *adapters]}
    fresh['adapter_source'] = [byid[writer_export_id(w['ref'])] for w in fresh['writers']]
    bind_reducers(fresh); bind_adapters(fresh)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), fresh, *authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(**kwargs)


def test_public_score_matmul_tracer():
    subject = api(); args = prepared(); observed = []; original = predecessor.render
    def fresh(*six):
        result = original(*six); observed.append(result); return result
    with patch.object(predecessor, 'render', side_effect=fresh) as refresh:
        text, result = subject.render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args, args, strict=True))
    closed = observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [7,2,6,2,2]
    assert result['consumed_frontier_indices'] == [0,1,4,5]
    assert result['retained_units'] == [result['frontier_units'][i] for i in (2,5)]
    assert [d['frontier_index'] for d in result['deferred_units']] == [2,6]
    for u,new in enumerate(result['units']):
        left,right = closed['frontier_units'][4*u:4*u+2]
        assert new['input_frontiers'][0] is left and new['input_frontiers'][1] is right
        assert new['predecessors'] == [left['facts_theorem'], right['facts_theorem']]
        assert new['ordered_join']['frontier_indices'] == [4*u,4*u+1]
        assert new['ordered_join']['sm_input_refs'] == [left['sm_output_ref'],right['sm_output_ref']]
        assert new['input_refs'] == [[q,k] for q,k in zip(left['pm_output_refs'],right['pm_output_refs'],strict=True)]
        assert new['dimensions'] == dict(D=2,T=3,B=1,H=1,Q=3,K=3,M=3)
        assert new['global_shape'] == [2,3,3,3] and new['local_shape'] == [1,1,3,3]
        assert new['gather_axis'] == new['output_gather_axis'] == 1
        assert new['source_output_slot'] == new['slot'] == 0 and new['pm_output_slots'] == [0,0,0]
        assert new['observed_consumer_ops'] == [['FW_div'],['AllToAllPrim']*3,['AllToAllPrim']*3,['AllToAllPrim']*3]
        assert all(c['value_proved'] is False for c in new['downstream_consumers'])
        assert new['downstream_consumers'][0]['source_kwargs'] == dict(rounding_mode=None,__consts=[4.0])
        assert all(c['source_kwargs']['odim']==3 for c in new['downstream_consumers'][1:])
        v = result['frontier_units'][3*u+1]
        assert v is closed['frontier_units'][4*u+2]
        assert v['gather_axis'] is None and v['layout']=='replicated_within_dp'
        deferred = result['deferred_units'][u]
        assert deferred['source_boundary'] is v and deferred['missing_operand_refs']
        assert deferred['reason']=='first-original-FW_matmul-missing-operand' and deferred['value_proved'] is False
        assert result['frontier_units'][3*u+2] is closed['frontier_units'][4*u+3]
    assert text.count('SourceMatmulRead.matmul_value_of_split') == 7
    assert text.count('source_matmul_unit_output_reconstruct') == 2
    assert '∀ z ∈' in text and 'allGatherPrimDimN 1 3 0' in text
    for r in result['reads']:
        assert r['op']=='FW_matmul' and r['source_signature']=='torch.matmul'
        assert r['operand_nonwrite_source_indices']==args[-1][r['world']]['execution_to_source'][r['execution_index']:]
    for bad in ('div_value_of_split','SourcePrimitiveRead','sorry','admit','native_decide','axiom ','(hshape :','(houtput :'):
        assert bad not in text
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    assert result['lean_bytes']==len(text.encode())
    with pytest.raises(TypeError): subject.render(*args,closed)


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def transport(args, closed):
    with patch.object(predecessor, 'render', return_value=('',closed)) as refresh:
        result = api().render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    return result


def selected(args, world='pm', rank=5, alias=271003):
    return next(c for c in args[3]._inputs[0 if world=='sm' else 1]
                if c.node.cid==alias+16000 and (world=='sm' or c.rank==rank))


def boundary(args, world='pm'):
    from Verdict.runtime_lineage import _Index
    index = _Index(args[0 if world=='sm' else 1],args[3]._inputs[0 if world=='sm' else 1])
    cell = selected(args,world)
    ports = [api()._transpose._producer(index,r) for r in cell.inputs]
    return index,cell,ports,api()._matmul(index,cell,ports)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['signature','signature-type','missing-signature','missing-ir',
    'input-missing','output-missing','input-extra','output-extra','input-parent','input-tid','output-tid',
    'input-ref','output-ref','shape-bool','shape-float','rank','parent-shape-float','parent-id-bool',
    'bounds-bool','bounds-float','bounds-negative','bounds-overrun','value-bool','value-float','value-partial',
    'param-type','grad-type','kwargs','consts','collective-scope','chunk-scope','wred-scope'])
def test_new_read_raw_authority(baseline,world,fault):
    args,_ = copy.deepcopy(baseline); index,cell,ports,step = boundary(args,world)
    x,y = cell._input_irs[0],cell._output_irs[0]
    if fault=='signature': cell.ir.signature='torch.bmm'
    elif fault=='signature-type': cell.ir.signature=123
    elif fault=='missing-signature': del cell.ir.signature
    elif fault=='missing-ir': cell.ir=None
    elif fault=='input-missing': cell._input_irs=None
    elif fault=='output-missing': cell._output_irs=None
    elif fault=='input-extra': cell._input_irs*=2
    elif fault=='output-extra': cell._output_irs*=2
    elif fault=='input-parent': x.parent.tid+=1
    elif fault=='input-tid': x.tid+=1
    elif fault=='output-tid': y.tid+=1
    elif fault=='input-ref': cell.inputs[0]=cell.inputs[0]._replace(mb=1)
    elif fault=='output-ref': cell.outputs[0]=cell.outputs[0]._replace(v=2)
    elif fault=='shape-bool': y.shape=(True,*y.shape[1:])
    elif fault=='shape-float': y.shape=(float(y.shape[0]),*y.shape[1:])
    elif fault=='rank': y.shape=y.shape[:3]
    elif fault=='parent-shape-float': y.parent.shape=(float(y.parent.shape[0]),*y.parent.shape[1:])
    elif fault=='parent-id-bool': y.parent.tid=True
    elif fault.startswith('bounds-'):
        lo={'bounds-bool':False,'bounds-float':0.0,'bounds-negative':-1,'bounds-overrun':0}[fault]
        hi=y.parent.shape[0]+1 if fault=='bounds-overrun' else y.indmap[0][1]
        y.indmap=((lo,hi),*y.indmap[1:])
    elif fault.startswith('value-'): y.valmap={'value-bool':(False,1),'value-float':(0.0,1),'value-partial':(0,2)}[fault]
    elif fault=='param-type': y.param=0
    elif fault=='grad-type': y.is_grad=lambda:0
    elif fault=='kwargs': cell.kwargs['extra']=0
    elif fault=='consts': cell.kwargs['__consts']=[1]
    else:
        key={'collective-scope':'collective_scopes','chunk-scope':'chunk_scopes','wred-scope':'wred_scopes'}[fault]
        setattr(index.view,key,dict(getattr(index.view,key,{}),**{}))
        getattr(index.view,key)[cell.node]=NS()
    with pytest.raises(ValueError): api()._read(index,world,step,args[-1][world])


@pytest.mark.parametrize('fault',['export','writer-inputs','writer-outputs','call-bool','call-negative','call-missing'])
def test_read_original_export(baseline,fault):
    args,_ = copy.deepcopy(baseline); index,cell,ports,step=boundary(args)
    writer=next(w for w in index.view._collective_source['writers'] if w['ref']['source_cid']==cell.node.cid and w['ref']['runtime_rank']==cell.rank)
    if fault=='export': writer['export_id']='forged'
    elif fault=='writer-inputs': writer['inputs'].reverse()
    elif fault=='writer-outputs': writer['outputs']=[]
    elif fault=='call-bool': writer['ref']['call_instance']=False
    elif fault=='call-negative': writer['ref']['call_instance']=-1
    else: writer['ref'].pop('call_instance')
    with pytest.raises((ValueError,KeyError)): api()._read(index,'pm',step,args[-1]['pm'])


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('operand',[0,1])
def test_read_full_backward_suffix(baseline,world,operand):
    args,_=copy.deepcopy(baseline); index,cell,ports,step=boundary(args,world)
    bw=next(n for n in reversed(index.view.nodes()) if index.view.node_opname(n).startswith('BW_'))
    index.view._node2outputs[bw]=[index.view.node_inputs(cell.node)[operand]]
    with pytest.raises(ValueError): api()._read(index,world,step,args[-1][world])


@pytest.mark.parametrize('fault',['descriptor','ordered-operands','schedule','inverse','output-shape'])
def test_read_fresh_step(baseline,fault):
    from dataclasses import replace
    args,_=copy.deepcopy(baseline); index,cell,ports,step=boundary(args)
    if fault=='descriptor': step=replace(step,inputs=(replace(ports[0],parent_name='forged'),ports[1]))
    elif fault=='ordered-operands': step=replace(step,inputs=tuple(reversed(ports)))
    elif fault=='output-shape': step=replace(step,outputs=(replace(step.outputs[0],parent_shape=(1,1,1,1)),))
    else: args[-1]['pm']['execution_to_source' if fault=='schedule' else 'source_to_execution'].reverse()
    with pytest.raises(ValueError): api()._read(index,'pm',step,args[-1]['pm'])


def reclassify(closed, rows):
    closed['frontier_units']=rows
    for i,row in enumerate(rows):
        current=row
        while 'input_frontier' in current:
            current['frontier_index']=i; current=current['input_frontier']
        row['frontier_index']=i
    closed['units']=[r for r in rows if r['facts_theorem'].startswith('frontierMiddleExchangeUnitFacts_')]
    closed['consumed_frontier_indices']=[i for i,r in enumerate(rows) if any(r is u for u in closed['units'])]
    closed['retained_units']=[r for r in rows if r['source_step']['op']=='FW_multiref' or r['layout']=='replicated_within_dp']
    closed['deferred_units']=[r for r in rows if not any(r is u for u in closed['units']+closed['retained_units'])]


@pytest.mark.parametrize('index',range(8))
@pytest.mark.parametrize('fault',['facts-missing','facts-rewritten','history','descriptor'])
def test_complete_incoming_records(baseline,index,fault):
    with patch.object(previous,'transport',side_effect=transport):
        previous.test_complete_incoming_records(baseline,index,fault)


@pytest.mark.parametrize('fault',['coherent-drop-q','coherent-drop-k','coherent-drop-v','coherent-drop-skip',
    'coherent-order','coherent-drop-dp','schedule','inverse','remote-peer-bw','earlier-exchange-bw'])
def test_source_derived_inventory(baseline,fault):
    head_tests=previous.previous.previous.previous
    with patch.object(head_tests,'transport',side_effect=transport),patch.object(head_tests,'reclassify',side_effect=reclassify):
        head_tests.test_frontier_history_inventory_and_suffix(baseline,fault)


@pytest.mark.parametrize('units',[(0,),(1,),(0,1)])
def test_earlier_same_shaped_carry_rejected(baseline,units):
    head_tests=previous.previous.previous.previous
    args,closed=copy.deepcopy(baseline)
    # The older helper mutates every retained row; at this mixed boundary only
    # original multiref rows are residual carries (V is a rank-four replica).
    closed['retained_units']=[r for r in closed['retained_units'] if r['source_step']['op']=='FW_multiref']
    with patch.object(head_tests,'transport',side_effect=transport),patch.object(head_tests,'reclassify',side_effect=reclassify):
        head_tests.test_earlier_real_skip_substitution((args,closed),units)


@pytest.mark.parametrize('key',['units','retained_units','deferred_units','consumed_frontier_indices'])
def test_incoming_classification_not_authority(baseline,key):
    args,closed=copy.deepcopy(baseline); closed[key]=[]
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('slot,stage',[(0,'first'),(1,'first'),(2,'first'),(1,'second'),(2,'gather')])
@pytest.mark.parametrize('fault',['signature','parent','shape','remote-descriptor'])
def test_reauthenticate_original_transposes_and_v(baseline,slot,stage,fault):
    with patch.object(previous,'transport',side_effect=transport):
        previous.test_reauthenticate_original_transposes_and_v(baseline,slot,stage,fault)


@pytest.mark.parametrize('fault',['signature','peer-parent','peer-order','descriptor','proof'])
def test_reauthenticate_middle_exchange(baseline,fault):
    args,closed=copy.deepcopy(baseline); cell=previous.selected(args)
    if fault=='signature': cell.ir.signature='torch.transpose'
    elif fault=='peer-parent': cell._input_irs[0].parent.tid+=1
    elif fault=='peer-order': cell.inputs.reverse()
    elif fault=='descriptor': closed['frontier_units'][5]['local_steps'][0]['inputs'][0]['parent_name']='wrong-remote'
    else: closed['frontier_units'][5]['facts_theorem']='wrong_facts'
    with pytest.raises(ValueError): transport(args,closed)


def unit_inputs(args,closed):
    from Verdict.runtime_lineage import _Index
    si,pi=[_Index(v,raw) for v,raw in zip(args[:2],args[3]._inputs[:2],strict=True)]
    left,right=closed['frontier_units'][4:6]
    gc=selected(args,'sm')
    global_=api()._matmul(si,gc,[api()._transpose._producer(si,r) for r in gc.inputs])
    locals_=[]
    for rank in left['ranks']:
        cell=selected(args,rank=rank)
        locals_.append(api()._matmul(pi,cell,[api()._transpose._producer(pi,r) for r in cell.inputs]))
    names={s.node:f'read_{i}' for i,s in enumerate([global_,*locals_])}
    join=dict(frontier_indices=[4,5],emitted_at_frontier_index=4,unit=left['unit'],ranks=left['ranks'],
        sm_input_refs=[left['sm_output_ref'],right['sm_output_ref']],
        pm_ordered_input_refs=[[q,k] for q,k in zip(left['pm_output_refs'],right['pm_output_refs'],strict=True)],
        sm_node=list(global_.node),pm_nodes=[list(s.node) for s in locals_])
    return si,pi,left,right,global_,locals_,names,join


@pytest.mark.parametrize('fault',['sm-parent','pm-parent','peer-order','both-peer-order','left-peer','right-peer','both-operands'])
def test_original_unit_pairing(baseline,fault):
    from dataclasses import replace
    args,closed=copy.deepcopy(baseline)
    si,pi,left,right,g,ps,names,join=unit_inputs(args,closed)
    assert hasattr(api(),'_unit'), 'source-bound matmul unit guard missing'
    if fault=='sm-parent': si.raw[g.node]._output_irs[0].parent.tid+=1
    elif fault=='pm-parent': pi.raw[ps[-1].node]._output_irs[0].parent.tid+=1
    elif fault=='peer-order': ps.reverse()
    elif fault=='both-peer-order':
        for row in (left,right):
            row['pm_output_refs'].reverse(); row['pm_output_tids'].reverse(); row['local_steps'].reverse()
        ps.reverse()
    elif fault=='both-operands': ps=[replace(s,inputs=tuple(reversed(s.inputs))) for s in ps]
    else:
        operand=0 if fault=='left-peer' else 1
        inputs=list(ps[-1].inputs); inputs[operand]=ps[0].inputs[operand]
        ps[-1]=replace(ps[-1],inputs=tuple(inputs))
    with pytest.raises(ValueError): api()._unit(si,pi,left,right,g,ps,names,join)


@pytest.mark.parametrize('kind',['absent','FW_unknown','FW_view','AllToAllPrim','FW_matmul'])
def test_consumer_classification_is_explicit(kind):
    assert hasattr(api(),'_classification'), 'explicit consumer classifier missing'
    groups=[[] if kind=='absent' else [NS(opname=kind)] for _ in range(4)]
    assert api()._classification(False,groups)==('ready' if kind=='FW_matmul' else 'deferred')
    assert api()._classification(True,groups)=='retained'


@pytest.mark.parametrize('fault',['signature','shape-float','value-partial','input-parent','scope'])
def test_division_inventory_stays_source_bound(baseline,fault):
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); si=_Index(args[0],args[3]._inputs[0])
    cell=next(c for c in si.raw.values() if c.node.cid==271003+18000)
    if fault=='signature': cell.ir.signature='torch.mul'
    elif fault=='shape-float': cell._output_irs[0].shape=tuple(float(d) for d in cell._output_irs[0].shape)
    elif fault=='value-partial': cell._output_irs[0].valmap=(0,2)
    elif fault=='input-parent': cell._input_irs[0].parent.tid+=1
    else: args[0].chunk_scopes={cell.node:NS()}
    with pytest.raises(ValueError): api()._successor(si,cell)


@pytest.mark.parametrize('metadata',['local-only','all-peers'])
def test_dynamic_non_square_public(metadata):
    args=prepared(D=1,alias_tid=390019,seqlen=6,metadata=metadata,successor_metadata=metadata)
    text,result=api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[4,1,3,1,1]
    row=result['units'][0]
    assert row['dimensions']==dict(D=1,T=3,B=1,H=1,Q=6,K=3,M=6)
    assert row['global_shape']==[1,3,6,6] and row['local_shape']==[1,1,6,6]
    assert all(c['input_metadata']==metadata for c in row['downstream_consumers'][1:])
    assert text.count('source_matmul_unit_output_reconstruct')==1


@pytest.mark.parametrize('world',['sm','pm'])
def test_score_output_original_parent_cross_binding(baseline,world):
    args,closed=copy.deepcopy(baseline)
    selected(args,world)._output_irs[0].parent.tid+=123
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['signature','shape-float','input-parent','scope','arity','kwargs'])
def test_next_inventory_guards(baseline,world,fault):
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); index=_Index(args[0 if world=='sm' else 1],args[3]._inputs[0 if world=='sm' else 1])
    cell=next(c for c in index.raw.values() if c.node.cid==271003+18000 and (world=='sm' or c.rank==5))
    if fault=='signature': cell.ir.signature='torch.floor_divide'
    elif fault=='shape-float': cell._output_irs[0].shape=(float(cell._output_irs[0].shape[0]),*cell._output_irs[0].shape[1:])
    elif fault=='input-parent': cell._input_irs[0].parent.tid+=1
    elif fault=='scope':
        index.view.chunk_scopes=dict(getattr(index.view,'chunk_scopes',{}))
        index.view.chunk_scopes[cell.node]=NS()
    elif fault=='arity': cell._input_irs=[]
    else: cell.kwargs['extra']=0
    with pytest.raises((ValueError,KeyError)): api()._successor(index,cell)


@pytest.mark.parametrize('fault',['both-operands','peer','source-both-operands','local-order'])
def test_ordered_pair_and_peer_reversal(baseline,fault):
    from dataclasses import replace
    args,closed=copy.deepcopy(baseline); index,cell,ports,step=boundary(args)
    if fault=='both-operands':
        step=replace(step,inputs=tuple(reversed(ports)))
        with pytest.raises(ValueError): api()._read(index,'pm',step,args[-1]['pm'])
    elif fault=='peer':
        other=selected(args,rank=4)
        peer=api()._transpose._producer(index,other.inputs[0])
        step=replace(step,inputs=(peer,ports[1]))
        with pytest.raises(ValueError): api()._read(index,'pm',step,args[-1]['pm'])
    elif fault=='source-both-operands':
        for world in ('sm','pm'):
            raw=selected(args,world); raw.inputs.reverse(); raw._input_irs.reverse()
        with pytest.raises(ValueError): transport(args,closed)
    else:
        for r in closed['frontier_units'][4:6]:
            r['pm_output_refs'].reverse(); r['pm_output_tids'].reverse(); r['local_steps'].reverse(); r['ranks'].reverse()
        with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('kind',[None,'FW_unknown','FW_transpose','AllToAllPrim','FW_matmul'])
def test_unavailable_unknown_explicitly_deferred(kind):
    groups=[[] if kind is None else [NS(opname=kind)] for _ in range(4)]
    assert api()._ready(groups) is (kind=='FW_matmul')


@pytest.mark.parametrize('metadata',['local-only','all-peers'])
def test_dynamic_public_original_metadata(metadata):
    args=prepared(D=1,alias_tid=390019,metadata=metadata,successor_metadata=metadata)
    text,result=api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[4,1,3,1,1]
    assert all(c['input_metadata']==metadata for c in result['units'][0]['downstream_consumers'][1:])
    assert result['units'][0]['dimensions']['D']==1
    assert 'InitialParameterValues s p' in text


def test_actual_backend_contract_is_reused(baseline):
    subject=api(); args,closed=copy.deepcopy(baseline)
    with patch.object(subject.backend,'_unit',wraps=subject.backend._unit) as unit, patch.object(subject.backend,'_read',wraps=subject.backend._read) as read:
        _,result=transport(args,closed)
    assert unit.call_count==len(result['units']) and read.call_count==len(result['reads'])
    for call,new in zip(unit.call_args_list,result['units'],strict=True):
        assert len(call.args)==6 and call.args[0] is new['input_frontiers'][0] and call.args[1] is new['input_frontiers'][1]
        assert call.args[5] is new['ordered_join']
