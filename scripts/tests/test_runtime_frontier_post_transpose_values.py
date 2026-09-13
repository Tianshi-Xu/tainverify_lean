"""Portable source-authenticated mixed second-transpose/AllGather frontier."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_projection_transpose_values as previous
from Verdict import runtime_frontier_projection_transpose_values as predecessor


AG = 'nnscaler.runtime.adapter.nn.allgather_reducescatter'


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_post_transpose_values'), 'mixed post transpose renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_post_transpose_values')


def fixture(metadata='local-only', next_exchange=False, **kwargs):
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(next_consumers=True, next_metadata=metadata, **kwargs)
    snapshot = copy.deepcopy(authority[2]); alias = kwargs.get('alias_tid', 271003)
    old = 'nnscaler.runtime.adapter.all_gather'
    for cell in pm.cells:
        if cell.opname == 'AllGatherPrim' and cell.node.cid == alias+16002:
            cell.ir.signature = AG
    for row in snapshot['adapter_source']:
        if row['ref']['source_cid'] == alias+16002:
            row['primitive']['signature'] = AG
    for rank,text in snapshot['rank_sources'].items():
        snapshot['rank_sources'][rank] = '\n'.join(line.replace(old+'(', AG+'(')
            if line.strip().startswith('projection_next_2 =') else line for line in text.splitlines())+'\n'
    rows = []; new_adapters = []
    for graph,world in ((sm,'s'),(pm,'p')):
        for producer in list(graph.cells):
            if producer.node.cid not in (alias+16001,alias+16002): continue
            # SM V already has the actual downstream matmul (no global gather).
            if world == 's' and producer.node.cid == alias+16002: continue
            slot = producer.node.cid-alias-16000; x=producer._output_irs[0]
            y = IR(alias+17000+slot, f'downstream.{slot}', x.parent.shape, x.indmap)
            cell=NS(node=N(world,producer.rank,0,y.tid,'FW_matmul'),rank=producer.rank,opname='FW_matmul',
                inputs=producer.outputs*2, outputs=[T(world,producer.rank,0,y.tid,1)],kwargs=dict(__consts=[]),
                _input_irs=[copy.deepcopy(x),copy.deepcopy(x)],_output_irs=[y])
            cell.ir=NS(signature='torch.matmul',inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
            call=f'torch.matmul(projection_next_{slot}, projection_next_{slot})'
            if next_exchange and world=='p' and slot==1:
                tp=kwargs.get('tp',2); rank=producer.rank; ranks=list(range(rank//tp*tp,(rank//tp+1)*tp))
                assert x.parent.shape[1]%tp==0
                bounds=list(x.indmap); width=x.parent.shape[1]//tp
                bounds[2]=(0,x.parent.shape[2]); bounds[1]=(rank%tp*width,(rank%tp+1)*width)
                y=IR(y.tid,x.parent.name,x.parent.shape,tuple(bounds)); y.parent.tid=x.parent.tid
                cell.opname='AllToAllPrim'; cell.node=N(world,rank,0,y.tid,cell.opname)
                cell.kwargs=dict(idim=2,odim=1,ranks=ranks)
                cell.inputs=[producer.outputs[0]._replace(rank=r) for r in ranks]
                cell._input_irs=[copy.deepcopy(x)] if metadata=='local-only' else [copy.deepcopy(next(
                    c._output_irs[0] for c in graph.cells if c.outputs==[ref])) for ref in cell.inputs]
                cell._output_irs=[y]; cell.ir.signature='nnscaler.runtime.adapter.nn.alltoall_alltoall'
                call=f'{cell.ir.signature}(projection_next_{slot}, idim=2, odim=1, ranks={ranks})'
            graph.cells.insert(graph.cells.index(producer)+1,cell); graph.shapes[cell.outputs[0]]=y.shape
            if world=='s': continue
            row=dict(ref=dict(world=world,runtime_rank=cell.rank,microbatch=0,source_cid=y.tid,
                call_instance=0,op=cell.opname,origin='fixture'),source_irname=cell.opname,
                inputs=[tref(r) for r in cell.inputs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[])
            adapter=copy.deepcopy(row)
            if cell.opname=='AllToAllPrim':
                row['adapter_kwargs']=cell.kwargs.copy(); adapter['adapter_kwargs']=cell.kwargs.copy()
                adapter['inputs']=[tref(producer.outputs[0])]
                adapter['primitive']=dict(kind=cell.opname,forward=True,kwargs=cell.kwargs.copy(),signature=cell.ir.signature,
                    generated_inputs=[f'projection_next_{slot}'],generated_outputs=[f'after_post_{slot}'])
            rows.append(row); new_adapters.append(adapter)
            snapshot['rank_sources'][str(cell.rank)]=snapshot['rank_sources'][str(cell.rank)].replace('\ndef _train_step',
                f'\n        after_post_{slot} = {call}\ndef _train_step')
    fresh=build_snapshot([*snapshot['writers'],*rows])
    fresh.update({k:snapshot[k] for k in ('source','runtime_ndevs','rank_sources')})
    byid={writer_export_id(w['ref']):w for w in [*snapshot['adapter_source'],*new_adapters]}
    fresh['adapter_source']=[byid[writer_export_id(w['ref'])] for w in fresh['writers']]
    bind_reducers(fresh); bind_adapters(fresh)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),fresh,*authority[3:])


def prepared(**kwargs):
    f=fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(**kwargs)


def test_public_mixed_tracer():
    subject=api(); args=prepared(); observed=[]; original=predecessor.render
    def fresh(*six):
        result=original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh:
        text,result=subject.render(*args)
    assert refresh.call_count==1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed=observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[9,4,8,2,2]
    assert result['consumed_frontier_indices']==[1,2,5,6]
    assert result['deferred_units']==[result['frontier_units'][i] for i in (0,4)]
    assert result['retained_units']==[result['frontier_units'][i] for i in (3,7)]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in result['consumed_frontier_indices']:
            assert new is old; continue
        assert new['input_frontier'] is old and new['predecessor_facts']==old['facts_theorem']
        assert new['dimensions']==dict(D=2,T=2,**dict(zip(('B','S','H','C'),new['local_shape'])))
        assert new['source_output_slot']==0 and new['pm_output_slots']==[0,0]
        assert new['input_refs']==[list(s['inputs'][s['local_index'] if s['op']=='AllGatherPrim' else 0]['endpoint']['ref']) for s in new['local_steps']]
        assert new['ranks']==old['ranks'] and new['positions']==old['positions']
        assert new['observed_consumer_ops']==[['FW_matmul']]*3
        assert all(r['value_proved'] is False for r in new['downstream_consumers'])
        if i%4==1:
            assert new['gather_axis']==2 and new['layout']=='sharded'
            assert new['local_shape']==[1,3,1,2] and new['global_shape']==[2,3,2,2]
            assert new['sm_output_ref']!=old['sm_output_ref']
        else:
            assert new['gather_axis'] is None and new['layout']=='replicated_within_dp'
            assert new['local_shape']==[1,2,2,3] and new['global_shape']==old['global_shape']
            assert new['sm_output_ref']==old['sm_output_ref'] and new['source_step']==old['source_step']
        assert f'have predecessor := {old["facts_theorem"]} ' in text
    assert text.count('source_transpose23_inner_unit_output_reconstruct')==2
    assert text.count('SourceLayoutRead.transposeAxes_value_of_split')==5
    assert text.count('SourceAllGatherRead.allGather_value_of_split')==4
    assert '∀ y ∈' in text and 'y = chunkPrimDimN 0 2' in text
    for bad in ('matmul_value_of_split','SourcePrimitiveRead','sorry','admit','native_decide','axiom ','hxpre','(hshape :','(houtput :'):
        assert bad not in text
    for read in result['reads']:
        assert read['operand_nonwrite_source_indices']==args[-1][read['world']]['execution_to_source'][read['execution_index']:]
        if read['op']=='FW_transpose': assert read['source_kwargs']==dict(dim0=-2,dim1=-1,__consts=[])
        else: assert read['source_signature']==AG and read['input_metadata']=='local-only'
    assert result['lean_bytes']==len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    with pytest.raises(TypeError): subject.render(*args,closed)


@pytest.fixture(scope='module')
def baseline():
    args=prepared()
    return args,predecessor.render(*args)[1]


def transport(args,closed):
    with patch.object(predecessor,'render',return_value=('',closed)) as refresh:
        result=api().render(*args)
    assert refresh.call_count==1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    return result


def selected(args,world='pm',slot=1,rank=3,alias=271003):
    return next(c for c in args[3]._inputs[0 if world=='sm' else 1]
        if c.node.cid==alias+16000+slot and (world=='sm' or c.rank==rank))


def test_read_rejects_remote_peer_descriptor_forgery(baseline):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); subject=api(); index=_Index(args[1],args[3]._inputs[1])
    cell=selected(args,slot=2)
    ports=[predecessor._producer(index,r) for r in cell.inputs]
    step,_=subject._boundary(index,cell,ports,[2,3],1)
    other=replace(ports[0],endpoint=replace(ports[0].endpoint,writer=ports[1].endpoint.writer))
    with pytest.raises(ValueError):
        subject._read(index,'pm',replace(step,inputs=(other,ports[1])),args[-1]['pm'])


@pytest.mark.parametrize('metadata',['local-only','all-peers'])
def test_three_peer_public_next_exchange_inventory(metadata):
    args=prepared(D=1,tp=3,seqlen=3,alias_tid=390019,metadata=metadata,next_exchange=True,successor_metadata=metadata)
    text,result=api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[7,2,4,1,1]
    assert result['consumed_frontier_indices']==[1,2]
    assert result['units'][0]['observed_consumer_ops']==[['FW_matmul']]+[['AllToAllPrim']*3]*3
    assert result['units'][1]['gather_axis'] is None
    assert all(r['op']!='AllToAllPrim' for r in result['reads'])
    assert 'SourcePrimitiveRead' not in text
    for row in result['units']:
        assert row['dimensions']==dict(D=1,T=3,**dict(zip(('B','S','H','C'),row['local_shape'])))
    assert all(r['input_metadata']==metadata for r in result['reads'] if r['op']=='AllGatherPrim')
    # Logical all-peer source refs and physical local-only IR are distinct.
    from Verdict.runtime_lineage import _Index
    index=_Index(args[1],args[3]._inputs[1]); cell=selected(args,slot=2,rank=2,alias=390019)
    ports=[predecessor._producer(index,r) for r in cell.inputs]
    step,_=api()._boundary(index,cell,ports,[0,1,2],2)
    if metadata=='all-peers': cell._input_irs.reverse()
    else: cell._input_irs=copy.deepcopy(previous.selected(args,slot=2,rank=0,alias=390019)._output_irs)
    with pytest.raises(ValueError): api()._read(index,'pm',step,args[-1]['pm'])


@pytest.mark.parametrize('world,slot',[('sm',1),('pm',1),('pm',2)])
@pytest.mark.parametrize('fault',['signature','signature-type','missing-signature','missing-ir',
    'input-missing','output-missing','input-extra','output-extra','input-parent',
    'input-tid','output-tid','input-ref','output-ref','shape-bool','shape-float','rank',
    'parent-shape-float','parent-id-bool','bounds-bool','bounds-float','bounds-negative','bounds-overrun',
    'value-bool','value-float','value-partial','param-type','grad-type','raw-axis-bool','raw-axis-float','raw-axis-wrong','kwargs','consts'])
def test_new_read_raw_authority(baseline,world,slot,fault):
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); subject=api(); which=0 if world=='sm' else 1
    index=_Index(args[which],args[3]._inputs[which]); cell=selected(args,world,slot)
    ports=[predecessor._producer(index,r) for r in cell.inputs]
    if slot==1: step=subject._transpose(index,cell,ports[0])
    else: step,_=subject._boundary(index,cell,ports,[2,3],1)
    x=cell._input_irs[0]; y=cell._output_irs[0]
    if fault=='signature': cell.ir.signature='nnscaler.runtime.adapter.all_gather' if slot==2 else 'torch.reshape'
    elif fault=='signature-type': cell.ir.signature=123
    elif fault=='missing-signature': del cell.ir.signature
    elif fault=='missing-ir': cell.ir=None
    elif fault=='input-missing': cell._input_irs=None
    elif fault=='output-missing': cell._output_irs=None
    elif fault=='input-extra': cell._input_irs*=3
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
    elif fault.startswith('raw-axis-'): cell.kwargs['dim' if slot==2 else 'dim0']={'raw-axis-bool':True,'raw-axis-float':2.0,'raw-axis-wrong':1}[fault]
    elif fault=='kwargs': cell.kwargs['extra']=0
    elif fault=='consts': cell.kwargs['__consts']=[1]
    with pytest.raises(ValueError): subject._read(index,world,step,args[-1][world])


@pytest.mark.parametrize('world',['sm','pm'])
def test_negative_raw_axes_are_not_normalized_into_admission(baseline,world):
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); subject=api(); which=0 if world=='sm' else 1
    index=_Index(args[which],args[3]._inputs[which]); cell=selected(args,world)
    producer=predecessor._producer(index,cell.inputs[0]); kwargs=copy.deepcopy(cell.kwargs)
    with patch.object(subject.backend,'_ordinary',return_value=([3,2],None)):
        with pytest.raises(ValueError): subject._transpose(index,cell,producer)
    assert cell.kwargs==kwargs==dict(dim0=-2,dim1=-1,__consts=[])


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('scope',['collective_scopes','chunk_scopes','wred_scopes'])
def test_transpose_rejects_conflicting_scope(baseline,world,scope):
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); which=0 if world=='sm' else 1
    index=_Index(args[which],args[3]._inputs[which]); cell=selected(args,world)
    port=predecessor._producer(index,cell.inputs[0])
    step=api()._transpose(index,cell,port)
    setattr(index.view,scope,dict(getattr(index.view,scope,{})))
    getattr(index.view,scope)[cell.node]=object()
    with pytest.raises(ValueError): api()._read(index,world,step,args[-1][world])


@pytest.mark.parametrize('fault',['scope-axis','scope-ranks','scope-local','scope-shape','scope-writer',
    'scope-missing','conflicting-scope','raw-ranks','peer-parent','local-substitute','output-parent','writer-inputs','writer-export'])
def test_allgather_logical_peer_authority(baseline,fault):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); subject=api(); index=_Index(args[1],args[3]._inputs[1]); cell=selected(args,slot=2)
    ports=[predecessor._producer(index,r) for r in cell.inputs]
    step,_=subject._boundary(index,cell,ports,[2,3],1)
    if fault.startswith('scope-') and fault!='scope-missing':
        changes={'scope-axis':dict(params=(1,)),'scope-ranks':dict(ranks=(3,2)),
            'scope-local':dict(local_index=True),'scope-shape':dict(input_shape=(1,2,3,1)),
            'scope-writer':dict(source_writer='forged')}
        args[1].collective_scopes[cell.node]=replace(args[1].collective_scopes[cell.node],**changes[fault])
    elif fault=='scope-missing': del args[1].collective_scopes[cell.node]
    elif fault=='conflicting-scope': args[1].chunk_scopes[cell.node]=args[1].collective_scopes[cell.node]
    elif fault=='raw-ranks': cell.kwargs['ranks'].reverse()
    elif fault=='peer-parent': previous.selected(args,slot=2,rank=2)._output_irs[0].parent.tid+=1
    elif fault=='local-substitute': cell._input_irs=copy.deepcopy(previous.selected(args,slot=2,rank=2)._output_irs)
    elif fault=='output-parent': cell._output_irs[0].parent.tid+=1
    else:
        writer=next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid']==cell.node.cid and w['ref']['runtime_rank']==cell.rank)
        if fault=='writer-inputs': writer['inputs'].reverse()
        else: writer['export_id']='forged'
    with pytest.raises((ValueError,KeyError)): subject._read(index,'pm',step,args[-1]['pm'])


@pytest.mark.parametrize('world,slot',[('sm',1),('pm',1),('pm',2)])
@pytest.mark.parametrize('peer',[0,-1])
def test_new_reads_cover_complete_backward_suffix(baseline,world,slot,peer):
    from Verdict.runtime_lineage import _Index
    args,_=copy.deepcopy(baseline); subject=api(); which=0 if world=='sm' else 1
    index=_Index(args[which],args[3]._inputs[which]); cell=selected(args,world,slot)
    ports=[predecessor._producer(index,r) for r in cell.inputs]
    if slot==1: step=subject._transpose(index,cell,ports[0])
    else: step,_=subject._boundary(index,cell,ports,[2,3],1)
    backward=next(n for n in reversed(index.view.nodes()) if index.view.node_opname(n).startswith('BW_'))
    index.view._node2outputs[backward]=[index.view.node_inputs(cell.node)[peer]]
    with pytest.raises(ValueError): subject._read(index,world,step,args[-1][world])


def reclassify(closed,rows):
    closed['frontier_units']=rows
    for i,row in enumerate(rows):
        current=row
        while 'input_frontier' in current:
            current['frontier_index']=i; current=current['input_frontier']
        row['frontier_index']=i
    closed['units']=[r for r in rows if r['source_step']['op']=='FW_transpose']
    closed['consumed_frontier_indices']=[i for i,r in enumerate(rows) if r['source_step']['op']=='FW_transpose']
    closed['retained_units']=[r for r in rows if r['source_step']['op']=='FW_multiref']
    closed['deferred_units']=[]


@pytest.mark.parametrize('fault',['source-input','source-output','local-input','local-output','history',
    'input-frontier','facts','source-slot','dimensions','ranks','positions','unit',
    'coherent-drop-q','coherent-drop-k','coherent-drop-v','coherent-drop-skip','coherent-order','coherent-drop-dp',
    'schedule','inverse','view-bw','exchange-bw','remote-peer-bw','earlier-exchange-bw'])
def test_entire_history_and_carry_inventory(baseline,fault):
    with patch.object(previous.previous,'transport',side_effect=transport),patch.object(previous.previous,'reclassify',side_effect=reclassify):
        previous.previous.test_frontier_history_inventory_and_suffix(baseline,fault)


@pytest.mark.parametrize('units',[(0,),(1,),(0,1)])
def test_earlier_real_skip_is_not_current_carry(baseline,units):
    with patch.object(previous.previous,'transport',side_effect=transport),patch.object(previous.previous,'reclassify',side_effect=reclassify):
        previous.previous.test_earlier_real_skip_substitution(baseline,units)


@pytest.mark.parametrize('layer',['transpose','head','view'])
@pytest.mark.parametrize('fault',['signature','input-parent','shape'])
def test_original_ancestry_is_reauthenticated(baseline,layer,fault):
    args,closed=copy.deepcopy(baseline)
    if layer=='transpose': cell=previous.selected(args,slot=1)
    elif layer=='head': cell=previous.previous.selected(args,slot=1)
    else: cell=previous.previous.previous.selected(args,slot=1)
    if fault=='signature': cell.ir.signature='torch.reshape'
    elif fault=='input-parent': cell._input_irs[0].parent.tid+=1
    else: cell._output_irs[0].shape=(True,*cell._output_irs[0].shape[1:])
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('world,slot',[('sm',1),('pm',1),('pm',2)])
@pytest.mark.parametrize('fault',['signature','missing-ir','output-parent'])
def test_public_new_consumption_guard(baseline,world,slot,fault):
    args,closed=copy.deepcopy(baseline); cell=selected(args,world,slot)
    if fault=='signature': cell.ir.signature='torch.reshape'
    elif fault=='missing-ir': cell.ir=None
    else: cell._output_irs[0].parent.tid+=1
    with pytest.raises(ValueError): transport(args,closed)
