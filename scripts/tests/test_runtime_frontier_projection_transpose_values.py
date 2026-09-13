"""Portable original projection transpose candidates; parent owns kernel closure."""
import copy
import importlib
import importlib.util
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_head_exchange_values as previous
from Verdict import runtime_frontier_head_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_projection_transpose_values'), 'projection transpose renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_projection_transpose_values')


def fixture(next_consumers=False, next_metadata="local-only", **kwargs):
    sm, pm, authority = previous.fixture(**kwargs)
    alias = kwargs.get('alias_tid', 271003)
    for graph in (sm, pm):
        for cell in graph.cells:
            base = alias+(13000 if graph is sm else 14000)
            if cell.opname != 'FW_transpose' or not base <= cell.node.cid <= base+2: continue
            cell.ir.signature = 'torch.transpose'
            cell.kwargs = dict(dim0=1, dim1=2, __consts=[])
            # Transpose creates a NEW parent, shared across SM/PM, not its input parent.
            slot = cell.node.cid-alias-(13000 if graph is sm else 14000)
            cell._output_irs[0].parent.tid = alias+15000+slot
    snapshot=copy.deepcopy(authority[2])
    if next_consumers: _successors(sm,pm,snapshot,alias,kwargs.get('tp',2),next_metadata)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(**kwargs)


def test_public_projection_transpose_tracer():
    subject = api(); args = prepared(); observed = []; original = predecessor.render
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
        if i not in result['consumed_frontier_indices']:
            assert new is old; continue
        assert new['input_frontier'] is old
        assert new['predecessor_facts'] == old['facts_theorem']
        assert new['gather_axis'] == [1,3,2][i%4]
        assert new['local_shape'] == [[1,1,2,3],[1,3,2,1],[1,2,1,3]][i%4]
        assert new['dimensions'] == dict(D=2,T=2,**dict(zip(('B','S','H','C'),new['local_shape'])))
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
        assert new['source_step']['op'] == 'FW_transpose'
        assert all(s['op']=='FW_transpose' for s in new['local_steps'])
        assert new['input_refs']==[list(s['inputs'][0]['endpoint']['ref']) for s in new['local_steps']]
        assert new['family']=='FW_transpose'
        assert f'have predecessor := {old["facts_theorem"]} ' in text
    for law in ('query','inner','sequence'):
        assert text.count(f'source_transpose12_{law}_unit_output_reconstruct') == 2
    assert text.count('SourceLayoutRead.transposeAxes_value_of_split') == 15
    assert 'SourcePrimitiveRead.allToAll_value_of_split' not in text
    for row in result['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
        assert row['source_kwargs'] == dict(dim0=1,dim1=2,__consts=[])
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


def selected(args, world='pm', slot=0, rank=3, alias=271003):
    return previous.selected(args,world=world,slot=slot,rank=rank,kind='FW_transpose',alias=alias)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['signature','missing-signature','missing-ir','signature-type','input-parent','output-parent',
    'input-missing','output-missing','input-extra','output-extra','shape-bool','shape-float','parent-float',
    'bounds-bool','bounds-float','bounds-negative','bounds-overrun','input-rank','output-rank',
    'value-bool','value-float','value-partial','param-type','grad-type','dims-missing','dims-bool','dims-float',
    'dims-wrong','consts','kwargs','input-ref','output-ref','input-tid','output-tid'])
def test_raw_transpose_authority(baseline,world,fault):
    args,closed = copy.deepcopy(baseline); cell=selected(args,world); x=cell._input_irs[0]; y=cell._output_irs[0]
    if fault=='signature': cell.ir.signature='torch.Tensor.transpose'
    elif fault=='missing-signature': del cell.ir.signature
    elif fault=='missing-ir': cell.ir=None
    elif fault=='signature-type': cell.ir.signature=123
    elif fault=='input-parent': x.parent.tid+=1
    elif fault=='output-parent': y.parent.tid+=1
    elif fault=='input-missing': cell._input_irs=None
    elif fault=='output-missing': cell._output_irs=None
    elif fault=='input-extra': cell._input_irs*=2
    elif fault=='output-extra': cell._output_irs*=2
    elif fault=='shape-bool': y.shape=(True,*y.shape[1:])
    elif fault=='shape-float': y.shape=(float(y.shape[0]),*y.shape[1:])
    elif fault=='parent-float': y.parent.shape=(float(y.parent.shape[0]),*y.parent.shape[1:])
    elif fault.startswith('bounds-'):
        lo={'bounds-bool':False,'bounds-float':0.0,'bounds-negative':-1,'bounds-overrun':0}[fault]
        hi=y.parent.shape[0]+1 if fault=='bounds-overrun' else y.indmap[0][1]
        y.indmap=((lo,hi),*y.indmap[1:])
    elif fault=='input-rank': x.shape=x.shape[:3]
    elif fault=='output-rank': y.shape=y.shape[:3]
    elif fault.startswith('value-'): y.valmap={'value-bool':(False,1),'value-float':(0.0,1),'value-partial':(0,2)}[fault]
    elif fault=='param-type': y.param=0
    elif fault=='grad-type': y.is_grad=lambda:0
    elif fault=='dims-missing': del cell.kwargs['dim0']
    elif fault=='dims-bool': cell.kwargs['dim0']=True
    elif fault=='dims-float': cell.kwargs['dim1']=2.0
    elif fault=='dims-wrong': cell.kwargs['dim1']=3
    elif fault=='consts': cell.kwargs['__consts']=[1]
    elif fault=='kwargs': cell.kwargs['extra']=0
    elif fault=='input-ref': cell.inputs[0]=cell.inputs[0]._replace(mb=1)
    elif fault=='output-ref': cell.outputs[0]=cell.outputs[0]._replace(v=2)
    elif fault=='input-tid': x.tid+=1
    elif fault=='output-tid': y.tid+=1
    with pytest.raises(ValueError): transport(args,closed)



def _successors(sm,pm,snapshot,alias,tp,metadata):
    from types import SimpleNamespace as NS
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR,N,T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot,bind_reducers,bind_adapters,writer_export_id
    rows=[]; adapters=[]
    for graph,world in ((sm,'s'),(pm,'p')):
        for producer in list(graph.cells):
            base=alias+(13000 if world=='s' else 14000)
            if producer.opname!='FW_transpose' or not base<=producer.node.cid<=base+2: continue
            slot=producer.node.cid-base; rank=producer.rank; x=producer._output_irs[0]
            shape=list(x.parent.shape); bounds=list(x.indmap)
            kind='FW_matmul'; kw=dict(__consts=[]); sig='torch.matmul'
            refs=producer.outputs*2; ins=[copy.deepcopy(x),copy.deepcopy(x)]
            if slot==1:
                kind='FW_transpose'; kw=dict(dim0=-2,dim1=-1,__consts=[]); sig='torch.transpose'
                shape[2],shape[3]=shape[3],shape[2]; bounds[2],bounds[3]=bounds[3],bounds[2]
                refs=producer.outputs[:]; ins=[copy.deepcopy(x)]
            elif slot==2 and world=='p':
                kind='AllGatherPrim'; ranks=list(range(rank//tp*tp,(rank//tp+1)*tp))
                kw=dict(dim=2,ranks=ranks); sig='nnscaler.runtime.adapter.all_gather'
                bounds[2]=(0,shape[2]); refs=[producer.outputs[0]._replace(rank=r) for r in ranks]
                ins=[copy.deepcopy(x)] if metadata=='local-only' else [copy.deepcopy(next(
                    c._output_irs[0] for c in graph.cells if c.outputs==[ref])) for ref in refs]
            y=IR(alias+16000+slot,x.parent.name if kind=='AllGatherPrim' else f'next.{slot}',tuple(shape),tuple(bounds))
            if kind=='AllGatherPrim': y.parent.tid=x.parent.tid
            cell=NS(node=N(world,rank,0,y.tid,kind),rank=rank,opname=kind,inputs=refs,
                outputs=[T(world,rank,0,y.tid,1)],kwargs=kw,_input_irs=ins,_output_irs=[y])
            cell.ir=NS(signature=sig,inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
            graph.cells.insert(graph.cells.index(producer)+1,cell); graph.shapes[cell.outputs[0]]=y.shape
            if world=='s': continue
            row=dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=y.tid,
                call_instance=0,op=kind,origin='fixture'),source_irname=kind,inputs=[tref(r) for r in refs],
                outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[])
            adapter=copy.deepcopy(row); variable=f'head_transpose_{slot}'
            if kind=='AllGatherPrim':
                row['adapter_kwargs']=kw.copy(); adapter['adapter_kwargs']=kw.copy()
                adapter['inputs']=[tref(producer.outputs[0])]
                adapter['primitive']=dict(kind=kind,forward=True,kwargs=kw.copy(),signature=sig,
                    generated_inputs=[variable],generated_outputs=[f'projection_next_{slot}'])
                call=f'nnscaler.runtime.adapter.all_gather({variable}, dim=2, ranks={ranks})'
            elif kind=='FW_transpose': call=f'{variable}.transpose(-2, -1)'
            else: call=f'torch.matmul({variable}, {variable})'
            rows.append(row); adapters.append(adapter)
            snapshot['rank_sources'][str(rank)]=snapshot['rank_sources'][str(rank)].replace('\ndef _train_step',
                f'\n        projection_next_{slot} = {call}\ndef _train_step')
    fresh=build_snapshot([*snapshot['writers'],*rows])
    fresh.update({k:snapshot[k] for k in ('source','runtime_ndevs','rank_sources')})
    byid={writer_export_id(w['ref']):w for w in [*snapshot['adapter_source'],*adapters]}
    fresh['adapter_source']=[byid[writer_export_id(w['ref'])] for w in fresh['writers']]
    bind_reducers(fresh); bind_adapters(fresh); snapshot.clear(); snapshot.update(fresh)


@pytest.mark.parametrize('metadata',['local-only','all-peers'])
def test_rank4_successor_public(metadata):
    args=prepared(next_consumers=True,next_metadata=metadata)
    text,result=api().render(*args)
    assert len(result['reads'])==15 and len(result['units'])==6
    for i,row in enumerate(result['units']):
        expected=[['FW_matmul']]*3 if i%3==0 else ([['FW_transpose']]*3 if i%3==1 else [['FW_matmul'],['AllGatherPrim']*2,['AllGatherPrim']*2])
        assert row['observed_consumer_ops']==expected
        for consumer in row['downstream_consumers']:
            assert consumer['value_proved'] is False
            if consumer['op']=='FW_transpose': assert consumer['source_kwargs']==dict(dim0=-2,dim1=-1,__consts=[])
            if consumer['op']=='AllGatherPrim':
                assert len(consumer['source_inputs'])==2
                assert consumer['input_metadata']==metadata and consumer['producer_metadata']=='all-peers'
                assert consumer['input_parent_identity']==metadata and consumer['output_metadata']=='present'
    assert 'allGather_value_of_split' not in text and 'matmul_value_of_split' not in text



@pytest.mark.parametrize('slot',[0,1,2])
@pytest.mark.parametrize('fault',['input-parent','output-parent','signature','input-absent','output-shape-bool',
    'scope-local-bool','scope-axis','scope-writer','raw-axis-float','writer-inputs','peer-parent'])
def test_reauthenticate_all_head_families(baseline,slot,fault):
    with patch.object(previous,'transport',side_effect=transport):
        previous.test_original_exchange_authority(baseline,slot,fault)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['signature','missing-ir','input-parent','output-parent','parent-shape-float'])
def test_reauthenticate_incoming_views(baseline,world,fault):
    with patch.object(previous,'transport',side_effect=transport):
        previous.test_incoming_view_original_authority(baseline,world,fault)


@pytest.mark.parametrize('fault',['source-input','source-output','local-input','local-output','history',
    'input-frontier','facts','source-slot','dimensions','ranks','positions','unit','axis',
    'coherent-drop-q','coherent-drop-k','coherent-drop-v','coherent-drop-skip','coherent-order','coherent-drop-dp',
    'schedule','inverse','view-bw','exchange-bw','remote-peer-bw','earlier-exchange-bw'])
def test_complete_frontier_history_and_suffix(baseline,fault):
    if fault=='axis':
        args,closed=copy.deepcopy(baseline)
        closed['frontier_units'][4]['gather_axis']=3
        with pytest.raises(ValueError): transport(args,closed)
        return
    with patch.object(previous,'transport',side_effect=transport):
        previous.test_frontier_history_inventory_and_suffix(baseline,fault)


@pytest.mark.parametrize('units',[(0,),(1,),(0,1)])
def test_source_derived_carry_inventory(baseline,units):
    with patch.object(previous,'transport',side_effect=transport):
        previous.test_earlier_real_skip_substitution(baseline,units)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['signature','shape','parent','dims','backward-write'])
def test_read_rechecks_live_original_and_full_bw_suffix(baseline,world,fault):
    from Verdict.runtime_lineage import _Index
    args,closed=copy.deepcopy(baseline); subject=api()
    index=_Index(args[0 if world=='sm' else 1],args[3]._inputs[0 if world=='sm' else 1])
    cell=selected(args,world); producer=subject._producer(index,cell.inputs[0])
    step=subject._transpose(index,cell,producer)
    if fault=='signature': cell.ir.signature='torch.reshape'
    elif fault=='shape': cell._output_irs[0].shape=(True,*cell._output_irs[0].shape[1:])
    elif fault=='parent': cell._input_irs[0].parent.tid+=1
    elif fault=='dims': cell.kwargs['dim0']=True
    else:
        backward=next(n for n in reversed(index.view.nodes()) if index.view.node_opname(n).startswith('BW_'))
        index.view._node2outputs[backward]=[index.view.node_inputs(cell.node)[0]]
    with pytest.raises(ValueError): subject._read(index,world,step,args[-1][world])


@pytest.fixture(scope='module')
def successor_baseline():
    args=prepared(next_consumers=True)
    return args,predecessor.render(*args)[1]


@pytest.mark.parametrize('slot',[0,1,2])
@pytest.mark.parametrize('fault',['input-missing','input-extra','input-parent','input-bool',
    'output-missing','output-bool','output-parent-float','output-tid','input-ref'])
def test_rank4_successor_metadata_rejects(successor_baseline,slot,fault):
    args,closed=copy.deepcopy(successor_baseline)
    cell=next(c for c in args[3]._inputs[1] if c.node.cid==271003+16000+slot and c.rank==3)
    if fault=='input-missing': cell._input_irs=None
    elif fault=='input-extra': cell._input_irs*=3
    elif fault=='input-parent': cell._input_irs[0].parent.tid+=1
    elif fault=='input-bool': cell._input_irs[0].shape=(True,*cell._input_irs[0].shape[1:])
    elif fault=='output-missing': cell._output_irs=None
    elif fault=='output-bool': cell._output_irs[0].shape=(True,*cell._output_irs[0].shape[1:])
    elif fault=='output-parent-float': cell._output_irs[0].parent.shape=(1.0,*cell._output_irs[0].parent.shape[1:])
    elif fault=='output-tid': cell._output_irs[0].tid+=1
    elif fault=='input-ref': cell.inputs[0]=cell.inputs[0]._replace(mb=1)
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['scope-axis','scope-ranks','scope-local','scope-shape','scope-writer',
    'raw-axis-bool','raw-ranks','peer-parent','local-substitute','output-parent'])
def test_rank4_gather_ordered_logical_peers(successor_baseline,fault):
    from dataclasses import replace
    args,closed=copy.deepcopy(successor_baseline)
    cell=next(c for c in args[3]._inputs[1] if c.node.cid==287005 and c.rank==3)
    if fault.startswith('scope-'):
        changes={'scope-axis':dict(params=(1,)),'scope-ranks':dict(ranks=(3,2)),
            'scope-local':dict(local_index=True),'scope-shape':dict(input_shape=(1,2,3,1)),
            'scope-writer':dict(source_writer='forged')}
        args[1].collective_scopes[cell.node]=replace(args[1].collective_scopes[cell.node],**changes[fault])
    elif fault=='raw-axis-bool': cell.kwargs['dim']=True
    elif fault=='raw-ranks': cell.kwargs['ranks'].reverse()
    elif fault=='peer-parent': selected(args,slot=2,rank=2)._output_irs[0].parent.tid+=1
    elif fault=='local-substitute': cell._input_irs=copy.deepcopy(selected(args,slot=2,rank=2)._output_irs)
    else: cell._output_irs[0].parent.tid+=1
    with pytest.raises(ValueError): transport(args,closed)



@pytest.mark.parametrize('metadata',['local-only','all-peers'])
def test_dynamic_three_peer_public_and_reversed_metadata(metadata):
    args=prepared(D=1,tp=3,seqlen=3,alias_tid=390019,successor_metadata=metadata,
        next_consumers=True,next_metadata=metadata)
    observed=[]; original=predecessor.render
    def fresh(*six):
        result=original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh:
        text,result=api().render(*args)
    assert refresh.call_count==1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units')]==[12,3,4,1]
    assert [r['gather_axis'] for r in result['units']]==[1,3,2]
    assert text.count('SourceLayoutRead.transposeAxes_value_of_split')==len(result['reads'])
    for row in result['units']:
        assert row['dimensions']==dict(D=1,T=3,**dict(zip(('B','S','H','C'),row['local_shape'])))
    args,closed=copy.deepcopy((args,observed[0][1]))
    cell=next(c for c in args[3]._inputs[1] if c.node.cid==390019+16002 and c.rank==2)
    if metadata=='all-peers': cell._input_irs.reverse()
    else: cell._input_irs=copy.deepcopy(selected(args,slot=2,rank=0,alias=390019)._output_irs)
    with pytest.raises(ValueError): transport(args,closed)



def test_same_shaped_original_primal_is_not_the_transpose_operand(baseline):
    from dataclasses import replace
    from Verdict.runtime_lineage import _Index
    args,closed=copy.deepcopy(baseline); subject=api(); index=_Index(args[0],args[3]._inputs[0])
    cell=selected(args,'sm',slot=0)
    correct=subject._producer(index,cell.inputs[0])
    other_cell=selected(args,'sm',slot=2)
    other=subject._producer(index,other_cell.inputs[0])
    assert correct.endpoint.shape==other.endpoint.shape
    assert correct.endpoint.ref!=other.endpoint.ref
    step=subject._transpose(index,cell,correct)
    with pytest.raises(ValueError): subject._read(index,'sm',replace(step,inputs=(other,)),args[-1]['sm'])
