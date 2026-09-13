"""Portable original AA(2,1) continuation. No capture or kernel claims."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_post_transpose_values as previous
from Verdict import runtime_frontier_post_transpose_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_middle_exchange_values'), 'middle exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_middle_exchange_values')


def fixture(**kwargs):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    kwargs = dict({'D':2,'tp':3,'seqlen':3}, **kwargs)
    sm, pm, authority = previous.fixture(next_exchange=True, **kwargs)
    alias = kwargs.get('alias_tid',271003)
    snapshot = copy.deepcopy(authority[2])
    # Inventory a real two-input score boundary without proving it. Keep Q first,
    # K second, and schedule the original matmul after its K producer. The TP=3
    # fixture uses the inherited divisible head factor; production derives T.
    for graph in (sm,pm):
        for score in [c for c in graph.cells if c.node.cid==alias+16000]:
            k = next(c for c in graph.cells if c.rank==score.rank
                     and c.node.cid==alias+(16001 if graph is sm else 17001))
            score.inputs=[score.inputs[0],k.outputs[0]]
            score._input_irs=[score._input_irs[0],copy.deepcopy(k._output_irs[0])]
            graph.cells.remove(score); graph.cells.insert(graph.cells.index(k)+1,score)
            if graph is sm:
                unused=next(c for c in graph.cells if c.node.cid==alias+17001)
                graph.cells.remove(unused)
                for ref in unused.outputs: graph.shapes.pop(ref)
                continue
            for inventory in ('writers','adapter_source'):
                writer=next(w for w in snapshot[inventory] if w['ref']['runtime_rank']==score.rank
                            and w['ref']['source_cid']==score.node.cid)
                writer['inputs']=[tref(r) for r in score.inputs]
                snapshot[inventory].remove(writer)
                k_writer=next(w for w in snapshot[inventory] if w['ref']['runtime_rank']==score.rank
                              and w['ref']['source_cid']==k.node.cid)
                snapshot[inventory].insert(snapshot[inventory].index(k_writer)+1,writer)
            lines=[line for line in snapshot['rank_sources'][str(score.rank)].splitlines()
                   if not line.strip().startswith('projection_next_0 =')]
            text='\n'.join(lines)+'\n'
            snapshot['rank_sources'][str(score.rank)]=text.replace('\ndef _train_step',
                '\n        projection_next_0 = torch.matmul(head_transpose_0, after_post_1)\ndef _train_step')
    fresh=build_snapshot(snapshot['writers'])
    fresh.update({k:snapshot[k] for k in ('source','runtime_ndevs','rank_sources')})
    byid={writer_export_id(w['ref']):w for w in snapshot['adapter_source']}
    fresh['adapter_source']=[byid[writer_export_id(w['ref'])] for w in fresh['writers']]
    bind_reducers(fresh); bind_adapters(fresh)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),fresh,*authority[3:])


def prepared(**kwargs):
    kwargs=dict({'D':2,'tp':3,'seqlen':3},**kwargs)
    f=fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(**kwargs)


def test_public_middle_exchange_tracer():
    subject=api(); args=prepared(); observed=[]; original=predecessor.render
    def fresh(*six):
        result=original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh:
        text,result=subject.render(*args)
    assert refresh.call_count==1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed=observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[6,2,8,4,2]
    assert result['consumed_frontier_indices']==[1,5]
    assert result['deferred_units']==[result['frontier_units'][i] for i in (0,4)]
    assert result['retained_units']==[result['frontier_units'][i] for i in (2,3,6,7)]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in (1,5):
            assert new is old
            if i in (2,6):
                assert new['gather_axis'] is None and new['layout']=='replicated_within_dp'
            continue
        assert new['input_frontier'] is old and new['predecessor_facts']==old['facts_theorem']
        assert new['source_step']==old['source_step'] and new['sm_output_ref']==old['sm_output_ref']
        assert new['source_output_slot']==old['source_output_slot']
        assert new['global_shape']==old['global_shape']
        assert new['input_refs']==old['pm_output_refs']
        assert new['gather_axis']==1 and new['input_gather_axis']==2
        assert new['dimensions']==dict(D=2,T=3,**dict(zip(('B','S','H','C'),new['local_shape'])))
        assert new['observed_consumer_ops']==[['FW_matmul']]*4
        q=closed['frontier_units'][i-1]
        consumers=new['downstream_consumers']
        assert consumers[0]['source_inputs']==[q['sm_output_ref'],new['sm_output_ref']]
        assert [c['source_inputs'] for c in consumers[1:]]==[
            [qr,kr] for qr,kr in zip(q['pm_output_refs'],new['pm_output_refs'],strict=True)]
        assert all(r['value_proved'] is False for r in new['downstream_consumers'])
        assert f'have predecessor := {old["facts_theorem"]} ' in text
    assert text.count('SourceRank4MiddleExchange.axis2_output_facts')==2
    assert '∀ y ∈' in text and 'allGatherPrimDimN 1 3 0' in text
    for read in result['reads']:
        assert read['op']=='AllToAllPrim' and read['world']=='pm'
        assert read['params']==[2,1]
        assert read['source_signature']=='nnscaler.runtime.adapter.nn.alltoall_alltoall'
        assert read['operand_nonwrite_source_indices']==args[-1]['pm']['execution_to_source'][read['execution_index']:]
    for bad in ('matmul_value_of_split','sorry','admit','native_decide','axiom ','hxpre','(hshape :','(houtput :'):
        assert bad not in text
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    assert result['lean_bytes']==len(text.encode())
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


def selected(args,rank=5,alias=271003):
    return next(c for c in args[3]._inputs[1] if c.node.cid==alias+17001 and c.rank==rank)


def boundary(args):
    from Verdict.runtime_lineage import _Index
    index=_Index(args[1],args[3]._inputs[1]); cell=selected(args)
    ports=[predecessor.predecessor._producer(index,ref) for ref in cell.inputs]
    ranks=[p.endpoint.ref[1] for p in ports]
    step,_=api()._boundary(index,cell,ports,ranks,ranks.index(cell.rank))
    return index,cell,ports,step


@pytest.mark.parametrize('index',[0,1,2,3,4,5,6,7])
@pytest.mark.parametrize('fault',['facts-missing','facts-rewritten','history','descriptor'])
def test_complete_incoming_records(baseline,index,fault):
    args,closed=copy.deepcopy(baseline); row=closed['frontier_units'][index]
    if fault=='facts-missing': row.pop('facts_theorem')
    elif fault=='facts-rewritten':
        row['theorem']=row['facts_theorem']='value_only'
    elif fault=='history': row['predecessor_facts']='earlier_same_shape'
    else:
        row['local_steps'][0]['inputs'][0]['endpoint']['writer']=row['local_steps'][0]['outputs'][0]['endpoint']['writer']
    with pytest.raises(ValueError): transport(args,closed)


def test_read_rejects_remote_descriptor(baseline):
    from dataclasses import replace
    args,_=copy.deepcopy(baseline); index,cell,ports,step=boundary(args)
    other=replace(ports[0],endpoint=replace(ports[0].endpoint,writer=ports[1].endpoint.writer))
    with pytest.raises(ValueError):
        api()._read(index,'pm',replace(step,inputs=(other,*ports[1:])),args[-1]['pm'])


@pytest.mark.parametrize('fault',[
    'signature','signature-type','missing-signature','missing-ir','input-missing','output-missing',
    'input-extra','output-extra','input-parent','input-tid','output-tid','input-ref','output-ref',
    'shape-bool','shape-float','rank','parent-shape-float','parent-id-bool',
    'bounds-bool','bounds-float','bounds-negative','bounds-overrun','value-bool','value-float',
    'value-partial','param-type','grad-type','raw-axis-bool','raw-axis-float','raw-axis-wrong','kwargs','consts'])
def test_new_read_raw_authority(baseline,fault):
    args,_=copy.deepcopy(baseline); index,cell,ports,step=boundary(args)
    x=cell._input_irs[0]; y=cell._output_irs[0]
    if fault=='signature': cell.ir.signature='nnscaler.runtime.adapter.all_to_all'
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
    elif fault.startswith('raw-axis-'): cell.kwargs['idim']={'raw-axis-bool':True,'raw-axis-float':2.0,'raw-axis-wrong':1}[fault]
    elif fault=='kwargs': cell.kwargs['extra']=0
    elif fault=='consts': cell.kwargs['__consts']=[1]
    with pytest.raises((ValueError,KeyError)): api()._read(index,'pm',step,args[-1]['pm'])


@pytest.mark.parametrize('fault',['scope-axis','scope-ranks','scope-local','scope-shape','scope-writer',
    'scope-missing','conflicting-scope','raw-ranks','peer-parent','local-substitute','output-parent','writer-inputs','writer-export'])
def test_logical_peers_scope_and_export(baseline,fault):
    from dataclasses import replace
    args,_=copy.deepcopy(baseline); index,cell,ports,step=boundary(args)
    if fault.startswith('scope-') and fault!='scope-missing':
        changes={'scope-axis':dict(params=(1,2)),'scope-ranks':dict(ranks=tuple(reversed(step.ranks))),
            'scope-local':dict(local_index=True),'scope-shape':dict(input_shape=(1,2,3,4)),
            'scope-writer':dict(source_writer='forged')}
        args[1].collective_scopes[cell.node]=replace(args[1].collective_scopes[cell.node],**changes[fault])
    elif fault=='scope-missing': del args[1].collective_scopes[cell.node]
    elif fault=='conflicting-scope': args[1].chunk_scopes[cell.node]=args[1].collective_scopes[cell.node]
    elif fault=='raw-ranks': cell.kwargs['ranks'].reverse()
    elif fault=='peer-parent': index.raw[ports[0].endpoint.writer]._output_irs[0].parent.tid+=1
    elif fault=='local-substitute': cell._input_irs=copy.deepcopy(index.raw[ports[0].endpoint.writer]._output_irs)
    elif fault=='output-parent': cell._output_irs[0].parent.tid+=1
    else:
        writer=next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid']==cell.node.cid and w['ref']['runtime_rank']==cell.rank)
        if fault=='writer-inputs': writer['inputs'].reverse()
        else: writer['export_id']='forged'
    with pytest.raises((ValueError,KeyError)): api()._read(index,'pm',step,args[-1]['pm'])


@pytest.mark.parametrize('peer',[0,-1])
def test_original_full_backward_suffix(baseline,peer):
    args,_=copy.deepcopy(baseline); index,cell,ports,step=boundary(args)
    backward=next(n for n in reversed(index.view.nodes()) if index.view.node_opname(n).startswith('BW_'))
    index.view._node2outputs[backward]=[index.view.node_inputs(cell.node)[peer]]
    with pytest.raises(ValueError): api()._read(index,'pm',step,args[-1]['pm'])


def reclassify(closed,rows):
    closed['frontier_units']=rows
    for i,row in enumerate(rows):
        current=row
        while 'input_frontier' in current:
            current['frontier_index']=i; current=current['input_frontier']
        row['frontier_index']=i
    closed['units']=[r for r in rows if r.get('family') in ('FW_transpose','AllGatherPrim') and r['facts_theorem'].startswith('frontierPostTranspose')]
    closed['consumed_frontier_indices']=[i for i,r in enumerate(rows) if any(r is u for u in closed['units'])]
    closed['retained_units']=[r for r in rows if r['source_step']['op']=='FW_multiref']
    closed['deferred_units']=[r for r in rows if not any(r is u for u in closed['units']+closed['retained_units'])]


@pytest.mark.parametrize('fault',['coherent-drop-q','coherent-drop-k','coherent-drop-v','coherent-drop-skip',
    'coherent-order','coherent-drop-dp','schedule','inverse','remote-peer-bw','earlier-exchange-bw'])
def test_source_derived_inventory(baseline,fault):
    head_tests=previous.previous.previous
    with patch.object(head_tests,'transport',side_effect=transport),patch.object(head_tests,'reclassify',side_effect=reclassify):
        head_tests.test_frontier_history_inventory_and_suffix(baseline,fault)


@pytest.mark.parametrize('units',[(0,),(1,),(0,1)])
def test_earlier_same_shaped_carry_rejected(baseline,units):
    head_tests=previous.previous.previous
    with patch.object(head_tests,'transport',side_effect=transport),patch.object(head_tests,'reclassify',side_effect=reclassify):
        head_tests.test_earlier_real_skip_substitution(baseline,units)


@pytest.mark.parametrize('key',['units','retained_units','deferred_units','consumed_frontier_indices'])
def test_incoming_classification_not_authority(baseline,key):
    args,closed=copy.deepcopy(baseline); closed[key]=[]
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('slot,stage',[(0,'first'),(1,'first'),(2,'first'),(1,'second'),(2,'gather')])
@pytest.mark.parametrize('fault',['signature','parent','shape','remote-descriptor'])
def test_reauthenticate_original_transposes_and_v(baseline,slot,stage,fault):
    args,closed=copy.deepcopy(baseline)
    cell=(previous.previous.selected(args,slot=slot,rank=5) if stage=='first'
          else previous.selected(args,slot=slot,rank=5))
    if fault=='signature': cell.ir.signature='torch.reshape'
    elif fault=='parent': cell._input_irs[0].parent.tid+=1
    elif fault=='shape': cell._output_irs[0].shape=(True,*cell._output_irs[0].shape[1:])
    else:
        row=closed['frontier_units'][slot+4]
        row['local_steps'][0]['inputs'][0]['parent_name']='forged-remote-parent'
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('metadata',['local-only','all-peers'])
def test_dynamic_public_ordered_metadata(metadata):
    args=prepared(D=1,alias_tid=390019,metadata=metadata,successor_metadata=metadata)
    text,result=api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[3,1,4,2,1]
    assert all(r['input_metadata']==metadata for r in result['reads'])
    from Verdict.runtime_lineage import _Index
    index=_Index(args[1],args[3]._inputs[1]); cell=selected(args,rank=2,alias=390019)
    ports=[predecessor.predecessor._producer(index,ref) for ref in cell.inputs]
    step,_=api()._boundary(index,cell,ports,[0,1,2],2)
    if metadata=='all-peers': cell._input_irs.reverse()
    else: cell._input_irs=copy.deepcopy(index.raw[ports[0].endpoint.writer]._output_irs)
    with pytest.raises(ValueError): api()._read(index,'pm',step,args[-1]['pm'])


@pytest.mark.parametrize('kind',['FW_transpose','FW_view','FW_unknown','FW_matmul'])
def test_only_recognized_replicas_are_retained(kind):
    row=dict(layout='replicated_within_dp',gather_axis=None,ranks=[0,1],
             local_steps=[dict(op='AllGatherPrim'),dict(op='AllGatherPrim')])
    cells=[NS(opname=kind),NS(opname=kind)]
    assert api()._unconsumed(row,[NS(opname='FW_matmul')],cells)==('retained' if kind=='FW_matmul' else 'deferred')
