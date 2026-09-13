"""Source-shaped score AA(1,3) frontier, without division/kernel claims."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_score_matmul_values as previous
from Verdict import runtime_frontier_score_matmul_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_score_exchange_values'), 'score exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_score_exchange_values')


def fixture(**kwargs):
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(**kwargs)
    alias = kwargs.get('alias_tid', 271003)
    snapshot = copy.deepcopy(authority[2])
    smdiv = next(c for c in sm.cells if c.node.cid == alias+18000)
    for aa in [c for c in pm.cells if c.node.cid == alias+18000]:
        rank = aa.rank; x = aa._output_irs[0]
        y = IR(alias+19000, 'scaled_scores', x.parent.shape, x.indmap)
        y.parent.tid = smdiv._output_irs[0].parent.tid
        kw = dict(rounding_mode=None, __consts=[4.0])
        div = NS(node=N('p',rank,0,y.tid,'FW_div'), rank=rank, opname='FW_div',
            inputs=aa.outputs[:], outputs=[T('p',rank,0,y.tid,1)], kwargs=kw,
            _input_irs=[copy.deepcopy(x)], _output_irs=[y])
        div.ir = NS(signature='torch.div', inputs=lambda c=div:c._input_irs, outputs=lambda c=div:c._output_irs)
        pm.cells.insert(pm.cells.index(aa)+1,div); pm.shapes[div.outputs[0]]=y.shape
        v = next(c for c in pm.cells if c.rank==rank and c.node.cid==alias+17002)
        v.inputs[0]=div.outputs[0]; v._input_irs[0]=copy.deepcopy(y)
        pm.cells.remove(v)
        writers=[c for c in pm.cells if any(r in c.outputs for r in v.inputs)]
        pm.cells.insert(max(pm.cells.index(c) for c in writers)+1,v)
        row=dict(ref=dict(world='p',runtime_rank=rank,microbatch=0,source_cid=y.tid,
            call_instance=0,op='FW_div',origin='fixture'),source_irname='FW_div',
            inputs=[tref(r) for r in div.inputs],outputs=[tref(r) for r in div.outputs],parameter_grad_tids=[])
        adapter=copy.deepcopy(row)
        adapter['primitive']=dict(kind='FW_div',forward=True,kwargs=kw.copy(),signature='torch.div',
            generated_inputs=['after_score'],generated_outputs=['after_div'])
        for key,new in [('writers',row),('adapter_source',adapter)]:
            old=next(w for w in snapshot[key] if w['ref']['runtime_rank']==rank and w['ref']['source_cid']==v.node.cid)
            old['inputs']=[tref(r) for r in v.inputs]
            snapshot[key].remove(old)
            snapshot[key].extend([new,old])
        snapshot['rank_sources'][str(rank)]=snapshot['rank_sources'][str(rank)].replace(
            '        after_post_2 = torch.matmul(after_score, projection_next_2)',
            '        after_div = torch.div(after_score, 4.0, rounding_mode=None)\n'
            '        after_post_2 = torch.matmul(after_div, projection_next_2)')
    fresh=build_snapshot(snapshot['writers'])
    fresh.update({k:snapshot[k] for k in ('source','runtime_ndevs','rank_sources')})
    adapters={writer_export_id(w['ref']):w for w in snapshot['adapter_source']}
    fresh['adapter_source']=[adapters[writer_export_id(w['ref'])] for w in fresh['writers']]
    bind_reducers(fresh); bind_adapters(fresh)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),fresh,*authority[3:])


def prepared(**kwargs):
    f=fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(**kwargs)


def test_public_score_exchange_tracer():
    subject=api(); args=prepared(); observed=[]; original=predecessor.render
    def fresh(*six):
        result=original(*six); observed.append(result)
        # The public chain also uses these legacy backends for earlier layers.
        unit.reset_mock(); read.reset_mock()
        return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh, \
         patch.object(subject.backend,'_unit',wraps=subject.backend._unit) as unit, \
         patch.object(subject.backend,'_read',wraps=subject.backend._read) as read:
        text,result=subject.render(*args)
    assert refresh.call_count==1 and all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed=observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[6,2,6,2,2]
    assert unit.call_count==2 and read.call_count==6
    assert result['consumed_frontier_indices']==[0,3]
    for u,new in enumerate(result['units']):
        old=closed['frontier_units'][3*u]
        assert len(unit.call_args_list[u].args)==5 and unit.call_args_list[u].args[0] is old
        assert new['input_frontier'] is old and new['source_step'] is old['source_step']
        assert new['sm_output_ref']==old['sm_output_ref'] and new['source_step']['op']=='FW_matmul'
        assert new['dimensions']==dict(D=2,T=3,B=1,S=3,H=3,C=1)
        assert new['global_shape']==[2,3,3,3] and new['local_shape']==[1,3,3,1]
        assert new['gather_axis']==new['output_gather_axis']==3
        assert new['input_refs']==old['pm_output_refs']
        assert new['source_output_slot']==new['slot']==0 and new['pm_output_slots']==[0,0,0]
        assert new['observed_consumer_ops']==[['FW_div'],['FW_div'],['FW_div'],['FW_div']]
        assert all(c['value_proved'] is False and c['source_kwargs']==dict(rounding_mode=None,__consts=[4.0])
                   for c in new['downstream_consumers'])
        v=result['frontier_units'][3*u+1]
        assert v is closed['frontier_units'][3*u+1] and v['layout']=='replicated_within_dp' and v['gather_axis'] is None
        assert result['deferred_units'][u]['source_boundary'] is v
        assert result['deferred_units'][u]['value_proved'] is False
        assert result['frontier_units'][3*u+2] is closed['frontier_units'][3*u+2]
        assert result['retained_units'][u] is closed['frontier_units'][3*u+2]
    assert text.count('SourceRank4Exchange.axis1_output_facts')==2
    assert '∀ y ∈' in text and 'allGatherPrimDimN 3 3 0' in text and 'InitialParameterValues s p' in text
    assert all(r['op']=='AllToAllPrim' and r['source_signature']=='nnscaler.runtime.adapter.nn.alltoall_alltoall' for r in result['reads'])
    for r in result['reads']:
        assert r['operand_nonwrite_source_indices']==args[-1]['pm']['execution_to_source'][r['execution_index']:]
    for bad in ('div_value_of_split','source_matmul_unit_output_reconstruct','sorry','admit','native_decide','axiom ','(hshape :','(houtput :'):
        assert bad not in text
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    assert result['lean_bytes']==len(text.encode())
    with pytest.raises(TypeError): subject.render(*args,closed)


@pytest.fixture(scope='module')
def source():
    return prepared()


@pytest.fixture(scope='module')
def baseline(source):
    return source,predecessor.render(*source)[1]


def transport(args,closed):
    with patch.object(predecessor,'render',return_value=('',closed)) as refresh:
        result=api().render(*args)
    assert refresh.call_count==1 and all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    return result


def boundary(args,rank=5):
    from Verdict.runtime_lineage import _Index
    index=_Index(args[1],args[3]._inputs[1])
    cell=next(c for c in index.raw.values() if c.node.cid==271003+18000 and c.rank==rank)
    ports=[api()._transpose._producer(index,r) for r in cell.inputs]
    step,_=api()._boundary(index,cell,ports,list(cell.kwargs['ranks']),cell.kwargs['ranks'].index(rank))
    return index,cell,ports,step


@pytest.mark.parametrize('fault',['signature','signature-type','missing-ir','input-missing','output-missing',
    'input-extra','output-extra','input-parent','output-parent','remote-parent','input-tid','output-tid',
    'shape-bool','shape-float','shape-rank','parent-shape-float','parent-id-bool','bounds-bool','bounds-float',
    'bounds-negative','bounds-overrun','value-bool','value-float','value-partial','param-type','grad-type',
    'kwargs','consts','axis-bool','axis-wrong','ranks-bool','peer-reverse','remote-descriptor',
    'chunk-scope','wred-scope','scope-absent','scope-axes','scope-ranks','scope-receiver'])
def test_strict_raw_boundary(source,fault):
    from dataclasses import replace
    args=copy.deepcopy(source); index,cell,ports,step=boundary(args)
    x,y=cell._input_irs[0],cell._output_irs[0]
    if fault=='signature': cell.ir.signature='nnscaler.runtime.adapter.nn.alltoall'
    elif fault=='signature-type': cell.ir.signature=0
    elif fault=='missing-ir': cell.ir=None
    elif fault=='input-missing': cell._input_irs=None
    elif fault=='output-missing': cell._output_irs=None
    elif fault=='input-extra': cell._input_irs*=2
    elif fault=='output-extra': cell._output_irs*=2
    elif fault=='input-parent': x.parent.tid+=1
    elif fault=='output-parent': y.parent.tid+=1
    elif fault=='remote-parent': index.raw[ports[0].endpoint.writer]._output_irs[0].parent.tid+=1
    elif fault=='input-tid': x.tid+=1
    elif fault=='output-tid': y.tid+=1
    elif fault=='shape-bool': y.shape=(True,*y.shape[1:])
    elif fault=='shape-float': y.shape=(float(y.shape[0]),*y.shape[1:])
    elif fault=='shape-rank': y.shape=y.shape[:3]
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
    elif fault=='axis-bool': cell.kwargs['idim']=True
    elif fault=='axis-wrong': cell.kwargs['odim']=2
    elif fault=='ranks-bool': cell.kwargs['ranks'][0]=True
    elif fault=='peer-reverse': cell.inputs.reverse()
    elif fault=='remote-descriptor': ports[0]=replace(ports[0],parent_name='forged')
    elif fault in ('chunk-scope','wred-scope'):
        key=fault.split('-')[0]+'_scopes'; setattr(index.view,key,dict(getattr(index.view,key,{})))
        getattr(index.view,key)[cell.node]=NS()
    elif fault=='scope-absent': index.view.collective_scopes.pop(cell.node)
    else:
        scope=index.view.collective_scopes[cell.node]
        key,value={'scope-axes':('params',(True,3)),'scope-ranks':('ranks',tuple(reversed(step.ranks))),
                   'scope-receiver':('local_index',0)}[fault]
        index.view.collective_scopes[cell.node]=replace(scope,**{key:value})
    with pytest.raises((ValueError,KeyError)):
        api()._boundary(index,cell,ports,list(step.ranks),step.local_index)


@pytest.mark.parametrize('fault',['export','writer-inputs','writer-outputs','call-bool','call-negative','call-missing'])
def test_original_export(source,fault):
    args=copy.deepcopy(source); index,cell,ports,step=boundary(args)
    writer=next(w for w in index.view._collective_source['writers'] if w['ref']['source_cid']==cell.node.cid and w['ref']['runtime_rank']==cell.rank)
    if fault=='export': writer['export_id']='forged'
    elif fault=='writer-inputs': writer['inputs'].reverse()
    elif fault=='writer-outputs': writer['outputs']=[]
    elif fault=='call-bool': writer['ref']['call_instance']=False
    elif fault=='call-negative': writer['ref']['call_instance']=-1
    else: writer['ref'].pop('call_instance')
    with pytest.raises((ValueError,KeyError)): api()._read(index,step,args[-1]['pm'])


@pytest.mark.parametrize('fault',['descriptor','remote-peer-reverse','receiver','schedule','inverse'])
def test_fresh_read_order(source,fault):
    from dataclasses import replace
    args=copy.deepcopy(source); index,cell,ports,step=boundary(args)
    if fault=='descriptor': step=replace(step,inputs=(replace(ports[0],parent_name='forged'),*ports[1:]))
    elif fault=='remote-peer-reverse': step=replace(step,inputs=tuple(reversed(ports)),peers=tuple(reversed(step.peers)))
    elif fault=='receiver': step=replace(step,local_index=0)
    else: args[-1]['pm']['execution_to_source' if fault=='schedule' else 'source_to_execution'].reverse()
    with pytest.raises(ValueError): api()._read(index,step,args[-1]['pm'])


@pytest.mark.parametrize('peer',[0,1,2])
def test_whole_backward_suffix(source,peer):
    args=copy.deepcopy(source); index,cell,ports,step=boundary(args)
    bw=next(n for n in reversed(index.view.nodes()) if index.view.node_opname(n).startswith('BW_'))
    index.view._node2outputs[bw]=[index.view.node_inputs(cell.node)[peer]]
    with pytest.raises(ValueError): api()._read(index,step,args[-1]['pm'])


@pytest.mark.parametrize('kind',[None,'FW_unknown','FW_matmul','FW_div','AllToAllPrim'])
def test_explicit_deferred_classifier(kind):
    assert hasattr(api(),'_classification'), 'explicit score-exchange classifier missing'
    cells=[] if kind is None else [NS(opname=kind)]
    assert api()._classification('FW_multiref',cells)=='retained'
    assert api()._classification('FW_matmul',cells)==('ready' if kind=='AllToAllPrim' else 'deferred')
    assert api()._classification('FW_transpose',cells)=='deferred'


def unit_inputs(args,closed):
    from Verdict.runtime_lineage import _Index
    si,pi=[_Index(v,raw) for v,raw in zip(args[:2],args[3]._inputs[:2],strict=True)]
    row=closed['frontier_units'][3]
    g=api()._transpose._producer(si,row['sm_output_ref'])
    ports=[api()._transpose._producer(pi,r) for r in row['pm_output_refs']]
    steps=[boundary(args,rank)[-1] for rank in row['ranks']]
    names={s.node:f'frontierScoreExchangeRead_pm_{s.outputs[0].endpoint.tid}' for s in steps}
    return pi,row,g,ports,steps,names


@pytest.mark.parametrize('fault',['receiver-reverse','duplicate','cross-dp','remote-peer-reverse'])
def test_unit_original_order(baseline,fault):
    from dataclasses import replace
    assert hasattr(api(),'_unit'), 'source-bound score-exchange unit guard missing'
    args,closed=copy.deepcopy(baseline); pi,row,g,ports,steps,names=unit_inputs(args,closed)
    if fault=='receiver-reverse': steps.reverse()
    elif fault=='duplicate': steps[-1]=steps[0]
    elif fault=='cross-dp': steps[-1]=boundary(args,rank=2)[-1]
    else: steps[-1]=replace(steps[-1],inputs=tuple(reversed(ports)))
    with pytest.raises(ValueError): api()._unit(pi,row,g,ports,steps,names)


def reclassify(closed,rows):
    """Coherently update every top-level classification, not just the rows."""
    closed['frontier_units']=rows
    closed['units']=[r for r in rows if r['source_step']['op']=='FW_matmul']
    closed['retained_units']=[r for r in rows if r['source_step']['op']=='FW_multiref']
    closed['deferred_units']=[d for d in closed['deferred_units'] if any(d['source_boundary'] is r for r in rows)]
    closed['ordered_joins']=[r['ordered_join'] for r in closed['units']]
    closed['consumed_frontier_indices']=sorted(j for r in closed['units'] for j in r['ordered_join']['frontier_indices'])
    allowed={tuple(r['source_step']['node']) for r in closed['units']}
    allowed.update(tuple(s['node']) for r in closed['units'] for s in r['local_steps'])
    closed['reads']=[r for r in closed['reads'] if tuple(r['node']) in allowed]


@pytest.mark.parametrize('operand',[0,1])
@pytest.mark.parametrize('fault',['facts','history','remote-descriptor'])
def test_binary_operand_histories(baseline,operand,fault):
    args,closed=copy.deepcopy(baseline)
    row=closed['frontier_units'][3]['input_frontiers'][operand]
    if fault=='facts': row['theorem']=row['facts_theorem']='forged_full_facts'
    elif fault=='history': row['input_frontier']['local_steps']=[]
    else: row['local_steps'][-1]['inputs'][0]['parent_name']='wrong-remote'
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('index',[1,2,4,5])
@pytest.mark.parametrize('fault',['proof','history'])
def test_v_and_carry_full_records(baseline,index,fault):
    args,closed=copy.deepcopy(baseline); row=closed['frontier_units'][index]
    if fault=='proof': row.pop('facts_theorem')
    elif row['source_step']['op']=='FW_multiref': row['local_steps'][-1]['inputs']=()
    else: row['input_frontier']['local_steps'][-1]['inputs']=()
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['score-proof','score-descriptor','join-reverse','operand-reverse',
    'drop-v','drop-carry','drop-dp','drop-score','duplicate','order','replica-axis'])
def test_complete_mixed_source_inventory(baseline,fault):
    args,closed=copy.deepcopy(baseline); rows=closed['frontier_units']
    if fault=='score-proof': rows[3]['theorem']=rows[3]['facts_theorem']='value_only'
    elif fault=='score-descriptor': rows[3]['source_step']['inputs']=()
    elif fault=='join-reverse': rows[3]['ordered_join']['pm_ordered_input_refs'][-1].reverse()
    elif fault=='operand-reverse': rows[3]['input_frontiers'].reverse()
    elif fault=='replica-axis': rows[4]['layout']='sharded'; rows[4]['gather_axis']=1
    else:
        if fault=='drop-v': rows=[r for i,r in enumerate(rows) if i%3!=1]
        elif fault=='drop-carry': rows=[r for i,r in enumerate(rows) if i%3!=2]
        elif fault=='drop-score': rows=[r for i,r in enumerate(rows) if i%3!=0]
        elif fault=='drop-dp': rows=rows[:3]
        elif fault=='duplicate': rows=rows+rows[:3]
        else: rows[0],rows[1]=rows[1],rows[0]
        reclassify(closed,rows)
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('key',['units','retained_units','deferred_units','ordered_joins','consumed_frontier_indices'])
def test_classification_is_not_authority(baseline,key):
    args,closed=copy.deepcopy(baseline); closed[key]=[]
    with pytest.raises(ValueError): transport(args,closed)


def test_earlier_genuine_same_shaped_carry(baseline):
    from dataclasses import asdict
    from Verdict.runtime_lineage import _Index
    args,closed=copy.deepcopy(baseline)
    si,pi=[_Index(v,raw) for v,raw in zip(args[:2],args[3]._inputs[:2],strict=True)]
    # Use the same original alias constructor as the accepted head fixture.
    head_tests=previous.previous.previous.previous.previous
    alias_api=head_tests.predecessor
    for row in closed['retained_units']:
        steps=[]; slot=1
        for index,rank in [(si,0),*[(pi,r) for r in row['ranks']]]:
            cell=next(c for c in index.raw.values() if c.node[3]==27000 and c.rank==rank)
            port=alias_api.gathered._producer(index,cell.outputs[slot])
            step,actual_slot=alias_api._alias_producer(index,port,row['ranks'])
            assert actual_slot==slot
            steps.append(step)
        g=steps[0].outputs[slot]; ps=[s.outputs[slot] for s in steps[1:]]
        assert list(g.endpoint.shape)==row['global_shape']
        assert all(list(p.endpoint.shape)==row['local_shape'] for p in ps)
        row.update(source_step=asdict(steps[0]),local_steps=[asdict(s) for s in steps[1:]],source_output_slot=slot,slot=slot,
            sm_output_tid=g.endpoint.tid,sm_output_ref=list(g.endpoint.ref),
            pm_output_tids=[p.endpoint.tid for p in ps],pm_output_refs=[list(p.endpoint.ref) for p in ps])
    reclassify(closed,closed['frontier_units'])
    with pytest.raises(ValueError,match='inventory'): transport(args,closed)


@pytest.mark.parametrize('operand',[0,1])
def test_binary_input_whole_bw_history(baseline,operand):
    args,closed=copy.deepcopy(baseline)
    score=previous.selected(args)
    bw=next(n for n in reversed(args[1].nodes()) if args[1].node_opname(n).startswith('BW_'))
    args[1]._node2outputs[bw]=[args[1].node_inputs(score.node)[operand]]
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['signature','parent','shape-float','scalar'])
def test_both_divisions_inventory_only(source,world,fault):
    from Verdict.runtime_lineage import _Index
    args=copy.deepcopy(source); n=0 if world=='sm' else 1
    index=_Index(args[n],args[3]._inputs[n])
    cell=next(c for c in index.raw.values() if c.node.cid==271003+(18000 if world=='sm' else 19000))
    if fault=='signature': cell.ir.signature='torch.mul'
    elif fault=='parent': cell._input_irs[0].parent.tid+=1
    elif fault=='shape-float': cell._output_irs[0].shape=tuple(float(d) for d in cell._output_irs[0].shape)
    else: cell.kwargs['__consts']=[True]
    with pytest.raises(ValueError): predecessor._successor(index,cell)


def test_dynamic_nonsquare_all_peers_public():
    args=prepared(D=1,alias_tid=390019,seqlen=6,metadata='all-peers',successor_metadata='all-peers')
    text,result=api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[3,1,3,1,1]
    row=result['units'][0]
    assert row['global_shape']==[1,3,6,6] and row['local_shape']==[1,3,6,2]
    assert row['dimensions']==dict(D=1,T=3,B=1,S=3,H=6,C=2)
    assert row['input_shape']==[1,1,6,6] and row['input_frontier']['dimensions']['H']==1
    assert all(r['input_metadata']=='all-peers' and r['producer_metadata']=='all-peers' for r in result['reads'])
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split')==3
    assert text.count('SourceRank4Exchange.axis1_output_facts')==1
    assert all(c['op']=='FW_div' and c['value_proved'] is False for c in row['downstream_consumers'])
