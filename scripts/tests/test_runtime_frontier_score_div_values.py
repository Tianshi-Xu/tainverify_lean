"""Original mixed score division boundary; portable source authority, no kernel claim."""
import copy
import importlib
import importlib.util
from unittest.mock import patch
import pytest
from scripts.tests import test_runtime_frontier_score_exchange_values as previous
from Verdict import runtime_frontier_score_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_score_div_values'), 'score division renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_score_div_values')


def test_public_score_div_tracer():
    subject=api(); args=previous.prepared(); observed=[]
    original=predecessor.render
    def fresh(*six):
        result=original(*six); observed.append(result)
        read.reset_mock(); unit.reset_mock()
        return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh, \
         patch.object(subject.backend,'_read',wraps=subject.backend._read) as read, \
         patch.object(subject.backend,'_unit',wraps=subject.backend._unit) as unit:
        text,result=subject.render(*args)
    assert refresh.call_count==1 and all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    old=observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[7,2,6,2,2]
    assert read.call_count==7 and unit.call_count==2
    assert result['consumed_frontier_indices']==[0,3]
    for u,row in enumerate(result['units']):
        assert row['input_frontier'] is old['frontier_units'][3*u]
        assert unit.call_args_list[u].args[0] is row['input_frontier']
        assert row['global_shape']==[2,3,3,3] and row['local_shape']==[1,3,3,1]
        assert row['dimensions']==dict(D=2,T=3,B=1,H=3,Q=3,C=1)
        assert row['gather_axis']==3 and row['scalar_nat']==4
        v=result['frontier_units'][3*u+1]
        assert v is old['frontier_units'][3*u+1] and v['layout']=='replicated_within_dp' and v['gather_axis'] is None
        assert result['deferred_units'][u]['source_boundary'] is v
        assert result['retained_units'][u] is old['frontier_units'][3*u+2]
    assert text.count('SourceDivRead.div_value_of_split')==7
    assert text.count('source_div_unit_output_reconstruct')==2
    assert '∀ y ∈' in text and 'InitialParameterValues s p' in text
    assert all(result[f] is False for f in ('kernel_value_proved','proof_admissible','public_complete','torch_refinement'))
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'):
        assert bad not in text
    import os,json
    from pathlib import Path
    if os.environ.get('SCORE_DIV_EVIDENCE'):
        dest=Path(os.environ['SCORE_DIV_EVIDENCE']); dest.mkdir(parents=True,exist_ok=True)
        (dest/'portable-public.lean').write_text(text)
        (dest/'portable-public.json').write_text(json.dumps(result,indent=2))
        (dest/'predecessor.lean').write_text(observed[0][0])
        (dest/'predecessor.json').write_text(json.dumps(old,indent=2))
        (dest/'public-calls.json').write_text(json.dumps(dict(predecessor=refresh.call_count,
            identical_six=True,backend_reads=read.call_count,backend_units=unit.call_count),indent=2))


@pytest.fixture(scope='module')
def source():
    return previous.prepared()


@pytest.fixture(scope='module')
def baseline(source):
    return source,predecessor.render(*source)[1]


def boundary(args,world='pm',rank=5):
    from Verdict.runtime_lineage import _Index
    n=0 if world=='sm' else 1
    index=_Index(args[n],args[3]._inputs[n])
    cid=271003+(18000 if world=='sm' else 19000)
    cell=next(c for c in index.raw.values() if c.node.cid==cid and c.rank==(0 if n==0 else rank))
    producer=api()._transpose._producer(index,cell.inputs[0])
    return index,cell,producer


RAW_FAULTS=['signature','signature-type','missing-ir','input-missing','output-missing',
    'input-extra','output-extra','input-parent','input-tid','output-tid','shape-bool','shape-float',
    'shape-rank','parent-shape-float','parent-id-bool','bounds-bool','bounds-overrun','value-bool',
    'value-float','value-partial','param-type','grad-type','kwargs','rounding','scalar-bool','scalar-str',
    'scalar-fraction','scalar-inf','scalar-nan','scalar-zero','scalar-negative','scalar-extra',
    'scalar-missing','collective_scopes','chunk_scopes','wred_scopes','input-version','output-version',
    'raw-normalized-scalar']


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',RAW_FAULTS)
def test_strict_raw_boundary(source,world,fault):
    from types import SimpleNamespace as NS
    args=copy.deepcopy(source); index,cell,p=boundary(args,world)
    x,y=cell._input_irs[0],cell._output_irs[0]
    if fault=='signature': cell.ir.signature='torch.mul'
    elif fault=='signature-type': cell.ir.signature=0
    elif fault=='missing-ir': cell.ir=None
    elif fault=='input-missing': cell._input_irs=None
    elif fault=='output-missing': cell._output_irs=None
    elif fault=='input-extra': cell._input_irs*=2
    elif fault=='output-extra': cell._output_irs*=2
    elif fault=='input-parent': x.parent.tid+=1
    elif fault=='input-tid': x.tid+=1
    elif fault=='output-tid': y.tid+=1
    elif fault=='shape-bool': y.shape=(True,*y.shape[1:])
    elif fault=='shape-float': y.shape=tuple(float(d) for d in y.shape)
    elif fault=='shape-rank': y.shape=y.shape[:3]
    elif fault=='parent-shape-float': y.parent.shape=tuple(float(d) for d in y.parent.shape)
    elif fault=='parent-id-bool': y.parent.tid=True
    elif fault=='bounds-bool': y.indmap=((False,y.indmap[0][1]),*y.indmap[1:])
    elif fault=='bounds-overrun': y.indmap=((0,y.parent.shape[0]+1),*y.indmap[1:])
    elif fault=='value-bool': y.valmap=(False,1)
    elif fault=='value-float': y.valmap=(0.0,1)
    elif fault=='value-partial': y.valmap=(0,2)
    elif fault=='param-type': y.param=0
    elif fault=='grad-type': y.is_grad=lambda:0
    elif fault=='kwargs': cell.kwargs['extra']=0
    elif fault=='rounding': cell.kwargs['rounding_mode']='floor'
    elif fault.startswith('scalar-'):
        cell.kwargs['__consts']={'scalar-bool':[True],'scalar-str':['4'],'scalar-fraction':[4.5],
            'scalar-inf':[float('inf')],'scalar-nan':[float('nan')],'scalar-zero':[0],
            'scalar-negative':[-4],'scalar-extra':[4,4],'scalar-missing':[]}[fault]
    elif fault.endswith('_scopes'):
        setattr(index.view,fault,dict(getattr(index.view,fault,{})))
        getattr(index.view,fault)[cell.node]=NS()
    elif fault=='input-version': cell.inputs[0]=cell.inputs[0]._replace(v=0)
    elif fault=='output-version': cell.outputs[0]=cell.outputs[0]._replace(v=0)
    else: cell.kwargs=dict(cell.kwargs,__consts=[5.0])
    with pytest.raises((ValueError,KeyError)):
        api()._div(index,cell,p)


@pytest.mark.parametrize('fault',['export','writer-input','writer-output','call-bool','call-negative','call-missing'])
def test_original_export(source,fault):
    args=copy.deepcopy(source); index,cell,p=boundary(args)
    writer=next(w for w in index.view._collective_source['writers']
        if w['ref']['source_cid']==cell.node.cid and w['ref']['runtime_rank']==cell.rank)
    if fault=='export': writer['export_id']='forged'
    elif fault=='writer-input': writer['inputs']=[]
    elif fault=='writer-output': writer['outputs']=[]
    elif fault=='call-bool': writer['ref']['call_instance']=False
    elif fault=='call-negative': writer['ref']['call_instance']=-1
    else: writer['ref'].pop('call_instance')
    with pytest.raises((ValueError,KeyError)): api()._div(index,cell,p)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['descriptor','label','execution','inverse','selected-write','bw-write'])
def test_read_schedule_suffix(source,world,fault):
    from dataclasses import replace
    args=copy.deepcopy(source); index,cell,p=boundary(args,world)
    step,_=api()._div(index,cell,p); label=world; order=args[-1][world]
    if fault=='descriptor': step=replace(step,inputs=(replace(p,parent_name='forged'),))
    elif fault=='label': label='pm' if world=='sm' else 'sm'
    elif fault in ('execution','inverse'): order['execution_to_source' if fault=='execution' else 'source_to_execution'].reverse()
    else:
        node=cell.node if fault=='selected-write' else next(n for n in reversed(index.view.nodes()) if str(index.view.node_opname(n)).startswith('BW_'))
        index.view._node2outputs[node]=[index.view.node_inputs(cell.node)[0]]
    with pytest.raises(ValueError): api()._read(index,label,step,order)


def unit_inputs(args,closed):
    si,gc,g=boundary(args,'sm'); old=closed['frontier_units'][3]
    global_,ga=api()._div(si,gc,g); steps=[]
    for rank in old['ranks']:
        pi,cell,p=boundary(args,rank=rank); steps.append(api()._div(pi,cell,p)[0])
    names={s.node:f'frontierScoreDivRead_{s.outputs[0].endpoint.tid}' for s in [global_,*steps]}
    return si,pi,old,global_,steps,names,ga['scalar_nat']


@pytest.mark.parametrize('fault',['reverse','duplicate','cross-dp','omitted','input-reverse','output-parent','scalar','local-scalar','missing-consumer','extra-consumer'])
def test_unit_original_cover(baseline,fault):
    from dataclasses import replace
    args,closed=copy.deepcopy(baseline); si,pi,old,g,steps,names,c=unit_inputs(args,closed)
    if fault=='reverse': steps.reverse()
    elif fault=='duplicate': steps[-1]=steps[0]
    elif fault=='cross-dp':
        other,cell,p=boundary(args,rank=2); steps[-1]=api()._div(other,cell,p)[0]
    elif fault=='omitted': steps.pop()
    elif fault=='input-reverse': old['pm_output_refs'].reverse()
    elif fault=='output-parent': pi.raw[steps[-1].node]._output_irs[0].parent.tid+=1
    elif fault=='scalar': c=5
    elif fault=='local-scalar':
        cell=pi.raw[steps[-1].node]; cell.kwargs=dict(cell.kwargs,__consts=[5.0])
        original=next(c for c in pi.view.source.cells if tuple(c.node)==steps[-1].node)
        original.kwargs=dict(cell.kwargs)
        assert api()._div(pi,cell,steps[-1].inputs[0])[1]['scalar_nat']==5
    elif fault=='missing-consumer': pi.raw[steps[-1].node].inputs=[]
    else:
        # Another forward reader of an existing selected source: not an omitted peer.
        node=next(n for n in pi.view.nodes() if n.rank==5 and n.cid==271003+17002)
        pi.view._node2inputs[node]=[pi.view.node_inputs(steps[-1].node)[0]]
    with pytest.raises((ValueError,KeyError)): api()._unit(si,pi,old,g,steps,names,c)


def authenticate(args,closed):
    from Verdict.runtime_lineage import _Index
    si,pi=[_Index(v,raw) for v,raw in zip(args[:2],args[3]._inputs[:2],strict=True)]
    return api()._frontiers(*args[:2],si,pi,*args[2:],closed)


def test_history_preflight_uses_source_identity(request):
    assert hasattr(api(),'_history_identity'), 'source-derived history identity preflight missing'
    from Verdict.runtime_lineage import _Index
    args,closed=copy.deepcopy(request.getfixturevalue('baseline'))
    si,pi=[_Index(v,raw) for v,raw in zip(args[:2],args[3]._inputs[:2],strict=True)]
    row=closed['frontier_units'][0]
    assert hasattr(api(),'_history_identity'), 'source-derived history identity preflight missing'
    api()._history_identity(si,pi,row,args[3]._inputs[3]['config']['units'])
    row['facts_theorem']=row['theorem']='forged'
    with pytest.raises(ValueError): api()._history_identity(si,pi,row,args[3]._inputs[3]['config']['units'])


@pytest.mark.parametrize('operand',[0,1])
@pytest.mark.parametrize('fault',['facts','history','join'])
def test_binary_histories(baseline,operand,fault):
    args,closed=copy.deepcopy(baseline); score=closed['frontier_units'][3]['input_frontier']
    row=score['input_frontiers'][operand]
    if fault=='facts': row['facts_theorem']=row['theorem']='forged'
    elif fault=='history': row['input_frontier']['local_steps']=[]
    else: score['ordered_join']['pm_ordered_input_refs'][-1].reverse()
    with pytest.raises(ValueError): authenticate(args,closed)


@pytest.mark.parametrize('fault',['score-facts','v-facts','carry-facts','carry-history','replica-axis',
    'drop-v','drop-carry','drop-dp','drop-score','reorder','duplicate','classification'])
def test_complete_mixed_inventory(baseline,fault):
    args,closed=copy.deepcopy(baseline); rows=closed['frontier_units']
    if fault.endswith('-facts'):
        row=rows[{'score-facts':3,'v-facts':4,'carry-facts':5}[fault]]
        row['facts_theorem']=row['theorem']='genuine_but_wrong_previous_fact'
    elif fault=='carry-history': rows[5]['local_steps'][-1]['inputs']=()
    elif fault=='replica-axis': rows[4]['gather_axis']=1; rows[4]['layout']='sharded'
    elif fault=='classification': closed['retained_units']=[]
    else:
        if fault=='drop-v': rows=[r for i,r in enumerate(rows) if i%3!=1]
        elif fault=='drop-carry': rows=[r for i,r in enumerate(rows) if i%3!=2]
        elif fault=='drop-dp': rows=rows[:3]
        elif fault=='drop-score': rows=[r for i,r in enumerate(rows) if i%3!=0]
        elif fault=='duplicate': rows=rows+rows[:3]
        else: rows[0],rows[1]=rows[1],rows[0]
        closed['frontier_units']=rows
        closed['units']=[r for r in rows if r['source_step']['op']=='FW_matmul']
        closed['retained_units']=[r for r in rows if r['source_step']['op']=='FW_multiref']
        closed['deferred_units']=[d for d in closed['deferred_units'] if any(d['source_boundary'] is r for r in rows)]
        closed['consumed_frontier_indices']=[i for i,r in enumerate(rows) if r in closed['units']]
        nodes={tuple(s['node']) for r in closed['units'] for s in r['local_steps']}
        closed['reads']=[r for r in closed['reads'] if tuple(r['node']) in nodes]
    with pytest.raises(ValueError): authenticate(args,closed)


@pytest.mark.parametrize('kind',[None,'FW_unknown','FW_matmul','FW_div','AllToAllPrim'])
def test_classifier(kind):
    from types import SimpleNamespace as NS
    groups=[] if kind is None else [[NS(opname=kind)]]
    assert api()._classification(True,groups)=='retained'
    assert api()._classification(False,groups)==('ready' if kind=='FW_div' else 'deferred')


@pytest.mark.parametrize('other',[[],['FW_unknown'],['FW_div','FW_div'],['FW_matmul']])
def test_incomplete_division_cover(other):
    from types import SimpleNamespace as NS
    groups=[[NS(opname='FW_div')],[NS(opname=k) for k in other]]
    with pytest.raises(ValueError): api()._classification(False,groups)


def exchange_fixture(**kwargs):
    """Add the actual NEXT AA(3,2), never the earlier exchange route."""
    from types import SimpleNamespace as NS
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR,N,T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot,bind_reducers,bind_adapters,writer_export_id
    sm,pm,authority=previous.fixture(**kwargs); snapshot=copy.deepcopy(authority[2])
    alias=kwargs.get('alias_tid',271003); tp=kwargs.get('tp',3)
    divs=[c for c in pm.cells if c.node.cid==alias+19000]
    for div in divs:
        rank=div.rank; ranks=list(range(rank//tp*tp,(rank//tp+1)*tp)); x=div._output_irs[0]
        bounds=list(x.indmap); width=x.parent.shape[2]//tp
        bounds[3]=(0,x.parent.shape[3]); bounds[2]=(rank%tp*width,(rank%tp+1)*width)
        y=IR(alias+20000,'scaled_scores',x.parent.shape,tuple(bounds)); y.parent.tid=x.parent.tid
        refs=[div.outputs[0]._replace(rank=r) for r in ranks]
        inputs=[copy.deepcopy(next(c._output_irs[0] for c in divs if c.rank==r)) for r in ranks]
        kw=dict(idim=3,odim=2,ranks=ranks)
        aa=NS(node=N('p',rank,0,y.tid,'AllToAllPrim'),rank=rank,opname='AllToAllPrim',
            inputs=refs,outputs=[T('p',rank,0,y.tid,1)],kwargs=kw,_input_irs=inputs,_output_irs=[y])
        sig='nnscaler.runtime.adapter.nn.alltoall_alltoall'
        aa.ir=NS(signature=sig,inputs=lambda c=aa:c._input_irs,outputs=lambda c=aa:c._output_irs)
        # Preserve each rank's collective order; schedule adds remote peers.
        pm.cells.insert(pm.cells.index(div)+1,aa); pm.shapes[aa.outputs[0]]=y.shape
        v=next(c for c in pm.cells if c.rank==rank and c.node.cid==alias+17002)
        v.inputs[0]=aa.outputs[0]; v._input_irs[0]=copy.deepcopy(y)
        pm.cells.remove(v)
        writers=[c for c in pm.cells if any(r in c.outputs for r in v.inputs)]
        pm.cells.insert(max(pm.cells.index(c) for c in writers)+1,v)
        row=dict(ref=dict(world='p',runtime_rank=rank,microbatch=0,source_cid=y.tid,call_instance=0,
            op='AllToAllPrim',origin='fixture'),source_irname='AllToAllPrim',inputs=[tref(r) for r in refs],
            outputs=[tref(r) for r in aa.outputs],parameter_grad_tids=[],adapter_kwargs=kw.copy())
        adapter=copy.deepcopy(row); adapter['inputs']=[tref(div.outputs[0])]
        adapter['primitive']=dict(kind='AllToAllPrim',forward=True,kwargs=kw.copy(),signature=sig,
            generated_inputs=['after_div'],generated_outputs=['after_score_div_exchange'])
        for key,new in [('writers',row),('adapter_source',adapter)]:
            old=next(w for w in snapshot[key] if w['ref']['runtime_rank']==rank and w['ref']['source_cid']==v.node.cid)
            old['inputs']=[tref(r) for r in v.inputs]; snapshot[key].remove(old); snapshot[key].extend([new,old])
        snapshot['rank_sources'][str(rank)]=snapshot['rank_sources'][str(rank)].replace(
            '        after_post_2 = torch.matmul(after_div, projection_next_2)',
            f'        after_score_div_exchange = {sig}(after_div, idim=3, odim=2, ranks={ranks})\n'
            '        after_post_2 = torch.matmul(after_score_div_exchange, projection_next_2)')
    fresh=build_snapshot(snapshot['writers']); fresh.update({k:snapshot[k] for k in ('source','runtime_ndevs','rank_sources')})
    adapters={writer_export_id(w['ref']):w for w in snapshot['adapter_source']}
    fresh['adapter_source']=[adapters[writer_export_id(w['ref'])] for w in fresh['writers']]
    bind_reducers(fresh); bind_adapters(fresh)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),fresh,*authority[3:])


def test_dynamic_nonsquare_next_exchange_public():
    kwargs=dict(D=1,tp=3,alias_tid=390019,seqlen=6,metadata='all-peers',successor_metadata='all-peers')
    fixture=exchange_fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=fixture): args=previous.prepared(**kwargs)
    text,result=api().render(*args); row=result['units'][0]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')]==[4,1,3,1,1]
    assert row['global_shape']==[1,3,6,6] and row['local_shape']==[1,3,6,2]
    assert row['dimensions']==dict(D=1,T=3,B=1,H=3,Q=6,C=2)
    aa=[c for c in row['downstream_consumers'] if c['op']=='AllToAllPrim']
    assert len(aa)==3 and all(c['source_kwargs']['idim']==3 and c['source_kwargs']['odim']==2 and c['value_proved'] is False for c in aa)
    assert text.count('SourceDivRead.div_value_of_split')==4
    assert text.count('source_div_unit_output_reconstruct')==1
    assert 'SourcePrimitiveRead' not in text and 'softmax_value' not in text
    import os,json
    from pathlib import Path
    if os.environ.get('SCORE_DIV_EVIDENCE'):
        dest=Path(os.environ['SCORE_DIV_EVIDENCE']); dest.mkdir(parents=True,exist_ok=True)
        (dest/'dynamic-public.lean').write_text(text)
        (dest/'dynamic-public.json').write_text(json.dumps(result,indent=2))

@pytest.fixture(scope='module')
def next_source():
    kwargs=dict(D=1,tp=3,alias_tid=390019,seqlen=6,metadata='all-peers',successor_metadata='all-peers')
    f=exchange_fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f): return previous.prepared(**kwargs)


def test_next_exchange_inventory_boundary(next_source):
    from Verdict.runtime_lineage import _Index
    pi=_Index(next_source[1],next_source[3]._inputs[1])
    cell=next(c for c in pi.raw.values() if c.node.cid==410019)
    row=api()._successor(pi,cell)
    assert row['op']=='AllToAllPrim' and row['source_kwargs']['idim']==3 and row['source_kwargs']['odim']==2
    assert row['value_proved'] is False and row['output_shapes']==[[1,3,2,6]]




def test_next_exchange_inventory(next_source):
    from Verdict.runtime_lineage import _Index
    subject=api()
    assert hasattr(subject,'_successor'), 'next AA(3,2) inventory adapter missing'
    index=_Index(next_source[1],next_source[3]._inputs[1])
    cells=[c for c in index.raw.values() if c.node.cid==410019]
    assert len(cells)==3
    for cell in cells:
        row=subject._successor(index,cell)
        assert row['op']=='AllToAllPrim' and row['axes']==[3,2] and row['value_proved'] is False
        assert row['output_shapes']==[[1,3,2,6]]
        assert len(row['source_inputs'])==3
