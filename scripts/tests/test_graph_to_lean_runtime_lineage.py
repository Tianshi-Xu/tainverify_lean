"""Portable source-only entry tracer; no captures, GPU, or filesystem outputs."""
from nnscaler.ir.cten import IRObject
from collections import namedtuple
from types import SimpleNamespace as NS
from unittest.mock import patch
import copy
import unittest
from Verdict import graph_to_lean as c
from trainverify.batch_source_authority import build_batch_record
from trainverify.runtime_source_authority import build_snapshot

T = namedtuple('T', 'wtype rank mb tid v')
N = namedtuple('N', 'wtype rank mb cid irname')

class IR:
    def __init__(self, tid, name, shape, bounds=None, param=False):
        self.tid = tid
        self.parent = NS(tid=tid, name=name, shape=shape)
        self.indmap = bounds or tuple((0, d) for d in shape)
        self.valmap = (0, 1)
        self.shape = tuple(b-a for a,b in self.indmap)
        self.param = param
    def is_param(self): return self.param
    def is_attr(self): return self.param
    def is_grad(self): return False

class Graph:
    def __init__(self, world, units, tp):
        self.W = NS(num_dp=units if world=='p' else 1, num_mb=1, num_tp=tp, plan_ndevs=tp, runtime_ndevs=units*tp)
        self.cells=[]; self.shapes={}
        for r in range(units*tp if world=='p' else 1):
            b=1 if world=='p' else units
            k=r%tp if world=='p' else 0
            x=IR(10,'input_ids',(b,2)); pos=IR(11,'position_ids',(b,2))
            w=IR(20,'weight',(32,tp*3),((0,32),(k*3,(k+1)*3)) if world=='p' else None,True)
            y=IR(30,'embedding',(b,2,tp*3),((0,b),(0,2),(k*3,(k+1)*3)) if world=='p' else None)
            refs={i.tid:T(world,r,-1 if i.param else 0,i.tid,0 if i.param else 1) for i in (x,pos,w,y)}
            for cid,op,ins,outs in [(5,'DATALOADER',[],[x,pos]),(9,'FW_embedding',[x,w],[y])]:
                n=N(world,r,0,cid,op)
                kw={} if op=='DATALOADER' else dict(start=0,stop=32,padding_idx=None)
                ir=NS(signature=op,kwargs=kw,mirror=NS(cid=cid+100),inputs=lambda ins=ins:ins,outputs=lambda outs=outs:outs)
                if op=='DATALOADER':
                    ir.input=lambda i: IRObject('loader',tid=99)
                    ir.outputs=lambda: [IRObject('input_ids',tid=10),IRObject('position_ids',tid=11)]
                cell=NS(node=n,rank=r,opname=op,ir=ir,kwargs=kw,_input_irs=ins,_output_irs=outs,inputs=[refs[i.tid] for i in ins],outputs=[refs[i.tid] for i in outs])
                self.cells.append(cell)
            self.shapes.update({refs[i.tid]:i.shape for i in (x,pos,w,y)})
    def nodes(self): return [x.node for x in self.cells]
    def tensors(self): return list(self.shapes)
    def cell(self,n): return next(x for x in self.cells if x.node==n)
    def node_inputs(self,n): return self.cell(n).inputs
    def node_outputs(self,n): return self.cell(n).outputs
    def node_opname(self,n): return self.cell(n).opname
    def node_kwargs(self,n): return self.cell(n).kwargs
    def tensor_shape(self,t): return self.shapes[t]
    def is_initialized(self,t): return t.v==0

def fixture(units=2,tp=2):
    sm,pm=Graph('s',units,tp),Graph('p',units,tp)
    fields=('world','runtime_rank','microbatch','source_tid','version')
    writers=[dict(ref=dict(world='p',runtime_rank=x.rank,microbatch=0,source_cid=x.node.cid,call_instance=0,op=x.opname,origin='fixture'),inputs=[dict(zip(fields,t)) for t in x.inputs],outputs=[dict(zip(fields,t)) for t in x.outputs]) for x in pm.cells]
    snapshot=build_snapshot(writers)
    snapshot['source']=dict(plan_ndevs=tp,runtime_ndevs=units*tp);snapshot['runtime_ndevs']=units*tp
    snapshot['rank_sources']={str(r):f'class GenModel:\n    rank={r}\n    world_size={units*tp}\n    def __init__(self): pass\n    def segment9(self, input_ids_10, position_ids_11): pass\ndef _train_step(model, loader_99):\n    _ = None\n    model.zero_grad()\n    input_ids_10, position_ids_11 = next(*(loader_99,))\n    result = nnscaler.runtime.executor.fexecute(\'segment9\', model.segment9, *(input_ids_10, position_ids_11), requires_grad=True)\n    del input_ids_10, position_ids_11\n    return result\n' for r in range(units*tp)}
    from trainverify.runtime_source_authority import bind_reducers
    for writer in snapshot["writers"]: writer["parameter_grad_tids"]=[]
    bind_reducers(snapshot)
    model=dict(seqlen=2,num_embeddings=32)
    receipt=dict(model=model,batch_size=1,compute=dict(plan_ngpus=tp,runtime_ngpus=units*tp))
    reference=dict(model=model,batch_size=units)
    cfg=dict(num_pp=1,num_mb=1,gbs=units,normalizer=1,objective='sum',units=[dict(unit=u,ranks=list(range(u*tp,(u+1)*tp)),positions=[u]) for u in range(units)])
    payloads=[dict(input_ids=[[u, u+1]],position_ids=[[0,1]]) for u in range(units)]
    global_inputs={k:sum([p[k] for p in payloads],[]) for k in payloads[0]}
    record=build_batch_record(cfg,payloads,global_inputs,snapshot)
    snapshot['adapter_source']=copy.deepcopy(writers)
    for row in snapshot['adapter_source']:
        if row['ref']['op']!='DATALOADER': continue
        names=['input_ids_10','position_ids_11']
        row['generated_dataloader']=dict(loader='loader_99',outputs=names,
            output_refs=copy.deepcopy(row['outputs']),writer=copy.deepcopy(row['ref']),ordinal=1,runtime={},
            training_calls=[dict(method='segment9',source_cid=9,runtime_rank=row['ref']['runtime_rank'],
                microbatch=0,call_instance=0,ordinal=1,arguments=names,parameters=names,
                input_refs=copy.deepcopy(row['outputs']))])
    from trainverify.runtime_source_authority import bind_adapters
    bind_adapters(snapshot)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),snapshot,record,receipt,reference)

class RuntimeLineageTests(unittest.TestCase):
    def test_entry_consumes_closure_and_initial_boundary_before_later_block(self):
        sm,pm,authority=fixture()
        v=NS(get_graph=lambda:(sm,pm),get_graph_compact=lambda:(sm,pm))
        with patch('sys.argv',['graph_to_lean','--out','never-emitted.lean','--module','NeverEmitted']):
            args=c.parse_args()
        args.runtime_batch_authority='observation.json'
        with patch.object(c,'load_verifier',return_value=v), patch.object(c,'_load_runtime_lineage_inputs',return_value=authority,create=True), patch.object(c,'backward_closure_tids',wraps=c.backward_closure_tids) as closure:
            with self.assertRaises(ValueError) as caught:
                c._generate(args)
        self.assertIn('runtime-world-render/public-adapter',str(caught.exception))
        receipt=caught.exception.receipt
        self.assertEqual(closure.call_count,2)
        self.assertEqual(len(receipt['lineages']),4)
        self.assertFalse(receipt['proof_admissible'])
        self.assertTrue(receipt['boundary'])
        self.assertEqual(receipt['lineages'][-1]['units'][1]['positions'],[1])
        self.assertEqual(receipt['lineages'][-1]['units'][0]['pieces'][1]['bounds'][-1],[3,6])

class ValidationTests(unittest.TestCase):
    def run_trace(self, units=2, tp=2):
        from Verdict.runtime_lineage import trace
        sm,pm,a=fixture(units,tp)
        sv,pv=c._lower_runtime_graphs(sm,pm)
        return sv,pv,trace(sv,pv,*a)

    def test_heldout_uniform_three_units_and_three_tp(self):
        sv,pv,(ls,gaps,v)=self.run_trace(3,3)
        self.assertEqual(len(ls[-1].units),3)
        self.assertEqual([u.positions for u in ls[-1].units],[(0,),(1,),(2,)])
        self.assertEqual(ls[-1].units[-1].pieces[-1].bounds[-1],(6,9))
        self.assertEqual(len({p.endpoint.ref for l in ls for u in l.units for p in u.pieces}),36)

    def test_two_embedding_coordinated_export_swaps(self):
        from Verdict.runtime_lineage import trace
        sm,pm,a=fixture()
        for graph,raw in ((sm,a[0]),(pm,a[1])):
            for cell in list(graph.cells):
                if cell.opname!='FW_embedding': continue
                other=copy.deepcopy(cell)
                other.node=other.node._replace(cid=other.node.cid+1)
                other.inputs=[cell.inputs[0]._replace(tid=11),cell.inputs[1]._replace(tid=21)]
                other.outputs=[cell.outputs[0]._replace(tid=31)]
                other._input_irs[0].tid=11; other._input_irs[0].parent.name='position_ids'
                other._input_irs[1].tid=21; other._input_irs[1].parent.name='other_weight'
                other._output_irs[0].tid=31
                other.ir=NS(signature=cell.ir.signature,kwargs=other.kwargs,mirror=NS(cid=110),
                            inputs=lambda other=other:other._input_irs,outputs=lambda other=other:other._output_irs)
                graph.shapes[other.inputs[1]]=graph.shapes[cell.inputs[1]]
                graph.shapes[other.outputs[0]]=graph.shapes[cell.outputs[0]]
                graph.cells.append(other);raw.append(copy.deepcopy(other))
                # Coordinated source-address exports are internally consistent,
                # but do not alter the independently retained raw original ports.
                cell.inputs,other.inputs=other.inputs,cell.inputs
                cell.outputs,other.outputs=other.outputs,cell.outputs
        sv,pv=c._lower_runtime_graphs(sm,pm)
        with self.assertRaisesRegex(ValueError,'raw ordered port'): trace(sv,pv,*a)

    def test_current_rank_input_unpacking_order_is_authority(self):
        from Verdict.runtime_lineage import trace
        sm,pm,a=fixture();sv,pv=c._lower_runtime_graphs(sm,pm)
        a[2]['rank_sources']['0']=a[2]['rank_sources']['0'].replace('input_ids_10, position_ids_11','position_ids_11, input_ids_10')
        with self.assertRaisesRegex(ValueError,'generated.*order'): trace(sv,pv,*a)

    def test_batch_mutations_and_noncontiguous_guard(self):
        from Verdict.runtime_lineage import trace
        for fault in ('position','readref','portorder','noncontiguous'):
            sm,pm,a=fixture(); sv,pv=c._lower_runtime_graphs(sm,pm)
            if fault=='position': a[3]['groups'][1]['positions']=[0]
            if fault=='readref': a[3]['rank_inputs'][0]['refs'][0]['version']=0
            if fault=='portorder': a[3]['rank_inputs'][0]['refs'].reverse()
            if fault=='noncontiguous': a[3]['config']['units'][0]['ranks']=[0,2]
            with self.subTest(fault=fault), self.assertRaises(ValueError): trace(sv,pv,*a)

    def test_coordinated_export_swap_rejected_by_raw_ports(self):
        from Verdict.runtime_lineage import trace
        sm,pm,a=fixture()
        # Two indistinguishable-shaped loader roles swapped on BOTH exports;
        # authoritative original IR parents and original port order remain unchanged.
        for graph in (sm,pm):
            for cell in graph.cells:
                if cell.opname=='DATALOADER': cell.outputs.reverse()
                else: cell.inputs[0]=cell.inputs[0]._replace(tid=11)
        sv,pv=c._lower_runtime_graphs(sm,pm)
        with self.assertRaisesRegex(ValueError,'raw ordered port'): trace(sv,pv,*a)

    def test_consumer_rejects_graph_written_initial_and_unimplemented_roles(self):
        from dataclasses import replace
        from Verdict.runtime_lineage import consume,Role
        sv,pv,(ls,gaps,v)=self.run_trace()
        for bad in (replace(ls[-1],target=replace(ls[-1].target,phase='initial')),
                    replace(ls[-1],role=Role.GRADIENT),replace(ls[-1],role=Role.VALUE_PART)):
            with self.subTest(role=bad.role),self.assertRaises(ValueError):
                consume(sv,pv,(*ls[:-1],bad),gaps,v,c.backward_closure_tids)

    def test_consumer_rejects_forged_nested_lineage(self):
        from dataclasses import replace
        from Verdict.runtime_lineage import consume,Role
        for fault in ('positions','copy','parameter','pieces','bounds'):
            with self.subTest(fault=fault):
                sv,pv,(ls,gaps,v)=self.run_trace()
                consume(sv,pv,ls,gaps,v,c.backward_closure_tids)
                target=ls[-1];units=target.units
                if fault=='positions': units=tuple(replace(u,positions=units[1-i].positions) for i,u in enumerate(units))
                elif fault=='copy': units=tuple(replace(u,reconstruction='tp-copy-obligation') for u in units)
                elif fault=='pieces': units=tuple(replace(u,pieces=()) for u in units)
                elif fault=='bounds': units=tuple(replace(u,pieces=tuple(replace(p,bounds=(*p.bounds[:-1],(0,6))) for p in u.pieces)) for u in units)
                else:
                    target=replace(target,role=Role.PARAMETER,composition='unit-parameter-copies',obligations=('initial-parameter-value-equality-unproved',))
                    units=tuple(replace(u,positions=()) for u in units)
                forged=replace(target,units=units)
                with self.assertRaises(ValueError): consume(sv,pv,(*ls[:-1],forged),gaps,v,c.backward_closure_tids)

    def test_unreachable_wrong_loader_and_stale_input_rejected(self):
        from Verdict.runtime_lineage import trace
        for fault in ('return','wrong_loader','nested','stale'):
            with self.subTest(fault=fault):
                sm,pm,a=fixture();sv,pv=c._lower_runtime_graphs(sm,pm)
                trace(sv,pv,*a)
                text=a[2]['rank_sources']['0']
                if fault=='return': text=text.replace('    input_ids_10,','    return\n    input_ids_10,')
                elif fault=='wrong_loader': text=text.replace('next(*(loader_99,))','next(*(unrelated_loader,))')
                elif fault=='nested': text=text.replace('    input_ids_10,','    def unused():\n        input_ids_10,')
                else: text=text.replace('    result =', '    input_ids_10 = stale_input\n    result =')
                a[2]['rank_sources']['0']=text
                with self.assertRaises(ValueError): trace(sv,pv,*a)

    def test_nested_types_order_obligations_and_metadata_from_fresh_baselines(self):
        from dataclasses import replace
        from Verdict.runtime_lineage import consume
        for fault in ('unit', 'boolunit', 'unitorder', 'pieceorder', 'valuepart', 'obligations', 'emptyunits', 'metadata', 'plainmetadata'):
            with self.subTest(fault=fault):
                sv,pv,(ls,gaps,v)=self.run_trace()
                target=ls[-1]; u=target.units[0]
                if fault=='unit': u=None
                elif fault=='boolunit': u=replace(u,unit=False)
                elif fault=='pieceorder': u=replace(u,pieces=tuple(reversed(u.pieces)))
                elif fault=='valuepart': u=replace(u,pieces=(replace(u.pieces[0],value_part=(1,2)),*u.pieces[1:]))
                if fault in ('unit','boolunit','pieceorder','valuepart'): target=replace(target,units=(u,*target.units[1:]))
                elif fault=='unitorder': target=replace(target,units=tuple(reversed(target.units)))
                elif fault=='obligations': target=replace(target,obligations=())
                elif fault=='emptyunits': target=replace(target,units=())
                elif fault=='metadata': v['batch_input_mapping_verified']=False
                elif fault=='plainmetadata': v=dict(v)
                with self.assertRaises(ValueError): consume(sv,pv,(*ls[:-1],target),gaps,v,c.backward_closure_tids)

    def test_consumer_rechecks_live_raw_and_source_before_first_closure(self):
        from Verdict.runtime_lineage import trace, consume
        for fault in ('raw', 'source', 'loader', 'batch'):
            with self.subTest(fault=fault):
                sm,pm,a=fixture(); sv,pv=c._lower_runtime_graphs(sm,pm)
                ls,gaps,v=trace(sv,pv,*a)
                if fault=='raw': a[1][1]._output_irs[0].indmap=((0,1),(0,2),(0,6))
                elif fault=='source': a[2]['rank_sources']['0']=a[2]['rank_sources']['0'].replace('    result =','    return\n    result =')
                elif fault=='loader': a[1][0].ir.input=lambda i: IRObject('unrelated',tid=99)
                else: a[3]['groups'][0]['positions']=[1]
                with patch.object(c,'backward_closure_tids',wraps=c.backward_closure_tids) as closure:
                    with self.assertRaises(ValueError): consume(sv,pv,ls,gaps,v,closure)
                    closure.assert_not_called()

    def test_strict_prefix_rejects_hidden_chained_writes_but_keeps_postconsumer_delete(self):
        from Verdict.runtime_lineage import trace, consume
        for insertion in ('    del input_ids_10\n', '    input_ids_10 = alias = stale_input\n',
                          '    input_ids_10 = (alias := stale_input)\n', '    mutate(input_ids_10)\n',
                          '    if True: input_ids_10 = stale_input\n'):
            with self.subTest(insertion=insertion):
                sm,pm,a=fixture(); sv,pv=c._lower_runtime_graphs(sm,pm)
                ls,gaps,v=trace(sv,pv,*a)
                healthy=consume(sv,pv,ls,gaps,v,c.backward_closure_tids)
                self.assertEqual(healthy['coverage']['typed_targets'],4)
                self.assertIn('    del input_ids_10, position_ids_11',a[2]['rank_sources']['0'])
                a[2]['rank_sources']['0']=a[2]['rank_sources']['0'].replace('    result =',insertion+'    result =')
                with self.assertRaises(ValueError): trace(sv,pv,*a)

    def test_current_raw_loader_and_training_signature_not_self_metadata(self):
        from Verdict.runtime_lineage import trace
        for fault in ('signature','coherentloader','arguments','consumer','chainednext','chainedconsumer'):
            with self.subTest(fault=fault):
                sm,pm,a=fixture(); sv,pv=c._lower_runtime_graphs(sm,pm)
                trace(sv,pv,*a)
                text=a[2]['rank_sources']['0']
                if fault=='signature': text=text.replace('_train_step(model, loader_99)', '_train_step(model, unrelated_loader)')
                elif fault=='coherentloader':
                    text=text.replace('loader_99','unrelated_loader')
                    a[2]['adapter_source'][0]['generated_dataloader']['loader']='unrelated_loader'
                elif fault=='arguments': text=text.replace('*(input_ids_10, position_ids_11)', '*(position_ids_11, input_ids_10)')
                elif fault=='consumer': text=text.replace('model.segment9','model.unrelated')
                elif fault=='chainednext': text=text.replace('input_ids_10, position_ids_11 = next','alias = input_ids_10, position_ids_11 = next')
                else: text=text.replace('    result =','    alias = result =')
                a[2]['rank_sources']['0']=text
                with self.assertRaises(ValueError): trace(sv,pv,*a)

    def test_gap_receipt_independent_of_tensor_registration_order(self):
        from Verdict.runtime_lineage import consume
        sv,pv,(ls,gaps,v)=self.run_trace()
        before=consume(sv,pv,ls[:1],gaps,v,c.backward_closure_tids)
        sv._tensors.reverse();pv._tensors.reverse()
        after=consume(sv,pv,ls[:1],gaps,v,c.backward_closure_tids)
        self.assertEqual(before,after)

    def test_partial_map_never_complete_and_roles_do_not_collapse(self):
        from Verdict.runtime_lineage import consume,Role
        sv,pv,(ls,gaps,v)=self.run_trace()
        self.assertEqual(ls[2].role,Role.PARAMETER)
        self.assertEqual(ls[0].role,Role.BATCH)
        self.assertEqual(ls[2].units[0].positions,())
        receipt=consume(sv,pv,ls[:1],gaps,v,c.backward_closure_tids)
        self.assertFalse(receipt['global_complete'])
        self.assertTrue(receipt['gaps'])

if __name__=='__main__': unittest.main()
