"""Source-scoped prefix availability must not break complete input schedules."""
import tempfile
import unittest
from pathlib import Path
from scripts.tests.test_runtime_input_schedule_kernel import mixed_world


def collective_world(root, k, unsupported=False, chain=False, between=False, fault=None, normalize=False, project=False, gather=False):
    """Independent raw IR + source-adapter snapshot, with actual CPU loader feeds."""
    import copy
    from types import SimpleNamespace as NS
    from Verdict import graph_to_lean as c
    from Verdict.runtime_world import render
    from Verdict.runtime_input_feed import bind
    from scripts.tests.test_runtime_input_feed import observed
    from scripts.tests.test_graph_to_lean_runtime_lineage import Graph, T, N, IR
    from trainverify.runtime_source_authority import build_snapshot, bind_adapters
    source = observed(root, 1, k)
    sm, pm = Graph('s', 1, k), Graph('p', 1, k)
    producers = pm.cells[1::2]
    for p in producers:
        for ir in (p._input_irs[1], p._output_irs[0]):
            sh = (32, k*3) if ir.is_param() else (1, 2, k*3)
            ir.parent.shape = sh; ir.shape = sh; ir.indmap = tuple((0,d) for d in sh)
        pm.shapes[p.inputs[1]] = p._input_irs[1].shape
        pm.shapes[p.outputs[0]] = p._output_irs[0].shape
    cells = []
    for rank, p in enumerate(producers):
        collective = NS(node=N('p',rank,0,20,'AllToAllAllToAllPrim'), rank=rank,
            opname='AllToAllPrim', kwargs=dict(ranks=list(range(k)),idim=1,odim=2),
            inputs=[q.outputs[0] for q in producers], outputs=[T('p',rank,0,90,1)])
        pm.shapes[collective.outputs[0]] = (1,2*k,3)
        cells += [pm.cells[2*rank],p]
        if unsupported:
            unknown=copy.deepcopy(p); unknown.node=unknown.node._replace(cid=15,irname='FW_contiguous')
            unknown.opname='FW_contiguous';unknown.kwargs={};unknown.inputs=[p.outputs[0]]
            unknown.outputs=[T('p',rank,0,80,1)]
            unknown._input_irs=[p._output_irs[0]];unknown._output_irs=[IR(80,'unused',(1,2,k*3))]
            pm.shapes[unknown.outputs[0]]=(1,2,k*3);cells.append(unknown)
        cells.append(collective)
    aliases = []
    if chain:
        first = [cell for cell in cells if cell.opname == 'AllToAllPrim']
        aliases = []
        for rank, a in enumerate(first):
            def ordinary(cid, op, ins, tids, shape, kwargs):
                outs = [T('p', rank, 0, tid, 1) for tid in tids]
                cell = NS(node=N('p',rank,0,cid,op), rank=rank, opname=op,
                    kwargs=kwargs, inputs=ins, outputs=outs,
                    _input_irs=[IR(t.tid,'activation',pm.shapes[t]) for t in ins],
                    _output_irs=[IR(t.tid,'activation',shape) for t in outs])
                pm.shapes.update({t:shape for t in outs})
                cells.append(cell)
                return cell
            add = ordinary(21, 'FW_add', a.outputs*2, [91], (1,2*k,3), {})
            ref = ordinary(22, 'FW_multiref', add.outputs, list(range(100,100+k)),
                           (1,2*k,3), dict(times=k))
            aliases.append(ref)
        for rank in range(k):
            a=NS(node=N('p',rank,0,30,'AllToAllAllToAllPrim'), rank=rank,
                 opname='AllToAllPrim', kwargs=dict(ranks=list(range(k)),idim=2,odim=1),
                 inputs=[q.outputs[-1] for q in aliases], outputs=[T('p',rank,0,120,1)])
            pm.shapes[a.outputs[0]]=(1,2,k*3)
            cells.append(a)
        if between:
            # A real raw ordinary producer in rank zero's order, after a good guard.
            u=copy.deepcopy(aliases[0]); u.node=u.node._replace(cid=23,irname='FW_contiguous')
            u.opname='FW_contiguous';u.kwargs={};u.inputs=[aliases[0].outputs[0]]
            u.outputs=[T('p',0,0,119,1)]
            u._input_irs=[IR(100,'activation',(1,2*k,3))]
            u._output_irs=[IR(119,'activation',(1,2*k,3))]
            pm.shapes[u.outputs[0]]=(1,2*k,3)
            cells.insert(cells.index(aliases[0])+1,u)
    if normalize:
        first = [cell for cell in cells if cell.opname == 'AllToAllPrim']
        normalized = []
        for rank, a in enumerate(first):
            shape = pm.shapes[a.outputs[0]]
            params = [T('p',rank,-1,tid,0) for tid in (200,201)]
            pm.shapes.update({t:(shape[-1],) for t in params})
            outs = [T('p',rank,0,210,1)]
            n = NS(node=N('p',rank,0,40,'FW_layernorm'),rank=rank,opname='FW_layernorm',
                kwargs=dict(normalized_shape=(shape[-1],),eps=1e-5),
                inputs=a.outputs+params,outputs=outs,
                _input_irs=[IR(a.outputs[0].tid,'activation',shape)]+[IR(t.tid,'norm'+str(t.tid),(shape[-1],),param=True) for t in params],
                _output_irs=[IR(210,'normalized',shape)])
            pm.shapes[outs[0]]=shape; cells.append(n); normalized.append(n)
            if project:
                w=T('p',rank,-1,220,0); pm.shapes[w]=(5,shape[-1])
                y=T('p',rank,0,221,1); pm.shapes[y]=shape[:-1]+(5,)
                linear=NS(node=N('p',rank,0,41,'FW_linear'),rank=rank,opname='FW_linear',
                    kwargs=dict(bias=None),inputs=outs+[w],outputs=[y],
                    _input_irs=n._output_irs+[IR(220,'linear_weight',pm.shapes[w],param=True)],
                    _output_irs=[IR(221,'projection',pm.shapes[y])])
                cells.append(linear)

        if gather:
            for rank in range(k):
                inputs=[q.outputs[0] for q in normalized]
                y=T('p',rank,0,230,1); shape=list(pm.shapes[inputs[0]]);shape[1]*=k
                pm.shapes[y]=tuple(shape)
                cells.append(NS(node=N('p',rank,0,42,'AllGatherReduceScatterPrim'),rank=rank,
                    opname='AllGatherPrim',kwargs=dict(ranks=list(range(k)),dim=1),inputs=inputs,outputs=[y]))
    if normalize and fault:
        ln=next(c for c in cells if c.opname=='FW_layernorm')
        linear=next((c for c in cells if c.opname=='FW_linear'),None)
        if fault == 'epsilon': ln.kwargs['eps']=1e-4
        elif fault == 'normalized-shape': ln.kwargs['normalized_shape']=(2,3)
        elif fault == 'unauthorized-weight': linear._input_irs[1].param=False
        elif fault == 'written-weight':
            w=linear.inputs[1];ir=linear._input_irs[1]
            cells.append(NS(node=N('p',linear.rank,0,44,'FW_contiguous'),rank=linear.rank,opname='FW_contiguous',
                kwargs={},inputs=[w],outputs=[w],_input_irs=[ir],_output_irs=[ir]))
        elif fault == 'gamma-shape':
            t=ln.inputs[1];pm.shapes[t]=(4,);ln._input_irs[1]=IR(t.tid,'norm'+str(t.tid),(4,),param=True)
        elif fault == 'gradient-weight': linear._input_irs[1].is_grad=lambda:True
        elif fault == 'linear-width':
            w=linear.inputs[1];pm.shapes[w]=(5,4)
            linear._input_irs[1]=IR(w.tid,'linear_weight',(5,4),param=True)
        elif fault == 'linear-bias': linear.kwargs['bias']=True
        elif fault == 'unsupported-after':
            last=cells[-1];t=T('p',last.rank,0,250,1);shape=pm.shapes[last.outputs[0]]
            pm.shapes[t]=shape
            cells.append(NS(node=N('p',last.rank,0,43,'FW_contiguous'),rank=last.rank,opname='FW_contiguous',
                kwargs={},inputs=last.outputs,outputs=[t],_input_irs=[IR(last.outputs[0].tid,'activation',shape)],
                _output_irs=[IR(t.tid,'activation',shape)]))
    if fault and not normalize:
        cell = aliases[0] if fault != 'unary-add' else next(c for c in cells if c.opname=='FW_add')
        if fault == 'missing-times':
            cell.kwargs = {}
        elif fault == 'unary-add':
            cell.inputs=cell.inputs[:1]; cell._input_irs=cell._input_irs[:1]
        elif fault == 'output-shape':
            t=cell.outputs[0]
            pm.shapes[t]=(1,2*k,4);cell._output_irs[0]=IR(t.tid,'activation',(1,2*k,4))
    pm.cells=cells
    fields=('world','runtime_rank','microbatch','source_tid','version')
    writers=[]; prepared=[]
    for cell in cells:
        row=dict(ref=dict(world='p',runtime_rank=cell.rank,microbatch=0,source_cid=cell.node.cid,
                 call_instance=0,op=cell.opname,origin='nnscaler'),source_irname=cell.node.irname,
                 inputs=[dict(zip(fields,t)) for t in cell.inputs],outputs=[dict(zip(fields,t)) for t in cell.outputs])
        pr=copy.deepcopy(row)
        if cell.opname in ('AllToAllPrim','AllGatherPrim'):
            row['adapter_kwargs']=copy.deepcopy(cell.kwargs)
            pr['inputs']=[dict(zip(fields,cell.inputs[cell.rank]))]
            pr['primitive']=dict(kind='AllToAllAllToAllPrim' if cell.opname=='AllToAllPrim' else 'AllGatherReduceScatterPrim',forward=True,kwargs=copy.deepcopy(cell.kwargs))
        writers.append(row);prepared.append(pr)
    snapshot=build_snapshot(writers);snapshot['runtime_ndevs']=k;snapshot['adapter_source']=prepared
    bind_adapters(snapshot)
    sv,pv=c._lower_runtime_graphs(sm,pm);c.attach_collective_scopes(pv,snapshot)
    legacy=render(sv,pv,sm.cells,pm.cells)
    return bind(legacy,sv,pv,sm.cells,pm.cells,*source,root)

class PrefixTests(unittest.TestCase):
    def test_shape_proofs_do_not_unfold_unrelated_value_operators(self):
        import re
        with tempfile.TemporaryDirectory() as d:
            fed = collective_world(Path(d), 2, normalize=True, project=True, gather=True)
            proofs = re.findall(r'theorem pmPrefixShape_.*?(?=#print axioms)', fed.lean, re.S)
            self.assertTrue(proofs)
            self.assertIn('attribute [local irreducible] pmPrefixState_', fed.lean)
            self.assertIn('rw [pmPrefixSkip_', fed.lean)
            self.assertNotIn('  change (pmPrefixState_', fed.lean)
            for proof in proofs:
                # Layernorm carries the input shape; unfolding its arithmetic (or
                # unrelated operators) makes real-width prefix proofs explode.
                self.assertNotIn('fw_layernorm', proof)
                self.assertLessEqual(sum(op in proof for op in
                    ('fw_linear', 'allGatherPrimDimN', 'chunkPrimDimN',
                     'fw_embedding_shape', 'elemwiseAdd')), 1)

    def test_normalization_after_computed_collective(self):
        for k in (2,3):
            with self.subTest(k=k), tempfile.TemporaryDirectory() as d:
                fed=collective_world(Path(d),k,normalize=True)
                p=fed.receipt['scoped_prefix']['pm']
                self.assertIsNone(p['frontier'])
                self.assertEqual(len(p['initial_premises']),3*k)
                self.assertIn(':= fw_layernorm ',fed.lean)
                self.assertEqual(p['prefix_nodes'],fed.receipt['execution_order']['pm']['execution_to_source'])

    def test_linear_after_normalization(self):
        for k in (2,3):
            with self.subTest(k=k), tempfile.TemporaryDirectory() as d:
                fed=collective_world(Path(d),k,normalize=True,project=True)
                p=fed.receipt['scoped_prefix']['pm']
                self.assertIsNone(p['frontier'])
                self.assertEqual(len(p['initial_premises']),4*k)
                self.assertIn(':= fw_linear ',fed.lean)

    def test_gather_after_normalization(self):
        for k in (2,3):
            with self.subTest(k=k), tempfile.TemporaryDirectory() as d:
                fed=collective_world(Path(d),k,normalize=True,project=True,gather=True)
                p=fed.receipt['scoped_prefix']['pm']
                self.assertIsNone(p['frontier'])
                self.assertEqual(p['output_shape'],[1,2*k*k,3])
                self.assertIn(':= allGatherPrimDimN 1 ',fed.lean)

    def test_normalization_source_contract_controls(self):
        for k in (2,3):
            for fault in ('epsilon','normalized-shape','linear-bias','gamma-shape','written-weight'):
                with self.subTest(k=k,fault=fault), tempfile.TemporaryDirectory() as d:
                    with self.assertRaises(ValueError):
                        collective_world(Path(d),k,normalize=True,project=True,gather=True,fault=fault)
            for fault,reason in [('unauthorized-weight','unauthorized-initial-weight'), ('gradient-weight','unauthorized-initial-weight'),
                                 ('linear-width','linear-shape-contract'),('unsupported-after','unsupported-producer')]:
                with self.subTest(k=k,fault=fault), tempfile.TemporaryDirectory() as d:
                    fed=collective_world(Path(d),k,normalize=True,project=True,gather=True,fault=fault)
                    p=fed.receipt['scoped_prefix']['pm']
                    self.assertEqual(p['frontier']['reason'],reason)
                    self.assertEqual(p['prefix_nodes'],fed.receipt['execution_order']['pm']['execution_to_source'][:p['prefix_length']])
                    self.assertEqual(p['frontier']['execution_index'],p['prefix_length'])
                    self.assertIn('pmPrefixContinuation',fed.lean)
                    if fault!='unsupported-after':
                        self.assertFalse(any(row['ref'][3]==220 for row in p['initial_premises']))

    def test_no_boundary_is_structured_and_preserves_full_feed(self):
        for k in (2, 3):
            with self.subTest(k=k), tempfile.TemporaryDirectory() as d:
                legacy, fed = mixed_world(Path(d), k)
                self.assertIn('scoped_prefix', fed.receipt)
                self.assertEqual(fed.receipt['scoped_prefix']['pm']['reason'], 'no-state-dependent-boundary')
                self.assertTrue(fed.lean.startswith(legacy.lean))
                self.assertFalse(fed.receipt['input_feed']['whole_world_option_success'])

    def test_source_validated_collective_heldouts(self):
        for k in (2,3):
            with self.subTest(k=k), tempfile.TemporaryDirectory() as d:
                fed=collective_world(Path(d),k)
                p=fed.receipt['scoped_prefix']['pm']
                self.assertEqual(p['status'],'conditional-prefix-emitted')
                self.assertEqual(p['prefix_nodes'],fed.receipt['execution_order']['pm']['execution_to_source'])
                self.assertEqual(p['prefix_length'],3*k)
                self.assertEqual(len(p['guards']),k)
                self.assertIsNone(p['frontier'])
                self.assertEqual(p['output_shape'],[1,2*k,3])
                self.assertEqual(len(p['initial_premises']),k)
                self.assertTrue(all(row['ref'][2] == -1 for row in p['initial_premises']))
                self.assertIn('pmInputRequests.take',fed.lean)
                self.assertIn('pmInputRequests.drop',fed.lean)
                self.assertIn('theorem pmPrefixSuccess',fed.lean)
                self.assertFalse(p['whole_world_option_success'])

    def test_add_multiref_inverse_chain_and_first_frontier(self):
        for k in (2,3):
            for between in (False,True):
                with self.subTest(k=k,between=between), tempfile.TemporaryDirectory() as d:
                    fed=collective_world(Path(d),k,chain=True,between=between)
                    p=fed.receipt['scoped_prefix']['pm']
                    order=fed.receipt['execution_order']['pm']['execution_to_source']
                    self.assertEqual(p['status'],'conditional-prefix-emitted')
                    self.assertEqual(p['prefix_nodes'],order[:p['prefix_length']])
                    if between:
                        self.assertEqual(p['frontier']['op'],'FW_contiguous')
                        self.assertEqual(p['frontier']['execution_index'],p['prefix_length'])
                        self.assertLess(p['prefix_length'],len(order))
                    else:
                        self.assertEqual(p['prefix_nodes'],order)
                        self.assertEqual(len(p['guards']),2*k)
                        self.assertEqual(p['output_shape'],[1,2,k*3])
                    self.assertEqual(len(p['initial_premises']),k)
                    self.assertEqual(fed.lean.count('def pmPrefixInitShapes '),1)
                    self.assertEqual(len({g['theorem'] for g in p['guards']}),len(p['guards']))

    def test_source_arity_and_computed_shape_frontiers(self):
        for k in (2,3):
            for fault in ('missing-times','unary-add','output-shape'):
                with self.subTest(k=k,fault=fault), tempfile.TemporaryDirectory() as d:
                    fed=collective_world(Path(d),k,chain=True,fault=fault)
                    p=fed.receipt['scoped_prefix']['pm']
                    self.assertEqual(p['status'],'conditional-prefix-emitted')
                    self.assertIsNotNone(p['frontier'])
                    self.assertEqual(p['frontier']['execution_index'],p['prefix_length'])
                    self.assertEqual(p['prefix_nodes'],fed.receipt['execution_order']['pm']['execution_to_source'][:p['prefix_length']])
                    self.assertEqual(p['frontier']['reason'], 'computed-source-shape-mismatch' if fault=='output-shape' else 'unsupported-source-arity')
                    self.assertIn('theorem pmPrefixContinuation',fed.lean)

    def test_unsupported_producer_keeps_complete_feed(self):
        with tempfile.TemporaryDirectory() as d:
            fed=collective_world(Path(d),2,unsupported=True)
            p=fed.receipt['scoped_prefix']['pm']
            self.assertEqual(p['status'],'prefix-proof-unavailable')
            self.assertEqual(p['reason'],'unsupported-producer')
            self.assertIn('theorem pmDenoteWithInputs_entry',fed.lean)
            self.assertNotIn('theorem pmPrefixSuccess',fed.lean)

if __name__ == '__main__': unittest.main()
