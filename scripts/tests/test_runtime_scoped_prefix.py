"""Source-scoped prefix availability must not break complete input schedules."""
import tempfile
import unittest
from pathlib import Path
from scripts.tests.test_runtime_input_schedule_kernel import mixed_world


def collective_world(root, k, unsupported=False, chain=False, between=False, fault=None):
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
    if fault:
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
        if cell.opname=='AllToAllPrim':
            row['adapter_kwargs']=copy.deepcopy(cell.kwargs)
            pr['inputs']=[dict(zip(fields,cell.inputs[cell.rank]))]
            pr['primitive']=dict(kind='AllToAllAllToAllPrim',forward=True,kwargs=copy.deepcopy(cell.kwargs))
        writers.append(row);prepared.append(pr)
    snapshot=build_snapshot(writers);snapshot['runtime_ndevs']=k;snapshot['adapter_source']=prepared
    bind_adapters(snapshot)
    sv,pv=c._lower_runtime_graphs(sm,pm);c.attach_collective_scopes(pv,snapshot)
    legacy=render(sv,pv,sm.cells,pm.cells)
    return bind(legacy,sv,pv,sm.cells,pm.cells,*source,root)

class PrefixTests(unittest.TestCase):
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
