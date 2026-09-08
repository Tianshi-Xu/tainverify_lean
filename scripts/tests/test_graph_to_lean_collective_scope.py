"""Portable independent raw graph / prepared-source collective scope checks."""
from collections import namedtuple
from copy import deepcopy
from types import SimpleNamespace
import unittest
from Verdict import graph_to_lean as compiler
from trainverify.runtime_source_authority import build_snapshot, bind_adapters

Tensor = namedtuple('Tensor', 'wtype rank mb tid v')
Node = namedtuple('Node', 'wtype rank mb cid irname')
OPS = ('AllToAllPrim', 'AllGatherPrim', 'ReduceScatterPrim', 'AllReducePrim')

def tref(t):
    return dict(zip(('world', 'runtime_rank', 'microbatch', 'source_tid', 'version'), t))

class Graph:
    def nodes(self): return self.ns
    def tensors(self): return self.ts
    def node_inputs(self, n): return self.ins[n]
    def node_outputs(self, n): return self.outs[n]
    def node_opname(self, n): return self.ops[n]
    def node_kwargs(self, n): return self.kw[n]
    def tensor_shape(self, t): return self.shapes[t]

def fixture(op='AllToAllPrim', ranks=(0, 2, 5), forward=True, dims=None):
    g = Graph(); g.W = SimpleNamespace(runtime_ndevs=max(ranks)+2, num_dp=2, num_mb=1)
    g.ns=[]; g.ts=[]; g.ins={}; g.outs={}; g.ops={}; g.kw={}; g.shapes={}
    k=len(ranks); shape=(6*k, 4*k)
    kw=dict(ranks=list(ranks))
    if op=='AllToAllPrim': kw.update(idim=0, odim=1)
    elif op!='AllReducePrim': kw['dim']=1
    if dims is not None: kw.update(dims)
    kinds={'AllToAllPrim':'AllToAllAllToAllPrim', 'AllGatherPrim':'AllGatherReduceScatterPrim',
           'ReduceScatterPrim':'ReduceScatterAllGatherPrim', 'AllReducePrim':'AllReduceIdentityPrim'}
    kind=kinds[op]
    if not forward and op=='AllGatherPrim': kind='ReduceScatterAllGatherPrim'
    if not forward and op=='ReduceScatterPrim': kind='AllGatherReduceScatterPrim'
    inputs=[Tensor('p', r, 0, 70+i, 1) for i,r in enumerate(ranks)]
    writers=[]; prepared=[]
    for i,r in enumerate(ranks):
        x=inputs[i]; y=Tensor('p', r, 0, 90+i, 1)
        for n,ins,outs,operation,kwargs in (
            (Node('p',r,0,10,'producer'),[],[x],'FW_embedding',{}),
            (Node('p',r,0,20,kind),inputs,[y],op,kw)):
            g.ns.append(n);g.ts.extend(outs);g.ins[n]=list(ins);g.outs[n]=outs
            g.ops[n]='OpName.'+operation;g.kw[n]=deepcopy(kwargs)
            w=dict(ref=dict(world='p',runtime_rank=r,microbatch=0,source_cid=n.cid,
                call_instance=0,op=operation,origin='nnscaler'),source_irname=n.irname,
                inputs=[tref(t) for t in ins],outputs=[tref(t) for t in outs])
            row=deepcopy({f:w[f] for f in ('ref','inputs','outputs')})
            if operation==op:
                w['adapter_kwargs']=deepcopy(kw);row['inputs']=[tref(x)]
                row['primitive']=dict(kind=kind,forward=forward,kwargs=deepcopy(kw))
            writers.append(w);prepared.append(row)
        out=list(shape)
        if op=='AllGatherPrim': out[1]*=k
        elif op=='ReduceScatterPrim': out[1]//=k
        elif op=='AllToAllPrim':
            a,b=(0,1) if forward else (1,0);out[a]*=k;out[b]//=k
        g.shapes[x]=shape;g.shapes[y]=tuple(out)
    s=build_snapshot(writers);s['runtime_ndevs']=g.W.runtime_ndevs;s['adapter_source']=prepared
    bind_adapters(s)
    return g,s

class CollectiveCompilerTests(unittest.TestCase):
    def test_four_families_same_world_conditional_steps(self):
        self.assertTrue(callable(getattr(compiler,'attach_collective_scopes',None)),
                        'missing source-backed collective attachment')
        for op in OPS:
            for forward in (True,False) if op!='AllReducePrim' else (True,):
                with self.subTest(op=op,forward=forward):
                    g,s=fixture(op,forward=forward);view,=compiler._lower_runtime_graphs(g)
                    compiler.attach_collective_scopes(view,s)
                    self.assertIs(view.source,g);self.assertEqual(view.nodes(),g.nodes())
                    self.assertEqual(len(view.collective_scopes),3)
                    c=view.collective_scopes[g.ns[3]]
                    self.assertEqual((c.ranks,c.local_index),((0,2,5),1))
                    self.assertFalse(c.proof_admissible)
                    text=compiler.emit_collective_scope_certificates(view)
                    self.assertIn('GroupScopedEval.step_scoped',text)
                    self.assertIn('op := "OpName.'+op+'"',text)
                    self.assertIn('hworld : g.numRanks = 7',text)
                    self.assertNotIn('sorry',text);self.assertNotIn('houtput',text)
                    self.assertEqual(text,compiler.emit_collective_scope_certificates(view))

    def test_coherent_unsupported_parameter_does_not_get_dropped(self):
        g,s=fixture('AllReducePrim')
        for n in g.ns[1::2]: g.kw[n]['op']='max'
        for w in s['writers']:
            if 'adapter_kwargs' in w: w['adapter_kwargs']['op']='max'
        for row in s['adapter_source']:
            if 'primitive' in row: row['primitive']['kwargs']['op']='max'
        bind_adapters(s);view,=compiler._lower_runtime_graphs(g)
        with self.assertRaisesRegex(ValueError,'parameter'):
            compiler.attach_collective_scopes(view,s)

    def test_emitter_revalidates_edges_and_claimed_scope(self):
        from dataclasses import replace
        for mutation in ('edges','scope','read','unsupported'):
            g,s=fixture();view,=compiler._lower_runtime_graphs(g)
            compiler.attach_collective_scopes(view,s);n=g.ns[1]
            if mutation=='edges': view._node2inputs[n].reverse()
            elif mutation=='scope': view.collective_scopes[n]=replace(view.collective_scopes[n],local_index=2)
            elif mutation=='read': view._collective_source['writers'][1]['adapter']['generated_read_binding']='rejected'
            else: view._collective_source['writers'][0]['adapter']={}
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                compiler.emit_collective_scope_certificates(view)

    def test_arbitrary_group_cardinality(self):
        for ranks in ((1,), (1,4), (0,2,5,8)):
            for op in OPS:
                g,s=fixture(op,ranks);view,=compiler._lower_runtime_graphs(g)
                compiler.attach_collective_scopes(view,s)
                self.assertEqual(len(view.collective_scopes),len(ranks))

    def test_ingress_loads_source_once_for_all_five_primitives(self):
        from unittest.mock import patch
        from pathlib import Path
        g,s=fixture()
        v=SimpleNamespace(get_graph=lambda:(g,g),get_graph_compact=lambda:(g,g))
        args=SimpleNamespace(definitions_only=False,emit_spec_template=False,split_goals=False,
            emit_segment_patterns=False,out='unused-public.lean',spec_out='unused-spec.lean',
            sm_pkl='sm',pm_pkl='pm',verifier_cache_dir=None,runtime_rank_code_directory='source')
        observed=[]
        def stop(sm,pm):
            observed.append(pm.collective_scopes)
            raise ValueError('remaining DP lineage')
        with patch.object(compiler,'load_verifier',return_value=v), \
             patch.object(compiler,'_load_chunk_source',return_value=s) as load, \
             patch.object(compiler,'aligned_logical_node_ids',return_value=({},{})), \
             patch.object(compiler,'infer_coarse_lineages_from_expanded',side_effect=stop):
            with self.assertRaisesRegex(ValueError,'remaining DP lineage'): compiler._generate(args)
        self.assertEqual(load.call_count,1);self.assertEqual(len(observed[0]),3)
        self.assertFalse(Path(args.out).exists())

    def test_same_axis_alltoall_is_not_gather_then_chunk(self):
        g,s=fixture()
        for n in g.ns[1::2]:
            g.kw[n]['odim']=0;g.shapes[g.outs[n][0]]=g.shapes[g.ins[n][0]]
        for w in s['writers']:
            if 'adapter_kwargs' in w: w['adapter_kwargs']['odim']=0
        for row in s['adapter_source']:
            if 'primitive' in row: row['primitive']['kwargs']['odim']=0
        bind_adapters(s);view,=compiler._lower_runtime_graphs(g)
        with self.assertRaisesRegex(ValueError,'same.axis'):
            compiler.attach_collective_scopes(view,s)

    def test_reference_object_field_order_is_not_identity(self):
        g,s=fixture()
        for row in s['adapter_source']: row['ref']=dict(reversed(list(row['ref'].items())))
        view,=compiler._lower_runtime_graphs(g)
        compiler.attach_collective_scopes(view,s)

    def test_raw_empty_constant_inventory_is_not_an_operator_parameter(self):
        g,s=fixture()
        for n in g.ns[1::2]: g.kw[n]['__consts']=[]
        view,=compiler._lower_runtime_graphs(g)
        compiler.attach_collective_scopes(view,s)
        g.kw[g.ns[1]]['__consts']=[3]
        with self.assertRaises(ValueError): compiler.attach_collective_scopes(view,s)

    def test_source_effective_operation_is_not_inferred_from_shapes(self):
        for op in OPS:
            g,s=fixture(op)
            for row in s['adapter_source']:
                if 'primitive' in row: row['primitive']['forward']=False
            bind_adapters(s)
            view,=compiler._lower_runtime_graphs(g)
            with self.subTest(op=op), self.assertRaises(ValueError):
                compiler.attach_collective_scopes(view,s)

    def test_raw_metadata_fullref_and_peer_shape_mutants(self):
        for op in OPS:
            for mutation in ('rankorder','missingpeer','fullref','version','output','params','peer_shape','output_shape','writer','stale'):
                g,s=fixture(op);n=g.ns[1]
                if mutation=='rankorder': g.kw[n]['ranks'].reverse()
                elif mutation=='missingpeer': g.ins[n].pop()
                elif mutation in ('fullref','version'): g.ins[n][0]=g.ins[n][0]._replace(**({'tid':999} if mutation=='fullref' else {'v':2}))
                elif mutation=='output': g.outs[n]=[g.ts[0]]
                elif mutation=='params': g.kw[n]['unexpected']=1
                elif mutation=='peer_shape': g.shapes[g.ins[n][-1]]=(18,13)
                elif mutation=='output_shape': g.shapes[g.outs[n][0]]=(99,99)
                elif mutation=='writer': s['writers'][0]['ref']['source_cid']=999
                else: s['writers'][1]['adapter']['source_writer']='wrong'
                with self.subTest(op=op,mutation=mutation), self.assertRaises(ValueError):
                    view,=compiler._lower_runtime_graphs(g)
                    compiler.attach_collective_scopes(view,s)

    def test_coherent_json_change_still_disagrees_with_raw_dfg(self):
        for mutation in ('params','writer','rankorder'):
            g,s=fixture('AllGatherPrim')
            if mutation=='params':
                for w in s['writers']:
                    if 'adapter_kwargs' in w: w['adapter_kwargs']['dim']=0
                for row in s['adapter_source']:
                    if 'primitive' in row: row['primitive']['kwargs']['dim']=0
            elif mutation=='writer':
                s['writers'][0]['ref']['source_cid']=999
                s['adapter_source'][0]['ref']['source_cid']=999
            else:
                for w in s['writers']:
                    if 'adapter_kwargs' in w: w['inputs'].reverse();w['adapter_kwargs']['ranks'].reverse()
                for row in s['adapter_source']:
                    if 'primitive' in row: row['primitive']['kwargs']['ranks'].reverse()
            rebuilt=build_snapshot(s['writers']);s['writers']=rebuilt['writers'];s['tensors']=rebuilt['tensors']
            bind_adapters(s)
            view,=compiler._lower_runtime_graphs(g)
            with self.subTest(mutation=mutation),self.assertRaises(ValueError): compiler.attach_collective_scopes(view,s)

    def test_dimension_boundaries_and_divisibility(self):
        for op in OPS[:-1]:
            for dim in (-3,2,False):
                dims={'idim':dim} if op=='AllToAllPrim' else {'dim':dim}
                with self.subTest(op=op,dim=dim),self.assertRaises(ValueError):
                    g,s=fixture(op,dims=dims);view,=compiler._lower_runtime_graphs(g)
                    compiler.attach_collective_scopes(view,s)
            dims={'idim':-2,'odim':-1} if op=='AllToAllPrim' else {'dim':-1}
            g,s=fixture(op,dims=dims);view,=compiler._lower_runtime_graphs(g)
            compiler.attach_collective_scopes(view,s)
            self.assertTrue(all(all(d>=0 for d in c.params) for c in view.collective_scopes.values()))
        for op in ('AllToAllPrim','ReduceScatterPrim'):
            g,s=fixture(op)
            for n in g.ns[1::2]:
                for t in g.ins[n]: g.shapes[t]=(18,11)
            view,=compiler._lower_runtime_graphs(g)
            with self.subTest(op=op),self.assertRaisesRegex(ValueError,'divisible'):
                compiler.attach_collective_scopes(view,s)

if __name__=='__main__': unittest.main()
