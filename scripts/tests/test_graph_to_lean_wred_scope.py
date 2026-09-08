"""Portable WRED source/DFG separation; no capture environment or kernel skips."""
from copy import deepcopy
from types import SimpleNamespace
import unittest
from Verdict import graph_to_lean as c
from scripts.tests.test_graph_to_lean_collective_scope import Graph, Node, Tensor, tref
from trainverify.runtime_source_authority import build_snapshot, bind_reducers


def fixture(ranks=(0, 2), shape=(2,)):
    g=Graph();g.W=SimpleNamespace(runtime_ndevs=max(ranks)+1,num_dp=2,num_mb=1)
    g.ns=[];g.ts=[];g.ins={};g.outs={};g.ops={};g.kw={};g.shapes={}
    rows=[];sources={};raw={}
    xs=[Tensor('p',r,-1,70,1) for r in ranks]
    placement=dict(parent_tid=1,name='weight',full_shape=list(shape),indmap=[[0,d] for d in shape],
                   valmap=[0,1],is_attr=True,is_grad=False,is_param=True,scale_unit=0,plan_rank=0)
    for r in range(g.W.runtime_ndevs):
        code=['class GenModel:',f'    rank = {r}',f'    world_size = {g.W.runtime_ndevs}','    def __init__(self):']
        if r not in ranks:
            sources[str(r)]='\n'.join(code+['        pass']);continue
        p=Tensor('p',r,-1,20,0);x=Tensor('p',r,-1,70,1);y=x._replace(v=2)
        slices=', '.join(f'slice(0, {d}, None)' for d in shape)
        code += ["        self.register_parameter('weight_20', torch.nn.Parameter(torch.empty(1)))",
          f"        self.add_full_map('weight_20', 1, True, 'weight', {shape!r}, ({slices}{',' if slices else ''}), 1)",
          f"        self.wreducer9 = nnscaler.runtime.adapter.Reducer(ranks={list(ranks)}, reduce_op='sum', zero=0, nreplicas=1)",
          '        self.wreducer9.add_param(self.weight_20)','        self.add_reducer(self.wreducer9)']
        sources[str(r)]='\n'.join(code)
        for n,ins,outs,op,pairs in ((Node('p',r,0,8,'producer'),[p],[x],'FW_embedding',[[70,20]]),
             (Node('p',r,0,9,'IRWeightReducer-w20'),xs,[y],'CROSS_DP_WRED',[])):
            g.ns.append(n);g.ins[n]=list(ins);g.outs[n]=outs;g.ops[n]='OpName.'+op;g.kw[n]={}
            row=dict(ref=dict(world='p',runtime_rank=r,microbatch=0,source_cid=n.cid,call_instance=0,op=op,origin='expanded'),
                source_irname=n.irname,inputs=[tref(t) for t in ins],outputs=[tref(t) for t in outs],parameter_grad_tids=pairs)
            if op=='CROSS_DP_WRED': row['reducer_ir']=dict(cid=9,ranks=list(ranks),nreplicas=1,parameter_tid=20)
            rows.append(row)
            raw[n]=dict(parameter_grad_tids=deepcopy(pairs),ref=deepcopy(row['ref']))
            if op=='CROSS_DP_WRED': raw[n].update(reducer_ir=deepcopy(row['reducer_ir']),parameter=tref(p),placement=deepcopy(placement),grad_input=tref(x),grad_output=tref(y))
        g.ts.extend([p,x,y])
        for t in (p,x,y):g.shapes[t]=shape
    s=build_snapshot(rows);s['runtime_ndevs']=g.W.runtime_ndevs;s['rank_sources']=sources
    for t in s['tensors']:
        if t['ref']['source_tid']==20:t['placement']=deepcopy(placement)
    bind_reducers(s)
    return g,s,raw,deepcopy(sources)


class WredScopeTests(unittest.TestCase):
    def test_versioned_noncontiguous_writers_remain_in_one_namespace(self):
        self.assertTrue(callable(getattr(c,'attach_wred_scopes',None)), 'missing authenticated versioned WRED attachment')
        for ranks in ((0,2),(1,3,5),(0,1,2,3)):
            g,s,raw,sources=fixture(ranks);v,=c._lower_runtime_graphs(g)
            c.attach_wred_scopes(v,s,raw,sources)
            self.assertEqual(len(v.wred_scopes),len(ranks))
            self.assertEqual(v.nodes(),g.nodes())
            for n,request in v.wred_scopes.items():
                self.assertEqual(request.ranks,ranks)
                self.assertNotIn(request.output_tid,request.input_tids)
                self.assertFalse(request.proof_admissible)

    def test_emits_checked_writer_and_contextual_fold(self):
        self.assertTrue(callable(getattr(c,'emit_wred_scope_certificates',None)), 'missing checked WRED emission')
        g,s,raw,sources=fixture();v,=c._lower_runtime_graphs(g);c.attach_wred_scopes(v,s,raw,sources)
        text=c.emit_wred_scope_certificates(v)
        self.assertEqual(text,c.emit_wred_scope_certificates(v))
        for token in ('SourceScopedEval.wred_output','SourceScopedEval.run_cons','cross_dp_wred','wred_1_fold'):
            self.assertIn(token,text)
        self.assertNotIn('inferOpShapes',text)

    def test_emitter_rejects_changed_node_inventory_and_order(self):
        for mutation in ('omit', 'reverse', 'duplicate'):
            with self.subTest(mutation=mutation):
                g,s,raw,sources=fixture();v,=c._lower_runtime_graphs(g)
                c.attach_wred_scopes(v,s,raw,sources)
                self.assertEqual(c.emit_wred_scope_certificates(v).count('theorem wred_'),4)
                if mutation == 'omit': v._nodes.pop()
                elif mutation == 'reverse': v._nodes.reverse()
                else: v._nodes.append(v._nodes[-1])
                with self.assertRaisesRegex(ValueError, 'WRED.*mismatch'):
                    c.emit_wred_scope_certificates(v)

    def test_failed_reattachment_invalidates_previous_authority(self):
        for failure in ('source', 'snapshot'):
            with self.subTest(failure=failure):
                g,s,raw,sources=fixture();v,=c._lower_runtime_graphs(g)
                c.attach_wred_scopes(v,s,raw,sources)
                baseline=c.emit_wred_scope_certificates(v)
                bad=deepcopy(s)
                if failure == 'source': bad['rank_sources']['0'] += '\n# changed'
                else: bad['proof_admissible'] = True
                with self.assertRaises(ValueError): c.attach_wred_scopes(v,bad,raw,sources)
                with self.assertRaisesRegex(ValueError, 'missing attached WRED'):
                    c.emit_wred_scope_certificates(v)
                for field in ('wred_scopes','_wred_source','_wred_raw','_wred_rank_sources'):
                    self.assertFalse(hasattr(v,field))
                c.attach_wred_scopes(v,s,raw,sources)
                self.assertEqual(c.emit_wred_scope_certificates(v),baseline)

    def test_mutations_start_from_valid_baseline(self):
        for mutation in ('parameter','world','rank','mb','version','cid','wid','output','update','peerorder',
                         'missing','duplicate','shape','coherent_shape','zero_shape','nonSUM','zero','nreplicas','coherent_owner','placement'):
            with self.subTest(mutation=mutation):
                g,s,raw,sources=fixture();v,=c._lower_runtime_graphs(g);c.attach_wred_scopes(v,s,raw,sources)
                w=s['writers'][1];b=w['reducer']
                if mutation=='parameter': b['parameter']['source_tid']=21
                elif mutation in ('world','rank','mb','version'):
                    field={'world':'world','rank':'runtime_rank','mb':'microbatch','version':'version'}[mutation]
                    b['ordered_inputs'][0][field]='s' if mutation=='world' else 99
                elif mutation=='cid': w['reducer_ir']['cid']=10
                elif mutation=='wid': w['reducer_ir']['parameter_tid']=21
                elif mutation=='output': b['outputs']=[]
                elif mutation=='update': b['grad_output']['version']=3
                elif mutation=='peerorder': v._node2inputs[g.ns[1]].reverse()
                elif mutation=='missing': s['writers'].pop()
                elif mutation=='duplicate': s['writers'].append(deepcopy(w))
                elif mutation=='shape': g.shapes[g.outs[g.ns[1]][0]]=(3,)
                elif mutation=='coherent_shape': g.shapes={t:(3,) for t in g.ts}
                elif mutation=='zero_shape': g.shapes={t:(0,) for t in g.ts}
                elif mutation=='nonSUM': s['rank_sources']['0']=s['rank_sources']['0'].replace("'sum'","'max'")
                elif mutation=='zero': s['rank_sources']['0']=s['rank_sources']['0'].replace('zero=0','zero=1')
                elif mutation=='nreplicas': s['rank_sources']['0']=s['rank_sources']['0'].replace('nreplicas=1','nreplicas=2')
                elif mutation=='coherent_owner':
                    for row in s['writers']:
                        row['parameter_grad_tids']=[[gid,21] for gid,wid in row['parameter_grad_tids']]
                else:
                    for row in s['tensors']:
                        if row.get('placement'): row['placement']['name']='renamed'
                    s['rank_sources']={r:t.replace("'weight'","'renamed'") for r,t in s['rank_sources'].items()}
                    bind_reducers(s)
                with self.assertRaises(ValueError): c.attach_wred_scopes(v,s,raw,sources)

    def test_coherent_json_and_dfg_still_require_independent_parameter_and_version(self):
        from trainverify.runtime_source_authority import validate_snapshot
        for kind in ('parameter','version'):
            with self.subTest(kind=kind):
                g,s,raw,sources=fixture();v,=c._lower_runtime_graphs(g);c.attach_wred_scopes(v,s,raw,sources)
                def change(t):
                    if kind=='parameter' and t.tid==20:return t._replace(tid=21)
                    if kind=='version' and t.tid==70:return t._replace(v=t.v+6)
                    return t
                old=s
                for row in s['writers']:
                    for f in ('inputs','outputs'):row[f]=[tref(change(Tensor(*(r[k] for k in ('world','runtime_rank','microbatch','source_tid','version'))))) for r in row[f]]
                    if kind=='parameter':
                        row['parameter_grad_tids']=[[gid,21] for gid,wid in row['parameter_grad_tids']]
                        if 'reducer_ir' in row:row['reducer_ir']['parameter_tid']=21
                changed_sources={r:t.replace('weight_20','weight_21') for r,t in sources.items()} if kind=='parameter' else deepcopy(sources)
                s=build_snapshot(s['writers']);s['runtime_ndevs']=g.W.runtime_ndevs;s['rank_sources']=changed_sources
                for t in s['tensors']:
                    if t['ref']['source_tid']==(21 if kind=='parameter' else 20):t['placement']=deepcopy(next(x['placement'] for x in old['tensors'] if 'placement' in x))
                bind_reducers(s);validate_snapshot(s)
                g.ts=[change(t) for t in g.ts];g.ins={n:[change(t) for t in ts] for n,ts in g.ins.items()};g.outs={n:[change(t) for t in ts] for n,ts in g.outs.items()};g.shapes={change(t):sh for t,sh in g.shapes.items()}
                v,=c._lower_runtime_graphs(g)
                c.attach_collective_scopes(v,s)  # Whole common validator accepts the coherent pair.
                with self.assertRaises(ValueError):c.attach_wred_scopes(v,s,raw,sources)

    def test_ingress_attaches_wred_before_unchanged_lineage_guard(self):
        from unittest.mock import patch
        g,s,raw,sources=fixture();s=c._SourceSnapshot(s);s.raw_writers=raw;s.raw_rank_sources=sources
        v=SimpleNamespace(get_graph=lambda:(g,g),get_graph_compact=lambda:(g,g))
        args=SimpleNamespace(definitions_only=False,emit_spec_template=False,split_goals=False,
            emit_segment_patterns=False,out='unused-public.lean',spec_out='unused-spec.lean',
            sm_pkl='sm',pm_pkl='pm',verifier_cache_dir=None,runtime_rank_code_directory='source')
        def stop(sm,pm):
            self.assertEqual(len(pm.wred_scopes),2)
            self.assertIn('wred_1_fold',pm.wred_conditional_lean)
            raise ValueError('remaining DP lineage')
        with patch.object(c,'load_verifier',return_value=v), patch.object(c,'_load_chunk_source',return_value=s) as load, \
             patch.object(c,'aligned_logical_node_ids',return_value=({},{})), \
             patch.object(c,'infer_coarse_lineages_from_expanded',side_effect=stop):
            with self.assertRaisesRegex(ValueError,'remaining DP lineage'):c._generate(args)
        self.assertEqual(load.call_count,1)

    def test_mixed_world_fixture_preserves_old_versions(self):
        self.assertTrue(callable(globals().get('mixed_witness')), 'missing generated single-world WRED fold')
        text=mixed_witness()
        self.assertEqual(text,mixed_witness())
        self.assertIn('SourceScopedEval.denote graph scope peers initial',text)
        self.assertIn('wred_2_fold graph s2',text)
        self.assertIn('wred_3_fold graph s3',text)

    def test_different_tp_parameter_slices_with_identical_local_shapes(self):
        for offset in (0,2):
            g,s,raw,sources=fixture()
            for t in s['tensors']:
                if 'placement' in t:t['placement'].update(full_shape=[4],indmap=[[offset,offset+2]])
            for row in raw.values():
                if 'placement' in row:row['placement'].update(full_shape=[4],indmap=[[offset,offset+2]])
            sources={r:t.replace("'weight', (2,)","'weight', (4,)").replace('slice(0, 2, None)',f'slice({offset}, {offset+2}, None)') for r,t in sources.items()}
            s['rank_sources']=deepcopy(sources);bind_reducers(s)
            v,=c._lower_runtime_graphs(g);c.attach_wred_scopes(v,s,raw,sources)
            self.assertTrue(all(x.input_shape==(2,) for x in v.wred_scopes.values()))
            self.assertIn('SourceScopedEval.wred_output',c.emit_wred_scope_certificates(v))

    def test_scalar_is_one_output_not_K_outputs(self):
        g,s,raw,sources=fixture(shape=());v,=c._lower_runtime_graphs(g)
        c.attach_wred_scopes(v,s,raw,sources)
        self.assertEqual(next(iter(v.wred_scopes.values())).input_shape,())

def mixed_witness():
    g,s,raw,sources=fixture()
    order=[0,2,1,3];g.ns=[g.ns[i] for i in order];rows=[s['writers'][i] for i in order]
    for n,row in zip(g.ns,rows):
        if row['ref']['op']!='CROSS_DP_WRED':
            row['ref']['op']='FW_contiguous';raw[n]['ref']['op']='FW_contiguous';g.ops[n]='OpName.FW_contiguous'
    old=s;s=build_snapshot(rows);s['runtime_ndevs']=g.W.runtime_ndevs;s['rank_sources']=sources
    for t in s['tensors']:
        match=next(x for x in old['tensors'] if x['ref']==t['ref'])
        if 'placement' in match:t['placement']=match['placement']
    bind_reducers(s);v,=c._lower_runtime_graphs(g);c.attach_wred_scopes(v,s,raw,sources)
    assert [(tuple(t.tid for t in v.node_inputs(n)),tuple(t.tid for t in v.node_outputs(n))) for n in g.ns]==[((0,),(1,)),((3,),(4,)),((1,4),(2,)),((1,4),(5,))]
    return c.emit_wred_scope_certificates(v)+MIXED_WITNESS


MIXED_WITNESS='''
namespace TrainVerify.Denote.WredMixed
set_option maxHeartbeats 500000
noncomputable section
open WredCompiler
 def n0 : NodeDecl := {rank := 0, op := "OpName.FW_contiguous", ins := [0], outs := [1]}
 def n2 : NodeDecl := {rank := 2, op := "OpName.FW_contiguous", ins := [3], outs := [4]}
 def r0 : NodeDecl := {rank := 0, op := "OpName.CROSS_DP_WRED", ins := [1,4], outs := [2]}
 def r2 : NodeDecl := {rank := 2, op := "OpName.CROSS_DP_WRED", ins := [1,4], outs := [5]}
 def graph : GraphDecl := {numRanks := 3, nodes := [n0,n2,r0,r2]}
 def scope (n : NodeDecl) : GroupScopedEval.Request :=
   if n.op = "OpName.CROSS_DP_WRED" then .group (some [0,2]) else .global
 def peers (_ : NodeDecl) : Nat → Tid := peer_2
 def initial : Store := fun tid => ⟨[2], fun _ => if tid = 0 then 1 else 3⟩
 def s1 : Store := storeSet initial [(1, initial 0)]
 def s2 : Store := storeSet s1 [(4, s1 3)]
 theorem mixed_value : ∃ final, SourceScopedEval.denote graph scope peers initial = some final ∧
     valAt (final 2) 0 = 4 ∧ valAt (final 5) 0 = 4 ∧
     valAt (final 1) 0 = 1 ∧ valAt (final 4) 0 = 3 := by
   have h0 : SourceScopedEval.step graph (scope n0) (peers n0) initial n0 = some s1 :=
     SourceScopedEval.step_global _ _ _ _ (by rfl)
   have h2 : SourceScopedEval.step graph (scope n2) (peers n2) s1 n2 = some s2 :=
     SourceScopedEval.step_global _ _ _ _ (by rfl)
   obtain ⟨s3, hr0, ho0, hf0⟩ := wred_2_fold graph s2 rfl rfl rfl scope peers rfl rfl [r2]
   have hx1 := hf0 1 (by decide)
   have hx4 := hf0 4 (by decide)
   obtain ⟨s4, hr2, ho2, hf2⟩ := wred_3_fold graph s3 rfl
     (by rw [hx1]; rfl) (by rw [hx4]; rfl) scope peers rfl rfl []
   refine ⟨s4, ?_, ?_, ?_, ?_, ?_⟩
   · change SourceScopedEval.run graph scope peers [n0,n2,r0,r2] (some initial) = _
     rw [SourceScopedEval.run_cons, h0, SourceScopedEval.run_cons, h2]
     change SourceScopedEval.run graph scope peers [r0,r2] (some s2) = _
     unfold r0
     rw [hr0]
     unfold r2
     rw [hr2]
     rfl
   · rw [hf2 2 (by decide), ho0]
     change (0 + 1 + 3 : Scalar) = 4
     norm_num
   · rw [ho2]
     simp only [List.map_cons,List.map_nil,hx1,hx4]
     change (0 + 1 + 3 : Scalar) = 4
     norm_num
   · rw [hf2 1 (by decide), hx1]
     rfl
   · rw [hf2 4 (by decide), hx4]
     rfl
#print axioms mixed_value
end
end TrainVerify.Denote.WredMixed
'''

if __name__=='__main__':unittest.main()
