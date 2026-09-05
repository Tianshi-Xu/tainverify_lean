"""Generic atomic renderer for SwiGLU over two ZigzagFeatureRel operands."""
from __future__ import annotations
import hashlib,json
from dataclasses import asdict
RULE="zigzag-feature-swiglu-two-rank"; THEOREM="TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.swiglu_two"
def _digest(c): return hashlib.sha256(json.dumps({"type":type(c).__name__,"fields":asdict(c)},sort_keys=True,separators=(",",":")).encode()).hexdigest()
def render_closed_zigzag_feature_swiglu_segment(ir,relation,segment_id):
 from .composer import _node_text,_shape_text
 from .relation_compiler import ZigzagFeatureBinaryCertificate
 chain=relation.dependent_chain_plan;segs=[] if chain is None else [s for s in chain.segments if s.segment_id==segment_id]
 if chain is None or not chain.complete or len(segs)!=1: raise ValueError("zigzag-feature SwiGLU requires one complete segment")
 seg=segs[0]
 if len(seg.transition_ids)!=1: raise ValueError("zigzag-feature SwiGLU requires one transition")
 t={x.transition_id:x for x in relation.transition_specs}[seg.transition_ids[0]]
 if t.rule_id!=RULE or t.lean_theorem!=THEOREM or len(t.pre_facts)!=2 or len(t.post_facts)!=1: raise ValueError("zigzag-feature SwiGLU theorem grammar disagrees")
 cs=[c for c in relation.certificates if type(c) is ZigzagFeatureBinaryCertificate and c.rule_id==RULE and c.lean_theorem==THEOREM and set(c.input_facts)==set(t.pre_facts) and c.output_fact==t.post_facts[0] and _digest(c)==t.certificate_digest]
 if len(cs)!=1: raise ValueError("zigzag-feature SwiGLU lacks one exact certificate")
 c=cs[0];records={x.source:x for x in chain.relation_facts};states={x.state_id:x for x in chain.states};inputs=[records[x] for x in c.input_facts];out=records[c.output_fact];before,after=states[seg.pre_state_id],states[seg.post_state_id]
 smids=tuple(range(*seg.sm_range));pmids=tuple(range(*seg.pm_range))
 if t.sm_node_indices!=smids or t.pm_node_indices!=pmids or len(smids)!=1 or len(pmids)!=2 or c.writer_steps!=(f"sm:{smids[0]}:0",f"pm:{pmids[0]}:0",f"pm:{pmids[1]}:0"): raise ValueError("zigzag-feature SwiGLU exact 1x2 writers disagree")
 sm=ir.sm_nodes[smids[0]];p0,p1=(ir.pm_nodes[i] for i in pmids);nodes=(sm,p0,p1)
 if (sm.rank,p0.rank,p1.rank)!=(0,0,1) or any(n.op!="FW_swiglu" or len(n.ins)!=2 or len(n.outs)!=1 or n.params for n in nodes): raise ValueError("zigzag-feature SwiGLU writer signature disagrees")
 by_sm={x.sm_tid:x for x in inputs}
 if len(by_sm)!=2 or any(x.kind!="zigzag_feature" or x.gather_dim!=1 or len(x.pm_tids)!=2 for x in inputs) or out.kind!="zigzag_feature" or out.gather_dim!=1 or len(out.pm_tids)!=2: raise ValueError("zigzag-feature SwiGLU layouts disagree")
 try:g,u=(by_sm[x] for x in sm.ins)
 except KeyError as e: raise ValueError("zigzag-feature SwiGLU SM operand role missing") from e
 if (p0.ins,p1.ins)!=([g.pm_tids[0],u.pm_tids[0]],[g.pm_tids[1],u.pm_tids[1]]) or (sm.outs[0],p0.outs[0],p1.outs[0])!=(out.sm_tid,*out.pm_tids): raise ValueError("zigzag-feature SwiGLU operand/output roles disagree")
 payload=lambda x:(x.full_shape,x.row_shard_shape,x.shard_shape,x.metadata_tid,x.metadata_region_id)
 if payload(g)!=payload(u) or payload(g)!=payload(out) or g.metadata_tid is None: raise ValueError("zigzag-feature SwiGLU relation payload changed")
 rows,input_dim,feature=c.rows,c.input_features,c.feature_features
 if min(rows,input_dim,feature)<=0 or input_dim!=2*feature or g.full_shape!=(2*rows,input_dim) or g.row_shard_shape!=(rows,input_dim) or g.shard_shape!=(2*rows,feature): raise ValueError("zigzag-feature SwiGLU shape contract disagrees")
 if not {g.fact_id,u.fact_id}<=set(before.fact_ids) or out.fact_id not in after.fact_ids or not set(after.fact_ids)<=set(before.fact_ids)|{out.fact_id}: raise ValueError("zigzag-feature SwiGLU liveness disagrees")
 smt,p0t,p1t=map(_node_text,nodes);fs=_shape_text(list(out.full_shape));rs=_shape_text(list(out.row_shard_shape));ss=_shape_text(list(out.shard_shape))
 def writer(name,graph,store,frame,pos,node,final,nodes_name):
  bef,aft=frame[:pos],frame[pos+1:]
  return [f"    have {name} : {final} {node.outs[0]} = fw_swiglu ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",f"      simpa [{final}, {nodes_name}] using",f"        (foldl_faithful_binary_middle_writer {graph} {store} [{', '.join(_node_text(x) for x in bef)}] [{', '.join(_node_text(x) for x in aft)}] {_node_text(node)}",f"          {node.ins[0]} {node.ins[1]} {node.outs[0]} fw_swiglu (by","            intro s","            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","            unfold applyNodeDistributed","            rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",f"            · exact applyNode_fw_swiglu_out_1p {graph} s {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}","            · native_decide","            · native_decide","          ) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))"]
 lines=[f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := [{smt}]",f"  pmNodes := [{p0t}, {p1t}]","  sound := by","    intro smStore pmStore hstate",f"    let smNodes : List NodeDecl := [{smt}]",f"    let pmNodes : List NodeDecl := [{p0t}, {p1t}]",f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by","      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide",f"    have hg : {g.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",f"    have hu : {u.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)"]
 lines+=writer("hsm",ir.sm_graph_ref,"smStore",(sm,),0,sm,"smFinal","smNodes")+writer("hp0",ir.pm_graph_ref,"pmStore",(p0,p1),0,p0,"pmFinal","pmNodes")+writer("hp1",ir.pm_graph_ref,"pmStore",(p0,p1),1,p1,"pmFinal","pmNodes")
 lines += [f"    have hmeta : pmFinal {out.metadata_tid} = pmStore {g.metadata_tid} := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore _ (by native_decide) (by native_decide)",f"    have hout : {out.fact_id}.Holds smFinal pmFinal := by",f"      change ZigzagFeatureRel (smStore {g.sm_tid}) [pmStore {g.pm_tids[0]}, pmStore {g.pm_tids[1]}] (pmStore {g.metadata_tid}) {fs} {rs} {ss} at hg",f"      change ZigzagFeatureRel (smStore {u.sm_tid}) [pmStore {u.pm_tids[0]}, pmStore {u.pm_tids[1]}] (pmStore {u.metadata_tid}) {fs} {rs} {ss} at hu",f"      have core := ZigzagFeatureRel.swiglu_two {rows} {input_dim} {feature} hg hu rfl (by native_decide) (by native_decide) (by native_decide)",f"      change ZigzagFeatureRel (smFinal {out.sm_tid}) [pmFinal {out.pm_tids[0]}, pmFinal {out.pm_tids[1]}] (pmFinal {out.metadata_tid}) {fs} {rs} {ss}","      rw [hsm, hp0, hp1, hmeta]","      exact core","    exact RelationState.Holds.mono_insert hframe hout (by native_decide)",""]
 return "\n".join(lines)
