"""Generic atomic renderer for shape-identity views over ZigzagFeatureRel."""
from __future__ import annotations
import hashlib,json
from dataclasses import asdict
RULE="zigzag-feature-view-id-two-rank"
THEOREM="TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.view_id_two"
def _digest(c): return hashlib.sha256(json.dumps({"type":type(c).__name__,"fields":asdict(c)},sort_keys=True,separators=(",",":")).encode()).hexdigest()
def render_closed_zigzag_feature_view_segment(ir,relation,segment_id):
 from .composer import _node_text,_shape_text
 from .relation_compiler import ZigzagFeatureUnaryViewCertificate
 chain=relation.dependent_chain_plan; segs=[] if chain is None else [s for s in chain.segments if s.segment_id==segment_id]
 if chain is None or not chain.complete or len(segs)!=1: raise ValueError("zigzag-feature view requires one complete segment")
 seg=segs[0]
 if len(seg.transition_ids)!=1: raise ValueError("zigzag-feature view requires one transition")
 t={x.transition_id:x for x in relation.transition_specs}[seg.transition_ids[0]]
 if t.rule_id!=RULE or t.lean_theorem!=THEOREM or len(t.pre_facts)!=1 or len(t.post_facts)!=1: raise ValueError("zigzag-feature view theorem grammar disagrees")
 cs=[c for c in relation.certificates if type(c) is ZigzagFeatureUnaryViewCertificate and c.rule_id==RULE and c.lean_theorem==THEOREM and c.input_fact==t.pre_facts[0] and c.output_fact==t.post_facts[0] and _digest(c)==t.certificate_digest]
 if len(cs)!=1: raise ValueError("zigzag-feature view lacks one exact certificate")
 c=cs[0]; records={x.source:x for x in chain.relation_facts}; states={x.state_id:x for x in chain.states}; pre,post=records[c.input_fact],records[c.output_fact]; before,after=states[seg.pre_state_id],states[seg.post_state_id]
 smids=tuple(range(*seg.sm_range));pmids=tuple(range(*seg.pm_range))
 if t.sm_node_indices!=smids or t.pm_node_indices!=pmids or len(smids)!=1 or len(pmids)!=2: raise ValueError("zigzag-feature view requires exact 1x2 frame")
 expected_steps=(f"sm:{smids[0]}:0",f"pm:{pmids[0]}:0",f"pm:{pmids[1]}:0")
 if c.writer_steps!=expected_steps: raise ValueError("zigzag-feature view certificate writers disagree")
 sm=ir.sm_nodes[smids[0]];p0,p1=(ir.pm_nodes[i] for i in pmids);nodes=(sm,p0,p1)
 if (sm.rank,p0.rank,p1.rank)!=(0,0,1) or len({n.op for n in nodes})!=1 or sm.op not in {"FW_view","FW_reshape"} or any(len(n.ins)!=1 or len(n.outs)!=1 for n in nodes): raise ValueError("zigzag-feature view writer signature disagrees")
 if pre.kind!="zigzag_feature" or post.kind!="zigzag_feature" or pre.gather_dim!=1 or post.gather_dim!=1 or len(pre.pm_tids)!=2 or len(post.pm_tids)!=2: raise ValueError("zigzag-feature view layouts disagree")
 if (pre.full_shape,pre.row_shard_shape,pre.shard_shape,pre.metadata_tid,pre.metadata_region_id)!=(post.full_shape,post.row_shard_shape,post.shard_shape,post.metadata_tid,post.metadata_region_id): raise ValueError("zigzag-feature view changes relation payload")
 if pre.metadata_tid is None or (sm.ins[0],p0.ins[0],p1.ins[0])!=(pre.sm_tid,*pre.pm_tids) or (sm.outs[0],p0.outs[0],p1.outs[0])!=(post.sm_tid,*post.pm_tids): raise ValueError("zigzag-feature view TID roles disagree")
 if tuple(sm.params or ())!=pre.full_shape or tuple(p0.params or ())!=pre.shard_shape or tuple(p1.params or ())!=pre.shard_shape: raise ValueError("zigzag-feature view literal target shapes disagree")
 if pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids or not set(after.fact_ids)<=set(before.fact_ids)|{post.fact_id}: raise ValueError("zigzag-feature view liveness disagrees")
 smt,p0t,p1t=map(_node_text,nodes); fs=_shape_text(list(pre.full_shape));rs=_shape_text(list(pre.row_shard_shape));ss=_shape_text(list(pre.shard_shape))
 def writer(name,graph,store,frame,pos,node,final,nodes_name,target):
  bef,aft=frame[:pos],frame[pos+1:]; lemma=(f"applyNode_fw_view_out {graph} s {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.outs[0]}" if node.op=="FW_view" else f"applyNode_fw_reshape_out {graph} s {node.rank} {node.ins[0]} {node.outs[0]} {_shape_text(node.params)}")
  return [f"    have {name} : {final} {node.outs[0]} = fw_view {target} ({store} {node.ins[0]}) := by",f"      simpa [{final}, {nodes_name}] using",f"        (foldl_faithful_unary_middle_writer {graph} {store} [{', '.join(_node_text(x) for x in bef)}] [{', '.join(_node_text(x) for x in aft)}] {_node_text(node)}",f"          {node.ins[0]} {node.outs[0]} (fun x => fw_view {target} x) (by","            intro s","            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","            unfold applyNodeDistributed","            rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",f"            · exact {lemma}","            · native_decide","            · native_decide","          ) (by native_decide) (by native_decide) (by native_decide) (by native_decide))"]
 lines=[f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := [{smt}]",f"  pmNodes := [{p0t}, {p1t}]","  sound := by","    intro smStore pmStore hstate",f"    let smNodes : List NodeDecl := [{smt}]",f"    let pmNodes : List NodeDecl := [{p0t}, {p1t}]",f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by","      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide",f"    have hin : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)"]
 lines+=writer("hsm",ir.sm_graph_ref,"smStore",(sm,),0,sm,"smFinal","smNodes",fs)+writer("hp0",ir.pm_graph_ref,"pmStore",(p0,p1),0,p0,"pmFinal","pmNodes",ss)+writer("hp1",ir.pm_graph_ref,"pmStore",(p0,p1),1,p1,"pmFinal","pmNodes",ss)
 lines += [f"    have hmeta : pmFinal {post.metadata_tid} = pmStore {pre.metadata_tid} := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore _ (by native_decide) (by native_decide)",f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",f"      change ZigzagFeatureRel (smStore {pre.sm_tid}) [pmStore {pre.pm_tids[0]}, pmStore {pre.pm_tids[1]}] (pmStore {pre.metadata_tid}) {fs} {rs} {ss} at hin",f"      change ZigzagFeatureRel (smFinal {post.sm_tid}) [pmFinal {post.pm_tids[0]}, pmFinal {post.pm_tids[1]}] (pmFinal {post.metadata_tid}) {fs} {rs} {ss}","      rw [hsm, hp0, hp1, hmeta]","      exact ZigzagFeatureRel.view_id_two hin","    exact RelationState.Holds.mono_insert hframe hout (by native_decide)",""]
 return "\n".join(lines)
