"""Closed CP2 feature-sharded SwiGLU renderer."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict


def _digest(c):
    return hashlib.sha256(json.dumps({"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def render_closed_sharded_swiglu_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import KRankBinaryRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import KRankBinaryRelationCertificate
    rule = "swiglu-sharded-two-rank-dim1"
    theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_swiglu_dim1_two_2d"
    chain = relation.dependent_chain_plan
    seg = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if seg is None or len(seg.transition_ids) != 1:
        raise ValueError("sharded SwiGLU requires one transition")
    t = {x.transition_id: x for x in relation.transition_specs}[seg.transition_ids[0]]
    if t.rule_id != rule or t.lean_theorem != theorem or len(t.pre_facts) != 2 or len(t.post_facts) != 1:
        raise ValueError("sharded SwiGLU theorem identity disagrees")
    matches = [c for c in relation.certificates if type(c) is KRankBinaryRelationCertificate
               and c.rule_id == rule and c.lean_theorem == theorem and c.op == "FW_swiglu"
               and set(c.input_facts) == set(t.pre_facts) and c.output_fact == t.post_facts[0]
               and _digest(c) == t.certificate_digest]
    if len(matches) != 1:
        raise ValueError("sharded SwiGLU lacks one exact certificate")
    c = matches[0]
    records = {f.source: f for f in chain.relation_facts}; states = {s.state_id: s for s in chain.states}
    facts = tuple(records[f] for f in t.pre_facts); post = records[t.post_facts[0]]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if (c.rank_count != 2 or c.gather_dim != 1 or post.kind != "sharded" or post.gather_dim != 1
            or len(post.pm_tids) != 2 or any(f.kind != "sharded" or f.gather_dim != 1 or len(f.pm_tids) != 2 for f in facts)):
        raise ValueError("sharded SwiGLU relation metadata disagrees")
    if (tuple(range(*seg.sm_range)) != t.sm_node_indices or tuple(range(*seg.pm_range)) != t.pm_node_indices
            or len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != 2):
        raise ValueError("sharded SwiGLU footprint is not exact 1x2")
    sm = ir.sm_nodes[t.sm_node_indices[0]]; p0,p1=(ir.pm_nodes[i] for i in t.pm_node_indices)
    by_tid = {f.sm_tid:f for f in facts}
    if len(by_tid)!=2 or any(tid not in by_tid for tid in sm.ins):
        raise ValueError("sharded SwiGLU operand roles are ambiguous")
    gate, up = (by_tid[tid] for tid in sm.ins)
    if ((sm.rank,p0.rank,p1.rank)!=(0,0,1)
            or any(n.op!="FW_swiglu" or len(n.ins)!=2 or len(n.outs)!=1 or n.params not in (None,[]) for n in (sm,p0,p1))
            or tuple(p0.ins)!=(gate.pm_tids[0],up.pm_tids[0]) or tuple(p1.ins)!=(gate.pm_tids[1],up.pm_tids[1])
            or (sm.outs[0],p0.outs[0],p1.outs[0])!=(post.sm_tid,*post.pm_tids)):
        raise ValueError("sharded SwiGLU writer topology disagrees")
    shapes={(f.full_shape,f.shard_shape) for f in (*facts,post)}
    if len(shapes)!=1:
        raise ValueError("sharded SwiGLU shapes disagree")
    full_shape,shard_shape=next(iter(shapes)); rows,shard=shard_shape
    if full_shape!=(rows,shard*2) or min(rows,shard)<=0:
        raise ValueError("sharded SwiGLU dim-1 shape contract disagrees")
    if not {f.fact_id for f in facts}<=set(before.fact_ids) or post.fact_id not in after.fact_ids or not set(after.fact_ids)<=set(before.fact_ids)|{post.fact_id}:
        raise ValueError("sharded SwiGLU liveness disagrees")
    smt,p0t,p1t=_node_text(sm),_node_text(p0),_node_text(p1); full=_shape_text(list(full_shape)); shard_text=_shape_text(list(shard_shape)); sid=segment_id
    return f'''private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := [{smt}]
  pmNodes := [{p0t}, {p1t}]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{smt}]
    let pmNodes : List NodeDecl := [{p0t}, {p1t}]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore
    have hframe : {before.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide
    have hsm : smFinal {sm.outs[0]} = fw_swiglu (smStore {sm.ins[0]}) (smStore {sm.ins[1]}) := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_swiglu_out_1p {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {sm.ins[1]} {sm.outs[0]}
    have hp0 : pmFinal {p0.outs[0]} = fw_swiglu (pmStore {p0.ins[0]}) (pmStore {p0.ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_swiglu_out_1p {ir.pm_graph_ref} pmStore 0 {p0.ins[0]} {p0.ins[1]} {p0.outs[0]}
      · decide
    have hp1 : pmFinal {p1.outs[0]} = fw_swiglu (pmStore {p1.ins[0]}) (pmStore {p1.ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_fw_swiglu_out_1p]
      rw [applyNode_eq_of_not_mem_outs, applyNode_eq_of_not_mem_outs] <;> decide
    have hg : {gate.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hu : {up.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hout : {post.fact_id}.Holds smFinal pmFinal := by
      change ShardedRel (smStore {gate.sm_tid}) [pmStore {gate.pm_tids[0]}, pmStore {gate.pm_tids[1]}] 1 {full} {shard_text} at hg
      change ShardedRel (smStore {up.sm_tid}) [pmStore {up.pm_tids[0]}, pmStore {up.pm_tids[1]}] 1 {full} {shard_text} at hu
      have core := ShardedRel.fw_swiglu_dim1_two_2d (rows := {rows}) (shard := {shard}) hg hu (by native_decide) (by native_decide)
      change ShardedRel (smFinal {post.sm_tid}) [pmFinal {post.pm_tids[0]}, pmFinal {post.pm_tids[1]}] 1 {full} {shard_text}
      rw [hsm, hp0, hp1]
      exact core
    intro fact hfact
    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
'''
