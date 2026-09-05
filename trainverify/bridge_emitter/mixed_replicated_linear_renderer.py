"""Atomic shared-writer renderer for ordinary and sharded replicated linear."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict


def _digest(c):
    return hashlib.sha256(json.dumps({"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def render_closed_mixed_replicated_linear_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import FrontierLinearCertificate, KRankLocalRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import FrontierLinearCertificate, KRankLocalRelationCertificate
    chain = relation.dependent_chain_plan
    segs = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segs) != 1:
        raise ValueError("mixed replicated linear requires one complete segment")
    seg = segs[0]
    if len(seg.transition_ids) != 2:
        raise ValueError("mixed replicated linear requires two typed views")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    ordinary_t, sharded_t = (by_id[x] for x in seg.transition_ids)
    if (ordinary_t.rule_id, sharded_t.rule_id) != (
        "mix-precision-linear-ordinary-two-rank", "mix-linear-sharded-two-rank-dim0"):
        raise ValueError("mixed replicated linear rule order disagrees")
    weight_specs = [f for f in ordinary_t.pre_facts if f.layout == "joined"]
    activation_specs = [f for f in ordinary_t.pre_facts if f.layout == "ordinary"]
    if len(weight_specs) != 1 or len(activation_specs) != 1:
        raise ValueError("mixed replicated linear typed input roles are ambiguous")
    weight_spec, activation_spec = weight_specs[0], activation_specs[0]
    ocs = [c for c in relation.certificates if type(c) is FrontierLinearCertificate
           and c.rule_id == ordinary_t.rule_id and c.lean_theorem == ordinary_t.lean_theorem
           and _digest(c) == ordinary_t.certificate_digest
           and c.input_step_triple == activation_spec.step_triple
           and c.weight_fact == weight_spec
           and c.output_step_triple == ordinary_t.post_facts[0].step_triple]
    scs = [c for c in relation.certificates if type(c) is KRankLocalRelationCertificate
           and c.rule_id == sharded_t.rule_id and c.lean_theorem == sharded_t.lean_theorem
           and _digest(c) == sharded_t.certificate_digest
           and c.input_fact == sharded_t.pre_facts[0]
           and c.output_fact == sharded_t.post_facts[0]]
    if len(ocs) != 1 or len(scs) != 1:
        raise ValueError("mixed replicated linear lacks exact certificates")
    oc, sc = ocs[0], scs[0]
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    weight = records[weight_spec]
    ordinary_pre = records[activation_spec]
    ordinary_post = records[ordinary_t.post_facts[0]]
    sharded_pre = records[sharded_t.pre_facts[0]]
    sharded_post = records[sharded_t.post_facts[0]]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if (
        ordinary_t.lean_theorem != "TrainVerify.Denote.fw_mix_precision_linear_allGather0_commute_2"
        or sharded_t.lean_theorem != "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_linear_dim0_two_2d"
        or weight.kind != "joined" or ordinary_post.kind != "ordinary"
        or ordinary_pre.kind != "ordinary" or sharded_pre.kind != "sharded" or sharded_post.kind != "sharded"
        or sc.rank_count != 2 or sc.gather_dim != 0 or sc.external_tids != (weight.sm_tid,)
        or sc.external_shapes != (weight.full_shape,)
        or ordinary_pre.sm_tid != sharded_pre.sm_tid or ordinary_pre.pm_tids != sharded_pre.pm_tids
        or ordinary_post.sm_tid != sharded_post.sm_tid or ordinary_post.pm_tids != sharded_post.pm_tids
    ):
        raise ValueError("mixed replicated linear relation payload disagrees")
    if (
        ordinary_t.sm_node_indices != sharded_t.sm_node_indices
        or ordinary_t.pm_node_indices != sharded_t.pm_node_indices
        or tuple(range(*seg.sm_range)) != ordinary_t.sm_node_indices
        or tuple(range(*seg.pm_range)) != ordinary_t.pm_node_indices
        or len(ordinary_t.sm_node_indices) != 1 or len(ordinary_t.pm_node_indices) != 2
    ):
        raise ValueError("mixed replicated linear does not share exact 1x2 writers")
    sm = ir.sm_nodes[ordinary_t.sm_node_indices[0]]
    p0, p1 = (ir.pm_nodes[i] for i in ordinary_t.pm_node_indices)
    wsm, wpm = weight.sm_tid, weight.joined_pm_tid
    if (
        wpm is None
        or (sm.rank, p0.rank, p1.rank) != (0, 0, 1)
        or any(n.op != "FW_mix_precision_linear" or len(n.ins) != 2 or len(n.outs) != 1
               or n.params not in (None, []) for n in (sm, p0, p1))
        or (sm.ins[0], p0.ins[0], p1.ins[0]) != (ordinary_pre.sm_tid, *ordinary_pre.pm_tids)
        or (sm.ins[1], p0.ins[1], p1.ins[1]) != (wsm, wpm, wpm)
        or (sm.outs[0], p0.outs[0], p1.outs[0]) != (ordinary_post.sm_tid, *ordinary_post.pm_tids)
    ):
        raise ValueError("mixed replicated linear writer topology disagrees")
    rows, input_dim = ordinary_pre.shard_shape
    output_dim = ordinary_post.shard_shape[1] if len(ordinary_post.shard_shape) == 2 else 0
    if (
        ordinary_pre.full_shape != (rows * 2, input_dim)
        or ordinary_post.full_shape != (rows * 2, output_dim)
        or ordinary_post.shard_shape != (rows, output_dim)
        or weight.full_shape != (output_dim, input_dim)
        or min(rows, input_dim, output_dim) <= 0
        or (ordinary_pre.full_shape, ordinary_pre.shard_shape) != (sharded_pre.full_shape, sharded_pre.shard_shape)
        or (ordinary_post.full_shape, ordinary_post.shard_shape) != (sharded_post.full_shape, sharded_post.shard_shape)
    ):
        raise ValueError("mixed replicated linear shape contract disagrees")
    required = {weight.fact_id, ordinary_pre.fact_id, sharded_pre.fact_id}
    fresh = {ordinary_post.fact_id, sharded_post.fact_id}
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids) or not set(after.fact_ids) <= set(before.fact_ids) | fresh:
        raise ValueError("mixed replicated linear liveness disagrees")
    smt, p0t, p1t = _node_text(sm), _node_text(p0), _node_text(p1)
    full_in, shard_in = _shape_text(list(ordinary_pre.full_shape)), _shape_text(list(ordinary_pre.shard_shape))
    full_out, shard_out = _shape_text(list(ordinary_post.full_shape)), _shape_text(list(ordinary_post.shard_shape))
    weight_shape = _shape_text(list(weight.full_shape))
    sid = segment_id
    return f'''private def {sid} :
    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
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
    have hsm : smFinal {sm.outs[0]} = fw_linear (smStore {sm.ins[0]}) (smStore {wsm}) := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_mix_precision_linear_out_1p {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {wsm} {sm.outs[0]}
    have hp0 : pmFinal {p0.outs[0]} = fw_linear (pmStore {p0.ins[0]}) (pmStore {wpm}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_mix_precision_linear_out_1p {ir.pm_graph_ref} pmStore 0 {p0.ins[0]} {wpm} {p0.outs[0]}
      · decide
    have hp1 : pmFinal {p1.outs[0]} = fw_linear (pmStore {p1.ins[0]}) (pmStore {wpm}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_fw_mix_precision_linear_out_1p]
      rw [applyNode_eq_of_not_mem_outs, applyNode_eq_of_not_mem_outs] <;> decide
    have hw : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have ho : {ordinary_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hs : {sharded_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hOrdOut : {ordinary_post.fact_id}.Holds smFinal pmFinal := by
      change smStore {wsm} = pmStore {wpm} ∧ (smStore {wsm}).shape = {weight_shape} ∧ (pmStore {wpm}).shape = {weight_shape} at hw
      change GeneratedPatterns.Ordinary2Rel (smStore {ordinary_pre.sm_tid}) (pmStore {ordinary_pre.pm_tids[0]}) (pmStore {ordinary_pre.pm_tids[1]}) {full_in} {shard_in} at ho
      have core := Ordinary2Rel.mix_precision_linear {rows} {input_dim} {output_dim} ho hw.2.2 hw.1 (by native_decide) (by native_decide) (by native_decide)
      change GeneratedPatterns.Ordinary2Rel (smFinal {ordinary_post.sm_tid}) (pmFinal {ordinary_post.pm_tids[0]}) (pmFinal {ordinary_post.pm_tids[1]}) {full_out} {shard_out}
      rw [hsm, hp0, hp1]
      exact core
    have hShOut : {sharded_post.fact_id}.Holds smFinal pmFinal := by
      change smStore {wsm} = pmStore {wpm} ∧ (smStore {wsm}).shape = {weight_shape} ∧ (pmStore {wpm}).shape = {weight_shape} at hw
      change ShardedRel (smStore {sharded_pre.sm_tid}) [pmStore {sharded_pre.pm_tids[0]}, pmStore {sharded_pre.pm_tids[1]}] 0 {full_in} {shard_in} at hs
      have core := ShardedRel.fw_linear_dim0_two_2d (rows := {rows}) (input := {input_dim}) (output := {output_dim}) hs hw.2.2 (by native_decide) (by native_decide) (by native_decide)
      change ShardedRel (smFinal {sharded_post.sm_tid}) [pmFinal {sharded_post.pm_tids[0]}, pmFinal {sharded_post.pm_tids[1]}] 0 {full_out} {shard_out}
      rw [hsm, hp0, hp1, hw.1]
      exact core
    intro fact hfact
    have covered : fact ∈ [{ordinary_post.fact_id}, {sharded_post.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{ordinary_post.fact_id}, {sharded_post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with (rfl | rfl) | old
    · exact hOrdOut
    · exact hShOut
    · exact hframe fact old
'''
