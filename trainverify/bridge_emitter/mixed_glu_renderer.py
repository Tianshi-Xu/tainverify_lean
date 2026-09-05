"""Atomic shared-writer renderer for ordinary and dim-0 sharded GLU views."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict


def _digest(certificate) -> str:
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        separators=(",", ":"), sort_keys=True,
    ).encode()).hexdigest()


def render_closed_mixed_glu_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import FrontierPointwiseCertificate, KRankBinaryRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import FrontierPointwiseCertificate, KRankBinaryRelationCertificate
    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("mixed GLU requires one complete segment")
    segment = segments[0]
    if len(segment.transition_ids) != 2:
        raise ValueError("mixed GLU requires two typed views")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    if len(by_id) != len(relation.transition_specs):
        raise ValueError("mixed GLU transition identity is ambiguous")
    try:
        ordinary_t, sharded_t = (by_id[tid] for tid in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("mixed GLU transition is missing") from exc
    if (ordinary_t.rule_id, sharded_t.rule_id) != (
        "glu-ordinary-two-rank", "glu-sharded-two-rank-dim0"
    ):
        raise ValueError("mixed GLU transition order disagrees")
    ordinary_cs = [c for c in relation.certificates if
        type(c) is FrontierPointwiseCertificate and c.rule_id == ordinary_t.rule_id
        and c.lean_theorem == ordinary_t.lean_theorem and _digest(c) == ordinary_t.certificate_digest
        and c.relation_kind == "ordinary" and c.operator == "FW_glu"
        and set(c.input_step_triples) == {f.step_triple for f in ordinary_t.pre_facts}
        and c.output_step_triple == ordinary_t.post_facts[0].step_triple]
    sharded_cs = [c for c in relation.certificates if
        type(c) is KRankBinaryRelationCertificate and c.rule_id == sharded_t.rule_id
        and c.lean_theorem == sharded_t.lean_theorem and _digest(c) == sharded_t.certificate_digest
        and set(c.input_facts) == set(sharded_t.pre_facts)
        and c.output_fact == sharded_t.post_facts[0]]
    if len(ordinary_cs) != 1 or len(sharded_cs) != 1:
        raise ValueError("mixed GLU lacks exact typed certificates")
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    if len(records) != len(chain.relation_facts) or len(states) != len(chain.states):
        raise ValueError("mixed GLU fact/state identity is ambiguous")
    try:
        ordinary_pre = tuple(records[f] for f in ordinary_t.pre_facts)
        sharded_pre = tuple(records[f] for f in sharded_t.pre_facts)
        ordinary_post = records[ordinary_t.post_facts[0]]
        sharded_post = records[sharded_t.post_facts[0]]
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("mixed GLU facts/states are unresolved") from exc
    if (
        ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2
        or ordinary_t.lean_theorem != "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.glu"
        or sharded_t.lean_theorem != "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_glu_dim0_two_2d"
        or ordinary_post.kind != "ordinary" or sharded_post.kind != "sharded"
        or any(f.kind != "ordinary" for f in ordinary_pre)
        or any(f.kind != "sharded" for f in sharded_pre)
        or len(ordinary_pre) != 2 or len(sharded_pre) != 2
    ):
        raise ValueError("mixed GLU relation kinds/theorems disagree")
    if (
        ordinary_t.sm_node_indices != sharded_t.sm_node_indices
        or ordinary_t.pm_node_indices != sharded_t.pm_node_indices
        or tuple(range(*segment.sm_range)) != ordinary_t.sm_node_indices
        or tuple(range(*segment.pm_range)) != ordinary_t.pm_node_indices
        or len(ordinary_t.sm_node_indices) != 1 or len(ordinary_t.pm_node_indices) != 2
    ):
        raise ValueError("mixed GLU views do not share one exact writer frame")
    sm = ir.sm_nodes[ordinary_t.sm_node_indices[0]]
    pms = tuple(ir.pm_nodes[i] for i in ordinary_t.pm_node_indices)
    if (
        (sm.rank, pms[0].rank, pms[1].rank) != (0, 0, 1)
        or any(n.op != "FW_glu" or len(n.ins) != 2 or len(n.outs) != 1
               or n.params not in (None, []) for n in (sm, *pms))
    ):
        raise ValueError("mixed GLU writer signature disagrees")
    def by_roles(facts):
        result = {fact.sm_tid: fact for fact in facts}
        if len(result) != 2 or any(tid not in result for tid in sm.ins):
            raise ValueError("mixed GLU operand roles are ambiguous")
        return tuple(result[tid] for tid in sm.ins)
    ordinary_x, ordinary_gate = by_roles(ordinary_pre)
    sharded_x, sharded_gate = by_roles(sharded_pre)
    if (
        (ordinary_x.sm_tid, ordinary_gate.sm_tid) != tuple(sm.ins)
        or (sharded_x.sm_tid, sharded_gate.sm_tid) != tuple(sm.ins)
        or tuple(pms[0].ins) != (ordinary_x.pm_tids[0], ordinary_gate.pm_tids[0])
        or tuple(pms[1].ins) != (ordinary_x.pm_tids[1], ordinary_gate.pm_tids[1])
        or (ordinary_post.sm_tid, *ordinary_post.pm_tids) != (sm.outs[0], pms[0].outs[0], pms[1].outs[0])
        or (sharded_post.sm_tid, *sharded_post.pm_tids) != (sm.outs[0], pms[0].outs[0], pms[1].outs[0])
    ):
        raise ValueError("mixed GLU TID roles disagree")
    shapes = {
        (fact.full_shape, fact.shard_shape)
        for fact in (*ordinary_pre, *sharded_pre, ordinary_post, sharded_post)
    }
    if len(shapes) != 1:
        raise ValueError("mixed GLU shapes disagree")
    full_shape, shard_shape = next(iter(shapes))
    if (len(shard_shape) != 2 or full_shape != (shard_shape[0] * 2, shard_shape[1])
            or min(shard_shape) <= 0 or sharded_post.gather_dim != 0
            or any(f.gather_dim != 0 for f in sharded_pre)):
        raise ValueError("mixed GLU dim-0 shape contract disagrees")
    fresh = (ordinary_post.fact_id, sharded_post.fact_id)
    required = {*(f.fact_id for f in ordinary_pre), *(f.fact_id for f in sharded_pre)}
    if (not required <= set(before.fact_ids) or any(fid not in after.fact_ids for fid in fresh)
            or not set(after.fact_ids) <= set(before.fact_ids) | set(fresh)):
        raise ValueError("mixed GLU liveness disagrees")
    sid = segment_id
    smt, pmt = _node_text(sm), tuple(_node_text(n) for n in pms)
    full, shard = _shape_text(list(full_shape)), _shape_text(list(shard_shape))
    rows, hidden = shard_shape
    return f'''private def {sid} :
    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := [{smt}]
  pmNodes := [{pmt[0]}, {pmt[1]}]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{smt}]
    let pmNodes : List NodeDecl := [{pmt[0]}, {pmt[1]}]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore
    have hframe : {before.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide
    have hsm : smFinal {sm.outs[0]} = fw_glu (smStore {sm.ins[0]}) (smStore {sm.ins[1]}) := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_glu_out_1p {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {sm.ins[1]} {sm.outs[0]}
    have hp0 : pmFinal {pms[0].outs[0]} = fw_glu (pmStore {pms[0].ins[0]}) (pmStore {pms[0].ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_glu_out_1p {ir.pm_graph_ref} pmStore 0 {pms[0].ins[0]} {pms[0].ins[1]} {pms[0].outs[0]}
      · decide
    have hp1 : pmFinal {pms[1].outs[0]} = fw_glu (pmStore {pms[1].ins[0]}) (pmStore {pms[1].ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_fw_glu_out_1p]
      rw [applyNode_eq_of_not_mem_outs, applyNode_eq_of_not_mem_outs] <;> decide
    have hoX : {ordinary_x.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hoG : {ordinary_gate.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hsX : {sharded_x.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hsG : {sharded_gate.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hOrdOut : {ordinary_post.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Ordinary2Rel (smStore {ordinary_x.sm_tid}) (pmStore {ordinary_x.pm_tids[0]}) (pmStore {ordinary_x.pm_tids[1]}) {full} {shard} at hoX
      change GeneratedPatterns.Ordinary2Rel (smStore {ordinary_gate.sm_tid}) (pmStore {ordinary_gate.pm_tids[0]}) (pmStore {ordinary_gate.pm_tids[1]}) {full} {shard} at hoG
      have core := Ordinary2Rel.glu {rows} {hidden} hoX hoG (by native_decide) (by native_decide)
      change GeneratedPatterns.Ordinary2Rel (smFinal {ordinary_post.sm_tid}) (pmFinal {ordinary_post.pm_tids[0]}) (pmFinal {ordinary_post.pm_tids[1]}) {full} {shard}
      rw [hsm, hp0, hp1]
      exact core
    have hShardedOut : {sharded_post.fact_id}.Holds smFinal pmFinal := by
      change ShardedRel (smStore {sharded_x.sm_tid}) [pmStore {sharded_x.pm_tids[0]}, pmStore {sharded_x.pm_tids[1]}] 0 {full} {shard} at hsX
      change ShardedRel (smStore {sharded_gate.sm_tid}) [pmStore {sharded_gate.pm_tids[0]}, pmStore {sharded_gate.pm_tids[1]}] 0 {full} {shard} at hsG
      have core := ShardedRel.fw_glu_dim0_two_2d (rows := {rows}) (hidden := {hidden}) hsX hsG (by native_decide) (by native_decide)
      change ShardedRel (smFinal {sharded_post.sm_tid}) [pmFinal {sharded_post.pm_tids[0]}, pmFinal {sharded_post.pm_tids[1]}] 0 {full} {shard}
      rw [hsm, hp0, hp1]
      exact core
    intro fact hfact
    have covered : fact ∈ [{ordinary_post.fact_id}, {sharded_post.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{ordinary_post.fact_id}, {sharded_post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with (rfl | rfl) | old
    · exact hOrdOut
    · exact hShardedOut
    · exact hframe fact old
'''
