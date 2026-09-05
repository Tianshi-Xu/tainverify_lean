"""Atomic renderer for one shared FW_float writer tuple with sharded and ordinary views."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict


def _digest(certificate) -> str:
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        separators=(",", ":"), sort_keys=True,
    ).encode()).hexdigest()


def render_closed_mixed_float_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import FrontierFloatCertificate, KRankContiguousRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import FrontierFloatCertificate, KRankContiguousRelationCertificate
    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("mixed float requires one complete segment")
    segment = segments[0]
    if len(segment.transition_ids) != 2:
        raise ValueError("mixed float requires two typed views")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    if any(tid not in by_id for tid in segment.transition_ids):
        raise ValueError("mixed float transition identity is missing")
    typed = tuple(by_id[tid] for tid in segment.transition_ids)
    sharded = [t for t in typed if t.rule_id == "float-sharded-k-rank"]
    ordinary = [t for t in typed if t.rule_id == "float-ordinary-two-rank"]
    if len(sharded) != 1 or len(ordinary) != 1:
        raise ValueError("mixed float requires one sharded and one ordinary typed view")
    sharded_t, ordinary_t = sharded[0], ordinary[0]
    sharded_c = [c for c in relation.certificates if
        type(c) is KRankContiguousRelationCertificate
        and c.rule_id == sharded_t.rule_id and c.lean_theorem == sharded_t.lean_theorem
        and (c.input_fact,) == sharded_t.pre_facts and (c.output_fact,) == sharded_t.post_facts
        and _digest(c) == sharded_t.certificate_digest]
    ordinary_c = [c for c in relation.certificates if
        type(c) is FrontierFloatCertificate
        and c.rule_id == ordinary_t.rule_id and c.lean_theorem == ordinary_t.lean_theorem
        and len(ordinary_t.pre_facts) == 1 and len(ordinary_t.post_facts) == 1
        and ordinary_t.pre_facts[0].layout == c.relation_kind
        and ordinary_t.pre_facts[0].step_triple == c.input_step_triple
        and ordinary_t.post_facts[0].layout == c.relation_kind
        and ordinary_t.post_facts[0].step_triple == c.output_step_triple
        and _digest(c) == ordinary_t.certificate_digest]
    if len(sharded_c) != 1 or len(ordinary_c) != 1:
        raise ValueError("mixed float lacks exact typed certificates")
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    try:
        sh_pre, sh_post = records[sharded_t.pre_facts[0]], records[sharded_t.post_facts[0]]
        or_pre, or_post = records[ordinary_t.pre_facts[0]], records[ordinary_t.post_facts[0]]
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("mixed float facts/states are unresolved") from exc
    if (
        sharded_t.lean_theorem != "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_contiguous"
        or ordinary_t.lean_theorem != "TrainVerify.Denote.fw_float_allGather0_commute_2"
        or ir.sm_num_ranks != 1
        or sh_pre.kind != "sharded" or sh_post.kind != "sharded"
        or or_pre.kind != "ordinary" or or_post.kind != "ordinary"
        or sharded_c[0].rank_count != 2 or ir.pm_num_ranks != 2
        or sharded_c[0].gather_dim != sh_pre.gather_dim
        or tuple(sharded_c[0].full_shape) != tuple(sh_pre.full_shape)
        or tuple(sharded_c[0].shard_shape) != tuple(sh_pre.shard_shape)
        or ordinary_c[0].relation_kind != "ordinary"
        or tuple(ordinary_c[0].shape) != tuple(or_pre.full_shape)
        or sh_pre.gather_dim != 0 or sh_post.gather_dim != 0
        or sh_pre.sm_tid != or_pre.sm_tid or sh_post.sm_tid != or_post.sm_tid
        or sh_pre.pm_tids != or_pre.pm_tids or sh_post.pm_tids != or_post.pm_tids
        or sh_pre.full_shape != or_pre.full_shape or sh_pre.shard_shape != or_pre.shard_shape
        or sh_post.full_shape != or_post.full_shape or sh_post.shard_shape != or_post.shard_shape
        or sh_pre.full_shape != sh_post.full_shape or sh_pre.shard_shape != sh_post.shard_shape
    ):
        raise ValueError("mixed float relation payload disagrees")
    if (
        sharded_t.sm_node_indices != ordinary_t.sm_node_indices
        or sharded_t.pm_node_indices != ordinary_t.pm_node_indices
        or len(sharded_t.sm_node_indices) != 1 or len(sharded_t.pm_node_indices) != 2
        or tuple(range(*segment.sm_range)) != sharded_t.sm_node_indices
        or tuple(range(*segment.pm_range)) != sharded_t.pm_node_indices
    ):
        raise ValueError("mixed float must share one exact 1x2 writer frame")
    sm = ir.sm_nodes[sharded_t.sm_node_indices[0]]
    pms = tuple(ir.pm_nodes[i] for i in sharded_t.pm_node_indices)
    nodes = (sm, *pms)
    if (
        tuple(n.rank for n in nodes) != (0, 0, 1)
        or any(n.op != "FW_float" or len(n.ins) != 1 or len(n.outs) != 1 for n in nodes)
        or any(tuple(n.params or ()) != tuple(sm.params or ()) for n in pms)
        or (sm.ins[0], *(n.ins[0] for n in pms)) != (sh_pre.sm_tid, *sh_pre.pm_tids)
        or (sm.outs[0], *(n.outs[0] for n in pms)) != (sh_post.sm_tid, *sh_post.pm_tids)
    ):
        raise ValueError("mixed float writer tuple disagrees")
    fresh = (sh_post.fact_id, or_post.fact_id)
    if (
        sh_pre.fact_id not in before.fact_ids or or_pre.fact_id not in before.fact_ids
        or any(fid not in after.fact_ids for fid in fresh)
        or not set(after.fact_ids) <= set(before.fact_ids) | set(fresh)
    ):
        raise ValueError("mixed float liveness disagrees")
    sm_text = _node_text(sm); pm_text = ", ".join(_node_text(n) for n in pms)
    full = _shape_text(list(sh_post.full_shape)); shard = _shape_text(list(sh_post.shard_shape))
    params = "[" + ", ".join(str(x) for x in (sm.params or [])) + "]"
    si, p0i, p1i = sh_pre.sm_tid, *sh_pre.pm_tids
    so, p0o, p1o = sh_post.sm_tid, *sh_post.pm_tids
    sid = segment_id
    return f'''private def {sid} :
    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := [{sm_text}]
  pmNodes := [{pm_text}]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{sm_text}]
    let pmNodes : List NodeDecl := [{pm_text}]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore
    have hframe : {before.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide
    have hSh : {sh_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hOrd : {or_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hsm : smFinal {so} = smStore {si} := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed,
        applyNodeRingAttn, applyNode_fw_float_out]
    have hp0 : pmFinal {p0o} = pmStore {p0i} := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_float_out {ir.pm_graph_ref} pmStore 0 {p0i} {p0o} {params}
      · decide
    have hp1 : pmFinal {p1o} = pmStore {p1i} := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_fw_float_out]
      apply applyNode_eq_of_not_mem_outs
      decide
    have hShOut : {sh_post.fact_id}.Holds smFinal pmFinal := by
      change ShardedRel (smStore {si}) [pmStore {p0i}, pmStore {p1i}] 0 {full} {shard} at hSh
      change ShardedRel (smFinal {so}) [pmFinal {p0o}, pmFinal {p1o}] 0 {full} {shard}
      rw [hsm, hp0, hp1]
      exact hSh
    have hOrdOut : {or_post.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Ordinary2Rel (smStore {si}) (pmStore {p0i}) (pmStore {p1i}) {full} {shard} at hOrd
      change GeneratedPatterns.Ordinary2Rel (smFinal {so}) (pmFinal {p0o}) (pmFinal {p1o}) {full} {shard}
      rw [hsm, hp0, hp1]
      exact hOrd
    intro fact hfact
    have covered : fact ∈ [{sh_post.fact_id}, {or_post.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{sh_post.fact_id}, {or_post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with (rfl | rfl) | old
    · exact hShOut
    · exact hOrdOut
    · exact hframe fact old
'''
