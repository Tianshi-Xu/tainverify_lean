"""Draft generic closed renderer for zigzag rows -> joined-zigzag AllGather."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict

RULE = "zigzag-allgather-joined-two-rank"
THEOREM = "TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.of_allGather"

def _digest(c):
    return hashlib.sha256(json.dumps(
        {"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":"),
    ).encode()).hexdigest()

def render_closed_joined_zigzag_allgather_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import JoinedZigzagAllGatherCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import JoinedZigzagAllGatherCertificate
    chain = relation.dependent_chain_plan
    segs = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segs) != 1:
        raise ValueError("joined-zigzag AllGather requires one complete segment")
    seg = segs[0]
    if len(seg.transition_ids) != 1:
        raise ValueError("joined-zigzag AllGather requires one transition")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    t = by_id[seg.transition_ids[0]]
    if (t.rule_id != RULE or t.lean_theorem != THEOREM
            or len(t.pre_facts) != 1 or len(t.post_facts) != 1):
        raise ValueError("joined-zigzag AllGather theorem identity disagrees")
    candidates = [c for c in relation.certificates
        if type(c) is JoinedZigzagAllGatherCertificate
        and c.rule_id == RULE and c.lean_theorem == THEOREM
        and c.input_fact == t.pre_facts[0] and c.output_fact == t.post_facts[0]
        and _digest(c) == t.certificate_digest]
    if len(candidates) != 1:
        raise ValueError("joined-zigzag AllGather lacks one exact typed certificate")
    c = candidates[0]
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    pre, post = records[t.pre_facts[0]], records[t.post_facts[0]]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    sm_indices, pm_indices = tuple(range(*seg.sm_range)), tuple(range(*seg.pm_range))
    if (sm_indices or t.sm_node_indices or len(pm_indices) != 1
            or tuple(t.pm_node_indices) != pm_indices
            or c.pm_allgather_step != f"pm:{pm_indices[0]}:0"):
        raise ValueError("joined-zigzag AllGather frame/writer ownership disagrees")
    node = ir.pm_nodes[pm_indices[0]]
    if (ir.pm_num_ranks != 2 or node.rank != 0 or node.op != "AllGatherPrim"
            or tuple(node.params or ()) != (0,) or len(node.ins) != 2
            or len(node.outs) != 1):
        raise ValueError("joined-zigzag AllGather node signature disagrees")
    if (pre.kind != "zigzag" or post.kind != "joined_zigzag"
            or len(pre.pm_tids) != 2 or tuple(node.ins) != tuple(pre.pm_tids)
            or post.sm_tid != pre.sm_tid or post.joined_pm_tid != node.outs[0]
            or pre.metadata_tid is None or post.metadata_tid != pre.metadata_tid
            or pre.full_shape != post.full_shape
            or pre.shard_shape != post.shard_shape
            or post.row_shard_shape != pre.shard_shape
            or len(pre.full_shape) < 1
            or pre.full_shape != (2 * pre.shard_shape[0], *pre.shard_shape[1:])):
        raise ValueError("joined-zigzag AllGather relation/shape payload disagrees")
    fresh = {post.fact_id}
    if (pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= set(before.fact_ids) | fresh):
        raise ValueError("joined-zigzag AllGather liveness disagrees")
    n = _node_text(node); fs = _shape_text(list(pre.full_shape)); ss = _shape_text(list(pre.shard_shape))
    return f'''private def {segment_id} :
    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := []
  pmNodes := [{n}]
  sound := by
    intro smStore pmStore hstate
    let smFinal := ([] : List NodeDecl).foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore
    let pmNodes : List NodeDecl := [{n}]
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore
    have hframe : {before.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame ([] : List NodeDecl) pmNodes smStore pmStore hstate <;> native_decide
    have hrow0 : pmFinal {pre.pm_tids[0]} = pmStore {pre.pm_tids[0]} := by
      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore _ (by native_decide) (by native_decide)
    have hrow1 : pmFinal {pre.pm_tids[1]} = pmStore {pre.pm_tids[1]} := by
      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore _ (by native_decide) (by native_decide)
    have hwriter : pmFinal {node.outs[0]} = allGatherPrimDimN 0 2 0 [pmStore {pre.pm_tids[0]}, pmStore {pre.pm_tids[1]}] := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_allGatherPrimDimN_out {ir.pm_graph_ref} pmStore 0 [{pre.pm_tids[0]}, {pre.pm_tids[1]}] {node.outs[0]} 0
    have hin : {pre.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)
    have hout : {post.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Zigzag2Rel (smFinal {pre.sm_tid}) (pmFinal {pre.pm_tids[0]}) (pmFinal {pre.pm_tids[1]}) (pmFinal {pre.metadata_tid}) {fs} {ss} at hin
      change JoinedZigzagRel (smFinal {post.sm_tid}) (pmFinal {post.joined_pm_tid}) (pmFinal {post.metadata_tid}) {fs} {ss}
      apply JoinedZigzagRel.of_allGather hin
      rw [hrow0, hrow1]
      exact hwriter
    intro fact hfact
    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
'''
