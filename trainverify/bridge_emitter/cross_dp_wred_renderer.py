"""Closed renderer for an in-place CROSS_DP_WRED reconstruction writer."""
from __future__ import annotations


def render_closed_cross_dp_wred_segment(ir, relation, segment_id: str) -> str:
    try:
        from .closed_fact_sources import fact_tids
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankAllReduceReconstructionCertificate
    except ImportError:
        from closed_fact_sources import fact_tids
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankAllReduceReconstructionCertificate

    rule = "cross-dp-wred-reconstruction-k-rank"
    theorem = "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce"
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("CROSS_DP_WRED requires one transition")
    transition = next(
        (item for item in relation.transition_specs
         if item.transition_id == segment.transition_ids[0]), None
    )
    if transition is None or transition.rule_id != rule or transition.lean_theorem != theorem:
        raise ValueError("CROSS_DP_WRED typed family mismatch")
    cert = _select_exact_typed_certificate(
        relation, transition, rule, theorem,
        KRankAllReduceReconstructionCertificate,
        lambda item: ((item.input_fact,), (item.output_fact,)),
    )
    records = {item.source: item for item in chain.relation_facts}
    states = {item.state_id: item for item in chain.states}
    before = records[cert.input_fact]
    after = records[cert.output_fact]
    pre_state = states[segment.pre_state_id]
    post_state = states[segment.post_state_id]
    if before.fact_id not in pre_state.fact_ids or after.fact_id not in post_state.fact_ids:
        raise ValueError("CROSS_DP_WRED boundary facts are not live")
    pre_ids = tuple(pre_state.fact_ids)
    post_ids = tuple(post_state.fact_ids)
    if len(pre_ids) != len(set(pre_ids)) or len(post_ids) != len(set(post_ids)):
        raise ValueError("CROSS_DP_WRED boundary state has duplicate facts")
    if post_ids.count(after.fact_id) != 1 or after.fact_id in pre_ids:
        raise ValueError("CROSS_DP_WRED output fact publication is not fresh and unique")
    retained_ids = tuple(item for item in post_ids if item != after.fact_id)
    if not retained_ids or not set(retained_ids) <= set(pre_ids):
        raise ValueError("CROSS_DP_WRED post-state has invalid retained facts")
    if (transition.sm_node_indices != () or len(transition.pm_node_indices) != 1
            or tuple(range(*segment.sm_range)) != ()):
        raise ValueError("CROSS_DP_WRED requires one PM-only writer")
    writer_index = transition.pm_node_indices[0]
    if tuple(range(*segment.pm_range)) != (writer_index,):
        raise ValueError("CROSS_DP_WRED requires one exact writer frame")
    writer = ir.pm_nodes[writer_index]
    k = cert.rank_count
    if (k < 1 or writer.rank != 0 or writer.op != "CROSS_DP_WRED"
            or writer.params or len(writer.ins) != k or len(writer.outs) != 1
            or writer.outs[0] != writer.ins[0]
            or tuple(writer.ins) != before.pm_tids
            or after.sm_tid != before.sm_tid
            or after.joined_pm_tid != writer.outs[0]
            or before.kind != "reduction" or after.kind != "joined"
            or before.full_shape != after.full_shape):
        raise ValueError("CROSS_DP_WRED writer/relation authority mismatch")
    all_records = [*chain.relation_facts, *chain.authority_facts, chain.anchor_fact]
    if len({item.fact_id for item in all_records}) != len(all_records):
        raise ValueError("CROSS_DP_WRED closed fact IDs are not globally unique")
    by_fact_id = {item.fact_id: item for item in all_records}
    retained_sm, retained_pm = set(), set()
    for fact_id in retained_ids:
        if fact_id not in by_fact_id:
            raise ValueError("CROSS_DP_WRED retained fact is not materialized")
        sm_tids, pm_tids = fact_tids(by_fact_id[fact_id])
        retained_sm.update(sm_tids); retained_pm.update(pm_tids)
    sm_writes = {tid for node in ir.sm_nodes[slice(*segment.sm_range)] for tid in node.outs}
    pm_writes = {tid for node in ir.pm_nodes[slice(*segment.pm_range)] for tid in node.outs}
    if sm_writes & retained_sm or pm_writes & retained_pm:
        raise ValueError("CROSS_DP_WRED retained fact is overwritten")
    _, consumed_pm = fact_tids(before)
    if writer.outs[0] not in consumed_pm or before.fact_id in retained_ids:
        raise ValueError("CROSS_DP_WRED in-place reduction input is not retired")

    sm_nodes_name = f"{segment_id}_smNodes"
    pm_nodes_name = f"{segment_id}_pmNodes"
    sm_final_name = f"{segment_id}_smFinal"
    pm_final_name = f"{segment_id}_pmFinal"
    retained_name = f"{segment_id}_retained"
    inputs = "[" + ", ".join(str(tid) for tid in writer.ins) + "]"
    retained_facts = "[" + ", ".join(retained_ids) + "]"
    shape = _shape_text(list(before.full_shape))
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := []",
        f"private def {pm_nodes_name} : List NodeDecl := [{_node_text(writer)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
        f"private def {retained_name} : RelationState where",
        f"  facts := {retained_facts}",
        "  nonempty := by native_decide", "",
        f"private theorem {segment_id}_writer (pmStore : Store) :",
        f"    ({pm_final_name} pmStore) {writer.outs[0]} =",
        f"      cross_dp_wred ({inputs}.map pmStore) := by",
        f"  unfold {pm_final_name} {pm_nodes_name}",
        "  simp only [List.foldl]",
        "  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "    (hshuffle := by native_decide) (hunshuffle := by native_decide)",
        "    (hattn := by native_decide)]",
        "  unfold applyNodeDistributed",
        "  rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
        f"  · exact applyNode_cross_dp_wred_out {ir.pm_graph_ref} pmStore 0",
        f"      {inputs} {writer.outs[0]}",
        "  · native_decide", "  · native_decide", "",
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {pre_state.state_id}.Holds smStore pmStore) :",
        f"    {post_state.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  let smFinal := {sm_final_name} smStore",
        f"  let pmFinal := {pm_final_name} pmStore",
        "  have hSmFinal : smFinal = smStore := by",
        f"    unfold smFinal {sm_final_name} {sm_nodes_name}", "    rfl",
        f"  have hRetainedBefore : {retained_name}.Holds smStore pmStore := by",
        "    intro fact hfact",
        "    exact hstate fact",
        f"      ((show {retained_name}.facts ⊆ {pre_state.state_id}.facts by native_decide) hfact)",
        f"  have hframe : {retained_name}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name}",
        "      smStore pmStore hRetainedBefore",
        "    · native_decide", "    · native_decide", "    · native_decide", "    · native_decide",
        f"  have hin : {before.fact_id}.Holds smStore pmStore :=",
        f"    hstate {before.fact_id} (by native_decide)",
        f"  change ReductionRel (smStore {before.sm_tid}) ({inputs}.map pmStore) {shape} at hin",
        f"  have hWriter := {segment_id}_writer pmStore",
        f"  change pmFinal {writer.outs[0]} = cross_dp_wred ({inputs}.map pmStore) at hWriter",
        f"  have hWriterReduce : pmFinal {writer.outs[0]} =",
        f"      allReducePrim ({inputs}.map pmStore).length 0 ({inputs}.map pmStore) := by",
        "    rw [hWriter]",
        "    exact cross_dp_wred_eq_allReducePrim _ (by simp)",
        f"  have hJoined : smFinal {before.sm_tid} = pmFinal {writer.outs[0]} := by",
        "    rw [hSmFinal]",
        "    exact hin.full_value.trans hWriterReduce.symm",
        f"  have hout : {after.fact_id}.Holds smFinal pmFinal := by",
        f"    unfold {after.fact_id} RelationFact.Holds",
        f"    refine ⟨hJoined, ?_, ?_⟩",
        "    · rw [hSmFinal]", "      exact hin.full_shape",
        "    · rw [← hJoined, hSmFinal]", "      exact hin.full_shape",
        f"  exact RelationState.Holds.mono_insert (before := {retained_name})",
        f"    (after := {post_state.state_id}) (fresh := {after.fact_id})",
        "    hframe hout (by native_decide)",
    ]
    lines.extend([
        "", f"private def {segment_id} : ClosedDepSegmentCertificate",
        f"    {ir.sm_graph_ref} {ir.pm_graph_ref} {pre_state.state_id} {post_state.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    simpa only [{sm_final_name}, {pm_final_name}] using",
        f"      {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
