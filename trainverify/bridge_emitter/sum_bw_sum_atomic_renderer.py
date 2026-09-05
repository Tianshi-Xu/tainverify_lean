"""Single-fold renderer for interleaved FW_sum and BW_sum transitions."""
from __future__ import annotations


def render_closed_sum_bw_sum_atomic_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value
        from .relation_compiler import KRankSumProducerCertificate, KRankBWSumCertificate
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value
        from relation_compiler import KRankSumProducerCertificate, KRankBWSumCertificate

    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 2:
        raise ValueError("sum/BW_sum atomic renderer requires exactly two transitions")
    by_id = {item.transition_id: item for item in relation.transition_specs}
    transitions = tuple(by_id[item] for item in segment.transition_ids)
    if tuple(item.rule_id for item in transitions) != (
        "sum-producer-sharded-k-rank-dim1",
        "bw-sum-scalar-broadcast-dim2-k-rank",
    ):
        raise ValueError("sum/BW_sum atomic renderer received the wrong family")
    sum_transition, bw_transition = transitions
    sum_theorem = "TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum"
    bw_theorem = "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3"
    if sum_transition.lean_theorem != sum_theorem or bw_transition.lean_theorem != bw_theorem:
        raise ValueError("sum/BW_sum theorem identity mismatch")

    records = {item.source: item for item in chain.relation_facts}
    try:
        activation = records[sum_transition.pre_facts[0]]
        sum_post = records[sum_transition.post_facts[0]]
        bw_post = records[bw_transition.post_facts[0]]
    except (IndexError, KeyError) as exc:
        raise ValueError("sum/BW_sum relation fact is not materialized") from exc
    if activation.source not in bw_transition.pre_facts:
        raise ValueError("sum/BW_sum transitions do not share exact activation authority")
    gradient_source = next((item for item in bw_transition.pre_facts if item != activation.source), None)
    if gradient_source is None or gradient_source not in records:
        raise ValueError("sum/BW_sum gradient authority is not materialized")
    gradient = records[gradient_source]

    sum_matches = [item for item in relation.certificates
                   if type(item) is KRankSumProducerCertificate
                   and item.rule_id == sum_transition.rule_id
                   and item.lean_theorem == sum_transition.lean_theorem
                   and (item.input_fact,) == sum_transition.pre_facts
                   and (item.output_fact,) == sum_transition.post_facts]
    bw_matches = [item for item in relation.certificates
                  if type(item) is KRankBWSumCertificate
                  and item.rule_id == bw_transition.rule_id
                  and item.lean_theorem == bw_transition.lean_theorem
                  and {item.gradient_fact, item.activation_fact} == set(bw_transition.pre_facts)
                  and (item.output_fact,) == bw_transition.post_facts]
    if len(sum_matches) != 1 or len(bw_matches) != 1:
        raise ValueError("sum/BW_sum requires one exact typed certificate per transition")
    sum_cert, bw_cert = sum_matches[0], bw_matches[0]

    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if not {activation.fact_id, gradient.fact_id} <= set(before.fact_ids):
        raise ValueError("sum/BW_sum pre-facts are not live")
    if not {sum_post.fact_id, bw_post.fact_id} <= set(after.fact_ids):
        raise ValueError("sum/BW_sum post-facts are not live")
    if not set(after.fact_ids) <= set(before.fact_ids) | {sum_post.fact_id, bw_post.fact_id}:
        raise ValueError("sum/BW_sum post-state introduces an unproved fact")

    k = len(activation.pm_tids)
    full_shape_meta = activation.full_shape
    shard_shape_meta = activation.shard_shape
    if (k < 2 or sum_cert.rank_count != k or bw_cert.rank_count != k
            or activation.kind != "sharded" or activation.gather_dim != 2
            or len(full_shape_meta) != 3 or len(shard_shape_meta) != 3
            or any(value <= 0 for value in shard_shape_meta)
            or full_shape_meta[:2] != shard_shape_meta[:2]
            or full_shape_meta[2] != shard_shape_meta[2] * k
            or gradient.kind != "reduction" or len(gradient.pm_tids) != 1
            or gradient.full_shape != (1,) or gradient.shard_shape != (1,)
            or sum_post.kind != "reduction" or len(sum_post.pm_tids) != k
            or sum_post.full_shape != (1,) or sum_post.shard_shape != (1,)
            or bw_post.kind != "sharded" or bw_post.gather_dim != 2
            or (bw_post.full_shape, bw_post.shard_shape)
               != (activation.full_shape, activation.shard_shape)):
        raise ValueError("sum/BW_sum relation metadata is not exact")

    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    sum_sm_index = sum_transition.sm_node_indices[0]
    bw_sm_index = bw_transition.sm_node_indices[0]
    sum_pm_indices = tuple(sum_transition.pm_node_indices)
    bw_pm_indices = tuple(bw_transition.pm_node_indices)
    if (len(sum_transition.sm_node_indices) != 1 or len(bw_transition.sm_node_indices) != 1
            or len(sum_pm_indices) != k or len(bw_pm_indices) != k
            or set(sum_transition.sm_node_indices + bw_transition.sm_node_indices)
               != set(range(sm_start, sm_end))
            or set(sum_pm_indices + bw_pm_indices) != set(range(pm_start, pm_end))
            or set(sum_pm_indices) & set(bw_pm_indices)):
        raise ValueError("sum/BW_sum writers do not exactly partition the atomic frame")
    sum_sm, bw_sm = ir.sm_nodes[sum_sm_index], ir.sm_nodes[bw_sm_index]
    sum_pm = tuple(ir.pm_nodes[index] for index in sum_pm_indices)
    bw_pm = tuple(ir.pm_nodes[index] for index in bw_pm_indices)
    if (sum_sm.op != "FW_sum" or sum_sm.ins != [activation.sm_tid]
            or sum_sm.outs != [sum_post.sm_tid]
            or tuple(node.rank for node in sum_pm) != tuple(range(k))
            or any(node.op != "FW_sum" or node.ins != [activation.pm_tids[r]]
                   or node.outs != [sum_post.pm_tids[r]] for r, node in enumerate(sum_pm))):
        raise ValueError("FW_sum writer binding is not exact")
    if (bw_sm.op != "BW_sum" or tuple(bw_sm.ins) != (gradient.sm_tid, activation.sm_tid)
            or bw_sm.outs != [bw_post.sm_tid]
            or tuple(node.rank for node in bw_pm) != tuple(range(k))
            or any(node.op != "BW_sum"
                   or tuple(node.ins) != (gradient.pm_tids[0], activation.pm_tids[r])
                   or node.outs != [bw_post.pm_tids[r]] for r, node in enumerate(bw_pm))):
        raise ValueError("BW_sum writer binding is not exact")

    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    sm_final_name, pm_final_name = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"@[irreducible] private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store", "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node, fn, apply):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {fn} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=fn.replace(final, "{store}"), apply_lines=apply,
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sum_sm_h = writer("sumSm", ir.sm_graph_ref, "smStore", sm_final_name, sm_nodes_name,
                      sm_frame, sum_sm_index-sm_start, sum_sm,
                      f"fw_sum (({sm_final_name} smStore) {activation.sm_tid})", [
                          "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                          "simp [applyNodeDistributed, applyNodeRingAttn]",
                          f"exact applyNode_fw_sum_out {ir.sm_graph_ref} t 0 {activation.sm_tid} {sum_post.sm_tid}",
                      ])
    bw_sm_h = writer("bwSm", ir.sm_graph_ref, "smStore", sm_final_name, sm_nodes_name,
                     sm_frame, bw_sm_index-sm_start, bw_sm,
                     f"bw_sum (({sm_final_name} smStore) {gradient.sm_tid}) (({sm_final_name} smStore) {activation.sm_tid})", [
                         "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                         "simp [applyNodeDistributed, applyNodeRingAttn]",
                         f"exact applyNode_bw_sum_out {ir.sm_graph_ref} t 0 {gradient.sm_tid} {activation.sm_tid} {bw_post.sm_tid}",
                     ])
    sum_pm_h, bw_pm_h = [], []
    for r in range(k):
        sn, bn = sum_pm[r], bw_pm[r]
        sum_pm_h.append(writer(f"sumPm{r}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, sum_pm_indices[r]-pm_start, sn,
            f"fw_sum (({pm_final_name} pmStore) {activation.pm_tids[r]})", [
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_fw_sum_out {ir.pm_graph_ref} t {r} {activation.pm_tids[r]} {sum_post.pm_tids[r]}",
            ]))
        bw_pm_h.append(writer(f"bwPm{r}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, bw_pm_indices[r]-pm_start, bn,
            f"bw_sum (({pm_final_name} pmStore) {gradient.pm_tids[0]}) (({pm_final_name} pmStore) {activation.pm_tids[r]})", [
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_sum_out {ir.pm_graph_ref} t {r} {gradient.pm_tids[0]} {activation.pm_tids[r]} {bw_post.pm_tids[r]}",
            ]))

    activation_list = "[" + ", ".join(f"pmFinal {t}" for t in activation.pm_tids) + "]"
    mapped_bw_list = "[" + ", ".join(
        f"bw_sum (smFinal {gradient.sm_tid}) (pmFinal {t})"
        for t in activation.pm_tids
    ) + "]"
    sum_list = "[" + ", ".join(f"pmFinal {t}" for t in sum_post.pm_tids) + "]"
    bw_list = "[" + ", ".join(f"pmFinal {t}" for t in bw_post.pm_tids) + "]"
    full = _shape_text(list(activation.full_shape)); shard = _shape_text(list(activation.shard_shape))
    d0, d1, d2 = shard_shape_meta
    lines.extend([
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  let smFinal := {sm_final_name} smStore", f"  let pmFinal := {pm_final_name} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "    · native_decide", "    · native_decide", "    · native_decide", "    · native_decide",
        f"  have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {activation.sm_tid}) {activation_list} 2 {full} {shard} at hx",
        f"  change ReductionRel (smFinal {gradient.sm_tid}) [pmFinal {gradient.pm_tids[0]}] [1] at hg",
        f"  have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN 2 {k} 0 {activation_list} := by",
        "    simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"  have hgValue : smFinal {gradient.sm_tid} = pmFinal {gradient.pm_tids[0]} := ReductionRel.singleton_value hg",
        f"  have hSumSm := {sum_sm_h} smStore",
        f"  change smFinal {sum_post.sm_tid} = fw_sum (smFinal {activation.sm_tid}) at hSumSm",
        f"  have hBwSm := {bw_sm_h} smStore",
        f"  change smFinal {bw_post.sm_tid} = bw_sum (smFinal {gradient.sm_tid}) (smFinal {activation.sm_tid}) at hBwSm",
    ])
    for r in range(k):
        lines.extend([f"  have hSumPm{r} := {sum_pm_h[r]} pmStore",
                      f"  change pmFinal {sum_post.pm_tids[r]} = fw_sum (pmFinal {activation.pm_tids[r]}) at hSumPm{r}",
                      f"  have hBwPm{r} := {bw_pm_h[r]} pmStore",
                      f"  change pmFinal {bw_post.pm_tids[r]} = bw_sum (pmFinal {gradient.pm_tids[0]}) (pmFinal {activation.pm_tids[r]}) at hBwPm{r}",
                      f"  have hXShape{r} := hx.shard_shapes (pmFinal {activation.pm_tids[r]}) (by simp)"])
    lines.extend([
        f"  have hSumComm := {sum_theorem} 2 {k} {activation_list} rfl (by simp) {shard}",
        "    (by simpa using hXShape0) hx.shard_shapes hx.gather_dim_lt (by native_decide) (by native_decide)",
        f"  have hSumValue : smFinal {sum_post.sm_tid} = allReducePrim {sum_list}.length 0 {sum_list} := by",
        "    rw [hSumSm, hxValue, hSumComm]", "    simp only [List.map, List.length_cons, List.length_nil]",
        "    rw [" + ", ".join(f"← hSumPm{r}" for r in range(k)) + "]",
        f"  have hSumOut : {sum_post.fact_id}.Holds smFinal pmFinal := by",
        f"    change ReductionRel (smFinal {sum_post.sm_tid}) {sum_list} [1]",
        "    refine { full_value := hSumValue, full_shape := ?_, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }",
        "    · rw [hSumSm]", "      exact fw_sum_shape _",
        "    · intro t ht", "      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht",
        "      rcases ht with " + " | ".join(f"h{r}" for r in range(k)),
    ])
    for r in range(k):
        lines.extend(["      · subst t", f"        rw [hSumPm{r}]", "        exact fw_sum_shape _"])
    lines.extend(["    · rw [← hSumValue]", "      rw [hSumSm]", "      exact fw_sum_shape _",
                  f"  have hBwComm : bw_sum (smFinal {gradient.sm_tid})",
                  f"      (allGatherPrimDimN 2 {k} 0 {activation_list}) =",
                  f"      allGatherPrimDimN 2 {k} 0 {mapped_bw_list} := by",
                  "    simpa only [List.length_cons, List.length_nil, List.map] using",
                  f"      ({bw_theorem}",
                  f"        (smFinal {gradient.sm_tid}) {activation_list} {d0} {d1} {d2}",
                  "        hx.shards_nonempty (by native_decide) hx.shard_shapes)",
                  f"  have hBwOut : {bw_post.fact_id}.Holds smFinal pmFinal := by",
                  f"    change ShardedRel (smFinal {bw_post.sm_tid}) {bw_list} 2 {full} {shard}",
                  "    constructor", f"    · change smFinal {bw_post.sm_tid} = allGatherPrimDimN 2 {k} 0 {bw_list}",
                  "      rw [hBwSm, hxValue, hBwComm, hgValue]",
                  "      rw [" + ", ".join(f"← hBwPm{r}" for r in range(k)) + "]",
                  "    · rw [hBwSm, bw_sum_shape, hx.full_shape]", "    · simp", "    · exact hx.gather_dim_lt",
                  "    · intro t ht", "      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht",
                  "      rcases ht with " + " | ".join(f"h{r}" for r in range(k)),])
    for r in range(k):
        lines.extend(["      · subst t", f"        rw [hBwPm{r}, bw_sum_shape, hXShape{r}]"])
    lines.extend(["    · exact hx.shape_contract", "  intro fact hfact",
                  f"  have covered : fact ∈ [{sum_post.fact_id}, {bw_post.fact_id}] ++ {before.state_id}.facts := by",
                  f"    exact (show {after.state_id}.facts ⊆ [{sum_post.fact_id}, {bw_post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
                  "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
                  "  rcases covered with fresh | old", "  · rcases fresh with rfl | rfl", "    · exact hSumOut", "    · exact hBwOut",
                  "  · exact hframe fact old", "",
                  f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
                  f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}", "  sound := by",
                  "    intro smStore pmStore hstate",
                  f"    simpa only [{sm_final_name}, {pm_final_name}] using {segment_id}_sound smStore pmStore hstate", ""])
    return "\n".join(lines)
