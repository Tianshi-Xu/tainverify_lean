"""Closed renderer for exact typed BW_sum scalar-broadcast certificates."""


def render_closed_k_rank_bw_sum_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("bw-sum-scalar-broadcast-dim2-k-rank")
    rule_id = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("bw-sum-scalar-broadcast-dim2-k-rank requires one atomic transition")
    transition = {item.transition_id: item for item in relation.transition_specs}[
        segment.transition_ids[0]
    ]
    if transition.rule_id != rule_id or transition.lean_theorem != theorem:
        raise ValueError("bw-sum-scalar-broadcast-dim2-k-rank theorem identity mismatch")
    records = {item.source: item for item in chain.relation_facts}
    try:
        post = records[transition.post_facts[0]]
    except (IndexError, KeyError) as exc:
        raise ValueError("K-rank BW_sum relation fact is not materialized") from exc
    k = len(post.pm_tids)
    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("K-rank BW_sum transition footprint is not exact 1+K")
    try:
        role_sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
        role_pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    except IndexError as exc:
        raise ValueError("K-rank BW_sum transition footprint names a missing writer") from exc

    transition_pre_set = set(transition.pre_facts)
    typed = []
    for item in relation.certificates:
        if (type(item) is not spec.certificate_type
                or item.rule_id != transition.rule_id
                or item.lean_theorem != transition.lean_theorem
                or transition.post_facts != (item.output_fact,)
                or len(transition.pre_facts) != 2
                or len(transition_pre_set) != 2
                or {item.gradient_fact, item.activation_fact} != transition_pre_set):
            continue
        try:
            candidate_g = records[item.gradient_fact]
            candidate_x = records[item.activation_fact]
        except KeyError:
            continue
        if tuple(role_sm_node.ins) != (candidate_g.sm_tid, candidate_x.sm_tid):
            continue
        typed.append((item, candidate_g, candidate_x))
    if len(typed) != 1:
        raise ValueError("BW_sum requires one exact typed certificate")
    certificate, gradient, activation = typed[0]
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if (not {gradient.fact_id, activation.fact_id} <= set(before.fact_ids)
            or post.fact_id not in after.fact_ids):
        raise ValueError("K-rank BW_sum pre/post facts are not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("K-rank BW_sum post-state introduces an unproved fact")
    k = len(post.pm_tids)
    full_shape_meta = activation.full_shape
    shard_shape_meta = activation.shard_shape
    if (k < 2 or certificate.rank_count != k or certificate.gather_dim != 2
            or gradient.kind != "reduction" or len(gradient.pm_tids) != 1
            or gradient.full_shape != (1,) or gradient.shard_shape != (1,)
            or activation.kind != "sharded" or activation.gather_dim != 2
            or post.kind != "sharded" or post.gather_dim != 2
            or len(activation.pm_tids) != k
            or len(full_shape_meta) != 3 or len(shard_shape_meta) != 3
            or any(value <= 0 for value in shard_shape_meta)
            or full_shape_meta[2] != shard_shape_meta[2] * k
            or full_shape_meta[:2] != shard_shape_meta[:2]
            or (activation.full_shape, activation.shard_shape)
               != (post.full_shape, post.shard_shape)):
        raise ValueError("K-rank BW_sum relation metadata is not exact")
    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("K-rank BW_sum transition footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if (not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("K-rank BW_sum writers are outside the complete segment frame")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    if sm_node.rank != 0 or sm_node.op != "BW_sum":
        raise ValueError("K-rank BW_sum SM writer is not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("K-rank BW_sum PM writers are not ordered ranks 0..K-1")
    writers = (sm_node, *pm_nodes)
    if any(node.params for node in writers):
        raise ValueError("K-rank BW_sum writers require no parameters")
    if any(node.op != "BW_sum" or len(node.ins) != 2 or len(node.outs) != 1 for node in writers):
        raise ValueError("K-rank BW_sum writers must be binary singleton-output BW_sum nodes")
    if tuple(sm_node.ins) != (gradient.sm_tid, activation.sm_tid):
        raise ValueError("K-rank BW_sum SM operand order disagrees with certificate inputs")
    expected_inputs = tuple(
        (gradient.pm_tids[0], activation.pm_tids[rank]) for rank in range(k)
    )
    actual_inputs = tuple(tuple(node.ins) for node in pm_nodes)
    if actual_inputs != expected_inputs:
        raise ValueError("K-rank BW_sum PM inputs disagree with exact ordered relation TIDs")
    if (sm_node.outs[0] != post.sm_tid
            or tuple(node.outs[0] for node in pm_nodes) != tuple(post.pm_tids)):
        raise ValueError("K-rank BW_sum outputs disagree with exact ordered relation TIDs")

    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    activation_list = "[" + ", ".join(
        f"pmFinal {tid}" for tid in activation.pm_tids
    ) + "]"
    mapped_activation_list = "[" + ", ".join(
        f"bw_sum (smFinal {gradient.sm_tid}) (pmFinal {tid})"
        for tid in activation.pm_tids
    ) + "]"
    out_list = "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]"
    full_shape = _shape_text(list(post.full_shape))
    shard_shape = _shape_text(list(post.shard_shape))

    sm_final_name, pm_final_name = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"@[irreducible] private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store", "",
    ]

    def bw_sum_writer(name, graph, initial, final_name, nodes_name, frame, position, node):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = bw_sum ({final} {node.ins[0]}) ({final} {node.ins[1]}) := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=f"bw_sum ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})",
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_sum_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = bw_sum_writer("hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
                           sm_nodes_name, sm_frame,
                           transition.sm_node_indices[0] - sm_start, sm_node)
    pm_helpers = []
    for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes)):
        pm_helpers.append(bw_sum_writer(
            f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, index - pm_start, node,
        ))

    lines.extend([
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smFinal := {sm_final_name} smStore",
        f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ReductionRel (smFinal {gradient.sm_tid}) [pmFinal {gradient.pm_tids[0]}]",
        f"      {_shape_text(list(gradient.full_shape))} at hg",
        f"    have hgValue : smFinal {gradient.sm_tid} = pmFinal {gradient.pm_tids[0]} :=",
        "      ReductionRel.singleton_value hg",
        f"    change ShardedRel (smFinal {activation.sm_tid}) {activation_list} 2 {full_shape} {shard_shape} at hx",
        f"    have hxValue : smFinal {activation.sm_tid} =",
        f"        allGatherPrimDimN 2 {k} 0 {activation_list} := by",
        "      simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"    have hSmWriter : smFinal {sm_node.outs[0]} =",
        f"        bw_sum (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) := by",
        f"      exact {sm_helper} smStore",
    ])
    for rank, (helper, node) in enumerate(zip(pm_helpers, pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {node.outs[0]} =",
            f"        bw_sum (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) := by",
            f"      exact {helper} pmStore",
            f"    have hXShape{rank} := hx.shard_shapes (pmFinal {activation.pm_tids[rank]}) (by simp)",
        ])
    d0, d1, d2 = shard_shape_meta
    lines.extend([
        f"    have hcomm : bw_sum (smFinal {gradient.sm_tid})",
        f"        (allGatherPrimDimN 2 {k} 0 {activation_list}) =",
        f"        allGatherPrimDimN 2 {k} 0 {mapped_activation_list} := by",
        "      simpa only [List.length_cons, List.length_nil, List.map] using",
        f"        ({theorem}",
        f"          (smFinal {gradient.sm_tid}) {activation_list} {d0} {d1} {d2}",
        "          hx.shards_nonempty (by native_decide) hx.shard_shapes)",
        f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {post.sm_tid}) {out_list} 2 {full_shape} {shard_shape}",
        "      constructor",
        "      · change smFinal " + str(post.sm_tid) +
        f" = allGatherPrimDimN 2 {k} 0 {out_list}",
        "        rw [hSmWriter, hxValue, hcomm, hgValue]",
        "        rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
        "      · rw [hSmWriter, bw_sum_shape, hx.full_shape]",
        "      · simp", "      · exact hx.gather_dim_lt", "      · intro shard hmem",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend([
            "        · subst shard", f"          rw [hPmWriter{rank}, bw_sum_shape, hXShape{rank}]",
        ])
    lines.extend([
        "      · exact hx.shape_contract",
        "    intro fact hfact",
        f"    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl", "      exact hout", "    · exact hframe fact old", "",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{sm_final_name}, {pm_final_name}] using {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
