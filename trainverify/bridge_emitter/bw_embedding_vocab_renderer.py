"""Sparse full-frame renderer for vocab-sharded BW_embedding."""
from __future__ import annotations


def render_closed_k_rank_bw_embedding_vocab_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("bw-embedding-vocab-sharded-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("vocab BW_embedding requires one transition")
    transition_map = {x.transition_id: x for x in relation.transition_specs}
    transition = transition_map.get(segment.transition_ids[0])
    if transition is None or transition.rule_id != rule or transition.lean_theorem != theorem:
        raise ValueError("vocab BW_embedding typed family mismatch")
    cert = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda c: (tuple(sorted((c.gradient_fact, c.ids_fact, c.weight_fact))), (c.output_fact,)),
    )
    records = {x.source: x for x in chain.relation_facts}
    try:
        gradient = records[cert.gradient_fact]
        ids = records[cert.ids_fact]
        weight = records[cert.weight_fact]
        output = records[cert.output_fact]
    except KeyError as exc:
        raise ValueError("vocab BW_embedding fact missing") from exc
    states = {x.state_id: x for x in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if not {gradient.fact_id, ids.fact_id, weight.fact_id} <= set(before.fact_ids):
        raise ValueError("vocab BW_embedding inputs are not live")
    if output.fact_id not in after.fact_ids or not set(after.fact_ids) <= ({output.fact_id} | set(before.fact_ids)):
        raise ValueError("vocab BW_embedding post-state mismatch")

    k = cert.rank_count
    full_shape = tuple(cert.full_shape); shard_shape = tuple(cert.shard_shape)
    if (k != 4 or cert.gather_dim != 0 or cert.shard_rows <= 0 or cert.hidden <= 0
            or full_shape != (cert.shard_rows * k, cert.hidden)
            or shard_shape != (cert.shard_rows, cert.hidden)
            or gradient.kind != "joined" or gradient.joined_pm_tid is None
            or ids.kind != "sharded" or ids.gather_dim != 0 or len(ids.pm_tids) != 1
            or weight.kind != "sharded" or weight.gather_dim != 0 or len(weight.pm_tids) != k
            or weight.full_shape != full_shape or weight.shard_shape != shard_shape
            or output.kind != "sharded" or output.gather_dim != 0 or len(output.pm_tids) != k
            or output.full_shape != full_shape or output.shard_shape != shard_shape):
        raise ValueError("vocab BW_embedding metadata mismatch")

    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("vocab BW_embedding writer cardinality mismatch")
    sm_start, sm_end = segment.sm_range; pm_start, pm_end = segment.pm_range
    sm_range = set(range(sm_start, sm_end)); pm_range = set(range(pm_start, pm_end))
    sm_indices = tuple(transition.sm_node_indices); pm_indices = tuple(transition.pm_node_indices)
    if (len(sm_indices) != len(set(sm_indices)) or len(pm_indices) != len(set(pm_indices))
            or not set(sm_indices) <= sm_range or not set(pm_indices) <= pm_range):
        raise ValueError("vocab BW_embedding writer/frame partition mismatch")
    sm_node = ir.sm_nodes[sm_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[i] for i in pm_indices)
    if (sm_node.rank != 0 or sm_node.op != "BW_embedding" or sm_node.params
            or tuple(sm_node.ins) != (gradient.sm_tid, ids.sm_tid, weight.sm_tid)
            or sm_node.outs != [output.sm_tid]):
        raise ValueError("vocab BW_embedding SM writer mismatch")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("vocab BW_embedding PM ranks are not ordered")
    for rank, node in enumerate(pm_nodes):
        if (node.op != "BW_embedding" or node.params != [rank * cert.shard_rows]
                or tuple(node.ins) != (gradient.joined_pm_tid, ids.pm_tids[0], weight.pm_tids[rank])
                or node.outs != [output.pm_tids[rank]]):
            raise ValueError("vocab BW_embedding PM writer mismatch")
    if cert.sm_step_id != f"sm:{sm_indices[0]}:0" or cert.pm_step_ids != tuple(
            f"pm:{index}:0" for index in pm_indices):
        raise ValueError("vocab BW_embedding certificate writer footprint mismatch")

    # Sparse frame nodes are retained, but may not overwrite any live relation or
    # tensor-equality/shape authority carried by either boundary state.
    live_ids = set(before.fact_ids) | set(after.fact_ids)
    relation_by_id = {x.fact_id: x for x in chain.relation_facts}
    live_sm, live_pm = set(), set()
    for fact_id in live_ids:
        record = relation_by_id.get(fact_id)
        if record is None:
            continue
        live_sm.add(record.sm_tid); live_pm.update(record.pm_tids)
        if record.joined_pm_tid is not None:
            live_pm.add(record.joined_pm_tid)
        if record.metadata_tid is not None:
            live_sm.add(record.metadata_tid); live_pm.add(record.metadata_tid)
    authority = {x.fact_id: x for x in chain.authority_facts}
    for fact_id in live_ids:
        fact = authority.get(fact_id)
        if fact is None:
            continue
        if fact.kind == "tensor_shape":
            (live_sm if fact.side == "sm" else live_pm).add(fact.tid)
        elif fact.kind == "tensor_eq":
            (live_sm if fact.left_side == "sm" else live_pm).add(fact.left_tid)
            (live_sm if fact.right_side == "sm" else live_pm).add(fact.right_tid)
        else:
            raise ValueError("vocab BW_embedding unsupported live authority kind")
    sm_frame_only = sm_range - set(sm_indices); pm_frame_only = pm_range - set(pm_indices)
    if (any(set(ir.sm_nodes[i].outs) & live_sm for i in sm_frame_only)
            or any(set(ir.pm_nodes[i].outs) & live_pm for i in pm_frame_only)):
        raise ValueError("vocab BW_embedding frame overwrites live authority")

    sm_frame = list(ir.sm_nodes[sm_start:sm_end]); pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    sm_nodes_name = f"{segment_id}_sm_nodes"; pm_nodes_name = f"{segment_id}_pm_nodes"
    sm_final_name = f"{segment_id}_sm_final"; pm_final_name = f"{segment_id}_pm_final"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(x) for x in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(x) for x in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node, offset):
        final = f"({final_name} {initial})"; theorem_name = f"{segment_id}_{name}"
        if offset is None:
            expression = f"bw_embedding ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})"
            apply = f"exact applyNode_bw_embedding_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]}"
        else:
            expression = f"bw_embedding_offset {offset} ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})"
            apply = f"exact applyNode_bw_embedding_offset_out {graph} t {node.rank} {offset} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]}"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        proof = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame, position=position,
            output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs}, expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]", apply,
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in proof)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = writer("hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
                       sm_nodes_name, sm_frame, sm_indices[0] - sm_start, sm_node, None)
    pm_helpers = tuple(
        writer(f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
               pm_nodes_name, pm_frame, index - pm_start, node, rank * cert.shard_rows)
        for rank, (index, node) in enumerate(zip(pm_indices, pm_nodes))
    )

    full = _shape_text(list(full_shape)); shard = _shape_text(list(shard_shape))
    weights = "[" + ", ".join(f"pmFinal {x}" for x in weight.pm_tids) + "]"
    outputs = "[" + ", ".join(f"pmFinal {x}" for x in output.pm_tids) + "]"
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  let smFinal := {sm_final_name} smStore", f"  let pmFinal := {pm_final_name} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate <;> native_decide",
        f"  have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change smFinal {gradient.sm_tid} = pmFinal {gradient.joined_pm_tid} ∧ _ ∧ _ at hg",
        f"  have hi : {ids.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {ids.sm_tid}) [pmFinal {ids.pm_tids[0]}] 0 {_shape_text(list(ids.full_shape))} {_shape_text(list(ids.shard_shape))} at hi",
        f"  have hiEq : smFinal {ids.sm_tid} = pmFinal {ids.pm_tids[0]} := by",
        f"    rw [hi.full_value]", f"    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hi.shard_shapes (pmFinal {ids.pm_tids[0]}) (by simp)]; native_decide)",
        f"  have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {weight.sm_tid}) {weights} 0 {full} {shard} at hw",
        f"  have hwV : smFinal {weight.sm_tid} = allGatherPrimDimN 0 4 0 {weights} := by",
        f"    simpa only [List.length_cons, List.length_nil] using hw.full_value",
        f"  have hSm := {sm_helper} smStore",
        f"  change smFinal {output.sm_tid} = bw_embedding (smFinal {gradient.sm_tid}) (smFinal {ids.sm_tid}) (smFinal {weight.sm_tid}) at hSm",
    ])
    for rank, helper in enumerate(pm_helpers):
        node = pm_nodes[rank]
        lines.extend([
            f"  have hPm{rank} := {helper} pmStore",
            f"  change pmFinal {output.pm_tids[rank]} = bw_embedding_offset {rank * cert.shard_rows} "
            f"(pmFinal {gradient.joined_pm_tid}) (pmFinal {ids.pm_tids[0]}) (pmFinal {weight.pm_tids[rank]}) at hPm{rank}",
            f"  have hwShape{rank} := hw.shard_shapes (pmFinal {weight.pm_tids[rank]}) (by simp)",
            f"  have houtShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
            f"    rw [hPm{rank}, bw_embedding_offset_shape]", f"    exact hwShape{rank}",
        ])
    theorem_args = " ".join(f"(pmFinal {x})" for x in weight.pm_tids)
    shape_args = " ".join(f"hwShape{rank}" for rank in range(k))
    lines.extend([
        f"  have hComm := {cert.lean_theorem} {cert.shard_rows} {cert.hidden} (by omega) (by omega) "
        f"(pmFinal {gradient.joined_pm_tid}) (pmFinal {ids.pm_tids[0]}) {theorem_args} {shape_args}",
        f"  have hValue : smFinal {output.sm_tid} = allGatherPrimDimN 0 4 0 {outputs} := by",
        "    rw [hSm, hg.1, hiEq, hwV, hComm]",
        "    rw [" + ", ".join(f"← hPm{rank}" for rank in range(k)) + "]",
        f"  have hValueL : smFinal {output.sm_tid} = allGatherPrimDimN 0 {outputs}.length 0 {outputs} := by",
        "    simpa only [List.length_cons, List.length_nil] using hValue",
        f"  have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
        "    rw [hSm, bw_embedding_shape]", "    exact hw.full_shape",
        f"  have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"    change ShardedRel (smFinal {output.sm_tid}) {outputs} 0 {full} {shard}",
        "    refine {", "      full_value := hValueL", "      full_shape := hFullShape",
        "      shards_nonempty := by simp", "      gather_dim_lt := by native_decide",
        "      shard_shapes := ?_", "      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide", "    }",
        "    intro x hx", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx",
        "    rcases hx with " + " | ".join("rfl" for _ in range(k)),
    ])
    for rank in range(k):
        lines.append(f"    · exact houtShape{rank}")
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ [{output.fact_id}] ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ [{output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered", "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh", "    rcases fresh with rfl", "    exact hout",
        "  · exact hframe fact old", "",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    have h := {segment_id}_sound smStore pmStore hstate",
        f"    unfold {sm_final_name} {pm_final_name} at h", "    exact h", "",
    ])
    return "\n".join(lines)
