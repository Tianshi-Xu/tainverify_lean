"""Closed renderer for exact dynamic-K sharded FW_add certificates."""


def render_closed_k_rank_add_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("add-sharded-k-rank")
    rule_id = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("add-sharded-k-rank requires one atomic transition")
    transition = {item.transition_id: item for item in relation.transition_specs}[
        segment.transition_ids[0]
    ]
    if transition.rule_id != rule_id or transition.lean_theorem != theorem:
        raise ValueError("add-sharded-k-rank theorem identity mismatch")
    records = {item.source: item for item in chain.relation_facts}
    try:
        post = records[transition.post_facts[0]]
    except (IndexError, KeyError) as exc:
        raise ValueError("K-rank add relation fact is not materialized") from exc
    k = len(post.pm_tids)
    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("K-rank add transition footprint is not exact 1+K")
    try:
        role_sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
        role_pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    except IndexError as exc:
        raise ValueError("K-rank add transition footprint names a missing writer") from exc

    # Dependency scheduling canonicalizes transition.pre_facts, but a binary
    # certificate preserves semantic operand roles. Match the same exact fact
    # set, then recover A/B only from the ordered SM inputs and confirm that
    # every ordered PM rank uses those same roles. Keeping this strict for add
    # is deliberate: this adapter must remain sound for noncommutative binaries.
    transition_pre_set = set(transition.pre_facts)
    typed = []
    for item in relation.certificates:
        if (type(item) is not spec.certificate_type
                or item.rule_id != transition.rule_id
                or item.lean_theorem != transition.lean_theorem
                or transition.post_facts != (item.output_fact,)
                or item.op != spec.op
                or len(item.input_facts) != 2
                or len(set(item.input_facts)) != 2
                or len(transition.pre_facts) != 2
                or len(transition_pre_set) != 2
                or set(item.input_facts) != transition_pre_set):
            continue
        try:
            candidate_a, candidate_b = (records[source] for source in item.input_facts)
        except KeyError:
            continue
        if tuple(role_sm_node.ins) != (candidate_a.sm_tid, candidate_b.sm_tid):
            continue
        typed.append((item, candidate_a, candidate_b))
    if len(typed) != 1:
        raise ValueError("add-sharded-k-rank requires one exact typed certificate")
    certificate, a, b = typed[0]
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if not {a.fact_id, b.fact_id} <= set(before.fact_ids) or post.fact_id not in after.fact_ids:
        raise ValueError("K-rank add pre/post facts are not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("K-rank add post-state introduces an unproved fact")
    k = len(post.pm_tids)
    if (k < 2 or certificate.rank_count != k or len(a.pm_tids) != k or len(b.pm_tids) != k
            or certificate.gather_dim != a.gather_dim
            or a.gather_dim != b.gather_dim or a.gather_dim != post.gather_dim
            or a.kind != "sharded" or b.kind != "sharded" or post.kind != "sharded"
            or (a.full_shape, a.shard_shape) != (b.full_shape, b.shard_shape)
            or (a.full_shape, a.shard_shape) != (post.full_shape, post.shard_shape)):
        raise ValueError("K-rank add relation metadata is not exact")
    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("K-rank add transition footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if (not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("K-rank add writers are outside the complete segment frame")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    if sm_node.rank != 0 or sm_node.op != spec.op:
        raise ValueError("K-rank add SM writer is not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("K-rank add PM writers are not ordered ranks 0..K-1")
    writers = (sm_node, *pm_nodes)
    if any(node.params for node in writers):
        raise ValueError("K-rank add writers require no parameters")
    if any(node.op != spec.op or len(node.ins) != 2 or len(node.outs) != 1 for node in writers):
        raise ValueError("K-rank add writers must be binary singleton-output FW_add nodes")
    if tuple(sm_node.ins) != (a.sm_tid, b.sm_tid):
        raise ValueError("K-rank add SM operand order disagrees with certificate inputs")
    expected_inputs = tuple((a.pm_tids[rank], b.pm_tids[rank]) for rank in range(k))
    actual_inputs = tuple(tuple(node.ins) for node in pm_nodes)
    if any(set(actual) == set(expected) and actual != expected
           for actual, expected in zip(actual_inputs, expected_inputs)):
        raise ValueError("K-rank add PM operand order disagrees with certificate inputs")
    if actual_inputs != expected_inputs:
        raise ValueError("K-rank add PM inputs disagree with exact ordered relation TIDs")
    if (sm_node.outs[0] != post.sm_tid
            or tuple(node.outs[0] for node in pm_nodes) != tuple(post.pm_tids)):
        raise ValueError("K-rank add outputs disagree with exact ordered relation TIDs")

    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    a_list = "[" + ", ".join(f"pmFinal {tid}" for tid in a.pm_tids) + "]"
    b_list = "[" + ", ".join(f"pmFinal {tid}" for tid in b.pm_tids) + "]"
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

    def add_writer(name, graph, initial, final_name, nodes_name, frame, position, node):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = elemwiseAdd ({final} {node.ins[0]}) ({final} {node.ins[1]}) := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=f"elemwiseAdd ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})",
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_fw_add2_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = add_writer("hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
                           sm_nodes_name, sm_frame,
                           transition.sm_node_indices[0] - sm_start, sm_node)
    pm_helpers = []
    for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes)):
        pm_helpers.append(add_writer(
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
        f"    have ha : {a.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    have hb : {b.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {a.sm_tid}) {a_list} {post.gather_dim} {full_shape} {shard_shape} at ha",
        f"    change ShardedRel (smFinal {b.sm_tid}) {b_list} {post.gather_dim} {full_shape} {shard_shape} at hb",
        f"    have hSmWriter : smFinal {sm_node.outs[0]} =",
        f"        elemwiseAdd (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) := by",
        f"      exact {sm_helper} smStore",
    ])
    for rank, (helper, node) in enumerate(zip(pm_helpers, pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {node.outs[0]} =",
            f"        elemwiseAdd (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) := by",
            f"      exact {helper} pmStore",
        ])
    lines.extend([
        f"    have hcomm := fw_add_allGather_dim_K {post.gather_dim} {shard_shape} {a_list} {b_list}",
        "      ha.shards_nonempty (by simp) ha.gather_dim_lt",
        "      (fun r hr => ha.shard_shapes _ (List.get_mem _ ⟨r, hr⟩))",
        "      (fun r hr => hb.shard_shapes _ (List.get_mem _ ⟨r, hr⟩))",
        f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {post.sm_tid}) {out_list} {post.gather_dim} {full_shape} {shard_shape}",
        "      constructor",
        "      · rw [hSmWriter, ha.full_value, hb.full_value, hcomm]",
        "        simp only [List.zipWith, List.length_cons, List.length_nil]",
        "        rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
        "      · rw [hSmWriter]",
        f"        exact elemwiseAdd_shape_of_shapes _ _ {full_shape} ha.full_shape hb.full_shape",
        "      · simp", "      · exact ha.gather_dim_lt", "      · intro shard hmem",
    ])
    for rank in range(k):
        lines.extend([
            f"        have hAShape{rank} := ha.shard_shapes (pmFinal {a.pm_tids[rank]}) (by simp)",
            f"        have hBShape{rank} := hb.shard_shapes (pmFinal {b.pm_tids[rank]}) (by simp)",
        ])
    lines.extend([
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend([
            "        · subst shard", f"          rw [hPmWriter{rank}]",
            f"          exact elemwiseAdd_shape_of_shapes _ _ {shard_shape} hAShape{rank} hBShape{rank}",
        ])
    lines.extend([
        "      · exact ha.shape_contract",
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
