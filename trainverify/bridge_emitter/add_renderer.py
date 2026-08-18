"""Closed renderer for exact dynamic-K sharded FW_add certificates."""


def render_closed_k_rank_add_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import KRankBinaryRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import KRankBinaryRelationCertificate

    rule_id = "add-sharded-k-rank"
    theorem = "TrainVerify.Denote.fw_add_allGather_dim_K"
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("add-sharded-k-rank requires one atomic transition")
    transition = {item.transition_id: item for item in relation.transition_specs}[
        segment.transition_ids[0]
    ]
    if transition.rule_id != rule_id or transition.lean_theorem != theorem:
        raise ValueError("add-sharded-k-rank theorem identity mismatch")
    typed = [
        item for item in relation.certificates
        if type(item) is KRankBinaryRelationCertificate
        and item.rule_id == transition.rule_id
        and item.lean_theorem == transition.lean_theorem
        and item.input_facts == transition.pre_facts
        and transition.post_facts == (item.output_fact,)
        and item.op == "FW_add"
    ]
    if len(typed) != 1:
        raise ValueError("add-sharded-k-rank requires one exact typed certificate")
    certificate = typed[0]
    records = {item.source: item for item in chain.relation_facts}
    try:
        a, b = (records[item] for item in transition.pre_facts)
        post = records[transition.post_facts[0]]
    except KeyError as exc:
        raise ValueError("K-rank add relation fact is not materialized") from exc
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
    if (tuple(transition.sm_node_indices) != tuple(range(sm_start, sm_end))
            or sm_end - sm_start != 1
            or tuple(transition.pm_node_indices) != tuple(range(pm_start, pm_end))
            or pm_end - pm_start != k):
        raise ValueError("K-rank add segment ranges do not equal its writer footprint")
    sm_node = ir.sm_nodes[sm_start]
    pm_nodes = tuple(ir.pm_nodes[index] for index in range(pm_start, pm_end))
    if sm_node.rank != 0 or sm_node.op != "FW_add":
        raise ValueError("K-rank add SM writer is not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("K-rank add PM writers are not ordered ranks 0..K-1")
    writers = (sm_node, *pm_nodes)
    if any(node.params for node in writers):
        raise ValueError("K-rank add writers require no parameters")
    if any(node.op != "FW_add" or len(node.ins) != 2 or len(node.outs) != 1 for node in writers):
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

    sm_node_name = f"{segment_id}_sm_node"
    pm_node_names = [f"{segment_id}_pm_node_{rank}" for rank in range(k)]
    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    a_list = "[" + ", ".join(f"pmStore {tid}" for tid in a.pm_tids) + "]"
    b_list = "[" + ", ".join(f"pmStore {tid}" for tid in b.pm_tids) + "]"
    out_list = "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]"
    full_shape = _shape_text(list(post.full_shape))
    shard_shape = _shape_text(list(post.shard_shape))

    def writer(name, graph, store, node_names, pos, node, node_name, final):
        prefix, suffix = node_names[:pos], node_names[pos + 1:]
        local_nodes = "smNodes" if final == "smFinal" else "pmNodes"
        return [
            f"    have {name} : {final} {node.outs[0]} = elemwiseAdd ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            f"      simpa [{final}, {local_nodes}, {sm_nodes_name if final == 'smFinal' else pm_nodes_name}] using",
            f"        (foldl_faithful_binary_middle_writer {graph} {store} "
            f"[{', '.join(prefix)}] [{', '.join(suffix)}] {node_name}",
            f"          {node.ins[0]} {node.ins[1]} {node.outs[0]} elemwiseAdd (by",
            "            intro t",
            "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "            simp [applyNodeDistributed, applyNodeRingAttn]",
            f"            exact applyNode_fw_add2_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]})",
            "          (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))",
        ]

    lines = [f"private def {sm_node_name} : NodeDecl := {_node_text(sm_node)}"]
    lines += [f"private def {name} : NodeDecl := {_node_text(node)}"
              for name, node in zip(pm_node_names, pm_nodes)]
    lines += [
        f"private def {sm_nodes_name} : List NodeDecl := [{sm_node_name}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(pm_node_names)}]", "",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_nodes_name}",
        f"    let pmNodes : List NodeDecl := {pm_nodes_name}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have ha : {a.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hb : {b.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    change ShardedRel (smStore {a.sm_tid}) {a_list} {post.gather_dim} {full_shape} {shard_shape} at ha",
        f"    change ShardedRel (smStore {b.sm_tid}) {b_list} {post.gather_dim} {full_shape} {shard_shape} at hb",
    ]
    lines += writer("hSmWriter", ir.sm_graph_ref, "smStore", (sm_node_name,), 0,
                    sm_node, sm_node_name, "smFinal")
    for rank, node in enumerate(pm_nodes):
        lines += writer(f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_node_names,
                        rank, node, pm_node_names[rank], "pmFinal")
    lines += [
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
        "      · simp",
        "      · exact ha.gather_dim_lt",
        "      · intro shard hmem",
    ]
    for rank in range(k):
        lines += [
            f"        have hAShape{rank} := ha.shard_shapes (pmStore {a.pm_tids[rank]}) (by simp)",
            f"        have hBShape{rank} := hb.shard_shapes (pmStore {b.pm_tids[rank]}) (by simp)",
        ]
    lines += [
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ]
    for rank in range(k):
        lines += [
            "        · subst shard",
            f"          rw [hPmWriter{rank}]",
            f"          exact elemwiseAdd_shape_of_shapes _ _ {shard_shape} hAShape{rank} hBShape{rank}",
        ]
    lines += [
        "      · exact ha.shape_contract",
        "    intro fact hfact",
        f"    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl", "      exact hout",
        "    · exact hframe fact old", "",
    ]
    return "\n".join(lines)
