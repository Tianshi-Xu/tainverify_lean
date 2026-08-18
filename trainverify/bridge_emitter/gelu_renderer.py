"""Closed renderer for exact dynamic-K sharded FW_gelu certificates."""


def render_closed_k_rank_gelu_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import KRankLocalRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import KRankLocalRelationCertificate

    rule_id = "gelu-sharded-k-rank"
    theorem = "TrainVerify.Denote.fw_gelu_allGatherPrimDimN_eq"
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("gelu-sharded-k-rank requires one atomic transition")
    transition_by_id = {item.transition_id: item for item in relation.transition_specs}
    try:
        transition = transition_by_id[segment.transition_ids[0]]
    except KeyError as exc:
        raise ValueError("gelu-sharded-k-rank lacks its exact transition") from exc
    if transition.rule_id != rule_id or transition.lean_theorem != theorem:
        raise ValueError("gelu-sharded-k-rank theorem identity mismatch")
    if len(transition.pre_facts) != 1 or len(transition.post_facts) != 1:
        raise ValueError("gelu-sharded-k-rank requires one exact pre/post fact")

    fact_sources = [item.source for item in chain.relation_facts]
    if len(set(fact_sources)) != len(fact_sources):
        raise ValueError("gelu-sharded-k-rank has a duplicate relation fact source")
    state_ids = [item.state_id for item in chain.states]
    if len(set(state_ids)) != len(state_ids):
        raise ValueError("gelu-sharded-k-rank has a duplicate relation state id")
    records = {item.source: item for item in chain.relation_facts}
    states = {item.state_id: item for item in chain.states}
    try:
        pre = records[transition.pre_facts[0]]
        post = records[transition.post_facts[0]]
        before = states[segment.pre_state_id]
        after = states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("gelu-sharded-k-rank fact/state framing is unresolved") from exc
    if len(set(before.fact_ids)) != len(before.fact_ids) or len(set(after.fact_ids)) != len(after.fact_ids):
        raise ValueError("gelu-sharded-k-rank state framing contains duplicate facts")
    if pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids:
        raise ValueError("gelu-sharded-k-rank pre/post facts are not live")
    if not set(after.fact_ids) <= ({post.fact_id} | set(before.fact_ids)):
        raise ValueError("gelu-sharded-k-rank post-state introduces an unproved fact")

    exact_certificates = [
        item for item in relation.certificates
        if type(item) is KRankLocalRelationCertificate
        and item.rule_id == transition.rule_id
        and item.lean_theorem == transition.lean_theorem
        and item.op == "FW_gelu"
        and ((item.input_fact,), (item.output_fact,))
            == (transition.pre_facts, transition.post_facts)
    ]
    if len(exact_certificates) != 1:
        raise ValueError("gelu-sharded-k-rank requires one exact typed certificate")
    certificate = exact_certificates[0]

    k = len(post.pm_tids)
    if (k == 0 or certificate.rank_count != k or len(pre.pm_tids) != k
            or len(certificate.pm_step_ids) != k
            or certificate.external_tids or certificate.external_shapes
            or pre.kind != "sharded" or post.kind != "sharded"
            or certificate.gather_dim != pre.gather_dim
            or pre.gather_dim != post.gather_dim
            or pre.full_shape != post.full_shape
            or pre.shard_shape != post.shard_shape
            or len(pre.full_shape) != len(pre.shard_shape)
            or not pre.full_shape or pre.gather_dim >= len(pre.full_shape)):
        raise ValueError("gelu-sharded-k-rank relation metadata is not exact")
    if any(value <= 0 for value in pre.shard_shape):
        raise ValueError("gelu-sharded-k-rank requires a positive shard shape")
    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("gelu-sharded-k-rank transition footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if (tuple(transition.sm_node_indices) != tuple(range(sm_start, sm_end))
            or sm_end - sm_start != 1
            or tuple(transition.pm_node_indices) != tuple(range(pm_start, pm_end))
            or pm_end - pm_start != k):
        raise ValueError("gelu-sharded-k-rank segment ranges do not equal its writer footprint")
    try:
        sm_node = ir.sm_nodes[sm_start]
        pm_nodes = tuple(ir.pm_nodes[index] for index in range(pm_start, pm_end))
    except IndexError as exc:
        raise ValueError("gelu-sharded-k-rank footprint names a missing writer") from exc
    if sm_node.rank != 0:
        raise ValueError("gelu-sharded-k-rank SM writer rank is not zero")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("gelu-sharded-k-rank PM writers are not ordered ranks 0..K-1")
    writers = (sm_node, *pm_nodes)
    if any(node.params for node in writers):
        raise ValueError("gelu-sharded-k-rank writers require no parameters")
    if any(node.op != "FW_gelu" or len(node.ins) != 1 or len(node.outs) != 1 for node in writers):
        raise ValueError("gelu-sharded-k-rank writers must be unary singleton-output FW_gelu nodes")
    if (sm_node.ins[0] != pre.sm_tid
            or tuple(node.ins[0] for node in pm_nodes) != tuple(pre.pm_tids)
            or sm_node.outs[0] != post.sm_tid
            or tuple(node.outs[0] for node in pm_nodes) != tuple(post.pm_tids)):
        raise ValueError("gelu-sharded-k-rank writers disagree with exact ordered relation TIDs")

    sm_node_name = f"{segment_id}_sm_node"
    pm_node_names = [f"{segment_id}_pm_node_{rank}" for rank in range(k)]
    sm_nodes_name = f"{segment_id}_sm_nodes"
    pm_nodes_name = f"{segment_id}_pm_nodes"
    input_list = "[" + ", ".join(f"pmStore {tid}" for tid in pre.pm_tids) + "]"
    output_list = "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]"
    full_shape = _shape_text(list(post.full_shape))
    shard_shape = _shape_text(list(post.shard_shape))

    def writer(name, graph, store, node_names, position, node, node_name, final):
        prefix = ", ".join(node_names[:position])
        suffix = ", ".join(node_names[position + 1:])
        nodes = "smNodes" if final == "smFinal" else "pmNodes"
        nodes_def = sm_nodes_name if final == "smFinal" else pm_nodes_name
        return [
            f"    have {name} : {final} {node.outs[0]} = fw_gelu ({store} {node.ins[0]}) := by",
            f"      simpa [{final}, {nodes}, {nodes_def}] using",
            f"        (foldl_faithful_unary_middle_writer {graph} {store}",
            f"          [{prefix}] [{suffix}] {node_name} {node.ins[0]} {node.outs[0]} fw_gelu (by",
            "            intro t",
            "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "              (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "            simp [applyNodeDistributed, applyNodeRingAttn]",
            f"            exact applyNode_fw_gelu_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]})",
            "          (by native_decide) (by native_decide) (by native_decide) (by native_decide))",
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
        f"    have hin : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    change ShardedRel (smStore {pre.sm_tid}) {input_list} {pre.gather_dim} {full_shape} {shard_shape} at hin",
    ]
    lines += writer("hSmWriter", ir.sm_graph_ref, "smStore", (sm_node_name,), 0,
                    sm_node, sm_node_name, "smFinal")
    for rank, node in enumerate(pm_nodes):
        lines += writer(f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_node_names,
                        rank, node, pm_node_names[rank], "pmFinal")
    lines += [
        f"    have hcomm := {theorem} {post.gather_dim} {input_list}.length {input_list} {shard_shape}",
        "      (by simp) rfl",
        "      (by simp only [List.head?, Option.map, Option.getD]; exact hin.shard_shapes _ (by simp))",
        "      (by intro i hi; exact hin.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))",
        f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {post.sm_tid}) {output_list} {post.gather_dim} {full_shape} {shard_shape}",
        "      constructor",
        "      · rw [hSmWriter, hin.full_value, hcomm]",
        "        simp only [List.map, List.length_cons, List.length_nil]",
        "        rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
        "      · rw [hSmWriter, fw_gelu_shape]",
        "        exact hin.full_shape",
        "      · simp",
        "      · exact hin.gather_dim_lt",
        "      · intro shard hmem",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ]
    for rank in range(k):
        lines += [
            "        · subst shard",
            f"          rw [hPmWriter{rank}, fw_gelu_shape]",
            f"          exact hin.shard_shapes (pmStore {pre.pm_tids[rank]}) (by simp)",
        ]
    lines += [
        "      · exact hin.shape_contract",
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
