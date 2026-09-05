"""Closed sparse-frame renderer for dynamic-K sharded-ID embedding."""
from __future__ import annotations


def render_closed_k_rank_sharded_ids_embedding_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _shape_text, _render_mixed_final_value,
            _select_exact_typed_certificate,
        )
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (
            _node_text, _shape_text, _render_mixed_final_value,
            _select_exact_typed_certificate,
        )
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("embedding-sharded-ids-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    found = [] if chain is None else [
        item for item in chain.segments if item.segment_id == segment_id
    ]
    if chain is None or not chain.complete or len(found) != 1:
        raise ValueError(f"{rule} requires one complete closed segment")
    segment = found[0]
    if len(segment.transition_ids) != 1:
        raise ValueError(f"{rule} requires one atomic transition")
    transition_matches = [
        item for item in relation.transition_specs
        if item.transition_id == segment.transition_ids[0]
    ]
    if len(transition_matches) != 1:
        raise ValueError(f"{rule} transition authority is missing or duplicated")
    transition = transition_matches[0]
    if transition.pre_facts != () or len(transition.post_facts) != 2:
        raise ValueError(f"{rule} requires zero relation pre-facts and two post-facts")
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, theorem,
        spec.certificate_type,
        lambda item: ((), (item.ids_chunks_fact, item.output_fact)),
    )
    records = {item.source: item for item in chain.relation_facts}
    states = {item.state_id: item for item in chain.states}
    try:
        ids_post = records[certificate.ids_chunks_fact]
        post = records[certificate.output_fact]
        before = states[segment.pre_state_id]
        after = states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError(f"{rule} fact/state framing is unresolved") from exc
    if post.fact_id not in after.fact_ids:
        raise ValueError(f"{rule} post fact is not live")
    fresh_records = tuple(
        item for item in (ids_post, post) if item.fact_id in after.fact_ids
    )
    if not set(after.fact_ids) <= ({item.fact_id for item in fresh_records} | set(before.fact_ids)):
        raise ValueError(f"{rule} post-state introduces an unproved fact")

    k = certificate.rank_count
    if (k <= 0 or certificate.shard_dim != 1
            or len(certificate.ids_full_shape) != 2
            or len(certificate.ids_shard_shape) != 2
            or len(certificate.weight_shape) != 2):
        raise ValueError(f"{rule} requires rank-2 IDs sharded on dim 1")
    b, full_seq = certificate.ids_full_shape
    shard_b, shard_seq = certificate.ids_shard_shape
    hidden = certificate.weight_shape[-1]
    if (b <= 0 or shard_seq <= 0 or hidden <= 0 or shard_b != b
            or full_seq != shard_seq * k
            or certificate.output_full_shape != (b, full_seq, hidden)
            or certificate.output_shard_shape != (b, shard_seq, hidden)
            or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k):
        raise ValueError(f"{rule} shape/rank authority is outside theorem domain")
    if (post.kind != "sharded" or post.gather_dim != 1
            or post.full_shape != certificate.output_full_shape
            or post.shard_shape != certificate.output_shard_shape
            or len(post.pm_tids) != k):
        raise ValueError(f"{rule} output relation metadata disagrees")
    if (ids_post.kind != "chunked" or ids_post.gather_dim != 1
            or ids_post.full_shape != certificate.ids_full_shape
            or ids_post.shard_shape != certificate.ids_shard_shape
            or len(ids_post.pm_tids) != k):
        raise ValueError(f"{rule} IDs-chunk relation metadata disagrees")

    sm_all = tuple(range(*segment.sm_range))
    pm_all = tuple(range(*segment.pm_range))
    sm_writer_indices = tuple(transition.sm_node_indices)
    pm_writer_indices = tuple(transition.pm_node_indices)
    if (len(sm_writer_indices) != 1 or len(pm_writer_indices) != 2 * k
            or len(set(pm_writer_indices)) != len(pm_writer_indices)
            or not set(sm_writer_indices) <= set(sm_all)
            or not set(pm_writer_indices) <= set(pm_all)):
        raise ValueError(f"{rule} lacks an exact sparse writer/frame partition")
    sm_index = sm_writer_indices[0]
    chunk_indices = pm_writer_indices[:k]
    embedding_indices = pm_writer_indices[k:]
    if certificate.sm_embedding_step != f"sm:{sm_index}:0":
        raise ValueError(f"{rule} SM writer identity mismatch")
    if certificate.pm_chunk_steps != tuple(f"pm:{index}:0" for index in chunk_indices):
        raise ValueError(f"{rule} chunk writer identity mismatch")
    if certificate.pm_embedding_steps != tuple(f"pm:{index}:0" for index in embedding_indices):
        raise ValueError(f"{rule} embedding writer identity mismatch")

    sm_node = ir.sm_nodes[sm_index]
    chunk_nodes = tuple(ir.pm_nodes[index] for index in chunk_indices)
    embedding_nodes = tuple(ir.pm_nodes[index] for index in embedding_indices)
    if (sm_node.rank != 0 or sm_node.op != "FW_embedding" or sm_node.params
            or tuple(sm_node.ins) != (certificate.ids_tid, certificate.weight_tid)
            or len(sm_node.outs) != 1 or sm_node.outs[0] != post.sm_tid):
        raise ValueError(f"{rule} SM embedding signature mismatch")
    for rank, (chunk, embedding) in enumerate(zip(chunk_nodes, embedding_nodes)):
        if (chunk.rank != rank or chunk.op != "ChunkPrim"
                or tuple(chunk.params or ()) != (1,)
                or tuple(chunk.ins) != (certificate.ids_tid,) or len(chunk.outs) != 1):
            raise ValueError(f"{rule} chunk signature mismatch")
        if (embedding.rank != rank or embedding.op != "FW_embedding" or embedding.params
                or tuple(embedding.ins) != (chunk.outs[0], certificate.weight_tid)
                or len(embedding.outs) != 1 or embedding.outs[0] != post.pm_tids[rank]):
            raise ValueError(f"{rule} PM embedding signature mismatch")

    sm_nodes = list(ir.sm_nodes[slice(*segment.sm_range)])
    pm_nodes = list(ir.pm_nodes[slice(*segment.pm_range)])
    sm_position = sm_index - segment.sm_range[0]
    chunk_positions = tuple(index - segment.pm_range[0] for index in chunk_indices)
    embedding_positions = tuple(index - segment.pm_range[0] for index in embedding_indices)
    for position, node in enumerate(sm_nodes):
        if position != sm_position and set(node.outs) & {
            certificate.ids_tid, certificate.weight_tid, post.sm_tid
        }:
            raise ValueError(f"{rule} SM frame overwrites live authority")
    live_pm = {certificate.ids_tid, certificate.weight_tid, *post.pm_tids,
               *(node.outs[0] for node in chunk_nodes)}
    semantic_pm = set(chunk_positions) | set(embedding_positions)
    for position, node in enumerate(pm_nodes):
        if position not in semantic_pm and set(node.outs) & live_pm:
            raise ValueError(f"{rule} PM frame overwrites live authority")

    def authority(kind, predicate):
        matches = [item for item in chain.authority_facts
                   if item.kind == kind and predicate(item)]
        if len(matches) != 1:
            raise ValueError(f"{rule} lacks one exact {kind} authority")
        if matches[0].fact_id not in before.fact_ids:
            raise ValueError(f"{rule} authority is not live in pre-state")
        return matches[0]

    ids_eq = authority("tensor_eq", lambda item:
        (item.left_side, item.left_tid, item.right_side, item.right_tid)
        == ("sm", certificate.ids_tid, "pm", certificate.ids_tid))
    ids_shape = authority("tensor_shape", lambda item:
        item.side == "pm" and item.tid == certificate.ids_tid
        and tuple(item.shape) == certificate.ids_full_shape)
    weight_eq = authority("tensor_eq", lambda item:
        (item.left_side, item.left_tid, item.right_side, item.right_tid)
        == ("sm", certificate.weight_tid, "pm", certificate.weight_tid))
    weight_shape = authority("tensor_shape", lambda item:
        item.side == "pm" and item.tid == certificate.weight_tid
        and tuple(item.shape) == certificate.weight_shape)

    sm_nodes_name = f"{segment_id}_smNodes"
    pm_nodes_name = f"{segment_id}_pmNodes"
    sm_final_name = f"{segment_id}_smFinal"
    pm_final_name = f"{segment_id}_pmFinal"
    chunk_tids_name = f"{segment_id}_chunkTids"
    output_tids_name = f"{segment_id}_outputTids"
    rank_count_name = f"{segment_id}_rankCount"
    chunk_tids = tuple(node.outs[0] for node in chunk_nodes)
    output_tids = tuple(node.outs[0] for node in embedding_nodes)
    chunk_tid_text = ", ".join(str(tid) for tid in chunk_tids)
    output_tid_text = ", ".join(str(tid) for tid in output_tids)
    sm_written = {tid for node in sm_nodes for tid in node.outs}
    pm_written = {tid for node in pm_nodes for tid in node.outs}
    full_shape = _shape_text(list(certificate.ids_full_shape))
    shard_shape = _shape_text(list(certificate.ids_shard_shape))
    output_full = _shape_text(list(certificate.output_full_shape))
    output_shard = _shape_text(list(certificate.output_shard_shape))

    def embedding_apply(graph, node):
        return [
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
            "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
            "(hattn := by native_decide)]",
            "simp [applyNodeDistributed, applyNodeRingAttn]",
            f"exact applyNode_fw_embedding_out {graph} t {node.rank} "
            f"{node.ins[0]} {node.ins[1]} {node.outs[0]}",
        ]

    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_nodes)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_nodes)}]",
        f"private def {chunk_tids_name} : List Tid := [{chunk_tid_text}]",
        f"private def {output_tids_name} : List Tid := [{output_tid_text}]",
        f"private def {rank_count_name} : Nat := {chunk_tids_name}.length",
        f"@[irreducible] private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"@[irreducible] private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store", "",
    ]

    def add_writer_theorem(name, graph, store_name, final_name, nodes_name,
                           nodes, position, node, input_tids, expression, apply_lines,
                           needs_rank=False):
        theorem_name = f"{segment_id}_{name}"
        final_store = f"({final_name} {store_name})"
        conclusion = expression.format(store=final_store)
        lines.extend([
            f"private theorem {theorem_name} ({store_name} : Store) :",
            f"    {final_store} {node.outs[0]} = {conclusion} := by",
            f"  have hfinal : {final_store} = {nodes_name}.foldl",
            f"      (applyNodeDistributedFaithful {graph}) {store_name} := by",
            f"    unfold {final_name}",
            "    rfl",
        ])
        if needs_rank:
            lines.append(
                f"  have hRankCount : {rank_count_name} = {ir.pm_graph_ref}.numRanks := by rfl"
            )
        helper_lines = _render_mixed_final_value(
            name=name, graph=graph, initial_store=store_name,
            final_store=final_store, final_equality="hfinal", nodes_name=nodes_name,
            nodes=nodes, position=position, output_tid=node.outs[0],
            input_tids=input_tids,
            written_tids={tid for item in nodes for tid in item.outs},
            expression=expression, apply_lines=apply_lines,
        )
        lines.extend(line[2:] if line.startswith("  ") else line for line in helper_lines)
        lines.extend([f"  exact {name}", ""])
        return theorem_name

    sm_helper = add_writer_theorem(
        "hSmEmbedding", ir.sm_graph_ref, "smStore", sm_final_name,
        sm_nodes_name, sm_nodes, sm_position, sm_node,
        (certificate.ids_tid, certificate.weight_tid),
        (f"fw_embedding ({{store}} {certificate.ids_tid}) "
         f"({{store}} {certificate.weight_tid})"),
        embedding_apply(ir.sm_graph_ref, sm_node),
    )
    chunk_names = []
    chunk_helpers = []
    for rank, (position, node) in enumerate(zip(chunk_positions, chunk_nodes)):
        name = f"hChunk{rank}"
        chunk_names.append(name)
        chunk_helpers.append(add_writer_theorem(
            name, ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_nodes, position, node, (certificate.ids_tid,),
            (f"chunkPrimDimN 1 {rank_count_name} {rank} "
             f"({{store}} {certificate.ids_tid})"),
            [
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]",
                "rw [hRankCount]",
                f"simpa using applyNode_chunkPrimDimN_out {ir.pm_graph_ref} t {rank} "
                f"{certificate.ids_tid} {node.outs[0]} 1",
            ], needs_rank=True,
        ))
    embedding_names = []
    embedding_helpers = []
    for rank, (position, node) in enumerate(zip(embedding_positions, embedding_nodes)):
        name = f"hPmEmbedding{rank}"
        embedding_names.append(name)
        embedding_helpers.append(add_writer_theorem(
            name, ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_nodes, position, node,
            (node.ins[0], certificate.weight_tid),
            (f"fw_embedding ({{store}} {node.ins[0]}) "
             f"({{store}} {certificate.weight_tid})"),
            embedding_apply(ir.pm_graph_ref, node),
        ))

    ids_helper = f"{segment_id}_ids_relation"
    global_pm = f"({pm_final_name} pmStore)"
    explicit_chunks = "[" + ", ".join(
        f"{global_pm} {tid}" for tid in chunk_tids
    ) + "]"
    explicit_chunk_exprs = "[" + ", ".join(
        f"chunkPrimDimN 1 {rank_count_name} {rank} ({global_pm} {certificate.ids_tid})"
        for rank in range(k)
    ) + "]"
    lines += [
        f"private theorem {ids_helper} (smStore pmStore : Store)",
        f"    (hIdsEq : ({sm_final_name} smStore) {certificate.ids_tid} =",
        f"      ({pm_final_name} pmStore) {certificate.ids_tid})",
        f"    (hIdsShape : (({pm_final_name} pmStore) {certificate.ids_tid}).shape = {full_shape}) :",
        f"    ChunkedRel (({sm_final_name} smStore) {certificate.ids_tid})",
        f"      ({chunk_tids_name}.map ({pm_final_name} pmStore)) 1",
        f"      [{b}, {shard_seq} * {chunk_tids_name}.length] {shard_shape} := by",
    ]
    for name, helper in zip(chunk_names, chunk_helpers):
        lines.append(f"  have {name} := {helper} pmStore")
    lines += [
        "  have hOrderedChunks :",
        f"      {chunk_tids_name}.map ({pm_final_name} pmStore) =",
        f"        List.ofFn (fun r : Fin {rank_count_name} =>",
        f"          chunkPrimDimN 1 {rank_count_name} r.1 ({global_pm} {certificate.ids_tid})) := by",
        f"    change {explicit_chunks} = {explicit_chunk_exprs}",
        f"    rw [{', '.join(chunk_names)}]",
        "  refine {", "    full_value := ?_", "    full_shape := ?_",
        "    shards_nonempty := ?_", "    gather_dim_lt := ?_",
        "    shard_shapes := ?_", "    shape_contract := ?_",
        "    chunk_values := ?_", "  }",
        "  · rw [hIdsEq, hOrderedChunks]",
        "    simp only [List.length_ofFn]",
        "    symm",
        f"    exact allGatherPrimDimN_chunks_ofFn 1 {rank_count_name}",
        f"      ({global_pm} {certificate.ids_tid})",
        f"      (by simp [{rank_count_name}, {chunk_tids_name}])",
        "      (by rw [hIdsShape]; native_decide)",
        f"      (by rw [hIdsShape]; simp [{rank_count_name}, {chunk_tids_name}])",
        "  · rw [hIdsEq, hIdsShape]",
        f"    simp [{chunk_tids_name}]",
        f"  · simp [{chunk_tids_name}]",
        "  · native_decide",
        "  · intro shard hmem",
        f"    simp only [{chunk_tids_name}, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "    rcases hmem with " + " | ".join("rfl" for _ in range(k)),
    ]
    for rank, name in enumerate(chunk_names):
        lines += [
            f"    · rw [{name}, chunkPrimDimN_shape 1 {rank_count_name} {rank}",
            f"          ({global_pm} {certificate.ids_tid}) {full_shape} hIdsShape",
            f"          (by simp [{rank_count_name}, {chunk_tids_name}])]",
            "      native_decide",
        ]
    lines += [
        f"  · simp [{chunk_tids_name}, List.set, List.getD]",
        "  · intro r hr",
        f"    simp only [{chunk_tids_name}, List.map, List.length_cons, List.length_nil] at hr",
        "    have cases : " + " ∨ ".join(f"r = {rank}" for rank in range(k)) + " := by omega",
        "    rcases cases with " + " | ".join(f"h{rank}" for rank in range(k)),
    ]
    for rank, name in enumerate(chunk_names):
        lines += [
            f"    · subst r",
            f"      simp only [{chunk_tids_name}, List.map, List.length_cons, List.length_nil]",
            "      rw [hIdsEq]",
            f"      simpa [{rank_count_name}, {chunk_tids_name}, List.getD] using {name}",
        ]
    lines.append("")

    fresh_fact_ids = tuple(item.fact_id for item in fresh_records)
    fresh_proofs = tuple(
        "hIdsOut" if item is ids_post else "hout" for item in fresh_records
    )
    fresh_list = "[" + ", ".join(fresh_fact_ids) + "]"

    lines += [
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smNodes : List NodeDecl := {sm_nodes_name}",
        f"    let pmNodes : List NodeDecl := {pm_nodes_name}",
        f"    let chunkTids : List Tid := {chunk_tids_name}",
        f"    let outputTids : List Tid := {output_tids_name}",
        f"    let rankCount := {rank_count_name}",
        f"    let smFinal := {sm_final_name} smStore",
        f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide",
        "      · simp only [smNodes]", "        native_decide",
        "      · simp only [pmNodes]", "        native_decide",
        f"    have hIdsEq : smFinal {certificate.ids_tid} = pmFinal {certificate.ids_tid} := by",
        f"      simpa [{ids_eq.fact_id}, RelationFact.Holds, StoreSide.read] using",
        f"        (hframe {ids_eq.fact_id} (by native_decide))",
        f"    have hIdsShape : (pmFinal {certificate.ids_tid}).shape = {_shape_text(list(certificate.ids_full_shape))} := by",
        f"      simpa [{ids_shape.fact_id}, RelationFact.Holds, StoreSide.read] using",
        f"        (hframe {ids_shape.fact_id} (by native_decide))",
        f"    have hWeightEq : smFinal {certificate.weight_tid} = pmFinal {certificate.weight_tid} := by",
        f"      simpa [{weight_eq.fact_id}, RelationFact.Holds, StoreSide.read] using",
        f"        (hframe {weight_eq.fact_id} (by native_decide))",
        f"    have hWeightShape : (pmFinal {certificate.weight_tid}).shape = {_shape_text(list(certificate.weight_shape))} := by",
        f"      simpa [{weight_shape.fact_id}, RelationFact.Holds, StoreSide.read] using",
        f"        (hframe {weight_shape.fact_id} (by native_decide))",
        "    let idsShards := chunkTids.map pmFinal",
        "    have hIds :",
        f"        ChunkedRel (smFinal {certificate.ids_tid}) idsShards 1",
        f"          [{b}, {shard_seq} * idsShards.length] {shard_shape} := by",
        f"      exact {ids_helper} smStore pmStore hIdsEq hIdsShape",
        f"    have hIdsOut : {ids_post.fact_id}.Holds smFinal pmFinal := by",
        f"      unfold {ids_post.fact_id} RelationFact.Holds",
        "      simpa only [idsShards, chunkTids,",
        f"        {chunk_tids_name}, List.map, List.length_cons, List.length_nil] using hIds",
        f"    have hSmEmbedding : smFinal {sm_node.outs[0]} =",
        f"        fw_embedding (smFinal {certificate.ids_tid}) (smFinal {certificate.weight_tid}) := by",
        f"      exact {sm_helper} smStore",
    ]
    for name, helper, node in zip(embedding_names, embedding_helpers, embedding_nodes):
        lines += [
            f"    have {name} : pmFinal {node.outs[0]} =",
            f"        fw_embedding (pmFinal {node.ins[0]}) (pmFinal {certificate.weight_tid}) := by",
            f"      exact {helper} pmStore",
        ]
    lines += [
        "    have hWeightLast :",
        f"        lastD (pmFinal {certificate.weight_tid}).shape = {hidden} := by",
        "      rw [hWeightShape]", "      rfl",
        "    have hEmbedding :=",
        "      ShardedRel.fw_embedding_shared_weight_dim1",
        "        (idsShards := idsShards)",
        f"        (b := {b}) (s := {shard_seq}) (hidden := {hidden})",
        "        hIds.toShardedRel hWeightEq hWeightLast",
        "        (by native_decide) (by native_decide) (by native_decide)",
        f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {post.sm_tid}) (outputTids.map pmFinal) 1",
        f"        {output_full} {output_shard}",
        "      rw [hSmEmbedding]",
        "      simp only [idsShards, chunkTids, outputTids,",
        f"        {chunk_tids_name}, {output_tids_name}, List.map,",
        "        List.length_cons, List.length_nil] at hEmbedding ⊢",
        f"      rw [{', '.join('← ' + name for name in embedding_names)}] at hEmbedding",
        "      exact hEmbedding",
        "    intro fact hfact",
        f"    have covered : fact ∈ {fresh_list} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {fresh_list} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with " + " | ".join("rfl" for _ in fresh_fact_ids),
        *(f"      · exact {proof}" for proof in fresh_proofs),
        "    · exact hframe fact old", "",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}",
        f"  pmNodes := {pm_nodes_name}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{sm_final_name}, {pm_final_name}] using",
        f"      {segment_id}_sound smStore pmStore hstate", "",
    ]
    return "\n".join(lines)
