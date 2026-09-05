"""Atomic renderer for interleaved vocab/sequence embeddings plus AllReduce."""
from __future__ import annotations

from dataclasses import replace


def render_closed_mixed_initial_embedding_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value
        from .relation_compiler import (
            KRankVocabShardedEmbeddingProducerCertificate,
            KRankShardedIdsEmbeddingCertificate,
            KRankAllReduceReconstructionCertificate,
        )
        from .sharded_ids_embedding_renderer import (
            render_closed_k_rank_sharded_ids_embedding_segment,
        )
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value
        from relation_compiler import (
            KRankVocabShardedEmbeddingProducerCertificate,
            KRankShardedIdsEmbeddingCertificate,
            KRankAllReduceReconstructionCertificate,
        )
        from sharded_ids_embedding_renderer import (
            render_closed_k_rank_sharded_ids_embedding_segment,
        )

    chain = relation.dependent_chain_plan
    segment = next((x for x in chain.segments if x.segment_id == segment_id), None)
    if segment is None:
        raise ValueError("mixed initial embedding segment is missing")
    by_id = {x.transition_id: x for x in relation.transition_specs}
    transitions = tuple(by_id[x] for x in segment.transition_ids)
    expected = (
        "embedding-vocab-sharded-reduction-k-rank",
        "embedding-sharded-ids-k-rank",
        "allreduce-reconstruction-k-rank",
    )
    if tuple(x.rule_id for x in transitions) != expected:
        raise ValueError("mixed initial embedding family/order mismatch")
    vocab_t, sequence_t, allreduce_t = transitions

    def exact(cls, transition, facts):
        found = [x for x in relation.certificates if type(x) is cls
                 and x.rule_id == transition.rule_id
                 and x.lean_theorem == transition.lean_theorem
                 and facts(x) == (transition.pre_facts, transition.post_facts)]
        if len(found) != 1:
            raise ValueError("mixed initial embedding lacks one exact typed certificate")
        return found[0]

    vocab = exact(KRankVocabShardedEmbeddingProducerCertificate, vocab_t,
                  lambda x: ((x.weight_fact,), (x.output_fact,)))
    sequence = exact(KRankShardedIdsEmbeddingCertificate, sequence_t,
                     lambda x: ((), (x.ids_chunks_fact, x.output_fact)))
    allreduce = exact(KRankAllReduceReconstructionCertificate, allreduce_t,
                      lambda x: ((x.input_fact,), (x.output_fact,)))
    k = sequence.rank_count
    if k < 1 or vocab.rank_count != k or allreduce.rank_count != k:
        raise ValueError("mixed initial embedding dynamic K disagrees")

    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    vocab_pre = records[vocab_t.pre_facts[0]]
    vocab_post = records[vocab_t.post_facts[0]]
    sequence_ids_post = records[sequence.ids_chunks_fact]
    sequence_post = records[sequence.output_fact]
    joined_post = records[allreduce_t.post_facts[0]]
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    expected_fresh = {sequence_post.fact_id, joined_post.fact_id}
    if sequence_ids_post.fact_id in after.fact_ids:
        expected_fresh.add(sequence_ids_post.fact_id)
    if set(after.fact_ids) - set(before.fact_ids) != expected_fresh:
        raise ValueError("mixed initial embedding post-state facts disagree")

    # Reuse the checked sequence renderer's writer/IDs helpers over this exact
    # complete frame, but replace its synthetic post-state by sequence-only state.
    sequence_live = tuple(
        item.fact_id for item in (sequence_ids_post, sequence_post)
        if item.fact_id in after.fact_ids
    )
    fake_after = replace(after, fact_ids=tuple((*before.fact_ids, *sequence_live)))
    fake_segment = replace(segment, transition_ids=(sequence_t.transition_id,))
    fake_chain = replace(
        chain,
        segments=tuple(fake_segment if x.segment_id == segment_id else x for x in chain.segments),
        states=tuple(fake_after if x.state_id == after.state_id else x for x in chain.states),
    )
    fake_relation = replace(relation, dependent_chain_plan=fake_chain)
    sequence_source = render_closed_k_rank_sharded_ids_embedding_segment(
        ir, fake_relation, segment_id
    )
    marker = f"private theorem {segment_id}_sound"
    if marker not in sequence_source:
        raise ValueError("sequence helper renderer did not expose its helper boundary")
    prefix = sequence_source.split(marker, 1)[0].rstrip()

    sm_nodes = list(ir.sm_nodes[slice(*segment.sm_range)])
    pm_nodes = list(ir.pm_nodes[slice(*segment.pm_range)])
    sm_nodes_name = f"{segment_id}_smNodes"
    pm_nodes_name = f"{segment_id}_pmNodes"
    sm_final_name = f"{segment_id}_smFinal"
    pm_final_name = f"{segment_id}_pmFinal"
    chunk_tids_name = f"{segment_id}_chunkTids"
    rank_count_name = f"{segment_id}_rankCount"
    seq_ids_helper = f"{segment_id}_ids_relation"
    seq_sm_helper = f"{segment_id}_hSmEmbedding"
    seq_pm_helpers = [f"{segment_id}_hPmEmbedding{r}" for r in range(k)]

    vocab_sm = ir.sm_nodes[vocab_t.sm_node_indices[0]]
    vocab_pm = tuple(ir.pm_nodes[i] for i in vocab_t.pm_node_indices)
    allreduce_node = ir.pm_nodes[allreduce_t.pm_node_indices[0]]
    if tuple(node.rank for node in vocab_pm) != tuple(range(k)):
        raise ValueError("mixed initial vocab writers are not ordered ranks")
    if allreduce_node.op != "AllReducePrim" or tuple(allreduce_node.ins) != tuple(vocab_post.pm_tids):
        raise ValueError("mixed initial AllReduce signature mismatch")

    def embedding_apply(graph, node, offset=None):
        if offset is None:
            lemma = (f"applyNode_fw_embedding_out {graph} t {node.rank} "
                     f"{node.ins[0]} {node.ins[1]} {node.outs[0]}")
        else:
            lemma = (f"applyNode_fw_embedding_offset_out {graph} t {node.rank} {offset} "
                     f"{node.ins[0]} {node.ins[1]} {node.outs[0]}")
        return [
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
            "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
            "(hattn := by native_decide)]",
            "simp [applyNodeDistributed, applyNodeRingAttn]",
            f"exact {lemma}",
        ]

    lines = [prefix, ""]

    def add_writer(name, graph, store_name, final_name, nodes_name, nodes,
                   position, node, inputs, expression, apply_lines):
        final = f"({final_name} {store_name})"
        lines.extend([
            f"private theorem {name} ({store_name} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl",
            f"      (applyNodeDistributedFaithful {graph}) {store_name} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=store_name,
            final_store=final, final_equality="hfinal", nodes_name=nodes_name,
            nodes=nodes, position=position, output_tid=node.outs[0],
            input_tids=tuple(inputs), written_tids={t for n in nodes for t in n.outs},
            expression=expression, apply_lines=apply_lines,
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout", ""])

    vocab_sm_helper = f"{segment_id}_vocab_sm_writer"
    add_writer(vocab_sm_helper, ir.sm_graph_ref, "smStore", sm_final_name,
               sm_nodes_name, sm_nodes,
               vocab_t.sm_node_indices[0] - segment.sm_range[0], vocab_sm,
               vocab_sm.ins,
               f"fw_embedding ({{store}} {vocab.ids_tid}) ({{store}} {vocab_pre.sm_tid})",
               embedding_apply(ir.sm_graph_ref, vocab_sm))
    vocab_pm_helpers = []
    for rank, (index, node) in enumerate(zip(vocab_t.pm_node_indices, vocab_pm)):
        name = f"{segment_id}_vocab_pm_writer_{rank}"
        vocab_pm_helpers.append(name)
        offset = node.params[0]
        add_writer(name, ir.pm_graph_ref, "pmStore", pm_final_name,
                   pm_nodes_name, pm_nodes, index - segment.pm_range[0], node,
                   node.ins,
                   f"fw_embedding_offset {offset} ({{store}} {vocab.ids_tid}) ({{store}} {node.ins[1]})",
                   embedding_apply(ir.pm_graph_ref, node, offset))

    allreduce_helper = f"{segment_id}_allreduce_writer"
    contribution_expr = "[" + ", ".join(
        f"{{store}} {tid}" for tid in vocab_post.pm_tids
    ) + "]"
    add_writer(
        allreduce_helper, ir.pm_graph_ref, "pmStore", pm_final_name,
        pm_nodes_name, pm_nodes,
        allreduce_t.pm_node_indices[0] - segment.pm_range[0], allreduce_node,
        tuple(vocab_post.pm_tids),
        f"allReducePrim {k} 0 {contribution_expr}",
        [
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
            "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
            "(hattn := by native_decide)]",
            "unfold applyNodeDistributed",
            "rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"exact applyNode_allReducePrim_out {ir.pm_graph_ref} t 0 "
            f"[{', '.join(str(t) for t in vocab_post.pm_tids)}] {allreduce_node.outs[0]}",
            "native_decide", "native_decide",
        ],
    )

    shape = lambda xs: _shape_text(list(xs))
    vocab_weights = "[" + ", ".join(str(t) for t in vocab_pre.pm_tids) + "]"
    vocab_outputs = "[" + ", ".join(str(t) for t in vocab_post.pm_tids) + "]"
    seq_outputs = "[" + ", ".join(str(t) for t in sequence_post.pm_tids) + "]"

    # Sequence fact helper.
    lines += [
        f"private theorem {segment_id}_sequence_out (smStore pmStore : Store)",
        f"    (hIdsEq : ({sm_final_name} smStore) {sequence.ids_tid} = ({pm_final_name} pmStore) {sequence.ids_tid})",
        f"    (hIdsShape : (({pm_final_name} pmStore) {sequence.ids_tid}).shape = {shape(sequence.ids_full_shape)})",
        f"    (hWeightEq : ({sm_final_name} smStore) {sequence.weight_tid} = ({pm_final_name} pmStore) {sequence.weight_tid})",
        f"    (hWeightShape : (({pm_final_name} pmStore) {sequence.weight_tid}).shape = {shape(sequence.weight_shape)}) :",
        f"    {sequence_post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hIds := {seq_ids_helper} smStore pmStore hIdsEq hIdsShape",
        f"  have hSm := {seq_sm_helper} smStore",
    ]
    for rank, helper in enumerate(seq_pm_helpers):
        lines.append(f"  have hPm{rank} := {helper} pmStore")
    lines += [
        f"  have hLast : lastD (({pm_final_name} pmStore) {sequence.weight_tid}).shape = {sequence.weight_shape[-1]} := by rw [hWeightShape]; rfl",
        "  have h := ShardedRel.fw_embedding_shared_weight_dim1",
        f"    (idsShards := {chunk_tids_name}.map ({pm_final_name} pmStore))",
        f"    (b := {sequence.ids_shard_shape[0]}) (s := {sequence.ids_shard_shape[1]})",
        f"    (hidden := {sequence.weight_shape[-1]}) hIds.toShardedRel hWeightEq hLast",
        "    (by native_decide) (by native_decide) (by native_decide)",
        f"  unfold {sequence_post.fact_id} RelationFact.Holds",
        f"  change ShardedRel (({sm_final_name} smStore) {sequence_post.sm_tid})",
        f"    ({seq_outputs}.map ({pm_final_name} pmStore)) {sequence.shard_dim}",
        f"    {shape(sequence.output_full_shape)} {shape(sequence.output_shard_shape)}",
        "  rw [hSm]",
        f"  simp only [{chunk_tids_name}, List.map, List.length_cons, List.length_nil] at h ⊢",
        f"  rw [{', '.join('← hPm'+str(r) for r in range(k))}] at h",
        "  exact h", "",
    ]

    # Vocab reduction helper.
    lines += [
        f"private theorem {segment_id}_vocab_out (smStore pmStore : Store)",
        f"    (hWeight : {vocab_pre.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore))",
        f"    (hIdsEq : ({sm_final_name} smStore) {vocab.ids_tid} = ({pm_final_name} pmStore) {vocab.ids_tid})",
        f"    (hIdsShape : (({pm_final_name} pmStore) {vocab.ids_tid}).shape = {shape(vocab.ids_shape)}) :",
        f"    {vocab_post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  change ShardedRel (({sm_final_name} smStore) {vocab_pre.sm_tid})",
        f"    ({vocab_weights}.map ({pm_final_name} pmStore)) 0",
        f"    {shape(vocab.full_weight_shape)} {shape(vocab.shard_weight_shape)} at hWeight",
        f"  have hSm := {vocab_sm_helper} smStore",
    ]
    for rank, helper in enumerate(vocab_pm_helpers):
        lines.append(f"  have hPm{rank} := {helper} pmStore")
    lines += [
        f"  have hBase := {vocab.lean_theorem} (numParts := {k})",
        f"    (shard := {vocab.shard_rows}) (hidden := {vocab.hidden_size})",
        "    (hparts := by native_decide) (hshard := by native_decide) (hhid := by native_decide)",
        f"    (ids := ({pm_final_name} pmStore) {vocab.ids_tid})",
        f"    (Ws := {vocab_weights}.map ({pm_final_name} pmStore))",
        "    (hlen := by rfl)",
        f"    (hWs_head := by simp only [List.map, List.head?, Option.map, Option.getD]; exact hWeight.shard_shapes _ (by simp))",
        "    (hWs_shape := by",
        "      intro r hr",
        "      have cases : " + " ∨ ".join(f"r = {rank}" for rank in range(k)) + " := by omega",
        "      rcases cases with " + " | ".join(f"h{rank}" for rank in range(k)),
    ]
    for rank in range(k):
        lines.append(f"      · subst r; simpa [List.getD, List.map] using hWeight.shard_shapes (({pm_final_name} pmStore) {vocab_pre.pm_tids[rank]}) (by simp)")
    lines += [
        "    )",
        "  simp only [List.map, List.ofFn_succ, List.ofFn_zero, List.getD] at hBase",
        "  simp at hBase",
        "  have hValue :",
        f"      ({sm_final_name} smStore) {vocab_post.sm_tid} =",
        f"        allReducePrim ({vocab_outputs}.map ({pm_final_name} pmStore)).length 0",
        f"          ({vocab_outputs}.map ({pm_final_name} pmStore)) := by",
        "    rw [hSm, hIdsEq, hWeight.full_value]",
        "    simp only [List.map, List.length_cons, List.length_nil]",
        "    rw [hBase]",
        f"    rw [{', '.join('← hPm'+str(r) for r in range(k))}]",
        f"  unfold {vocab_post.fact_id} RelationFact.Holds",
        f"  change ReductionRel (({sm_final_name} smStore) {vocab_post.sm_tid})",
        f"    ({vocab_outputs}.map ({pm_final_name} pmStore)) {shape(vocab_post.full_shape)}",
        "  refine {", "    full_value := hValue", "    full_shape := ?_",
        "    contributions_nonempty := by simp", "    contribution_shapes := ?_",
        "    reduced_shape := ?_", "  }",
        "  · rw [hSm, fw_embedding_shape, hIdsEq, hIdsShape, hWeight.full_shape]",
        "    rfl",
        "  · intro contribution hmem",
        f"    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "    rcases hmem with " + " | ".join("rfl" for _ in range(k)),
    ]
    for rank in range(k):
        lines += [
            f"    · rw [hPm{rank}, fw_embedding_offset_shape, hIdsShape,",
            f"          hWeight.shard_shapes (({pm_final_name} pmStore) {vocab_pre.pm_tids[rank]}) (by simp)]",
            "      rfl",
        ]
    lines += [
        "  · rw [← hValue]",
        "    rw [hSm, fw_embedding_shape, hIdsEq, hIdsShape, hWeight.full_shape]",
        "    rfl", "",
    ]

    final_fresh = tuple(
        item for item in (sequence_ids_post, sequence_post, joined_post)
        if item.fact_id in after.fact_ids
    )
    final_fact_list = "[" + ", ".join(item.fact_id for item in final_fresh) + "]"
    final_proofs = tuple(
        "hIdsChunks" if item is sequence_ids_post
        else "hSequence" if item is sequence_post
        else "hJoined"
        for item in final_fresh
    )

    # Joined AllReduce helper.
    lines += [
        f"private theorem {segment_id}_joined_out (smStore pmStore : Store)",
        f"    (hReduction : {vocab_post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore)) :",
        f"    {joined_post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hWriter := {allreduce_helper} pmStore",
        f"  unfold {vocab_post.fact_id} RelationFact.Holds at hReduction",
        f"  unfold {joined_post.fact_id} RelationFact.Holds",
        "  refine ⟨?_, hReduction.full_shape, ?_⟩",
        "  · rw [hWriter]",
        "    simpa only [List.map, List.length_cons, List.length_nil] using hReduction.full_value",
        "  · rw [hWriter]",
        "    exact hReduction.reduced_shape", "",
    ]

    # Final small sound theorem.
    lines += [
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    unfold {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "    · native_decide", "    · native_decide", "    · native_decide", "    · native_decide",
    ]
    # Exact authorities at final stores.
    def auth(kind, pred):
        found = [x for x in chain.authority_facts if x.kind == kind and pred(x)]
        if len(found) != 1:
            raise ValueError("mixed initial embedding exact authority missing")
        return found[0]
    seq_eq = auth("tensor_eq", lambda x: (x.left_side,x.left_tid,x.right_side,x.right_tid)==("sm",sequence.ids_tid,"pm",sequence.ids_tid))
    seq_shape = auth("tensor_shape", lambda x: x.side=="pm" and x.tid==sequence.ids_tid)
    seq_weq = auth("tensor_eq", lambda x: (x.left_side,x.left_tid,x.right_side,x.right_tid)==("sm",sequence.weight_tid,"pm",sequence.weight_tid))
    seq_wshape = auth("tensor_shape", lambda x: x.side=="pm" and x.tid==sequence.weight_tid)
    vocab_eq = auth("tensor_eq", lambda x: (x.left_side,x.left_tid,x.right_side,x.right_tid)==("sm",vocab.ids_tid,"pm",vocab.ids_tid))
    vocab_shape = auth("tensor_shape", lambda x: x.side=="pm" and x.tid==vocab.ids_tid)
    for name, fact in (("hSeqEq",seq_eq),("hSeqShape",seq_shape),("hSeqWEq",seq_weq),
                       ("hSeqWShape",seq_wshape),("hVocabEq",vocab_eq),("hVocabShape",vocab_shape)):
        lines += [f"  have {name} := hframe {fact.fact_id} (by native_decide)",
                  f"  unfold {fact.fact_id} RelationFact.Holds at {name}"]
    lines += [
        f"  have hIdsChunksRaw := {seq_ids_helper} smStore pmStore hSeqEq hSeqShape",
        f"  have hIdsChunks : {sequence_ids_post.fact_id}.Holds",
        f"      ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    unfold {sequence_ids_post.fact_id} RelationFact.Holds",
        "    simpa only [",
        f"      {chunk_tids_name}, List.map, List.length_cons, List.length_nil] using hIdsChunksRaw",
        f"  have hSequence := {segment_id}_sequence_out smStore pmStore hSeqEq hSeqShape hSeqWEq hSeqWShape",
        f"  have hWeight := hframe {vocab_pre.fact_id} (by native_decide)",
        f"  have hVocab := {segment_id}_vocab_out smStore pmStore hWeight hVocabEq hVocabShape",
        f"  have hJoined := {segment_id}_joined_out smStore pmStore hVocab",
        "  intro fact hfact",
        f"  have covered : fact ∈ {final_fact_list} ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ {final_fact_list} ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
        "  rcases covered with fresh | old",
        "  · rcases fresh with " + " | ".join("rfl" for _ in final_fresh),
        *(f"    · exact {proof}" for proof in final_proofs),
        "  · exact hframe fact old", "",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    simpa only [{sm_final_name}, {pm_final_name}] using {segment_id}_sound smStore pmStore hstate",
        "",
    ]
    return "\n".join(lines)
