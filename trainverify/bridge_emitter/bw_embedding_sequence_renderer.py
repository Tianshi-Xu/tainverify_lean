"""Sparse full-frame renderer for sequence-sharded BW_embedding reduction."""
from __future__ import annotations


def render_closed_k_rank_bw_embedding_sequence_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _render_mixed_final_value,
            _select_exact_typed_certificate, _shape_text,
        )
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value,
            _select_exact_typed_certificate, _shape_text,
        )
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("bw-embedding-sequence-reduction-k-rank")
    vocab_spec = get_closed_rule_spec("bw-embedding-vocab-sharded-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) not in (1, 2):
        raise ValueError("sequence BW_embedding requires one transition and optional vocab peer")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    try:
        transitions = tuple(transition_map[item] for item in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("sequence BW_embedding transition framing is unresolved") from exc
    if len({item.transition_id for item in transitions}) != len(transitions):
        raise ValueError("sequence BW_embedding transition framing is duplicated")
    permitted_rules = {rule, vocab_spec.rule_id}
    if (any(item.rule_id not in permitted_rules for item in transitions)
            or sum(item.rule_id == rule for item in transitions) != 1
            or sum(item.rule_id == vocab_spec.rule_id
                   for item in transitions) > 1):
        raise ValueError("sequence BW_embedding atomic family mismatch")
    transition = next(item for item in transitions if item.rule_id == rule)
    vocab_transition = next((item for item in transitions
                             if item.rule_id == vocab_spec.rule_id), None)
    if transition is None or transition.rule_id != rule or transition.lean_theorem != theorem:
        raise ValueError("sequence BW_embedding typed family mismatch")
    cert = _select_exact_typed_certificate(
        relation, transition, rule, theorem,
        spec.certificate_type,
        lambda item: (
            tuple(sorted((item.gradient_fact, item.ids_chunks_fact, item.weight_fact))),
            (item.output_fact,),
        ),
    )
    vocab_cert=None if vocab_transition is None else _select_exact_typed_certificate(
        relation,vocab_transition,vocab_spec.rule_id,
        vocab_spec.lean_theorems[0],
        vocab_spec.certificate_type,
        lambda c:(tuple(sorted((c.gradient_fact,c.ids_fact,c.weight_fact))),(c.output_fact,)))
    records = {item.source: item for item in chain.relation_facts}
    states = {item.state_id: item for item in chain.states}
    try:
        gradient = records[cert.gradient_fact]
        ids = records[cert.ids_chunks_fact]
        weight = records[cert.weight_fact]
        output = records[cert.output_fact]
        vg=records[vocab_cert.gradient_fact] if vocab_cert else None
        vi=records[vocab_cert.ids_fact] if vocab_cert else None
        vw=records[vocab_cert.weight_fact] if vocab_cert else None
        vo=records[vocab_cert.output_fact] if vocab_cert else None
        before = states[segment.pre_state_id]
        after = states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("sequence BW_embedding fact/state framing is unresolved") from exc
    required={gradient.fact_id,ids.fact_id,weight.fact_id}|({vg.fact_id,vi.fact_id,vw.fact_id} if vocab_cert else set())
    fresh={output.fact_id}|({vo.fact_id} if vocab_cert else set())
    if not required <= set(before.fact_ids):
        raise ValueError("sequence BW_embedding inputs are not live")
    if not fresh <= set(after.fact_ids) or not set(after.fact_ids) <= (
        fresh | set(before.fact_ids)
    ):
        raise ValueError("sequence BW_embedding post-state mismatch")

    k = cert.rank_count
    b, s, hidden, vocab = cert.batch_size, cert.shard_sequence, cert.hidden_size, cert.vocab_size
    if (min(k, b, s, hidden, vocab) <= 0 or k != ir.pm_num_ranks or cert.shard_dim != 1
            or gradient.kind != "sharded" or gradient.gather_dim != 1
            or gradient.full_shape != (b, s * k, hidden)
            or gradient.shard_shape != (b, s, hidden) or len(gradient.pm_tids) != k
            or ids.kind != "chunked" or ids.gather_dim != 1
            or ids.full_shape != (b, s * k) or ids.shard_shape != (b, s)
            or len(ids.pm_tids) != k
            or weight.kind != "sharded" or weight.gather_dim != 0 or len(weight.pm_tids) != 1
            or weight.full_shape != (vocab, hidden) or weight.shard_shape != (vocab, hidden)
            or output.kind != "reduction" or len(output.pm_tids) != k
            or output.full_shape != (vocab, hidden) or output.shard_shape != (vocab, hidden)):
        raise ValueError("sequence BW_embedding relation metadata mismatch")
    if vocab_cert and (vocab_cert.rank_count != k or vocab_cert.gather_dim != 0
            or vocab_cert.shard_rows <= 0 or vocab_cert.hidden <= 0
            or tuple(vocab_cert.full_shape) != (vocab_cert.shard_rows * k,
                                                vocab_cert.hidden)
            or tuple(vocab_cert.shard_shape) != (vocab_cert.shard_rows,
                                                 vocab_cert.hidden)
            or vg.kind != "joined" or vg.joined_pm_tid is None
            or vi.kind != "sharded" or vi.gather_dim != 0 or len(vi.pm_tids) != 1
            or vw.kind != "sharded" or vw.gather_dim != 0 or len(vw.pm_tids) != k
            or vo.kind != "sharded" or vo.gather_dim != 0 or len(vo.pm_tids) != k
            or vw.full_shape != tuple(vocab_cert.full_shape)
            or vw.shard_shape != tuple(vocab_cert.shard_shape)
            or vw.full_shape != vo.full_shape or vw.shard_shape != vo.shard_shape):
        raise ValueError("vocab BW_embedding relation metadata mismatch")
    if (len(transition.sm_node_indices) != 1
            or len(transition.pm_node_indices) != k):
        raise ValueError("sequence BW_embedding writer cardinality mismatch")

    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    sm_indices = tuple(transition.sm_node_indices)
    pm_indices = tuple(transition.pm_node_indices)
    if (not set(sm_indices) <= set(range(sm_start, sm_end))
            or not set(pm_indices) <= set(range(pm_start, pm_end))
            or len(set(pm_indices)) != k):
        raise ValueError("sequence BW_embedding writer/frame partition mismatch")
    sm_node = ir.sm_nodes[sm_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in pm_indices)
    if (cert.sm_step_id != f"sm:{sm_indices[0]}:0"
            or cert.pm_step_ids != tuple(f"pm:{index}:0" for index in pm_indices)):
        raise ValueError("sequence BW_embedding certificate writer footprint mismatch")
    if (sm_node.rank != 0 or sm_node.op != "BW_embedding" or sm_node.params
            or tuple(sm_node.ins) != (gradient.sm_tid, ids.sm_tid, weight.sm_tid)
            or sm_node.outs != [output.sm_tid]):
        raise ValueError("sequence BW_embedding SM writer mismatch")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("sequence BW_embedding PM writers are not rank ordered")
    for rank, node in enumerate(pm_nodes):
        if (node.op != "BW_embedding" or node.params
                or tuple(node.ins) != (
                    gradient.pm_tids[rank], ids.pm_tids[rank], weight.pm_tids[0]
                ) or node.outs != [output.pm_tids[rank]]):
            raise ValueError("sequence BW_embedding PM writer mismatch")
    vocab_sm_index = None
    vocab_pm_indices = ()
    vocab_sm_node = None
    vocab_pm_nodes = ()
    if vocab_cert:
        if (len(vocab_transition.sm_node_indices) != 1
                or len(vocab_transition.pm_node_indices) != k):
            raise ValueError("vocab BW_embedding writer cardinality mismatch")
        vocab_sm_index = vocab_transition.sm_node_indices[0]
        vocab_pm_indices = tuple(vocab_transition.pm_node_indices)
        if (len(set(vocab_pm_indices)) != k
                or vocab_sm_index not in range(sm_start, sm_end)
                or not set(vocab_pm_indices) <= set(range(pm_start, pm_end))):
            raise ValueError("vocab BW_embedding writer/frame partition mismatch")
        vocab_sm_node = ir.sm_nodes[vocab_sm_index]
        vocab_pm_nodes = tuple(ir.pm_nodes[i] for i in vocab_pm_indices)
        if (vocab_cert.sm_step_id != f"sm:{vocab_sm_index}:0"
                or vocab_cert.pm_step_ids != tuple(f"pm:{i}:0" for i in vocab_pm_indices)
                or vocab_sm_node.rank != 0 or vocab_sm_node.op != "BW_embedding"
                or vocab_sm_node.params
                or tuple(vocab_sm_node.ins) != (vg.sm_tid, vi.sm_tid, vw.sm_tid)
                or vocab_sm_node.outs != [vo.sm_tid]
                or tuple(n.rank for n in vocab_pm_nodes) != tuple(range(k))
                or any(n.op != "BW_embedding"
                       or n.params != [r * vocab_cert.shard_rows]
                       or tuple(n.ins) != (vg.joined_pm_tid, vi.pm_tids[0], vw.pm_tids[r])
                       or n.outs != [vo.pm_tids[r]]
                       for r, n in enumerate(vocab_pm_nodes))):
            raise ValueError("vocab BW_embedding writer authority mismatch")

    semantic_sm = set(sm_indices) | ({vocab_sm_index} if vocab_cert else set())
    semantic_pm = set(pm_indices) | set(vocab_pm_indices)
    if vocab_cert and (
        set(sm_indices) & {vocab_sm_index}
        or set(pm_indices) & set(vocab_pm_indices)
        or semantic_sm != set(range(sm_start, sm_end))
        or semantic_pm != set(range(pm_start, pm_end))
    ):
        raise ValueError("BW_embedding semantic footprints do not exactly partition the frame")

    # Frame-only writers may not overwrite any relation or authority live across
    # this transaction.
    relation_by_id = {item.fact_id: item for item in chain.relation_facts}
    authority_by_id = {item.fact_id: item for item in chain.authority_facts}
    live_sm, live_pm = set(), set()
    for fact_id in set(before.fact_ids) | set(after.fact_ids):
        record = relation_by_id.get(fact_id)
        if record is not None:
            live_sm.add(record.sm_tid); live_pm.update(record.pm_tids)
            if record.joined_pm_tid is not None:
                live_pm.add(record.joined_pm_tid)
        authority = authority_by_id.get(fact_id)
        if authority is None:
            continue
        if authority.kind == "tensor_shape":
            (live_sm if authority.side == "sm" else live_pm).add(authority.tid)
        elif authority.kind == "tensor_eq":
            (live_sm if authority.left_side == "sm" else live_pm).add(authority.left_tid)
            (live_sm if authority.right_side == "sm" else live_pm).add(authority.right_tid)
        else:
            raise ValueError("sequence BW_embedding unsupported live authority kind")
    if (any(set(ir.sm_nodes[index].outs) & live_sm
            for index in set(range(sm_start, sm_end)) - semantic_sm)
            or any(set(ir.pm_nodes[index].outs) & live_pm
                   for index in set(range(pm_start, pm_end)) - semantic_pm)):
        raise ValueError("sequence BW_embedding frame overwrites live authority")

    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    sm_nodes_name = f"{segment_id}_sm_nodes"
    pm_nodes_name = f"{segment_id}_pm_nodes"
    sm_final_name = f"{segment_id}_sm_final"
    pm_final_name = f"{segment_id}_pm_final"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(item) for item in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(item) for item in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node, offset=None):
        final = f"({final_name} {initial})"
        theorem_name = f"{segment_id}_{name}"
        if offset is None:
            expression = f"bw_embedding ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})"
            apply_line = f"exact applyNode_bw_embedding_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]}"
        else:
            expression = f"bw_embedding_offset {offset} ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})"
            apply_line = f"exact applyNode_bw_embedding_offset_out {graph} t {node.rank} {offset} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]}"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl",
            f"      (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        proof_lines = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                apply_line,
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in proof_lines)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = writer(
        "hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
        sm_nodes_name, sm_frame, sm_indices[0] - sm_start, sm_node,
    )
    pm_helpers = tuple(
        writer(
            f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, index - pm_start, node,
        )
        for rank, (index, node) in enumerate(zip(pm_indices, pm_nodes))
    )
    vocab_sm_helper=writer("hVocabSm",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,sm_frame,vocab_sm_index-sm_start,vocab_sm_node) if vocab_cert else None
    vocab_pm_helpers=tuple(writer(f"hVocabPm{r}",ir.pm_graph_ref,"pmStore",pm_final_name,pm_nodes_name,pm_frame,index-pm_start,node,r*vocab_cert.shard_rows) for r,(index,node) in enumerate(zip(vocab_pm_indices,vocab_pm_nodes))) if vocab_cert else ()

    gradients = "[" + ", ".join(f"pmFinal {tid}" for tid in gradient.pm_tids) + "]"
    ids_values = "[" + ", ".join(f"pmFinal {tid}" for tid in ids.pm_tids) + "]"
    outputs = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]"
    weight_tid = weight.pm_tids[0]
    full = _shape_text(list(output.full_shape))
    shard = _shape_text(list(output.shard_shape))
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  let smFinal := {sm_final_name} smStore",
        f"  let pmFinal := {pm_final_name} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate <;> native_decide",
        f"  have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {gradient.sm_tid}) {gradients} 1 [{b}, {s * k}, {hidden}] [{b}, {s}, {hidden}] at hg",
        f"  have hi : {ids.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ChunkedRel (smFinal {ids.sm_tid}) {ids_values} 1 [{b}, {s * k}] [{b}, {s}] at hi",
        f"  have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {weight.sm_tid}) [pmFinal {weight_tid}] 0 [{vocab}, {hidden}] [{vocab}, {hidden}] at hw",
        f"  have hwEq : smFinal {weight.sm_tid} = pmFinal {weight_tid} := by",
        "    rw [hw.full_value]",
        f"    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal {weight_tid}) (by simp)]; native_decide)",
        f"  have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 1 {k} 0 {gradients} := by",
        "    simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"  have hSm := {sm_helper} smStore",
        f"  change smFinal {output.sm_tid} = bw_embedding (smFinal {gradient.sm_tid})",
        f"    (smFinal {ids.sm_tid}) (smFinal {weight.sm_tid}) at hSm",
    ])
    for rank, helper in enumerate(pm_helpers):
        lines.extend([
            f"  have hPm{rank} := {helper} pmStore",
            f"  change pmFinal {output.pm_tids[rank]} =",
            f"    bw_embedding (pmFinal {gradient.pm_tids[rank]})",
            f"      (pmFinal {ids.pm_tids[rank]}) (pmFinal {weight_tid}) at hPm{rank}",
        ])
    lines.extend([
        f"  have hComm := {cert.lean_theorem} {k} {b} {s} {hidden} {vocab}",
        f"    {gradients} (smFinal {ids.sm_tid}) (pmFinal {weight_tid})",
        "    (by decide) (by decide) (by decide) (by decide) (by decide)",
        "    (by rfl) hg.shard_shapes hi.full_shape",
        f"    (hw.shard_shapes (pmFinal {weight_tid}) (by simp))",
        "  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,",
        "    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,",
        "    List.getElem?_cons_succ, Option.getD_some] at hComm",
    ])
    for rank in range(k):
        lines.extend([
            f"  have hIdChunk{rank} := hi.chunk_values {rank} (by simp)",
            f"  simp [List.getD] at hIdChunk{rank}",
        ])
    lines.extend([
        f"  have hValue : smFinal {output.sm_tid} = tensorSum {outputs} := by",
        "    rw [hSm, hgValue, hwEq, hComm]",
    ])
    for rank in range(k):
        lines.extend([
            f"    rw [← hIdChunk{rank}]",
            f"    rw [← hPm{rank}]",
        ])
    lines.extend([
        f"  have hValueReduce : smFinal {output.sm_tid} =",
        f"      allReducePrim {outputs}.length 0 {outputs} := by",
        "    rw [hValue]", "    rfl",
        f"  have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
        "    rw [hSm, bw_embedding_shape]", "    exact hw.full_shape",
    ])
    contribution_shapes = []
    for rank in range(k):
        contribution_shapes.extend([
            f"  have hShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
            f"    rw [hPm{rank}, bw_embedding_shape]",
            "    exact hw.shard_shapes _ (by simp)",
        ])
    lines.extend(contribution_shapes)
    lines.extend([
        f"  have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"    change ReductionRel (smFinal {output.sm_tid}) {outputs} {full}",
        "    refine {", "      full_value := hValueReduce",
        "      full_shape := hFullShape", "      contributions_nonempty := by simp",
        "      contribution_shapes := ?_", "      reduced_shape := ?_", "    }",
        "    · intro contribution hmem",
        "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with " + " | ".join("rfl" for _ in range(k)),
        *(f"      · exact hShape{rank}" for rank in range(k)),
        "    · rw [← hValueReduce]", "      exact hFullShape",
    ])

    if vocab_cert:
        vocab_full = _shape_text(list(vo.full_shape))
        vocab_shard = _shape_text(list(vo.shard_shape))
        vocab_ids_full = _shape_text(list(vi.full_shape))
        vocab_ids_shard = _shape_text(list(vi.shard_shape))
        vocab_weights = "[" + ", ".join(
            f"pmFinal {tid}" for tid in vw.pm_tids
        ) + "]"
        vocab_outputs = "[" + ", ".join(
            f"pmFinal {tid}" for tid in vo.pm_tids
        ) + "]"
        lines.extend([
            f"  have hvg : {vg.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change smFinal {vg.sm_tid} = pmFinal {vg.joined_pm_tid} ∧ _ ∧ _ at hvg",
            f"  have hvi : {vi.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {vi.sm_tid}) [pmFinal {vi.pm_tids[0]}] 0 {vocab_ids_full} {vocab_ids_shard} at hvi",
            f"  have hviEq : smFinal {vi.sm_tid} = pmFinal {vi.pm_tids[0]} := by",
            "    rw [hvi.full_value]",
            f"    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hvi.shard_shapes (pmFinal {vi.pm_tids[0]}) (by simp)]; native_decide)",
            f"  have hvw : {vw.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {vw.sm_tid}) {vocab_weights} 0 {vocab_full} {vocab_shard} at hvw",
            f"  have hvwValue : smFinal {vw.sm_tid} = allGatherPrimDimN 0 {k} 0 {vocab_weights} := by",
            "    simpa only [List.length_cons, List.length_nil] using hvw.full_value",
            f"  have hVSm := {vocab_sm_helper} smStore",
            f"  change smFinal {vo.sm_tid} = bw_embedding (smFinal {vg.sm_tid})",
            f"    (smFinal {vi.sm_tid}) (smFinal {vw.sm_tid}) at hVSm",
        ])
        for rank, helper in enumerate(vocab_pm_helpers):
            lines.extend([
                f"  have hVPm{rank} := {helper} pmStore",
                f"  change pmFinal {vo.pm_tids[rank]} = bw_embedding_offset {rank * vocab_cert.shard_rows}",
                f"    (pmFinal {vg.joined_pm_tid}) (pmFinal {vi.pm_tids[0]})",
                f"      (pmFinal {vw.pm_tids[rank]}) at hVPm{rank}",
                f"  have hvwShape{rank} := hvw.shard_shapes (pmFinal {vw.pm_tids[rank]}) (by simp)",
                f"  have hVOutShape{rank} : (pmFinal {vo.pm_tids[rank]}).shape = {vocab_shard} := by",
                f"    rw [hVPm{rank}, bw_embedding_offset_shape]",
                f"    exact hvwShape{rank}",
            ])
        lines.extend([
            f"  have hVComm := {vocab_cert.lean_theorem} {k} {vocab_cert.shard_rows} {vocab_cert.hidden}",
            "    (by decide) (by decide) (by decide)",
            f"    (pmFinal {vg.joined_pm_tid}) (pmFinal {vi.pm_tids[0]}) {vocab_weights}",
            "    (by rfl) hvw.shard_shapes",
            "  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,",
            "    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,",
            "    List.getElem?_cons_succ, Option.getD_some] at hVComm",
            f"  have hVValue : smFinal {vo.sm_tid} = allGatherPrimDimN 0 {k} 0 {vocab_outputs} := by",
            "    rw [hVSm, hvg.1, hviEq, hvwValue, hVComm]",
            "    rw [" + ", ".join(f"← hVPm{rank}" for rank in range(k)) + "]",
            f"  have hVValueLength : smFinal {vo.sm_tid} =",
            f"      allGatherPrimDimN 0 {vocab_outputs}.length 0 {vocab_outputs} := by",
            "    simpa only [List.length_cons, List.length_nil] using hVValue",
            f"  have hVFullShape : (smFinal {vo.sm_tid}).shape = {vocab_full} := by",
            "    rw [hVSm, bw_embedding_shape]",
            "    exact hvw.full_shape",
            f"  have hVOut : {vo.fact_id}.Holds smFinal pmFinal := by",
            f"    change ShardedRel (smFinal {vo.sm_tid}) {vocab_outputs} 0 {vocab_full} {vocab_shard}",
            "    refine {",
            "      full_value := hVValueLength",
            "      full_shape := hVFullShape",
            "      shards_nonempty := by simp",
            "      gather_dim_lt := by native_decide",
            "      shard_shapes := ?_",
            "      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide",
            "    }",
            "    intro shard hmem",
            "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            "    rcases hmem with " + " | ".join("rfl" for _ in range(k)),
            *(f"    · exact hVOutShape{rank}" for rank in range(k)),
        ])

    fresh_facts = [output.fact_id] + ([vo.fact_id] if vocab_cert else [])
    fresh_list = "[" + ", ".join(fresh_facts) + "]"
    if vocab_cert:
        publish_fresh = [
            "    rcases fresh with rfl | rfl",
            "    · exact hout",
            "    · exact hVOut",
        ]
    else:
        publish_fresh = ["    rcases fresh with rfl", "    exact hout"]
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ {fresh_list} ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ {fresh_list} ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered",
        "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        *publish_fresh,
        "  · exact hframe fact old", "",
        f"private def {segment_id} : ClosedDepSegmentCertificate",
        f"    {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    have h := {segment_id}_sound smStore pmStore hstate",
        f"    unfold {sm_final_name} {pm_final_name} at h", "    exact h", "",
    ])
    return "\n".join(lines)
