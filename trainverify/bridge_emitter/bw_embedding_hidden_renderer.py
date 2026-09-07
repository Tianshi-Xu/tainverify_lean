"""Closed hidden-axis BW_embedding replay over the complete sparse authority frame.

Only the supplied closed pre-state is assumed. Shared IDs are reconstructed from
its singleton gather, not from replicated shapes or an assumed output equality.
"""
from __future__ import annotations

import re


def render_closed_k_rank_bw_embedding_hidden_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import get_closed_rule_spec

    rule = "bw-embedding-hidden-sharded-k-rank"
    theorem = "TrainVerify.Denote.bw_embedding_hidden_allGather_rank3"
    spec = get_closed_rule_spec(rule)
    if spec.rule_id != rule or spec.lean_theorems != (theorem,):
        raise ValueError("hidden BW_embedding registry theorem mismatch")
    chain = relation.dependent_chain_plan
    if chain is None:
        raise ValueError("hidden BW_embedding requires a closed chain")
    segments = [x for x in chain.segments if x.segment_id == segment_id]
    if len(segments) != 1 or len(segments[0].transition_ids) != 1:
        raise ValueError("hidden BW_embedding requires one transition")
    segment = segments[0]
    transitions = [x for x in relation.transition_specs if x.transition_id == segment.transition_ids[0]]
    if len(transitions) != 1:
        raise ValueError("hidden BW_embedding transition missing or ambiguous")
    transition = transitions[0]
    cert = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda c: (tuple(sorted((c.gradient_fact, c.ids_fact, c.weight_fact))), (c.output_fact,)),
    )
    records = {x.source: x for x in chain.relation_facts}
    relation_by_id = {x.fact_id: x for x in chain.relation_facts}
    authority = {x.fact_id: x for x in chain.authority_facts}
    if (len(records) != len(chain.relation_facts)
            or len(relation_by_id) != len(chain.relation_facts)
            or len(authority) != len(chain.authority_facts)
            or set(relation_by_id) & set(authority)):
        raise ValueError("hidden BW_embedding ambiguous fact identity")
    try:
        gradient, ids, weight, output = (records[f] for f in
            (cert.gradient_fact, cert.ids_fact, cert.weight_fact, cert.output_fact))
        states = {x.state_id: x for x in chain.states}
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("hidden BW_embedding fact/state missing") from exc
    if len(states) != len(chain.states):
        raise ValueError("hidden BW_embedding ambiguous state identity")
    if not {gradient.fact_id, ids.fact_id, weight.fact_id} <= set(before.fact_ids):
        raise ValueError("hidden BW_embedding inputs are not live")
    if (output.fact_id in before.fact_ids or output.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= ({output.fact_id} | set(before.fact_ids))):
        raise ValueError("hidden BW_embedding post-state mismatch")

    k, b, s, v, d = (cert.rank_count, cert.batch_size, cert.sequence_size,
                     cert.vocab_size, cert.shard_hidden)
    if any(type(x) is not int or x <= 0 for x in (k, b, s, v, d)) or k != ir.pm_num_ranks:
        raise ValueError("hidden BW_embedding rank/dimensions mismatch")
    full_shape, shard_shape = (v, d * k), (v, d)

    def source_tid(ref, side):
        initial = re.fullmatch(r"init:(0|[1-9][0-9]*)", ref)
        if initial:
            return int(initial[1])
        writer = re.fullmatch(r"(sm|pm):(0|[1-9][0-9]*):(0|[1-9][0-9]*)", ref)
        if writer is None or writer[1] != side:
            raise ValueError("hidden BW_embedding invalid source reference")
        nodes = ir.sm_nodes if side == "sm" else ir.pm_nodes
        index, projection = int(writer[2]), int(writer[3])
        if index >= len(nodes) or projection >= len(nodes[index].outs):
            raise ValueError("hidden BW_embedding source reference outside authority")
        return nodes[index].outs[projection]

    for record, axis, full, local, ranks in (
        (gradient, 2, (b, s, d * k), (b, s, d), k),
        (ids, 0, (b, s), (b, s), 1),
        (weight, 1, full_shape, shard_shape, k),
        (output, 1, full_shape, shard_shape, k),
    ):
        source = record.source
        if (record.kind != "sharded" or source.layout != "sharded"
                or record.gather_dim != axis or source.gather_dim != axis
                or record.full_shape != full or record.shard_shape != local
                or len(record.pm_tids) != ranks or len(source.step_triple) != ranks + 1
                or record.metadata_tid is not None or record.metadata_region_id is not None
                or record.row_shard_shape is not None or record.source_tid_triples
                or record.joined_pm_tid is not None or source.source_step_triples
                or source.joined_pm_step is not None):
            raise ValueError("hidden BW_embedding relation metadata mismatch")
        if (source_tid(source.step_triple[0], "sm") != record.sm_tid
                or tuple(source_tid(ref, "pm") for ref in source.step_triple[1:]) != record.pm_tids):
            raise ValueError("hidden BW_embedding source/record TID mismatch")
    if ids.source.step_triple != (f"init:{ids.sm_tid}", f"init:{ids.pm_tids[0]}"):
        raise ValueError("hidden BW_embedding IDs must be singleton external authority")

    sm_indices, pm_indices = tuple(transition.sm_node_indices), tuple(transition.pm_node_indices)
    if len(sm_indices) != 1 or len(pm_indices) != k:
        raise ValueError("hidden BW_embedding writer cardinality mismatch")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if not (0 <= sm_start <= sm_end <= len(ir.sm_nodes) and 0 <= pm_start <= pm_end <= len(ir.pm_nodes)):
        raise ValueError("hidden BW_embedding frame range mismatch")
    sm_range, pm_range = set(range(sm_start, sm_end)), set(range(pm_start, pm_end))
    if (len(set(sm_indices)) != 1 or len(set(pm_indices)) != k
            or not set(sm_indices) <= sm_range or not set(pm_indices) <= pm_range):
        raise ValueError("hidden BW_embedding writer/frame partition mismatch")
    sm_node = ir.sm_nodes[sm_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[i] for i in pm_indices)
    if (sm_node.rank != 0 or sm_node.op != "BW_embedding" or tuple(sm_node.params or ()) != ()
            or tuple(sm_node.ins) != (gradient.sm_tid, ids.sm_tid, weight.sm_tid)
            or sm_node.outs != [output.sm_tid]):
        raise ValueError("hidden BW_embedding SM writer mismatch")
    for rank, node in enumerate(pm_nodes):
        if (node.rank != rank or node.op != "BW_embedding" or tuple(node.params or ()) != ()
                or tuple(node.ins) != (gradient.pm_tids[rank], ids.pm_tids[0], weight.pm_tids[rank])
                or node.outs != [output.pm_tids[rank]]):
            raise ValueError("hidden BW_embedding PM writer mismatch")
    if (cert.sm_step_id != f"sm:{sm_indices[0]}:0"
            or cert.pm_step_ids != tuple(f"pm:{index}:0" for index in pm_indices)
            or output.source.step_triple != (cert.sm_step_id, *cert.pm_step_ids)
            or len(set(output.pm_tids)) != k):
        raise ValueError("hidden BW_embedding certificate writer footprint mismatch")

    # Frame all retained pre-facts, including independent shape/equality authority.
    # Semantic writers must also preserve the pre-state (not merely frame nodes).
    def live_tids(fact_ids):
        sm, pm = set(), set()
        for fact_id in fact_ids:
            record = relation_by_id.get(fact_id)
            if record is not None:
                sm.add(record.sm_tid)
                pm.update(record.pm_tids)
                if record.joined_pm_tid is not None:
                    pm.add(record.joined_pm_tid)
                if record.metadata_tid is not None:
                    sm.add(record.metadata_tid)
                    pm.add(record.metadata_tid)
                for ts, tp0, tp1 in record.source_tid_triples:
                    sm.add(ts)
                    pm.update((tp0, tp1))
                continue
            fact = authority.get(fact_id)
            if fact is None and fact_id == chain.anchor_fact.fact_id:
                fact = chain.anchor_fact
            if fact is None:
                raise ValueError("hidden BW_embedding unknown live fact")
            if fact.kind == "tensor_shape" and fact.side in ("sm", "pm"):
                (sm if fact.side == "sm" else pm).add(fact.tid)
            elif fact.kind == "tensor_eq" and fact.left_side in ("sm", "pm") and fact.right_side in ("sm", "pm"):
                (sm if fact.left_side == "sm" else pm).add(fact.left_tid)
                (sm if fact.right_side == "sm" else pm).add(fact.right_tid)
            else:
                raise ValueError("hidden BW_embedding unsupported live authority kind")
        return sm, pm

    live_sm, live_pm = live_tids(set(before.fact_ids) | set(after.fact_ids))
    pre_sm, pre_pm = live_tids(before.fact_ids)
    if (any(set(ir.sm_nodes[i].outs) & live_sm for i in sm_range - set(sm_indices))
            or any(set(ir.pm_nodes[i].outs) & live_pm for i in pm_range - set(pm_indices))
            or set(sm_node.outs) & pre_sm
            or any(set(node.outs) & pre_pm for node in pm_nodes)):
        raise ValueError("hidden BW_embedding frame overwrites live authority")

    sm_frame, pm_frame = list(ir.sm_nodes[sm_start:sm_end]), list(ir.pm_nodes[pm_start:pm_end])
    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    sm_final_name, pm_final_name = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(x) for x in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(x) for x in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node):
        final, theorem_name = f"({final_name} {initial})", f"{segment_id}_{name}"
        expression = f"bw_embedding ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})"
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
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_embedding_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]}",
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in proof)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = writer("hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
                       sm_nodes_name, sm_frame, sm_indices[0] - sm_start, sm_node)
    pm_helpers = tuple(
        writer(f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
               pm_nodes_name, pm_frame, index - pm_start, node)
        for rank, (index, node) in enumerate(zip(pm_indices, pm_nodes))
    )
    full, shard = _shape_text(list(full_shape)), _shape_text(list(shard_shape))
    gradients = "[" + ", ".join(f"pmFinal {x}" for x in gradient.pm_tids) + "]"
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
        f"  change ShardedRel (smFinal {gradient.sm_tid}) {gradients} 2 {_shape_text(list(gradient.full_shape))} {_shape_text(list(gradient.shard_shape))} at hg",
        f"  have hgV : smFinal {gradient.sm_tid} = allGatherPrimDimN 2 {k} 0 {gradients} := by",
        "    simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"  have hi : {ids.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {ids.sm_tid}) [pmFinal {ids.pm_tids[0]}] 0 {_shape_text(list(ids.full_shape))} {_shape_text(list(ids.shard_shape))} at hi",
        f"  have hiShape := hi.shard_shapes (pmFinal {ids.pm_tids[0]}) (by simp)",
        f"  have hiEq : smFinal {ids.sm_tid} = pmFinal {ids.pm_tids[0]} := by",
        "    rw [hi.full_value]",
        "    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)",
        f"  have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {weight.sm_tid}) {weights} 1 {full} {shard} at hw",
        f"  have hwV : smFinal {weight.sm_tid} = allGatherPrimDimN 1 {k} 0 {weights} := by",
        "    simpa only [List.length_cons, List.length_nil] using hw.full_value",
        f"  have hSm := {sm_helper} smStore",
        f"  change smFinal {output.sm_tid} = bw_embedding (smFinal {gradient.sm_tid}) (smFinal {ids.sm_tid}) (smFinal {weight.sm_tid}) at hSm",
    ])
    for rank, helper in enumerate(pm_helpers):
        lines.extend([
            f"  have hPm{rank} := {helper} pmStore",
            f"  change pmFinal {output.pm_tids[rank]} = bw_embedding "
            f"(pmFinal {gradient.pm_tids[rank]}) (pmFinal {ids.pm_tids[0]}) (pmFinal {weight.pm_tids[rank]}) at hPm{rank}",
            f"  have houtShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
            f"    rw [hPm{rank}, bw_embedding_shape]",
            f"    exact hw.shard_shapes (pmFinal {weight.pm_tids[rank]}) (by simp)",
        ])
    lines.extend([
        f"  have hComm := {theorem} {k} {b} {s} {v} {d}",
        f"    {gradients} {weights} (pmFinal {ids.pm_tids[0]})",
        "    (by decide) (by decide) (by decide) (by decide) (by decide)",
        "    (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape",
        "  simp only [List.zipWith] at hComm",
        f"  have hValue : smFinal {output.sm_tid} = allGatherPrimDimN 1 {k} 0 {outputs} := by",
        "    rw [hSm, hgV, hiEq, hwV, hComm]",
        "    rw [" + ", ".join(f"← hPm{rank}" for rank in range(k)) + "]",
        f"  have hValueL : smFinal {output.sm_tid} = allGatherPrimDimN 1 {outputs}.length 0 {outputs} := by",
        "    simpa only [List.length_cons, List.length_nil] using hValue",
        f"  have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
        "    rw [hSm, bw_embedding_shape]", "    exact hw.full_shape",
        f"  have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"    change ShardedRel (smFinal {output.sm_tid}) {outputs} 1 {full} {shard}",
        "    refine {", "      full_value := hValueL", "      full_shape := hFullShape",
        "      shards_nonempty := by simp", "      gather_dim_lt := by native_decide",
        "      shard_shapes := ?_",
        "      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide", "    }",
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
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "    rcases fresh with rfl", "    exact hout", "  · exact hframe fact old", "",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    have h := {segment_id}_sound smStore pmStore hstate",
        f"    unfold {sm_final_name} {pm_final_name} at h", "    exact h", "",
    ])
    return "\n".join(lines)
