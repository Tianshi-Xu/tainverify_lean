"""Projection-aware atomic renderer for shared-node BW_add identity outputs."""
from __future__ import annotations


def render_closed_k_rank_bw_add_identity_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("bw-add-identity-sharded-k-rank")
    rule = spec.rule_id
    contracts = {
        ".1": (
            spec.lean_theorems[0],
            "applyNode_bw_add2_fst_out",
        ),
        ".2": (
            spec.lean_theorems[1],
            "applyNode_bw_add2_snd_out",
        ),
    }
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or not segment.transition_ids:
        raise ValueError("BW_add identity tuple requires a nonempty transition segment")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    try:
        transitions = tuple(transition_map[item] for item in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("BW_add identity transition authority is missing") from exc
    if any(item.rule_id != rule for item in transitions):
        raise ValueError("BW_add identity tuple contains another transition family")

    certs = []
    for transition in transitions:
        matches = [
            item for item in relation.certificates
            if type(item) is spec.certificate_type
            and item.rule_id == transition.rule_id
            and item.lean_theorem == transition.lean_theorem
            and tuple(sorted((item.input_fact, item.operand_fact))) == transition.pre_facts
            and (item.output_fact,) == transition.post_facts
        ]
        if len(matches) != 1:
            raise ValueError("BW_add identity requires one exact typed certificate")
        cert = matches[0]
        if contracts.get(cert.projection, (None,))[0] != cert.lean_theorem:
            raise ValueError("BW_add projection/theorem identity mismatch")
        certs.append(cert)
    certs = tuple(certs)
    projections = tuple(item.projection for item in certs)
    if len(projections) != len(set(projections)) or not set(projections) <= set(contracts):
        raise ValueError("BW_add identity tuple has duplicate or unknown projections")
    by_projection = {item.projection: item for item in certs}
    first = certs[0]
    if any(item.input_fact != first.input_fact for item in certs[1:]):
        raise ValueError("BW_add projections do not share exact gradient authority")

    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient = records[first.input_fact]
        operands = {projection: records[cert.operand_fact]
                    for projection, cert in by_projection.items()}
        outputs = {projection: records[cert.output_fact]
                   for projection, cert in by_projection.items()}
    except KeyError as exc:
        raise ValueError("BW_add identity relation fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {gradient.fact_id, *(item.fact_id for item in operands.values())}
    fresh = {item.fact_id for item in outputs.values()}
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids):
        raise ValueError("BW_add identity pre/post facts are not live")
    if not set(after.fact_ids) <= (fresh | set(before.fact_ids)):
        raise ValueError("BW_add identity post-state introduces an unproved fact")

    k = len(gradient.pm_tids)
    if k <= 0:
        raise ValueError("BW_add identity rank authority is empty")
    for cert in certs:
        operand, output = operands[cert.projection], outputs[cert.projection]
        if (cert.rank_count != k or cert.gather_dim != gradient.gather_dim
                or len(operand.pm_tids) != k or len(output.pm_tids) != k
                or gradient.kind != "sharded" or operand.kind != "sharded"
                or output.kind != "sharded"
                or (operand.full_shape, operand.shard_shape, operand.gather_dim)
                   != (gradient.full_shape, gradient.shard_shape, gradient.gather_dim)
                or (output.full_shape, output.shard_shape, output.gather_dim)
                   != (gradient.full_shape, gradient.shard_shape, gradient.gather_dim)):
            raise ValueError("BW_add identity relation metadata is not exact")

    sm_owners = {tuple(item.sm_node_indices) for item in transitions}
    pm_owners = {tuple(item.pm_node_indices) for item in transitions}
    if len(sm_owners) != 1 or len(pm_owners) != 1:
        raise ValueError("BW_add projections do not share physical writers")
    sm_indices = next(iter(sm_owners)); pm_indices = next(iter(pm_owners))
    if len(sm_indices) != 1 or len(pm_indices) != k:
        raise ValueError("BW_add physical footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if (not set(sm_indices) <= set(range(sm_start, sm_end))
            or not set(pm_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("BW_add physical writers are outside the complete frame")
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    sm_node = ir.sm_nodes[sm_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in pm_indices)
    if (sm_node.rank != 0 or sm_node.op != "BW_add" or sm_node.params
            or len(sm_node.ins) != 3 or len(sm_node.outs) != 2
            or sm_node.ins[0] != gradient.sm_tid):
        raise ValueError("BW_add SM writer roles/projections are not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("BW_add PM writer ranks are not ordered")
    for rank, node in enumerate(pm_nodes):
        if (node.op != "BW_add" or node.params or len(node.ins) != 3
                or len(node.outs) != 2 or node.ins[0] != gradient.pm_tids[rank]):
            raise ValueError("BW_add PM writer roles/projections are not exact")
    for projection, cert in by_projection.items():
        slot = 0 if projection == ".1" else 1
        operand = operands[projection]; output = outputs[projection]
        if (sm_node.ins[slot + 1] != operand.sm_tid or sm_node.outs[slot] != output.sm_tid
                or any(node.ins[slot + 1] != operand.pm_tids[rank]
                       or node.outs[slot] != output.pm_tids[rank]
                       for rank, node in enumerate(pm_nodes))):
            raise ValueError("BW_add selected projection roles are not exact")
    slots = []
    for cert, transition in zip(certs, transitions):
        projection_index = 0 if cert.projection == ".1" else 1
        expected_sm = f"sm:{sm_indices[0]}:{projection_index}"
        expected_pm = tuple(f"pm:{index}:{projection_index}" for index in pm_indices)
        if cert.sm_step_id != expected_sm or cert.pm_step_ids != expected_pm:
            raise ValueError("BW_add certificate output-slot footprint was tampered")
        slots.append(("sm", sm_indices[0], projection_index))
        slots.extend(("pm", index, projection_index) for index in pm_indices)
    if len(slots) != len(set(slots)):
        raise ValueError("BW_add output slot has duplicate ownership")

    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    sm_final_name, pm_final_name = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store",
        "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node,
               projection, output_index):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        expression = (
            f"(bw_add2 ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
            f"({{store}} {node.ins[2]})){projection}"
        )
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[output_index]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[output_index],
            input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact {contracts[projection][1]} {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.ins[2]} "
                f"{node.outs[0]} {node.outs[1]} (by native_decide)",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    helpers = {}
    selected = tuple((projection, 0 if projection == ".1" else 1)
                     for projection in projections)
    for projection, output_index in selected:
        sm_helper = writer(
            f"hSmWriter{output_index}", ir.sm_graph_ref, "smStore", sm_final_name,
            sm_nodes_name, sm_frame, sm_indices[0] - sm_start, sm_node,
            projection, output_index,
        )
        pm_helpers = tuple(
            writer(
                f"hPmWriter{output_index}_{rank}", ir.pm_graph_ref, "pmStore",
                pm_final_name, pm_nodes_name, pm_frame, index - pm_start, node,
                projection, output_index,
            )
            for rank, (index, node) in enumerate(zip(pm_indices, pm_nodes))
        )
        helpers[projection] = (sm_helper, pm_helpers)

    full_shape = _shape_text(list(gradient.full_shape))
    shard_shape = _shape_text(list(gradient.shard_shape))
    glist = "[" + ", ".join(f"pmFinal {tid}" for tid in gradient.pm_tids) + "]"
    lines.extend([
        "set_option maxHeartbeats 500000 in",
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
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} {gradient.gather_dim} {full_shape} {shard_shape} at hg",
    ])
    fresh_names = []
    for projection, output_index in selected:
        cert = by_projection[projection]
        operand, output = operands[projection], outputs[projection]
        operand_list = "[" + ", ".join(f"pmFinal {tid}" for tid in operand.pm_tids) + "]"
        output_list = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]"
        hop = f"hop{output_index}"; hout = f"hout{output_index}"
        sm_helper, pm_helpers = helpers[projection]
        lines.extend([
            f"    have {hop} : {operand.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"    change ShardedRel (smFinal {operand.sm_tid}) {operand_list} {operand.gather_dim} {full_shape} {shard_shape} at {hop}",
            f"    have hSmWriter{output_index} : smFinal {output.sm_tid} =",
            f"        (bw_add2 (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) (smFinal {sm_node.ins[2]})){projection} :=",
            f"      {sm_helper} smStore",
            f"    have hSmIdentity{output_index} : smFinal {output.sm_tid} = smFinal {gradient.sm_tid} := by",
            f"      rw [hSmWriter{output_index}]",
            f"      exact {cert.lean_theorem} _ _ _ (by rw [hg.full_shape, {hop}.full_shape])",
        ])
        for rank, (helper, node) in enumerate(zip(pm_helpers, pm_nodes)):
            lines.extend([
                f"    have hPmWriter{output_index}_{rank} : pmFinal {output.pm_tids[rank]} =",
                f"        (bw_add2 (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) (pmFinal {node.ins[2]})){projection} :=",
                f"      {helper} pmStore",
                f"    have hgShape{output_index}_{rank} := hg.shard_shapes (pmFinal {gradient.pm_tids[rank]}) (by simp)",
                f"    have hopShape{output_index}_{rank} := {hop}.shard_shapes (pmFinal {operand.pm_tids[rank]}) (by simp)",
                f"    have hPmIdentity{output_index}_{rank} : pmFinal {output.pm_tids[rank]} = pmFinal {gradient.pm_tids[rank]} := by",
                f"      rw [hPmWriter{output_index}_{rank}]",
                f"      exact {cert.lean_theorem} _ _ _ (by rw [hgShape{output_index}_{rank}, hopShape{output_index}_{rank}])",
            ])
        lines.extend([
            f"    have {hout} : {output.fact_id}.Holds smFinal pmFinal := by",
            f"      change ShardedRel (smFinal {output.sm_tid}) {output_list} {output.gather_dim} {full_shape} {shard_shape}",
            "      refine {",
            f"        full_value := ?_", f"        full_shape := ?_",
            "        shards_nonempty := by simp", "        gather_dim_lt := hg.gather_dim_lt",
            "        shard_shapes := ?_", "        shape_contract := hg.shape_contract", "      }",
            f"      · rw [hSmIdentity{output_index}]",
            "        rw [hg.full_value]",
            "        rw [" + ", ".join(f"hPmIdentity{output_index}_{rank}" for rank in range(k)) + "]",
            f"      · rw [hSmIdentity{output_index}]", "        exact hg.full_shape",
            "      · intro shard hmem",
            f"        rw [show {output_list} = [" + ", ".join(
                f"pmFinal {output.pm_tids[rank]}" for rank in range(k)
            ) + "] from rfl] at hmem",
            "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
        ])
        for rank in range(k):
            lines.extend([
                "        · subst shard", f"          rw [hPmIdentity{output_index}_{rank}]",
                f"          exact hgShape{output_index}_{rank}",
            ])
        fresh_names.append(hout)
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(item.fact_id for item in outputs.values())}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(item.fact_id for item in outputs.values())}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with " + " | ".join("rfl" for _ in fresh_names),
        *(f"      · exact {name}" for name in fresh_names),
        "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    exact {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
