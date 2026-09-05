"""Closed sparse/full-frame renderer for typed BW_layernorm dX sharding."""
from __future__ import annotations


def render_closed_k_rank_bw_layernorm_dx_segment(ir, relation, segment_id: str) -> str:
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

    spec = get_closed_rule_spec("bw-layernorm-dx-dim1-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("BW_layernorm dX requires one atomic transition")
    transition = {item.transition_id: item for item in relation.transition_specs}.get(
        segment.transition_ids[0]
    )
    if transition is None:
        raise ValueError("BW_layernorm dX transition authority is missing")
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda cert: (
            tuple(sorted((cert.gradient_fact, cert.activation_fact,
                          cert.gamma_fact, cert.beta_fact))),
            (cert.output_fact,),
        ),
    )
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient = records[certificate.gradient_fact]
        activation = records[certificate.activation_fact]
        gamma = records[certificate.gamma_fact]
        beta = records[certificate.beta_fact]
        output = records[certificate.output_fact]
    except KeyError as exc:
        raise ValueError("BW_layernorm dX relation fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {gradient.fact_id, activation.fact_id, gamma.fact_id, beta.fact_id}
    if not required <= set(before.fact_ids) or output.fact_id not in after.fact_ids:
        raise ValueError("BW_layernorm dX pre/post facts are not live")
    if not set(after.fact_ids) <= ({output.fact_id} | set(before.fact_ids)):
        raise ValueError("BW_layernorm dX post-state introduces an unproved fact")

    k = len(gradient.pm_tids)
    if len(certificate.shard_shape) != 3 or any(x <= 0 for x in certificate.shard_shape):
        raise ValueError("BW_layernorm dX certificate shape contract is not exact")
    batch, seq, width = certificate.shard_shape
    if (certificate.full_shape != (batch, seq * k, width)
            or gradient.full_shape != certificate.full_shape
            or gradient.shard_shape != certificate.shard_shape):
        raise ValueError("BW_layernorm dX certificate/fact shape contract mismatch")
    if (k == 0 or certificate.rank_count != k or certificate.gather_dim != 1
            or gradient.kind != "sharded" or gradient.gather_dim != 1
            or activation.kind != "sharded" or activation.gather_dim != 1
            or output.kind != "sharded" or output.gather_dim != 1
            or (activation.full_shape, activation.shard_shape)
               != (gradient.full_shape, gradient.shard_shape)
            or (output.full_shape, output.shard_shape)
               != (gradient.full_shape, gradient.shard_shape)
            or len(activation.pm_tids) != k or len(output.pm_tids) != k
            or any(
                not ((f.kind == "sharded" and f.gather_dim == 0)
                     or (width == 1 and f.kind == "reduction" and f.gather_dim is None))
                or f.kind != f.source.layout
                for f in (gamma, beta)
            )
            or gamma.full_shape != (width,) or gamma.shard_shape != (width,)
            or beta.full_shape != (width,) or beta.shard_shape != (width,)
            or len(gamma.pm_tids) != 1 or len(beta.pm_tids) != 1):
        raise ValueError("BW_layernorm dX metadata is not exact")

    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("BW_layernorm dX footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if (not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("BW_layernorm dX writers are outside the complete frame")
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    if (certificate.sm_step_id != f"sm:{transition.sm_node_indices[0]}:0"
            or certificate.pm_step_ids
               != tuple(f"pm:{index}:0" for index in transition.pm_node_indices)):
        raise ValueError("BW_layernorm dX certificate footprint was tampered")
    if (sm_node.rank != 0 or sm_node.op != "BW_layernorm" or sm_node.params
            or len(sm_node.ins) != 4 or len(sm_node.outs) != 3
            or tuple(sm_node.ins) != (
                gradient.sm_tid, activation.sm_tid, gamma.sm_tid, beta.sm_tid,
            )
            or sm_node.outs[0] != output.sm_tid):
        raise ValueError("BW_layernorm dX SM writer roles are not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("BW_layernorm dX PM writer ranks are not ordered")
    for rank, node in enumerate(pm_nodes):
        if (node.op != "BW_layernorm" or node.params or len(node.ins) != 4
                or len(node.outs) != 3
                or tuple(node.ins) != (
                    gradient.pm_tids[rank], activation.pm_tids[rank],
                    gamma.pm_tids[0], beta.pm_tids[0],
                )
                or node.outs[0] != output.pm_tids[rank]):
            raise ValueError("BW_layernorm dX PM writer roles/order are not exact")

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

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        expression = (
            f"(bw_layernorm ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
            f"({{store}} {node.ins[2]}) ({{store}} {node.ins[3]})).1"
        )
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
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
                f"exact applyNode_bw_layernorm_dx_out {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.ins[2]} {node.ins[3]} "
                f"{node.outs[0]} {node.outs[1]} {node.outs[2]}",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = writer(
        "hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name, sm_nodes_name,
        sm_frame, transition.sm_node_indices[0] - sm_start, sm_node,
    )
    pm_helpers = [
        writer(
            f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, index - pm_start, node,
        )
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
    ]

    lines.extend([
        f"private theorem {segment_id}_dx_shape (g x w b : Tensor) (s : Nat)",
        f"    (hx : x.shape = [{batch}, s, {width}]) :",
        f"    (bw_layernorm g x w b).1.shape = [{batch}, s, {width}] := by",
        "  calc",
        "    (bw_layernorm g x w b).1.shape = x.shape :=",
        f"      bw_layernorm_dx_shape g x w b {width} [s, {batch}] (by rw [hx]; rfl)",
        f"    _ = [{batch}, s, {width}] := hx",
        "",
    ])

    glist = "[" + ", ".join(f"pmFinal {tid}" for tid in gradient.pm_tids) + "]"
    xlist = "[" + ", ".join(f"pmFinal {tid}" for tid in activation.pm_tids) + "]"
    olist = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]"
    full_shape = _shape_text(list(output.full_shape))
    shard_shape = _shape_text(list(output.shard_shape))
    param_shape = _shape_text([width])
    def parameter_value(fact, label):
        name = label.lower()
        result = [f"    have h{name} : {fact.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)"]
        if fact.kind == "reduction":
            result += [
                f"    change ReductionRel (smFinal {fact.sm_tid}) [pmFinal {fact.pm_tids[0]}] {param_shape} at h{name}",
                f"    have h{label}Value : smFinal {fact.sm_tid} = pmFinal {fact.pm_tids[0]} := h{name}.singleton_value",
            ]
        else:
            result += [
                f"    change ShardedRel (smFinal {fact.sm_tid}) [pmFinal {fact.pm_tids[0]}] 0 {param_shape} {param_shape} at h{name}",
                f"    have h{label}Value : smFinal {fact.sm_tid} = pmFinal {fact.pm_tids[0]} := by",
                f"      rw [h{name}.full_value]",
                "      simpa only [List.length_cons, List.length_nil] using",
                f"        (allGatherPrimDimN_singleton_eq 0 (pmFinal {fact.pm_tids[0]}) (by",
                f"          rw [h{name}.shard_shapes (pmFinal {fact.pm_tids[0]}) (by simp)]; decide))",
            ]
        return result

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
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} 1 {full_shape} {shard_shape} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {activation.sm_tid}) {xlist} 1 {full_shape} {shard_shape} at hx",
        *parameter_value(gamma, "Gamma"),
        *parameter_value(beta, "Beta"),
        f"    have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 1 {k} 0 {glist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"    have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN 1 {k} 0 {xlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"    have hSmWriter : smFinal {sm_node.outs[0]} =",
        f"        (bw_layernorm (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]})",
        f"          (smFinal {sm_node.ins[2]}) (smFinal {sm_node.ins[3]})).1 :=",
        f"      {sm_helper} smStore",
    ])
    for rank, (helper, node) in enumerate(zip(pm_helpers, pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {node.outs[0]} =",
            f"        (bw_layernorm (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]})",
            f"          (pmFinal {node.ins[2]}) (pmFinal {node.ins[3]})).1 :=",
            f"      {helper} pmStore",
            f"    have hgShape{rank} := hg.shard_shapes (pmFinal {gradient.pm_tids[rank]}) (by simp)",
            f"    have hxShape{rank} := hx.shard_shapes (pmFinal {activation.pm_tids[rank]}) (by simp)",
            f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard_shape} := by",
            f"      rw [hPmWriter{rank}]",
            f"      exact {segment_id}_dx_shape _ _ _ _ {seq} hxShape{rank}",
        ])
    lines.extend([
        f"    have hcomm := {theorem} {k} {batch} {seq} {width}",
        f"      {glist} {xlist} (pmFinal {gamma.pm_tids[0]}) (pmFinal {beta.pm_tids[0]})",
        "      (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)",
        "      (by simp [" + ", ".join(f"hgShape{r}" for r in range(k)) + "])",
        "      (by simp [" + ", ".join(f"hxShape{r}" for r in range(k)) + "])",
        f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN 1 {k} 0 {olist} := by",
        "      rw [hSmWriter, hgValue, hxValue, hGammaValue, hBetaValue, hcomm]",
        "      simp only [List.zipWith]",
        "      rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
        f"    have hOutValueList : smFinal {output.sm_tid} =",
        f"        allGatherPrimDimN 1 {olist}.length 0 {olist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hOutValue",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {full_shape} := by",
        "      rw [hSmWriter]",
        f"      exact {segment_id}_dx_shape _ _ _ _ {seq * k} hx.full_shape",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {output.sm_tid}) {olist} 1 {full_shape} {shard_shape}",
        "      refine {",
        "        full_value := hOutValueList", "        full_shape := hFullShape",
        "        shards_nonempty := by simp", "        gather_dim_lt := by decide",
        "        shard_shapes := ?_", "        shape_contract := ?_", "      }",
        "      · intro shard hmem",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend(["        · subst shard", f"          exact hOutShape{rank}"])
    lines.extend([
        "      · simp only [List.length_cons, List.length_nil]",
        "        native_decide",
        "    intro fact hfact",
        f"    have covered : fact ∈ [{output.fact_id}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl", "      exact hout", "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    exact {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
