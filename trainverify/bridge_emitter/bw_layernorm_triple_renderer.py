"""Single-fold renderer for all three typed BW_layernorm projections."""
from __future__ import annotations


def render_closed_k_rank_bw_layernorm_triple_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import (
            KRankBWLayernormDxCertificate,
            KRankBWLayernormParamReductionCertificate,
        )
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import (
            KRankBWLayernormDxCertificate,
            KRankBWLayernormParamReductionCertificate,
        )

    rule = "bw-layernorm-dx-dim1-k-rank"
    theorem = "TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d"
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 3:
        raise ValueError("BW_layernorm triple requires exactly three transitions")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    transitions = tuple(transition_map[item] for item in segment.transition_ids)
    by_rule = {item.rule_id: item for item in transitions}
    required_rules = {rule, "bw-layernorm-dgamma-reduction-rank4", "bw-layernorm-dbeta-reduction-rank4"}
    if set(by_rule) != required_rules:
        raise ValueError("BW_layernorm triple family set mismatch")
    transition = by_rule[rule]
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, theorem, KRankBWLayernormDxCertificate,
        lambda cert: (
            tuple(sorted((cert.gradient_fact, cert.activation_fact,
                          cert.gamma_fact, cert.beta_fact))),
            (cert.output_fact,),
        ),
    )
    param_certificates = {}
    for param_rule, projection, expected_theorem in (
        ("bw-layernorm-dgamma-reduction-rank4", ".2.1",
         "TrainVerify.Denote.bw_layernorm_dw_dp_split_dim1_4_1_2_32"),
        ("bw-layernorm-dbeta-reduction-rank4", ".2.2",
         "TrainVerify.Denote.bw_layernorm_db_dp_split_dim1_4_1_2_32"),
    ):
        param_transition = by_rule[param_rule]
        param_cert = _select_exact_typed_certificate(
            relation, param_transition, param_rule, expected_theorem,
            KRankBWLayernormParamReductionCertificate,
            lambda cert: (
                tuple(sorted((cert.gradient_fact, cert.activation_fact,
                              cert.gamma_fact, cert.beta_fact))),
                (cert.output_fact,),
            ),
        )
        if param_cert.projection != projection:
            raise ValueError("BW_layernorm parameter projection mismatch")
        param_certificates[projection] = (param_transition, param_cert)
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient = records[certificate.gradient_fact]
        activation = records[certificate.activation_fact]
        gamma = records[certificate.gamma_fact]
        beta = records[certificate.beta_fact]
        output = records[certificate.output_fact]
        gamma_output = records[param_certificates[".2.1"][1].output_fact]
        beta_output = records[param_certificates[".2.2"][1].output_fact]
    except KeyError as exc:
        raise ValueError("BW_layernorm dX relation fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {gradient.fact_id, activation.fact_id, gamma.fact_id, beta.fact_id}
    fresh = {output.fact_id, gamma_output.fact_id, beta_output.fact_id}
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids):
        raise ValueError("BW_layernorm triple pre/post facts are not live")
    if not set(after.fact_ids) <= (fresh | set(before.fact_ids)):
        raise ValueError("BW_layernorm triple post-state introduces an unproved fact")

    k = len(gradient.pm_tids)
    if (k != 4 or certificate.rank_count != k or certificate.gather_dim != 1
            or certificate.full_shape != (1, 8, 32) or certificate.shard_shape != (1, 2, 32)
            or gradient.kind != "sharded" or gradient.gather_dim != 1
            or activation.kind != "sharded" or activation.gather_dim != 1
            or output.kind != "sharded" or output.gather_dim != 1
            or gradient.full_shape != (1, 8, 32)
            or gradient.shard_shape != (1, 2, 32)
            or (activation.full_shape, activation.shard_shape)
               != (gradient.full_shape, gradient.shard_shape)
            or (output.full_shape, output.shard_shape)
               != (gradient.full_shape, gradient.shard_shape)
            or len(activation.pm_tids) != k or len(output.pm_tids) != k
            or gamma.kind != "sharded" or gamma.gather_dim != 0
            or beta.kind != "sharded" or beta.gather_dim != 0
            or gamma.full_shape != (32,) or gamma.shard_shape != (32,)
            or beta.full_shape != (32,) or beta.shard_shape != (32,)
            or len(gamma.pm_tids) != 1 or len(beta.pm_tids) != 1):
        raise ValueError("BW_layernorm dX metadata is not exact")
    for projection, slot, param_output in ((".2.1", 1, gamma_output), (".2.2", 2, beta_output)):
        param_transition, param_cert = param_certificates[projection]
        if (param_cert.rank_count != k or param_output.kind != "reduction"
                or param_output.full_shape != (32,) or param_output.shard_shape != (32,)
                or len(param_output.pm_tids) != k
                or param_transition.sm_node_indices != transition.sm_node_indices
                or param_transition.pm_node_indices != transition.pm_node_indices
                or param_cert.sm_step_id != f"sm:{transition.sm_node_indices[0]}:{slot}"
                or param_cert.pm_step_ids
                   != tuple(f"pm:{index}:{slot}" for index in transition.pm_node_indices)):
            raise ValueError("BW_layernorm parameter reduction metadata/footprint is not exact")

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
            or tuple(sm_node.outs) != (output.sm_tid, gamma_output.sm_tid, beta_output.sm_tid)):
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
                or tuple(node.outs) != (output.pm_tids[rank], gamma_output.pm_tids[rank],
                                        beta_output.pm_tids[rank])):
            raise ValueError("BW_layernorm dX PM writer roles/order are not exact")

    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    sm_final_name, pm_final_name = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"@[irreducible] private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store",
        "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node, slot):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        projection = (".1", ".2.1", ".2.2")[slot]
        apply_lemma = ("applyNode_bw_layernorm_dx_out", "applyNode_bw_layernorm_dw_out",
                       "applyNode_bw_layernorm_db_out")[slot]
        side_conditions = ("", " (by native_decide)",
                           " (by native_decide) (by native_decide)")[slot]
        expression = (
            f"(bw_layernorm ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
            f"({{store}} {node.ins[2]}) ({{store}} {node.ins[3]})){projection}"
        )
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[slot]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[slot], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact {apply_lemma} {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.ins[2]} {node.ins[3]} "
                f"{node.outs[0]} {node.outs[1]} {node.outs[2]}{side_conditions}",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helpers = [writer(
        ("hSmDx", "hSmDgamma", "hSmDbeta")[slot], ir.sm_graph_ref, "smStore",
        sm_final_name, sm_nodes_name, sm_frame,
        transition.sm_node_indices[0] - sm_start, sm_node, slot,
    ) for slot in range(3)]
    pm_helpers = [[
        writer(
            f"hPm{('Dx','Dgamma','Dbeta')[slot]}{rank}", ir.pm_graph_ref, "pmStore",
            pm_final_name, pm_nodes_name, pm_frame, index - pm_start, node, slot,
        )
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
    ] for slot in range(3)]

    lines.extend([
        f"private theorem {segment_id}_dx_shape (g x w b : Tensor) (s : Nat)",
        "    (hx : x.shape = [1, s, 32]) :",
        "    (bw_layernorm g x w b).1.shape = [1, s, 32] := by",
        "  calc",
        "    (bw_layernorm g x w b).1.shape = x.shape :=",
        "      bw_layernorm_dx_shape g x w b 32 [s, 1] (by rw [hx]; rfl)",
        "    _ = [1, s, 32] := hx",
        "",
    ])

    glist = "[" + ", ".join(f"pmFinal {tid}" for tid in gradient.pm_tids) + "]"
    xlist = "[" + ", ".join(f"pmFinal {tid}" for tid in activation.pm_tids) + "]"
    olist = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]"
    gamma_olist = "[" + ", ".join(f"pmFinal {tid}" for tid in gamma_output.pm_tids) + "]"
    beta_olist = "[" + ", ".join(f"pmFinal {tid}" for tid in beta_output.pm_tids) + "]"
    full_shape = _shape_text(list(output.full_shape))
    shard_shape = _shape_text(list(output.shard_shape))
    param_shape = _shape_text([32])
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_dx_semantic (smFinal pmFinal : Store)",
        f"    (hg : ShardedRel (smFinal {gradient.sm_tid}) {glist} 1 {full_shape} {shard_shape})",
        f"    (hx : ShardedRel (smFinal {activation.sm_tid}) {xlist} 1 {full_shape} {shard_shape})",
        f"    (hgamma : ShardedRel (smFinal {gamma.sm_tid}) [pmFinal {gamma.pm_tids[0]}] 0 {param_shape} {param_shape})",
        f"    (hbeta : ShardedRel (smFinal {beta.sm_tid}) [pmFinal {beta.pm_tids[0]}] 0 {param_shape} {param_shape})",
        f"    (hSm : smFinal {output.sm_tid} = (bw_layernorm (smFinal {gradient.sm_tid})",
        f"      (smFinal {activation.sm_tid}) (smFinal {gamma.sm_tid}) (smFinal {beta.sm_tid})).1)",
    ])
    for rank in range(k):
        lines.extend([
            f"    (hPm{rank} : pmFinal {output.pm_tids[rank]} =",
            f"      (bw_layernorm (pmFinal {gradient.pm_tids[rank]}) (pmFinal {activation.pm_tids[rank]})",
            f"        (pmFinal {gamma.pm_tids[0]}) (pmFinal {beta.pm_tids[0]})).1)",
        ])
    lines.extend([
        f"    : {output.fact_id}.Holds smFinal pmFinal := by",
        f"  have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 1 4 0 {glist} := by",
        "    simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"  have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN 1 4 0 {xlist} := by",
        "    simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"  have hGammaValue : smFinal {gamma.sm_tid} = pmFinal {gamma.pm_tids[0]} := by",
        "    rw [hgamma.full_value]", "    simpa only [List.length_cons, List.length_nil] using",
        f"      (allGatherPrimDimN_singleton_eq 0 (pmFinal {gamma.pm_tids[0]}) (by",
        f"        rw [hgamma.shard_shapes (pmFinal {gamma.pm_tids[0]}) (by simp)]; decide))",
        f"  have hBetaValue : smFinal {beta.sm_tid} = pmFinal {beta.pm_tids[0]} := by",
        "    rw [hbeta.full_value]", "    simpa only [List.length_cons, List.length_nil] using",
        f"      (allGatherPrimDimN_singleton_eq 0 (pmFinal {beta.pm_tids[0]}) (by",
        f"        rw [hbeta.shard_shapes (pmFinal {beta.pm_tids[0]}) (by simp)]; decide))",
    ])
    for rank in range(k):
        lines.extend([
            f"  have hgShape{rank} := hg.shard_shapes (pmFinal {gradient.pm_tids[rank]}) (by simp)",
            f"  have hxShape{rank} := hx.shard_shapes (pmFinal {activation.pm_tids[rank]}) (by simp)",
            f"  have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard_shape} := by",
            f"    rw [hPm{rank}]", f"    exact {segment_id}_dx_shape _ _ _ _ 2 hxShape{rank}",
        ])
    lines.extend([
        f"  have hComm := {theorem} 4 1 2 32",
        f"    {glist} {xlist} (pmFinal {gamma.pm_tids[0]}) (pmFinal {beta.pm_tids[0]})",
        "    (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)",
        "    (by simp [" + ", ".join(f"hgShape{r}" for r in range(k)) + "])",
        "    (by simp [" + ", ".join(f"hxShape{r}" for r in range(k)) + "])",
        f"  have hValue : smFinal {output.sm_tid} = allGatherPrimDimN 1 4 0 {olist} := by",
        "    rw [hSm, hgValue, hxValue, hGammaValue, hBetaValue, hComm]",
        "    simp only [List.zipWith]",
        "    rw [" + ", ".join(f"← hPm{rank}" for rank in range(k)) + "]",
        f"  have hValueList : smFinal {output.sm_tid} = allGatherPrimDimN 1 {olist}.length 0 {olist} := by",
        "    simpa only [List.length_cons, List.length_nil] using hValue",
        f"  have hFull : (smFinal {output.sm_tid}).shape = {full_shape} := by",
        "    rw [hSm]", f"    exact {segment_id}_dx_shape _ _ _ _ 8 hx.full_shape",
        f"  change ShardedRel (smFinal {output.sm_tid}) {olist} 1 {full_shape} {shard_shape}",
        "  refine {", "    full_value := hValueList", "    full_shape := hFull",
        "    shards_nonempty := by simp", "    gather_dim_lt := by decide",
        "    shard_shapes := ?_", "    shape_contract := ?_", "  }",
        "  · intro shard hmem", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "    rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend(["    · subst shard", f"      exact hOutShape{rank}"])
    lines.extend(["  · simp only [List.length_cons, List.length_nil]", "    native_decide", ""])

    def emit_param_semantic_helper(projection, name, param_output, param_list, shape_prefix):
        param_transition, _ = param_certificates[projection]
        sm_projection = ".2.1" if projection == ".2.1" else ".2.2"
        lines.extend([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {segment_id}_{name}_semantic (smFinal pmFinal : Store)",
            f"    (hg : ShardedRel (smFinal {gradient.sm_tid}) {glist} 1 {full_shape} {shard_shape})",
            f"    (hx : ShardedRel (smFinal {activation.sm_tid}) {xlist} 1 {full_shape} {shard_shape})",
            f"    (hgamma : ShardedRel (smFinal {gamma.sm_tid}) [pmFinal {gamma.pm_tids[0]}] 0 {param_shape} {param_shape})",
            f"    (hbeta : ShardedRel (smFinal {beta.sm_tid}) [pmFinal {beta.pm_tids[0]}] 0 {param_shape} {param_shape})",
            f"    (hSm : smFinal {param_output.sm_tid} = (bw_layernorm (smFinal {gradient.sm_tid})",
            f"      (smFinal {activation.sm_tid}) (smFinal {gamma.sm_tid}) (smFinal {beta.sm_tid})){sm_projection})",
        ])
        for rank in range(k):
            lines.extend([
                f"    (hPm{rank} : pmFinal {param_output.pm_tids[rank]} =",
                f"      (bw_layernorm (pmFinal {gradient.pm_tids[rank]}) (pmFinal {activation.pm_tids[rank]})",
                f"        (pmFinal {gamma.pm_tids[0]}) (pmFinal {beta.pm_tids[0]})){sm_projection})",
            ])
        lines.extend([
            f"    : {param_output.fact_id}.Holds smFinal pmFinal := by",
            f"  have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 1 4 0 {glist} := by",
            "    simpa only [List.length_cons, List.length_nil] using hg.full_value",
            f"  have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN 1 4 0 {xlist} := by",
            "    simpa only [List.length_cons, List.length_nil] using hx.full_value",
            f"  have hGammaValue : smFinal {gamma.sm_tid} = pmFinal {gamma.pm_tids[0]} := by",
            "    rw [hgamma.full_value]", "    simpa only [List.length_cons, List.length_nil] using",
            f"      (allGatherPrimDimN_singleton_eq 0 (pmFinal {gamma.pm_tids[0]}) (by",
            f"        rw [hgamma.shard_shapes (pmFinal {gamma.pm_tids[0]}) (by simp)]; decide))",
            f"  have hBetaValue : smFinal {beta.sm_tid} = pmFinal {beta.pm_tids[0]} := by",
            "    rw [hbeta.full_value]", "    simpa only [List.length_cons, List.length_nil] using",
            f"      (allGatherPrimDimN_singleton_eq 0 (pmFinal {beta.pm_tids[0]}) (by",
            f"        rw [hbeta.shard_shapes (pmFinal {beta.pm_tids[0]}) (by simp)]; decide))",
        ])
        for rank in range(k):
            lines.extend([
                f"  have hgShape{rank} := hg.shard_shapes (pmFinal {gradient.pm_tids[rank]}) (by simp)",
                f"  have hxShape{rank} := hx.shard_shapes (pmFinal {activation.pm_tids[rank]}) (by simp)",
                f"  have hPieceShape{rank} : (pmFinal {param_output.pm_tids[rank]}).shape = {param_shape} := by",
                f"    rw [hPm{rank}]",
                ((f"    rw [bw_layernorm_dw_shape _ _ _ _ 32 [2, 1] (by rw [hxShape{rank}]; decide)]")
                 if projection == ".2.1" else
                 (f"    rw [bw_layernorm_db_shape _ _ _ _ 32 [2, 1] (by rw [hxShape{rank}]; decide)]")),
                (("    exact hgamma.shard_shapes _ (by simp)") if projection == ".2.1"
                 else ("    exact hbeta.shard_shapes _ (by simp)")),
            ])
        lines.extend([
            f"  have hComm := {param_transition.lean_theorem}",
            *(f"    (pmFinal {tid})" for tid in gradient.pm_tids),
            *(f"    (pmFinal {tid})" for tid in activation.pm_tids),
            f"    (pmFinal {gamma.pm_tids[0]}) (pmFinal {beta.pm_tids[0]})",
            *(f"    hgShape{rank}" for rank in range(k)),
            *(f"    hxShape{rank}" for rank in range(k)),
            ("    (hgamma.shard_shapes _ (by simp))" if projection == ".2.1"
             else "    (hbeta.shard_shapes _ (by simp))"),
            f"  have hValue : smFinal {param_output.sm_tid} = tensorSum {param_list} := by",
            "    rw [hSm, hgValue, hxValue, hGammaValue, hBetaValue, hComm]",
            "    rw [" + ", ".join(f"← hPm{rank}" for rank in range(k)) + "]",
            f"  have hValueReduce : smFinal {param_output.sm_tid} = allReducePrim {param_list}.length 0 {param_list} := by",
            "    rw [hValue]", "    rfl",
            f"  have hFull : (smFinal {param_output.sm_tid}).shape = {param_shape} := by",
            "    rw [hSm]",
            (("    rw [bw_layernorm_dw_shape _ _ _ _ 32 [8, 1] (by rw [hx.full_shape]; decide)]")
             if projection == ".2.1" else
             ("    rw [bw_layernorm_db_shape _ _ _ _ 32 [8, 1] (by rw [hx.full_shape]; decide)]")),
            (("    exact hgamma.full_shape") if projection == ".2.1" else ("    exact hbeta.full_shape")),
            f"  change ReductionRel (smFinal {param_output.sm_tid}) {param_list} {param_shape}",
            "  refine {", "    full_value := hValueReduce", "    full_shape := hFull",
            "    contributions_nonempty := by simp", "    contribution_shapes := ?_",
            "    reduced_shape := ?_", "  }", "  · intro contribution hmem",
            "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            "    rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
        ])
        for rank in range(k):
            lines.extend(["    · subst contribution", f"      exact hPieceShape{rank}"])
        lines.extend(["  · rw [← hValueReduce]", "    exact hFull", ""])

    emit_param_semantic_helper(".2.1", "dgamma", gamma_output, gamma_olist, "hDgammaShape")
    emit_param_semantic_helper(".2.2", "dbeta", beta_output, beta_olist, "hDbetaShape")
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
        f"    have hgamma : {gamma.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {gamma.sm_tid}) [pmFinal {gamma.pm_tids[0]}] 0 {param_shape} {param_shape} at hgamma",
        f"    have hbeta : {beta.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {beta.sm_tid}) [pmFinal {beta.pm_tids[0]}] 0 {param_shape} {param_shape} at hbeta",
        f"    have hSmWriter : smFinal {sm_node.outs[0]} =",
        f"        (bw_layernorm (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]})",
        f"          (smFinal {sm_node.ins[2]}) (smFinal {sm_node.ins[3]})).1 :=",
        f"      {sm_helpers[0]} smStore",
        f"    have hSmDgamma : smFinal {sm_node.outs[1]} =",
        f"        (bw_layernorm (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]})",
        f"          (smFinal {sm_node.ins[2]}) (smFinal {sm_node.ins[3]})).2.1 :=",
        f"      {sm_helpers[1]} smStore",
        f"    have hSmDbeta : smFinal {sm_node.outs[2]} =",
        f"        (bw_layernorm (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]})",
        f"          (smFinal {sm_node.ins[2]}) (smFinal {sm_node.ins[3]})).2.2 :=",
        f"      {sm_helpers[2]} smStore",
    ])
    for rank, node in enumerate(pm_nodes):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {node.outs[0]} =",
            f"        (bw_layernorm (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]})",
            f"          (pmFinal {node.ins[2]}) (pmFinal {node.ins[3]})).1 :=",
            f"      {pm_helpers[0][rank]} pmStore",
            f"    have hPmDgamma{rank} : pmFinal {node.outs[1]} =",
            f"        (bw_layernorm (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]})",
            f"          (pmFinal {node.ins[2]}) (pmFinal {node.ins[3]})).2.1 :=",
            f"      {pm_helpers[1][rank]} pmStore",
            f"    have hPmDbeta{rank} : pmFinal {node.outs[2]} =",
            f"        (bw_layernorm (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]})",
            f"          (pmFinal {node.ins[2]}) (pmFinal {node.ins[3]})).2.2 :=",
            f"      {pm_helpers[2][rank]} pmStore",
        ])
    lines.extend([
        f"    have hout := {segment_id}_dx_semantic smFinal pmFinal hg hx hgamma hbeta",
        "      hSmWriter " + " ".join(f"hPmWriter{rank}" for rank in range(k)),
        f"    have houtDgamma := {segment_id}_dgamma_semantic smFinal pmFinal hg hx hgamma hbeta",
        "      hSmDgamma " + " ".join(f"hPmDgamma{rank}" for rank in range(k)),
        f"    have houtDbeta := {segment_id}_dbeta_semantic smFinal pmFinal hg hx hgamma hbeta",
        "      hSmDbeta " + " ".join(f"hPmDbeta{rank}" for rank in range(k)),
        "    intro fact hfact",
        f"    have covered : fact ∈ [{output.fact_id}, {gamma_output.fact_id}, {beta_output.fact_id}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{output.fact_id}, {gamma_output.fact_id}, {beta_output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl | rfl | rfl", "      · exact hout",
        "      · exact houtDgamma", "      · exact houtDbeta", "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    have h := {segment_id}_sound smStore pmStore hstate",
        f"    unfold {sm_final_name} {pm_final_name} at h",
        "    exact h", "",
    ])
    return "\n".join(lines)
