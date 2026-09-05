"""Heartbeat-safe sparse/full-frame output-sharded linear renderer."""
from __future__ import annotations


def render_closed_sparse_output_sharded_linear_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("linear-output-sharded-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next(x for x in chain.segments if x.segment_id == segment_id)
    if len(segment.transition_ids) != 1:
        raise ValueError("sparse output linear requires one transition")
    transition = next(x for x in relation.transition_specs
                      if x.transition_id == segment.transition_ids[0])
    cert = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda c: (tuple(sorted((c.activation_fact, c.weight_fact))), (c.output_fact,)),
    )
    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    activation, weight, output = (records[cert.activation_fact], records[cert.weight_fact],
                                  records[cert.output_fact])
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    k = cert.rank_count
    if (k <= 0 or cert.output_gather_dim != 2
            or activation.kind != "joined" or activation.joined_pm_tid is None
            or weight.kind != "sharded" or weight.gather_dim != 0
            or output.kind != "sharded" or output.gather_dim != 2
            or len(weight.pm_tids) != k or len(output.pm_tids) != k
            or tuple(cert.activation_shape) != tuple(activation.full_shape)
            or tuple(cert.weight_full_shape) != tuple(weight.full_shape)
            or tuple(cert.weight_shard_shape) != tuple(weight.shard_shape)
            or tuple(cert.output_full_shape) != tuple(output.full_shape)
            or tuple(cert.output_shard_shape) != tuple(output.shard_shape)):
        raise ValueError("sparse output linear relation metadata mismatch")
    sm_start, sm_end = segment.sm_range; pm_start, pm_end = segment.pm_range
    if (len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k
            or not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("sparse output linear writer/frame partition mismatch")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
    if (sm_node.op != spec.op or sm_node.rank != 0 or sm_node.params
            or tuple(node.rank for node in pm_nodes) != tuple(range(k))
            or any(node.op != spec.op or node.params for node in pm_nodes)
            or sm_node.ins != [activation.sm_tid, weight.sm_tid]
            or sm_node.outs != [output.sm_tid]
            or any(node.ins != [activation.joined_pm_tid, weight.pm_tids[r]]
                   or node.outs != [output.pm_tids[r]] for r, node in enumerate(pm_nodes))):
        raise ValueError("sparse output linear writer signatures mismatch")
    sm_frame = list(ir.sm_nodes[sm_start:sm_end]); pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    live_outputs = {output.sm_tid, *output.pm_tids}
    if any(live_outputs.intersection(node.outs) for i, node in enumerate(ir.sm_nodes)
           if sm_start <= i < sm_end and i not in transition.sm_node_indices):
        raise ValueError("sparse output linear SM frame overwrites output")
    if any(live_outputs.intersection(node.outs) for i, node in enumerate(ir.pm_nodes)
           if pm_start <= i < pm_end and i not in transition.pm_node_indices):
        raise ValueError("sparse output linear PM frame overwrites output")

    activation_shape = tuple(activation.full_shape)
    weight_full, weight_shard = tuple(weight.full_shape), tuple(weight.shard_shape)
    output_full, output_shard = tuple(output.full_shape), tuple(output.shard_shape)
    if (len(activation_shape) != 3 or len(weight_full) != 2 or len(weight_shard) != 2
            or len(output_full) != 3 or len(output_shard) != 3):
        raise ValueError("sparse output linear shape ranks mismatch")
    b, seq, inner = activation_shape; local_out = weight_shard[0]
    if (weight_shard != (local_out, inner) or weight_full != (local_out * k, inner)
            or output_shard != (b, seq, local_out)
            or output_full != (b, seq, local_out * k)):
        raise ValueError("sparse output linear shape contract mismatch")

    shape = lambda xs: _shape_text(list(xs))
    sm_nodes_name=f"{segment_id}_smNodes"; pm_nodes_name=f"{segment_id}_pmNodes"
    sm_final_name=f"{segment_id}_smFinal"; pm_final_name=f"{segment_id}_pmFinal"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", "",
    ]

    def add_writer(name, graph, initial, final_name, nodes_name, frame, pos, node):
        final=f"({final_name} {initial})"; theorem_name=f"{segment_id}_{name}"
        expr=f"fw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame, position=pos,
            output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={t for n in frame for t in n.outs}, expression=expr,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_fw_linear_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            ])
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = add_writer("smWriter", ir.sm_graph_ref, "smStore", sm_final_name,
                           sm_nodes_name, sm_frame, transition.sm_node_indices[0]-sm_start, sm_node)
    pm_helpers=[]
    for rank,(index,node) in enumerate(zip(transition.pm_node_indices,pm_nodes)):
        pm_helpers.append(add_writer(f"pmWriter{rank}", ir.pm_graph_ref, "pmStore",
                                     pm_final_name, pm_nodes_name, pm_frame, index-pm_start, node))

    pm_weights="["+", ".join(f"({pm_final_name} pmStore) {tid}" for tid in weight.pm_tids)+"]"
    pm_outputs="["+", ".join(f"({pm_final_name} pmStore) {tid}" for tid in output.pm_tids)+"]"
    lines.extend([
        f"private theorem {segment_id}_out (smStore pmStore : Store)",
        f"    (hActivation : {activation.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore))",
        f"    (hWeight : {weight.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore)) :",
        f"    {output.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  change ({sm_final_name} smStore) {activation.sm_tid} = ({pm_final_name} pmStore) {activation.joined_pm_tid} ∧",
        f"    (({sm_final_name} smStore) {activation.sm_tid}).shape = {shape(activation_shape)} ∧",
        f"    (({pm_final_name} pmStore) {activation.joined_pm_tid}).shape = {shape(activation_shape)} at hActivation",
        f"  change ShardedRel (({sm_final_name} smStore) {weight.sm_tid}) {pm_weights} 0 {shape(weight_full)} {shape(weight_shard)} at hWeight",
        f"  have hSm := {sm_helper} smStore",
    ])
    for rank,helper in enumerate(pm_helpers): lines.append(f"  have hPm{rank} := {helper} pmStore")
    lines.extend([
        f"  have hComm := ({theorem}",
        f"    (K := {pm_weights}.length) (b := {b}) (s := {seq}) (i := {inner}) (o := {local_out})",
        f"    (x := ({pm_final_name} pmStore) {activation.joined_pm_tid}) (ws := {pm_weights})",
        "    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        "    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))",
        f"  have hValue : ({sm_final_name} smStore) {output.sm_tid} = allGatherPrimDimN 2 {pm_outputs}.length 0 {pm_outputs} := by",
        "    rw [hSm, hActivation.1, hWeight.full_value, hComm]",
        "    simp only [List.map, List.length_cons, List.length_nil]",
        f"    rw [{', '.join('← hPm'+str(r) for r in range(k))}]",
    ])
    for rank,node in enumerate(pm_nodes):
        lines.extend([
            f"  have hOutShape{rank} : (({pm_final_name} pmStore) {node.outs[0]}).shape = {shape(output_shard)} := by",
            f"    rw [hPm{rank}]",
            f"    exact fw_linear_3d_shape {b} {seq} {inner} {local_out} _ _ hActivation.2.2",
            f"      (hWeight.shard_shapes (({pm_final_name} pmStore) {weight.pm_tids[rank]}) (by simp))",
        ])
    lines.extend([
        f"  unfold {output.fact_id} RelationFact.Holds",
        f"  change ShardedRel (({sm_final_name} smStore) {output.sm_tid}) {pm_outputs} 2 {shape(output_full)} {shape(output_shard)}",
        "  refine {", "    full_value := hValue", "    full_shape := ?_",
        "    shards_nonempty := by simp", "    gather_dim_lt := by native_decide",
        "    shard_shapes := ?_", "    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide", "  }",
        "  · rw [hValue]",
        f"    rw [allGatherPrimDimN_shape 2 {pm_outputs}.length {pm_outputs} {shape(output_shard)}]",
        "    · simp only [List.length_cons, List.length_nil]", "      native_decide",
        "    · simp only [List.head?, Option.map, Option.getD]", "      exact hOutShape0",
        "  · intro shard hmem", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "    rcases hmem with "+" | ".join("rfl" for _ in range(k)),
    ])
    for rank in range(k): lines.append(f"    · exact hOutShape{rank}")
    lines.append("")

    lines.extend([
        f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    unfold {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "    · native_decide", "    · native_decide", "    · native_decide", "    · native_decide",
        f"  have hActivation := hframe {activation.fact_id} (by native_decide)",
        f"  have hWeight := hframe {weight.fact_id} (by native_decide)",
        f"  have hout := {segment_id}_out smStore pmStore hActivation hWeight",
        "  intro fact hfact",
        f"  have covered : fact ∈ [{output.fact_id}] ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ [{output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered", "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh", "    rcases fresh with rfl", "    exact hout",
        "  · exact hframe fact old", "",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{sm_final_name}, {pm_final_name}] using {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
