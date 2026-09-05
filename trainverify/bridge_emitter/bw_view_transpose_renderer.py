"""Atomic cross-axis renderer for independent joined BW_view and K-rank transpose."""
from __future__ import annotations


def render_closed_bw_view_transpose_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import JoinedBWViewCertificate, KRankTransposeRelationCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import JoinedBWViewCertificate, KRankTransposeRelationCertificate

    vrule = "bw-view-joined"
    trule = "transpose-sharded-k-rank"
    vtheorem = "TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view"
    allowed_transpose = {
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4",
    }
    chain = relation.dependent_chain_plan
    seg = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if seg is None or len(seg.transition_ids) != 2:
        raise ValueError("BW_view/transpose requires two atomic transitions")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    transitions = tuple(by_id[x] for x in seg.transition_ids)
    if tuple(t.rule_id for t in transitions) != (vrule, trule):
        raise ValueError("BW_view/transpose family order is not exact")
    view, transpose = transitions
    if view.lean_theorem != vtheorem or transpose.lean_theorem not in allowed_transpose:
        raise ValueError("BW_view/transpose theorem identity is not checked")
    vc = _select_exact_typed_certificate(
        relation, view, vrule, vtheorem, JoinedBWViewCertificate,
        lambda c: ((c.input_fact,), (c.output_fact,)),
    )
    tc = _select_exact_typed_certificate(
        relation, transpose, trule, transpose.lean_theorem,
        KRankTransposeRelationCertificate,
        lambda c: ((c.input_fact,), (c.output_fact,)),
    )
    records = {r.source: r for r in chain.relation_facts}
    vi, vo = records[vc.input_fact], records[vc.output_fact]
    ti, to = records[tc.input_fact], records[tc.output_fact]
    states = {s.state_id: s for s in chain.states}
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if not {vi.fact_id, ti.fact_id} <= set(before.fact_ids):
        raise ValueError("BW_view/transpose pre-facts are not live")
    if not {vo.fact_id, to.fact_id} <= set(after.fact_ids):
        raise ValueError("BW_view/transpose post-facts are not live")
    if not set(after.fact_ids) <= set(before.fact_ids) | {vo.fact_id, to.fact_id}:
        raise ValueError("BW_view/transpose post-state introduces an unproved fact")
    if (vi.kind != "joined" or vo.kind != "joined" or vi.pm_tids or vo.pm_tids
            or vi.joined_pm_tid is None or vo.joined_pm_tid is None
            or ti.kind != "sharded" or to.kind != "sharded"):
        raise ValueError("BW_view/transpose relation kinds are not exact")
    k = int(tc.rank_count)
    if k <= 0 or len(ti.pm_tids) != k or len(to.pm_tids) != k or ir.pm_num_ranks != k:
        raise ValueError("BW_view/transpose rank authority is malformed")

    ss, se = seg.sm_range; ps, pe = seg.pm_range
    sf = list(ir.sm_nodes[ss:se]); pf = list(ir.pm_nodes[ps:pe])
    if (len(view.sm_node_indices) != 1 or len(view.pm_node_indices) != 1
            or len(transpose.sm_node_indices) != 1 or len(transpose.pm_node_indices) != k):
        raise ValueError("BW_view/transpose semantic footprint is malformed")
    vsi, vpi = view.sm_node_indices[0], view.pm_node_indices[0]
    tsi, tpis = transpose.sm_node_indices[0], tuple(transpose.pm_node_indices)
    if set((vsi, tsi)) != set(range(ss, se)) or not ({vpi} | set(tpis)) <= set(range(ps, pe)):
        raise ValueError("BW_view/transpose writers are outside the full frame")
    vnsm, vnpm = ir.sm_nodes[vsi], ir.pm_nodes[vpi]
    tnsm, tnpm = ir.sm_nodes[tsi], tuple(ir.pm_nodes[i] for i in tpis)
    target = tuple(vc.target_shape)
    if (vc.sm_step_id != f"sm:{vsi}:0" or vc.pm_step_id != f"pm:{vpi}:0"
            or vnsm.op != "BW_view" or vnpm.op != "BW_view"
            or vnsm.ins[0] != vi.sm_tid or vnpm.ins[0] != vi.joined_pm_tid
            or vnsm.outs != [vo.sm_tid] or vnpm.outs != [vo.joined_pm_tid]
            or tuple(vnsm.params or ()) != target or tuple(vnpm.params or ()) != target):
        raise ValueError("joined BW_view writer authority is malformed")
    if (tc.sm_step_id != f"sm:{tsi}:0"
            or tuple(tc.pm_step_ids) != tuple(f"pm:{i}:0" for i in tpis)
            or tuple(n.rank for n in tnpm) != tuple(range(k))
            or tnsm.op not in ("FW_transpose", "BW_transpose")
            or any(n.op != tnsm.op for n in tnpm)
            or tuple(tnsm.params or ()) != tuple(tc.parameters)
            or any(tuple(n.params or ()) != tuple(tc.parameters) for n in tnpm)
            or tnsm.ins[0] != ti.sm_tid or tnsm.outs != [to.sm_tid]
            or tuple(n.ins[0] for n in tnpm) != tuple(ti.pm_tids)
            or tuple(n.outs[0] for n in tnpm) != tuple(to.pm_tids)):
        raise ValueError("transpose writer authority is malformed")

    smn, pmn = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    smf, pmf = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sf)}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pf)}]",
        f"@[irreducible] private def {smf} (z : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z",
        f"@[irreducible] private def {pmf} (z : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z",
        "",
    ]

    def helper(name, side, node, index, kind):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        initial = "smStore" if side == "sm" else "pmStore"
        fn = smf if side == "sm" else pmf
        nn = smn if side == "sm" else pmn
        frame = sf if side == "sm" else pf
        start = ss if side == "sm" else ps
        final = f"({fn} {initial})"
        if kind == "view":
            shape = _shape_text(list(target))
            expr = f"fw_view {shape} ({{store}} {node.ins[0]})"
            apply = f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.ins[1]} {node.outs[0]}"
        else:
            expr = f"transposeAxes {node.params[0]} {node.params[1]} ({{store}} {node.ins[0]})"
            if node.op == "FW_transpose":
                apply = f"exact applyNode_fw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {node.params[0]} {node.params[1]}"
            else:
                apply = f"exact applyNode_bw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]} {node.params[0]} {node.params[1]}"
        th = f"{segment_id}_{name}"
        lines.extend([
            f"private theorem {th} ({initial} : Store) : {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {fn}; rfl",
        ])
        body = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nn, nodes=frame, position=index-start,
            output_tid=node.outs[0], input_tids=(node.ins[0],),
            written_tids={u for n in frame for u in n.outs}, expression=expr,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]", apply,
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in body)
        lines.extend(["  exact hout", ""])
        return th

    hvs = helper("hViewSm", "sm", vnsm, vsi, "view")
    hvp = helper("hViewPm", "pm", vnpm, vpi, "view")
    hts = helper("hTransposeSm", "sm", tnsm, tsi, "transpose")
    htp = [helper(f"hTransposePm{r}", "pm", n, i, "transpose") for r, (i, n) in enumerate(zip(tpis, tnpm))]
    til = "[" + ", ".join(f"pmFinal {u}" for u in ti.pm_tids) + "]"
    tol = "[" + ", ".join(f"pmFinal {u}" for u in to.pm_tids) + "]"
    symbolic = [str(x) for x in ti.shard_shape]
    symbolic[ti.gather_dim] = f"{ti.shard_shape[ti.gather_dim]} * {til}.length"
    symbolic = "[" + ", ".join(symbolic) + "]"
    vin, vout = _shape_text(list(vi.full_shape)), _shape_text(list(vo.full_shape))
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  let smFinal := {smf} smStore",
        f"  let pmFinal := {pmf} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
        f"  have hvi : {vi.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change smFinal {vi.sm_tid} = pmFinal {vi.joined_pm_tid} ∧ (smFinal {vi.sm_tid}).shape = {vin} ∧ (pmFinal {vi.joined_pm_tid}).shape = {vin} at hvi",
        f"  have hti : {ti.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {ti.sm_tid}) {til} {ti.gather_dim} {symbolic} {_shape_text(list(ti.shard_shape))} at hti",
        f"  have hvs := {hvs} smStore",
        f"  have hvp := {hvp} pmStore",
        f"  change smFinal {vo.sm_tid} = fw_view {vout} (smFinal {vi.sm_tid}) at hvs",
        f"  change pmFinal {vo.joined_pm_tid} = fw_view {vout} (pmFinal {vi.joined_pm_tid}) at hvp",
        f"  have houtV : {vo.fact_id}.Holds smFinal pmFinal := by",
        f"    change smFinal {vo.sm_tid} = pmFinal {vo.joined_pm_tid} ∧ (smFinal {vo.sm_tid}).shape = {vout} ∧ (pmFinal {vo.joined_pm_tid}).shape = {vout}",
        "    rw [hvs, hvp]",
        f"    exact JoinedRel.fw_view {vout} {vin} hvi",
        f"  have hts := {hts} smStore",
        f"  change smFinal {to.sm_tid} = transposeAxes {tc.parameters[0]} {tc.parameters[1]} (smFinal {ti.sm_tid}) at hts",
    ])
    for r in range(k):
        lines.extend([
            f"  have htp{r} := {htp[r]} pmStore",
            f"  change pmFinal {to.pm_tids[r]} = transposeAxes {tc.parameters[0]} {tc.parameters[1]} (pmFinal {ti.pm_tids[r]}) at htp{r}",
        ])
    lines.extend([
        f"  have ht := {tc.lean_theorem} hti",
        f"  have houtT : {to.fact_id}.Holds smFinal pmFinal := by",
        f"    change ShardedRel (smFinal {to.sm_tid}) {tol} {to.gather_dim} {_shape_text(list(to.full_shape))} {_shape_text(list(to.shard_shape))}",
        f"    rw [hts, {', '.join(f'htp{r}' for r in range(k))}]",
        "    simpa using ht",
        "  intro fact hfact",
        f"  have covered : fact ∈ [{vo.fact_id}, {to.fact_id}] ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ [{vo.fact_id}, {to.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered",
        "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "    rcases fresh with rfl | rfl",
        "    · exact houtV",
        "    · exact houtT",
        "  · exact hframe fact old",
        "",
        "set_option maxRecDepth 32768 in",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {smn}",
        f"  pmNodes := {pmn}",
        f"  sound := by intro smStore pmStore hstate; have h := {segment_id}_sound smStore pmStore hstate; unfold {smf} {pmf} at h; exact h",
        "",
    ])
    return "\n".join(lines)
