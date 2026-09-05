"""Atomic transpose -> AllToAll -> transpose cross-axis SCC renderer."""
from __future__ import annotations


def render_closed_transpose_alltoall_transpose_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import (
            KRankAllToAllRelationCertificate, KRankTransposeRelationCertificate,
        )
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import (
            KRankAllToAllRelationCertificate, KRankTransposeRelationCertificate,
        )

    trule = "transpose-sharded-k-rank"
    arule = "alltoall-k-rank-layout-transport"
    atheorem = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    allowed_transpose = {
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4",
        "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4",
    }
    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("transpose/AllToAll/transpose requires one complete segment")
    segment = segments[0]
    by_id = {}
    for item in relation.transition_specs:
        by_id.setdefault(item.transition_id, []).append(item)
    matches = [by_id.get(tid, ()) for tid in segment.transition_ids]
    if any(len(items) != 1 for items in matches):
        raise ValueError("mixed transpose authority is missing or duplicated")
    transitions = [items[0] for items in matches]
    if tuple(t.rule_id for t in transitions) != (trule, arule, trule):
        raise ValueError("mixed transpose family order is not exact")
    first, collective, second = transitions
    if (first.lean_theorem not in allowed_transpose
            or second.lean_theorem not in allowed_transpose
            or collective.lean_theorem != atheorem):
        raise ValueError("mixed transpose theorem identity is not checked")

    cert1 = _select_exact_typed_certificate(
        relation, first, trule, first.lean_theorem,
        KRankTransposeRelationCertificate,
        lambda c: ((c.input_fact,), (c.output_fact,)),
    )
    certa = _select_exact_typed_certificate(
        relation, collective, arule, atheorem,
        KRankAllToAllRelationCertificate,
        lambda c: ((c.input_fact,), (c.output_fact,)),
    )
    cert2 = _select_exact_typed_certificate(
        relation, second, trule, second.lean_theorem,
        KRankTransposeRelationCertificate,
        lambda c: ((c.input_fact,), (c.output_fact,)),
    )
    records = {r.source: r for r in chain.relation_facts}
    if len(records) != len(chain.relation_facts):
        raise ValueError("mixed transpose relation facts are duplicated")
    try:
        p1, q1 = records[cert1.input_fact], records[cert1.output_fact]
        pa, qa = records[certa.input_fact], records[certa.output_fact]
        p2, q2 = records[cert2.input_fact], records[cert2.output_fact]
    except KeyError as exc:
        raise ValueError("mixed transpose relation fact is missing") from exc
    if qa.fact_id != p2.fact_id:
        raise ValueError("AllToAll output is not the second transpose input")
    states = {s.state_id: s for s in chain.states}
    if len(states) != len(chain.states):
        raise ValueError("mixed transpose states are duplicated")
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    before_ids, after_ids = set(before.fact_ids), set(after.fact_ids)
    if not {p1.fact_id, pa.fact_id} <= before_ids:
        raise ValueError("mixed transpose pre-facts are not live")
    proved_fresh = {q1.fact_id, qa.fact_id, q2.fact_id}
    if not after_ids <= (before_ids | proved_fresh):
        raise ValueError("mixed transpose post-state introduces an unproved fact")

    k = int(certa.rank_count)
    facts = (p1, q1, pa, qa, q2)
    if k <= 0 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("mixed transpose rank authority is malformed")
    if any(r.kind != "sharded" or len(r.pm_tids) != k for r in facts):
        raise ValueError("mixed transpose requires exact ShardedRel facts")
    if (cert1.rank_count != k or cert2.rank_count != k
            or certa.input_gather_dim != pa.gather_dim
            or certa.output_gather_dim != qa.gather_dim
            or pa.sm_tid != qa.sm_tid or pa.full_shape != qa.full_shape):
        raise ValueError("mixed transpose metadata is inconsistent")

    ss, se = segment.sm_range
    ps, pe = segment.pm_range
    sm_frame = list(ir.sm_nodes[ss:se])
    pm_frame = list(ir.pm_nodes[ps:pe])
    semantic_sm = tuple(first.sm_node_indices + second.sm_node_indices)
    semantic_pm = tuple(first.pm_node_indices + collective.pm_node_indices + second.pm_node_indices)
    if (len(first.sm_node_indices) != 1 or collective.sm_node_indices
            or len(second.sm_node_indices) != 1
            or len(first.pm_node_indices) != k
            or len(collective.pm_node_indices) != k
            or len(second.pm_node_indices) != k
            or len(set(semantic_sm)) != len(semantic_sm)
            or len(set(semantic_pm)) != len(semantic_pm)
            or set(semantic_sm) != set(range(ss, se))
            or not set(semantic_pm) <= set(range(ps, pe))):
        raise ValueError("mixed transpose semantic footprints are malformed")
    frame_pm = set(range(ps, pe)) - set(semantic_pm)
    if len(frame_pm) + len(semantic_pm) != pe - ps:
        raise ValueError("mixed transpose full PM frame is not partitioned")

    def validate_transpose(t, c, pre, post):
        sm_index = t.sm_node_indices[0]
        pm_indices = tuple(t.pm_node_indices)
        sm = ir.sm_nodes[sm_index]
        pm = tuple(ir.pm_nodes[i] for i in pm_indices)
        if (c.sm_step_id != f"sm:{sm_index}:0"
                or tuple(c.pm_step_ids) != tuple(f"pm:{i}:0" for i in pm_indices)
                or tuple(n.rank for n in pm) != tuple(range(k))
                or sm.op not in ("FW_transpose", "BW_transpose")
                or any(n.op != sm.op for n in pm)
                or tuple(sm.params or ()) != tuple(c.parameters)
                or any(tuple(n.params or ()) != tuple(c.parameters) for n in pm)
                or sm.ins[0] != pre.sm_tid or sm.outs != [post.sm_tid]
                or tuple(n.ins[0] for n in pm) != tuple(pre.pm_tids)
                or tuple(n.outs[0] for n in pm) != tuple(post.pm_tids)):
            raise ValueError("mixed transpose writer authority is malformed")
        return sm, pm

    sm1, pm1 = validate_transpose(first, cert1, p1, q1)
    sm2, pm2 = validate_transpose(second, cert2, p2, q2)
    ai = tuple(collective.pm_node_indices)
    an = tuple(ir.pm_nodes[i] for i in ai)
    if (tuple(certa.pm_step_ids) != tuple(f"pm:{i}:0" for i in ai)
            or tuple(n.rank for n in an) != tuple(range(k))
            or any(n.op != "AllToAllPrim" or tuple(n.ins) != tuple(pa.pm_tids)
                   or tuple(n.params or ()) != (certa.input_gather_dim, certa.output_gather_dim)
                   or n.outs != [qa.pm_tids[r]] for r, n in enumerate(an))):
        raise ValueError("mixed AllToAll writer authority is malformed")

    smn, pmn = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    smf, pmf = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {smf} (z : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z",
        f"@[irreducible] private def {pmf} (z : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z",
        "",
    ]
    written_sm = {tid for n in sm_frame for tid in n.outs}
    written_pm = {tid for n in pm_frame for tid in n.outs}

    def helper(name, side, node, index, kind, input_tids):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        initial = "smStore" if side == "sm" else "pmStore"
        final_def = smf if side == "sm" else pmf
        nodes_name = smn if side == "sm" else pmn
        frame = sm_frame if side == "sm" else pm_frame
        start = ss if side == "sm" else ps
        final = f"({final_def} {initial})"
        if kind == "transpose":
            expr = f"transposeAxes {node.params[0]} {node.params[1]} ({{store}} {node.ins[0]})"
            if node.op == "FW_transpose":
                apply = f"exact applyNode_fw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {node.params[0]} {node.params[1]}"
            else:
                apply = f"exact applyNode_bw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]} {node.params[0]} {node.params[1]}"
        else:
            tids = "[" + ", ".join(str(t) for t in pa.pm_tids) + "]"
            mapped = "[" + ", ".join(f"({{store}}) {tid}" for tid in pa.pm_tids) + "]"
            expr = f"allToAllPrimWithDims {graph}.numRanks {node.rank} {mapped} {certa.input_gather_dim} {certa.output_gather_dim}"
            apply = f"simpa only [List.map] using applyNode_allToAllPrimWithDims_out {graph} t {node.rank} {tids} {node.outs[0]} {certa.input_gather_dim} {certa.output_gather_dim}"
        theorem = f"{segment_id}_{name}"
        lines.extend([
            f"private theorem {theorem} ({initial} : Store) : {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {final_def}; rfl",
        ])
        body = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=index - start, output_tid=node.outs[0],
            input_tids=tuple(input_tids), written_tids=written_sm if side == "sm" else written_pm,
            expression=expr,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                apply,
            ],
        )
        lines.extend(x[2:] if x.startswith("  ") else x for x in body)
        lines.extend(["  exact hout", ""])
        return theorem

    hsm1 = helper("hTranspose1Sm", "sm", sm1, first.sm_node_indices[0], "transpose", (sm1.ins[0],))
    hpm1 = [helper(f"hTranspose1Pm{r}", "pm", n, i, "transpose", (n.ins[0],)) for r, (i, n) in enumerate(zip(first.pm_node_indices, pm1))]
    ha = [helper(f"hAllToAllPm{r}", "pm", n, i, "alltoall", tuple(pa.pm_tids)) for r, (i, n) in enumerate(zip(ai, an))]
    hsm2 = helper("hTranspose2Sm", "sm", sm2, second.sm_node_indices[0], "transpose", (sm2.ins[0],))
    hpm2 = [helper(f"hTranspose2Pm{r}", "pm", n, i, "transpose", (n.ins[0],)) for r, (i, n) in enumerate(zip(second.pm_node_indices, pm2))]

    def values(fact, store="pmFinal"):
        return "[" + ", ".join(f"{store} {t}" for t in fact.pm_tids) + "]"

    def symbolic_full(fact):
        dims = [str(x) for x in fact.shard_shape]
        dims[fact.gather_dim] = f"{fact.shard_shape[fact.gather_dim]} * {values(fact)}.length"
        return "[" + ", ".join(dims) + "]"

    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  let smFinal := {smf} smStore",
        f"  let pmFinal := {pmf} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
        f"  have hp1 : {p1.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {p1.sm_tid}) {values(p1)} {p1.gather_dim} {symbolic_full(p1)} {_shape_text(list(p1.shard_shape))} at hp1",
        f"  have hpa : {pa.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change ShardedRel (smFinal {pa.sm_tid}) {values(pa)} {pa.gather_dim} {symbolic_full(pa)} {_shape_text(list(pa.shard_shape))} at hpa",
        f"  have hw1s := {hsm1} smStore",
        f"  change smFinal {q1.sm_tid} = transposeAxes {cert1.parameters[0]} {cert1.parameters[1]} (smFinal {p1.sm_tid}) at hw1s",
    ])
    for r in range(k):
        lines.extend([
            f"  have hw1p{r} := {hpm1[r]} pmStore",
            f"  change pmFinal {q1.pm_tids[r]} = transposeAxes {cert1.parameters[0]} {cert1.parameters[1]} (pmFinal {p1.pm_tids[r]}) at hw1p{r}",
        ])
    lines.extend([
        f"  have ht1 := {cert1.lean_theorem} hp1",
        f"  have hout1 : {q1.fact_id}.Holds smFinal pmFinal := by",
        f"    change ShardedRel (smFinal {q1.sm_tid}) {values(q1)} {q1.gather_dim} {_shape_text(list(q1.full_shape))} {_shape_text(list(q1.shard_shape))}",
        f"    rw [hw1s, {', '.join(f'hw1p{r}' for r in range(k))}]",
        "    simpa using ht1",
    ])
    for r in range(k):
        lines.extend([
            f"  have hwa{r} := {ha[r]} pmStore",
            f"  change pmFinal {qa.pm_tids[r]} = allToAllPrimWithDims {k} {r} {values(pa)} {certa.input_gather_dim} {certa.output_gather_dim} at hwa{r}",
        ])
    in_shape = _shape_text(list(pa.shard_shape)); out_shape = _shape_text(list(qa.shard_shape)); full_shape = _shape_text(list(pa.full_shape))
    lines.extend([
        f"  have hHead : (({values(pa)}.head?.map (fun t => t.shape)).getD []) = {in_shape} := by",
        f"    exact hpa.shard_shapes _ (by simp)",
        f"  have hpaValue : smFinal {pa.sm_tid} = allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)} := by simpa only [List.length_cons, List.length_nil] using hpa.full_value",
        f"  have hGatherShape : (allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)}).shape = {full_shape} := by",
        f"    rw [← hpaValue]; exact hpa.full_shape",
        f"  have hOdim : {qa.gather_dim} < (allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)}).shape.length := by rw [hGatherShape]; native_decide",
        f"  have hDiv : (allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)}).shape.getD {qa.gather_dim} 0 % {k} = 0 := by rw [hGatherShape]; native_decide",
    ])
    for r in range(k):
        lines.extend([
            f"  have hAShape{r} : (pmFinal {qa.pm_tids[r]}).shape = {out_shape} := by",
            f"    rw [hwa{r}, allToAllPrimWithDims_shape {k} {r} {values(pa)} {pa.gather_dim} {qa.gather_dim} {in_shape} hHead (by native_decide)]",
            "    native_decide",
        ])
    lines.extend([
        f"  have hOrdered : {values(qa)} = List.ofFn (fun r : Fin {k} => allToAllPrimWithDims {k} r.1 {values(pa)} {pa.gather_dim} {qa.gather_dim}) := by",
        f"    rw [{', '.join(f'hwa{r}' for r in range(k))}]",
        "    rfl",
        f"  have hcomm := {atheorem} {pa.gather_dim} {qa.gather_dim} {values(pa)} (by simp) hOdim hDiv",
        f"  have hcommExact : allGatherPrimDimN {qa.gather_dim} {values(qa)}.length 0 {values(qa)} = allGatherPrimDimN {pa.gather_dim} {k} 0 {values(pa)} := by",
        "    rw [hOrdered]",
        "    simpa only [List.length_cons, List.length_nil, List.length_ofFn] using hcomm",
        f"  have houtA : {qa.fact_id}.Holds smFinal pmFinal := by",
        f"    change ShardedRel (smFinal {qa.sm_tid}) {values(qa)} {qa.gather_dim} {full_shape} {out_shape}",
        "    refine { full_value := ?_, full_shape := hpa.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide }",
        "    · rw [hcommExact]",
        "      exact hpaValue",
        "    · intro shard hmem",
        "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        f"      rcases hmem with {' | '.join(f'h{r}' for r in range(k))}",
    ])
    for r in range(k):
        lines.extend(["      · subst shard", f"        exact hAShape{r}"])
    lines.extend([
        f"  have hw2s := {hsm2} smStore",
        f"  change smFinal {q2.sm_tid} = transposeAxes {cert2.parameters[0]} {cert2.parameters[1]} (smFinal {p2.sm_tid}) at hw2s",
    ])
    for r in range(k):
        lines.extend([
            f"  have hw2p{r} := {hpm2[r]} pmStore",
            f"  change pmFinal {q2.pm_tids[r]} = transposeAxes {cert2.parameters[0]} {cert2.parameters[1]} (pmFinal {p2.pm_tids[r]}) at hw2p{r}",
        ])
    lines.extend([
        f"  change ShardedRel (smFinal {p2.sm_tid}) {values(p2)} {p2.gather_dim} {symbolic_full(p2)} {_shape_text(list(p2.shard_shape))} at houtA",
        f"  have ht2 := {cert2.lean_theorem} houtA",
        f"  have hout2 : {q2.fact_id}.Holds smFinal pmFinal := by",
        f"    change ShardedRel (smFinal {q2.sm_tid}) {values(q2)} {q2.gather_dim} {_shape_text(list(q2.full_shape))} {_shape_text(list(q2.shard_shape))}",
        f"    rw [hw2s, {', '.join(f'hw2p{r}' for r in range(k))}]",
        "    simpa using ht2",
        "  intro fact hfact",
        f"  have covered : fact ∈ [{q1.fact_id}, {qa.fact_id}, {q2.fact_id}] ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ [{q1.fact_id}, {qa.fact_id}, {q2.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered",
        "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "    rcases fresh with rfl | rfl | rfl",
        "    · exact hout1",
        "    · exact houtA",
        "    · exact hout2",
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
