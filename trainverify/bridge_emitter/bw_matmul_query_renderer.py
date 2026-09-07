"""Exact query-axis BW_matmul projections, one full store fold per side."""
from __future__ import annotations


def render_closed_bw_matmul_query_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import (
            KRankBWMatmulCertificate, JoinedBWViewCertificate,
            bw_matmul_query_shape_spec, get_closed_rule_spec,
        )
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import (
            KRankBWMatmulCertificate, JoinedBWViewCertificate,
            bw_matmul_query_shape_spec, get_closed_rule_spec,
        )
    rules = {
        "bw-matmul-fst-query-sharded-k-rank": (0, "fst-query-sharded"),
        "bw-matmul-snd-contraction-reduction-k-rank": (1, "snd-contraction-reduction"),
    }
    chain = relation.dependent_chain_plan
    seg = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if seg is None or not 1 <= len(seg.transition_ids) <= 3:
        raise ValueError("BW_matmul query requires one projection or a pair with optional view")
    tm = {t.transition_id: t for t in relation.transition_specs}
    ts = tuple(tm[i] for i in seg.transition_ids)
    families = tuple(t.rule_id for t in ts)
    if (len(set(families)) != len(families) or not set(families) <= {*rules, "bw-view-joined"}
            or not set(families) & rules.keys()
            or "bw-view-joined" in families and not rules.keys() <= set(families)):
        raise ValueError("BW_matmul query transition family mismatch")
    selected = []
    for t in ts:
        if t.rule_id not in rules:
            continue
        slot, family = rules[t.rule_id]
        theorem = get_closed_rule_spec(t.rule_id).lean_theorems[0]
        c = _select_exact_typed_certificate(relation, t, t.rule_id, theorem,
            KRankBWMatmulCertificate, lambda c: (tuple(sorted(c.input_facts)), (c.output_fact,)))
        if c.projection != f".{slot+1}" or c.family != family or len(c.input_facts) != 3:
            raise ValueError("BW_matmul query projection/family mismatch")
        selected.append((t, c, slot))
    first, cert, _ = selected[0]
    records = {r.source: r for r in chain.relation_facts}
    try:
        g, x, y = (records[f] for f in cert.input_facts)
        outputs = [(t, c, slot, records[c.output_fact]) for t, c, slot in selected]
    except KeyError as exc:
        raise ValueError("BW_matmul query missing materialized fact") from exc
    k = cert.rank_count
    if (type(k) is not int or k <= 0
            or any(r.kind != "sharded" or r.gather_dim != 2 or len(r.pm_tids) != k
                   or r.source.layout != "sharded" or r.source.gather_dim != 2
                   or r.joined_pm_tid is not None for r in (g, x))
            or y.source.layout != "joined" or y.source.gather_dim is not None
            or y.kind != "joined" or y.pm_tids or y.joined_pm_tid is None):
        raise ValueError("BW_matmul query input metadata mismatch")
    ss, se = seg.sm_range; ps, pe = seg.pm_range
    if (len(first.sm_node_indices) != 1 or len(first.pm_node_indices) != k
            or len(set(first.pm_node_indices)) != k
            or not set(first.sm_node_indices) <= set(range(ss, se))
            or not set(first.pm_node_indices) <= set(range(ps, pe))):
        raise ValueError("BW_matmul query writer footprint mismatch")
    mi = first.sm_node_indices[0]; pis = first.pm_node_indices
    sm = ir.sm_nodes[mi]; pms = tuple(ir.pm_nodes[i] for i in pis)
    if (type(sm.rank) is not int or sm.rank != 0
            or any(type(p.rank) is not int for p in pms)
            or tuple(p.rank for p in pms) != tuple(range(k))
            or any(n.op != "BW_matmul" or n.params or len(n.ins) != 3
                   or len(n.outs) != 2 or len(set(n.outs)) != 2 for n in (sm, *pms))
            or tuple(sm.ins) != (g.sm_tid, x.sm_tid, y.sm_tid)
            or tuple(tuple(p.ins) for p in pms) != tuple(
                (g.pm_tids[r], x.pm_tids[r], y.joined_pm_tid) for r in range(k))):
        raise ValueError("BW_matmul query writer syntax/roles mismatch")
    for t, c, slot, out in outputs:
        if (c.rank_count != k or c.input_facts != cert.input_facts
                or t.sm_node_indices != first.sm_node_indices or t.pm_node_indices != pis
                or c.sm_step_id != f"sm:{mi}:{slot}"
                or c.pm_step_ids != tuple(f"pm:{i}:{slot}" for i in pis)
                or c.output_fact.step_triple != (c.sm_step_id, *c.pm_step_ids)
                or c.output_fact.layout != out.kind or c.output_fact.gather_dim != out.gather_dim
                or len(out.pm_tids) != k or out.joined_pm_tid is not None
                or out.gather_dim != (2 if slot == 0 else None)
                or sm.outs[slot] != out.sm_tid
                or tuple(p.outs[slot] for p in pms) != out.pm_tids):
            raise ValueError("BW_matmul query shared writer/output authority mismatch")
        b, h, q, n, m = bw_matmul_query_shape_spec(k,
            (g.full_shape, x.full_shape, y.full_shape),
            (g.shard_shape, x.shard_shape, y.full_shape),
            out.full_shape, out.shard_shape, c.projection, out.kind)
    vt = next((t for t in ts if t.rule_id == "bw-view-joined"), None)
    vc = vi = vo = vs = vp = None
    if vt is not None:
        vc = _select_exact_typed_certificate(relation, vt, "bw-view-joined",
            "TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view", JoinedBWViewCertificate,
            lambda c: ((c.input_fact,), (c.output_fact,)))
        vi, vo = records[vc.input_fact], records[vc.output_fact]
        if (len(vt.sm_node_indices) != 1 or len(vt.pm_node_indices) != 1
                or not set(vt.sm_node_indices) <= set(range(ss, se))
                or not set(vt.pm_node_indices) <= set(range(ps, pe))
                or vi.kind != "joined" or vo.kind != "joined" or vi.pm_tids or vo.pm_tids
                or vi.joined_pm_tid is None or vo.joined_pm_tid is None
                or vi.full_shape != vc.input_shape or vo.full_shape != vc.target_shape
                or not vc.target_shape or any(d <= 0 for d in vc.target_shape)
                or vc.sm_step_id != f"sm:{vt.sm_node_indices[0]}:0"
                or vc.pm_step_id != f"pm:{vt.pm_node_indices[0]}:0"):
            raise ValueError("BW_matmul query/view metadata mismatch")
        vs = ir.sm_nodes[vt.sm_node_indices[0]]; vp = ir.pm_nodes[vt.pm_node_indices[0]]
        def check_view(node, pm):
            if (node.op != "BW_view" or len(node.ins) != 2
                    or node.ins[0] != (vi.joined_pm_tid if pm else vi.sm_tid)
                    or node.outs != [vo.joined_pm_tid if pm else vo.sm_tid]
                    or tuple(node.params) != vc.target_shape):
                raise ValueError("BW_matmul query/view writer mismatch")
        check_view(vs, False); check_view(vp, True)
    semantic_sm = {mi} | (set(vt.sm_node_indices) if vt else set())
    semantic_pm = set(pis) | (set(vt.pm_node_indices) if vt else set())
    if semantic_sm != set(range(ss, se)):
        raise ValueError("BW_matmul query SM frame coverage mismatch")
    for i in set(range(ps, pe)) - semantic_pm:
        if vt is None:
            raise ValueError("BW_matmul query unexplained PM frame writer")
        check_view(ir.pm_nodes[i], True)
    states = {s.state_id: s for s in chain.states}
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    required = {g.fact_id, x.fact_id, y.fact_id} | ({vi.fact_id} if vi else set())
    fresh = [out.fact_id for _, _, _, out in outputs] + ([vo.fact_id] if vo else [])
    if (not required <= set(before.fact_ids) or not set(fresh) <= set(after.fact_ids)
            or not set(after.fact_ids) <= set(fresh) | set(before.fact_ids)):
        raise ValueError("BW_matmul query liveness/post-state mismatch")
    # All retained facts are proved by the complete-frame theorem, never silently dropped.
    smframe = list(ir.sm_nodes[ss:se]); pmframe = list(ir.pm_nodes[ps:pe])
    sm_written = {tid for node in smframe for tid in node.outs}
    pm_written = {tid for node in pmframe for tid in node.outs}
    for record in chain.relation_facts:
        if record.fact_id not in before.fact_ids:
            continue
        pm_reads = set(record.pm_tids)
        if record.joined_pm_tid is not None:
            pm_reads.add(record.joined_pm_tid)
        if record.sm_tid in sm_written or pm_reads & pm_written:
            raise ValueError("BW_matmul query retained boundary fact is overwritten")
    smn, pmn = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    smf, pmf = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    shape = lambda s: "[" + ", ".join(map(str, s)) + "]"
    vals = lambda r: "[" + ", ".join(f"pmFinal {tid}" for tid in r.pm_tids) + "]"
    lines = [f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in smframe)}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pmframe)}]",
        f"@[irreducible] private def {smf} (s : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", ""]

    def writer(name, graph, initial, fn, nn, frame, pos, node, slot=None):
        final = f"({fn} {initial})"; out = node.outs[slot or 0]
        if slot is not None:
            expr = f"(bw_matmul ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})).{slot+1}"
            lemma = "applyNode_bw_matmul_fst_out" if slot == 0 else "applyNode_bw_matmul_snd_out"
            apply = f"exact {lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)"
            ins = tuple(node.ins)
        else:
            expr = f"fw_view {shape(vc.target_shape)} ({{store}} {node.ins[0]})"
            apply = f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {shape(node.params[1:])} {node.ins[0]} {node.ins[1]} {out}"
            ins = (node.ins[0],)
        th = f"{segment_id}_{name}"
        lines.extend([f"private theorem {th} ({initial} : Store) : {final} {out} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {fn}; rfl"])
        helper = _render_mixed_final_value(name="hout", graph=graph, initial_store=initial,
            final_store=final, final_equality="hfinal", nodes_name=nn, nodes=frame,
            position=pos, output_tid=out, input_tids=ins,
            written_tids={u for n in frame for u in n.outs}, expression=expr,
            apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]", apply])
        lines.extend(z[2:] if z.startswith("  ") else z for z in helper)
        lines.extend(["  exact hout", ""])
        return th

    helpers = {}
    for _, _, slot, _ in outputs:
        hs = writer(f"hSm{slot}", ir.sm_graph_ref, "smStore", smf, smn, smframe, mi-ss, sm, slot)
        hp = [writer(f"hPm{slot}_{r}", ir.pm_graph_ref, "pmStore", pmf, pmn, pmframe,
                     i-ps, node, slot) for r, (i, node) in enumerate(zip(pis, pms))]
        helpers[slot] = hs, hp
    if vt:
        hvs = writer("hViewSm", ir.sm_graph_ref, "smStore", smf, smn, smframe, vt.sm_node_indices[0]-ss, vs)
        # Frame-only copies were checked against the same exact view above.
        # Extract the last identical writer, not an overwritten earlier copy.
        view_index = max(i for i in range(ps, pe) if ir.pm_nodes[i].outs == vp.outs)
        hvp = writer("hViewPm", ir.pm_graph_ref, "pmStore", pmf, pmn, pmframe,
                     view_index-ps, ir.pm_nodes[view_index])
    transpose_shape = f"{segment_id}_transpose_shape"
    lines.extend([f"private theorem {transpose_shape} (t : Tensor) (a b c d : Nat)",
        "    (ht : t.shape = [a,b,c,d]) : (transpose2d t).shape = [a,b,d,c] := by",
        "  simp only [transpose2d, ht, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Tensor.mkShape]", ""])
    GF, GS, XF, XS, Y = map(shape, (g.full_shape, g.shard_shape, x.full_shape, x.shard_shape, y.full_shape))
    YT = shape((b,h,m,n))
    for _, c, slot, _ in outputs:
        name = f"{segment_id}_semantic_{'fst' if slot == 0 else 'snd'}"
        lines.extend([f"private theorem {name} (g x y py : Tensor) (gs xs : List Tensor)",
            f"    (hg : ShardedRel g gs 2 {GF} {GS}) (hx : ShardedRel x xs 2 {XF} {XS})",
            f"    (hy : y = py ∧ y.shape = {Y} ∧ py.shape = {Y})",
            f"    (hgl : gs.length = {k}) (hxl : xs.length = {k}) :"])
        if slot == 0:
            lines.extend([f"    ShardedRel (bw_matmul g x y).1 (gs.map (fun z => (bw_matmul z x py).1)) 2 {XF} {XS} := by",
                f"  have hyT : transpose2d y = transpose2d py ∧ (transpose2d y).shape = {YT} ∧ (transpose2d py).shape = {YT} :=",
                f"    ⟨congrArg transpose2d hy.1, {transpose_shape} y {b} {h} {n} {m} hy.2.1, {transpose_shape} py {b} {h} {n} {m} hy.2.2⟩",
                f"  exact {c.lean_theorem} (K := {k}) (b := {b}) (h := {h}) (q := {q}) (k := {m}) (m := {n}) hg hyT (by decide) (by decide) (by decide) (by decide) hgl", ""])
        else:
            lines.extend(["    (bw_matmul g x y).2 = tensorSum (List.zipWith (fun a z => (bw_matmul a z py).2) gs xs) := by",
                "  rw [hg.full_value, hx.full_value, hgl, hxl, hy.1]",
                f"  exact {c.lean_theorem} {k} {b} {h} {q} {n} {m} gs xs py (by decide) (by decide) (by decide) (by decide) (by decide) hgl hxl hg.shard_shapes hx.shard_shapes", ""])
    lines.extend(["set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  let smFinal := {smf} smStore", f"  let pmFinal := {pmf} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide"])
    for name, rec in (("g",g),("x",x)):
        lines.extend([f"  have h{name} : {rec.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {rec.sm_tid}) {vals(rec)} 2 {shape(rec.full_shape)} {shape(rec.shard_shape)} at h{name}"])
    lines.extend([f"  have hy : {y.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"  change smFinal {y.sm_tid} = pmFinal {y.joined_pm_tid} ∧ (smFinal {y.sm_tid}).shape = {Y} ∧ (pmFinal {y.joined_pm_tid}).shape = {Y} at hy"])
    output_proofs = []
    for _, _, slot, out in outputs:
        hs, hp = helpers[slot]; tag = "fst" if slot == 0 else "snd"
        lines.append(f"  have hS{slot} := {hs} smStore")
        lines.append(f"  change smFinal {out.sm_tid} = (bw_matmul (smFinal {g.sm_tid}) (smFinal {x.sm_tid}) (smFinal {y.sm_tid})).{slot+1} at hS{slot}")
        for r in range(k):
            lines.extend([f"  have hP{slot}_{r} := {hp[r]} pmStore",
                f"  change pmFinal {out.pm_tids[r]} = (bw_matmul (pmFinal {g.pm_tids[r]}) (pmFinal {x.pm_tids[r]}) (pmFinal {y.joined_pm_tid})).{slot+1} at hP{slot}_{r}"])
        lines.append(f"  have hC{slot} := {segment_id}_semantic_{tag} (smFinal {g.sm_tid}) (smFinal {x.sm_tid}) (smFinal {y.sm_tid}) (pmFinal {y.joined_pm_tid}) {vals(g)} {vals(x)} hg hx hy (by rfl) (by rfl)")
        proof = f"hout{slot}"; output_proofs.append(proof)
        if slot == 0:
            lines.extend([f"  have {proof} : {out.fact_id}.Holds smFinal pmFinal := by",
                f"    change ShardedRel (smFinal {out.sm_tid}) {vals(out)} 2 {XF} {XS}",
                "    rw [" + ", ".join([f"hS{slot}"] + [f"hP{slot}_{r}" for r in range(k)]) + "]",
                "    simpa only [List.map, bw_matmul, batchedMatmulBwd] using hC0"])
        else:
            lines.extend(["  simp only [List.zipWith] at hC1",
                "  rw [" + ", ".join(["←hS1"] + [f"←hP1_{r}" for r in range(k)]) + "] at hC1",
                f"  have hRV : smFinal {out.sm_tid} = allReducePrim {vals(out)}.length 0 {vals(out)} := hC1",
                f"  have hFull : (smFinal {out.sm_tid}).shape = {Y} := by",
                "    rw [hS1]",
                f"    exact fw_matmul_rank4_shape _ _ {b} {h} {n} {q*k} {m} ({transpose_shape} _ {b} {h} {q*k} {n} hx.full_shape) hg.full_shape"])
            for r in range(k):
                lines.extend([f"  have hShape{r} : (pmFinal {out.pm_tids[r]}).shape = {Y} := by",
                    f"    rw [hP1_{r}]",
                    f"    exact fw_matmul_rank4_shape _ _ {b} {h} {n} {q} {m} ({transpose_shape} _ {b} {h} {q} {n} (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))"])
            lines.extend([f"  have hShapes : ∀ z ∈ {vals(out)}, z.shape = {Y} := by",
                "    simp only [List.forall_mem_cons]",
                "    exact ⟨" + ", ".join(f"hShape{r}" for r in range(k)) + ", List.forall_mem_nil _⟩",
                f"  have {proof} : {out.fact_id}.Holds smFinal pmFinal := by",
                "    exact {", "      full_value := hRV", "      full_shape := hFull",
                "      contributions_nonempty := List.cons_ne_nil _ _",
                "      contribution_shapes := hShapes", "      reduced_shape := by simp only [List.map]; rw [←hRV]; exact hFull }"])
    if vt:
        lines.extend([f"  have hvi : {vi.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"  have hVS := {hvs} smStore", f"  have hVP := {hvp} pmStore",
            f"  change smFinal {vo.sm_tid} = fw_view {shape(vc.target_shape)} (smFinal {vi.sm_tid}) at hVS",
            f"  change pmFinal {vo.joined_pm_tid} = fw_view {shape(vc.target_shape)} (pmFinal {vi.joined_pm_tid}) at hVP",
            f"  have houtV : {vo.fact_id}.Holds smFinal pmFinal := by",
            f"    change smFinal {vo.sm_tid} = pmFinal {vo.joined_pm_tid} ∧ _ ∧ _",
            "    rw [hVS, hVP]",
            f"    exact JoinedRel.fw_view {shape(vc.target_shape)} {shape(vc.input_shape)} hvi"])
        output_proofs.append("houtV")
    fresh_text = "[" + ", ".join(fresh) + "]"
    lines.extend(["  intro fact hfact",
        f"  have hc : fact ∈ {fresh_text} ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ {fresh_text} ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at hc", "  rcases hc with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh"])
    if len(fresh) == 1:
        lines.extend(["    subst fact", f"    exact {output_proofs[0]}"])
    else:
        lines.append("    rcases fresh with " + " | ".join("rfl" for _ in fresh))
        lines.extend(f"    · exact {proof}" for proof in output_proofs)
    lines.extend(["  · exact hframe fact old", "",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {smn}", f"  pmNodes := {pmn}",
        f"  sound := by intro smStore pmStore h; have h' := {segment_id}_sound smStore pmStore h; unfold {smf} {pmf} at h'; exact h'", ""])
    return "\n".join(lines)
