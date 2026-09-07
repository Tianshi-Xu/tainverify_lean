"""Closed sparse/full-frame renderers for typed BW_linear dX relations."""
from __future__ import annotations


def _render_row_dx_commutation(*, name, theorem, k, gradient, weight,
                                activation, gradient_shapes, weight_shapes, activation_shape):
    """One checked value identity, shared by singleton and mixed row frames."""
    b, s, o = gradient.shard_shape
    i = weight.shard_shape[1]
    values = lambda tids: "[" + ", ".join(f"pmFinal {tid}" for tid in tids) + "]"
    gs, ws = values(gradient.pm_tids), values(weight.pm_tids)
    contributions = "[" + ", ".join(
        f"(bw_linear (pmFinal {g}) ({activation}) (pmFinal {w})).1"
        for g, w in zip(gradient.pm_tids, weight.pm_tids)) + "]"
    return [
        f"    have {name}_raw := {theorem} {k} {b} {s} {o} {i}",
        f"      {gs} {ws} ({activation})",
        "      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl",
        f"      {gradient_shapes} {weight_shapes} {activation_shape}",
        f"    have {name} : (bw_linear (allGatherPrimDimN 2 {k} 0 {gs})",
        f"      ({activation}) (allGatherPrimDimN 0 {k} 0 {ws})).1 =",
        f"      allReducePrim {k} 0 {contributions} := by",
        f"      simpa only [List.zipWith, tensorSum, allReducePrim, List.head?_cons, Option.map_some, Option.getD_some] using {name}_raw",
    ]


def render_closed_k_rank_bw_linear_dx_sequence_segment(ir, relation, segment_id: str) -> str:
    """One ordered SM/PM frame, arbitrary positive sequence-sharded dX."""
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import get_closed_rule_spec
    spec = get_closed_rule_spec("bw-linear-dx-sequence-sharded-k-rank")
    chain = relation.dependent_chain_plan
    seg = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if seg is None or len(seg.transition_ids) != 1:
        raise ValueError("sequence dX requires exactly one typed transition")
    transitions = {t.transition_id: t for t in relation.transition_specs}
    t = transitions[seg.transition_ids[0]]
    c = _select_exact_typed_certificate(relation, t, spec.rule_id, spec.lean_theorems[0],
        spec.certificate_type, lambda c: (tuple(sorted(c.input_facts)), (c.output_fact,)))
    if (c.family != "sequence-sharded" or len(c.input_facts) != 3
            or c.output_layout != "sharded" or c.gather_dim != 1):
        raise ValueError("sequence dX semantic certificate mismatch")
    records = {r.source: r for r in chain.relation_facts}
    try:
        g, x, w = (records[f] for f in c.input_facts)
        out = records[c.output_fact]
    except KeyError as exc:
        raise ValueError("sequence dX fact is not materialized") from exc
    k = c.rank_count
    if (k <= 0 or any(r.kind != "sharded" or r.gather_dim != 1
            or len(r.pm_tids) != k or len(r.shard_shape) != 3 for r in (g, x, out))
            or w.kind != "sharded" or w.gather_dim not in (0, 1) or len(w.pm_tids) != 1
            or w.full_shape != w.shard_shape or len(w.full_shape) != 2):
        raise ValueError("sequence dX rank/layout/weight authority mismatch")
    b, s, o = g.shard_shape
    i = x.shard_shape[2]
    if (min(b, s, o, i) <= 0 or x.shard_shape != (b, s, i)
            or g.full_shape != (b, s*k, o) or x.full_shape != (b, s*k, i)
            or out.full_shape != x.full_shape or out.shard_shape != x.shard_shape
            or w.full_shape != (o, i)):
        raise ValueError("sequence dX exact shape contract mismatch")
    states = {s.state_id: s for s in chain.states}
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if (not {r.fact_id for r in (g,x,w)} <= set(before.fact_ids)
            or out.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= set(before.fact_ids) | {out.fact_id}):
        raise ValueError("sequence dX live state mismatch")
    ss, se = seg.sm_range; ps, pe = seg.pm_range
    if (len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != k
            or len(set(t.pm_node_indices)) != k
            or not set(t.sm_node_indices) <= set(range(ss,se))
            or not set(t.pm_node_indices) <= set(range(ps,pe))
            or not 0 <= ss <= se <= len(ir.sm_nodes) or not 0 <= ps <= pe <= len(ir.pm_nodes)
            or c.sm_step_id != f"sm:{t.sm_node_indices[0]}:0"
            or c.pm_step_ids != tuple(f"pm:{p}:0" for p in t.pm_node_indices)):
        raise ValueError("sequence dX exact writer footprint mismatch")
    sm = ir.sm_nodes[t.sm_node_indices[0]]
    pms = tuple(ir.pm_nodes[p] for p in t.pm_node_indices)
    def check_node(n, rank, ins, output):
        if (n.op != "BW_linear" or n.rank != rank or n.params or tuple(n.ins) != ins
                or len(n.outs) != 2 or len(set(n.outs)) != 2 or n.outs[0] != output):
            raise ValueError("sequence dX writer rank/roles/order mismatch")
    check_node(sm,0,(g.sm_tid,x.sm_tid,w.sm_tid),out.sm_tid)
    for r,n in enumerate(pms):
        check_node(n,r,(g.pm_tids[r],x.pm_tids[r],w.pm_tids[0]),out.pm_tids[r])
    smframe, pmframe = list(ir.sm_nodes[ss:se]), list(ir.pm_nodes[ps:pe])
    # All retained relation/authority reads survive the entire frozen frame.
    by_id = {r.fact_id:r for r in chain.relation_facts}
    authority = {a.fact_id:a for a in chain.authority_facts}
    if chain.anchor_fact is not None:
        authority[chain.anchor_fact.fact_id] = chain.anchor_fact
    live_sm, live_pm = set(), set()
    for fid in set(before.fact_ids) | set(after.fact_ids):
        if fid in by_id:
            r=by_id[fid];live_sm.add(r.sm_tid);live_pm.update(r.pm_tids)
            if r.joined_pm_tid is not None: live_pm.add(r.joined_pm_tid)
            if r.metadata_tid is not None: live_sm.add(r.metadata_tid);live_pm.add(r.metadata_tid)
        elif fid in authority:
            a=authority[fid]
            if a.kind == "tensor_shape": (live_sm if a.side == "sm" else live_pm).add(a.tid)
            elif a.kind == "tensor_eq":
                (live_sm if a.left_side == "sm" else live_pm).add(a.left_tid)
                (live_sm if a.right_side == "sm" else live_pm).add(a.right_tid)
            else: raise ValueError("sequence dX unsupported frame authority")
        else: raise ValueError("sequence dX unknown live fact")
    for frame,start,owned,live,allowed in ((smframe,ss,set(t.sm_node_indices),live_sm,{out.sm_tid}),
            (pmframe,ps,set(t.pm_node_indices),live_pm,set(out.pm_tids))):
        for pos,n in enumerate(frame,start):
            if set(n.outs) & (live - (allowed if pos in owned else set())):
                raise ValueError("sequence dX frame overwrites live authority")
        for tid in allowed:
            if sum(tid in n.outs for n in frame) != 1:
                raise ValueError("sequence dX output has multiple writers")
    sn,pn,sf,pf=(f"{segment_id}_{suffix}" for suffix in ("sm_nodes","pm_nodes","sm_final","pm_final"))
    lines=[f"private def {sn} : List NodeDecl := [{', '.join(_node_text(n) for n in smframe)}]",
        f"private def {pn} : List NodeDecl := [{', '.join(_node_text(n) for n in pmframe)}]",
        f"@[irreducible] private def {sf} (s : Store) : Store := {sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pf} (s : Store) : Store := {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", ""]
    def writer(name,graph,fn,nn,frame,pos,n):
        final=f"({fn} store)";th=f"{segment_id}_{name}"
        expr=f"(bw_linear ({{store}} {n.ins[0]}) ({{store}} {n.ins[1]}) ({{store}} {n.ins[2]})).1"
        lines.extend([f"private theorem {th} (store : Store) : {final} {n.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) store := by unfold {fn}; rfl"])
        helper=_render_mixed_final_value(name="hout",graph=graph,initial_store="store",final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=n.outs[0],input_tids=tuple(n.ins),written_tids={v for n in frame for v in n.outs},expression=expr,apply_lines=[
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "simp [applyNodeDistributed, applyNodeRingAttn]",
            f"exact applyNode_bw_linear_fst_out {graph} t {n.rank} {' '.join(map(str,(*n.ins,*n.outs)))} (by native_decide)"])
        lines.extend(z[2:] if z.startswith("  ") else z for z in helper);lines.extend(["  exact hout",""])
        return th
    hs=writer("hSmWriter",ir.sm_graph_ref,sf,sn,smframe,t.sm_node_indices[0]-ss,sm)
    hp=[writer(f"hPmWriter{r}",ir.pm_graph_ref,pf,pn,pmframe,pos-ps,n) for r,(pos,n) in enumerate(zip(t.pm_node_indices,pms))]
    vals=lambda r: "["+", ".join(f"pmFinal {v}" for v in r.pm_tids)+"]"
    shape=lambda sh: _shape_text(list(sh))
    gl,xl,ol=map(vals,(g,x,out));gf,gs,xf,xs,wf=map(shape,(g.full_shape,g.shard_shape,x.full_shape,x.shard_shape,w.full_shape))
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({sf} smStore) ({pf} pmStore) := by",
        f" let smFinal := {sf} smStore",f" let pmFinal := {pf} pmStore",
        f" have hframe : {before.state_id}.Holds smFinal pmFinal := by unfold smFinal pmFinal {sf} {pf}; apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hstate <;> native_decide",
        f" have hg : {g.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f" change ShardedRel (smFinal {g.sm_tid}) {gl} 1 {gf} {gs} at hg",
        f" have hx : {x.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f" change ShardedRel (smFinal {x.sm_tid}) {xl} 1 {xf} {xs} at hx",
        f" have hw : {w.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f" change ShardedRel (smFinal {w.sm_tid}) [pmFinal {w.pm_tids[0]}] {w.gather_dim} {wf} {wf} at hw",
        f" have hwEq : smFinal {w.sm_tid} = pmFinal {w.pm_tids[0]} := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq {w.gather_dim} _ (by rw [hw.shard_shapes _ (by simp)]; decide)",
        f" have hgV : smFinal {g.sm_tid} = allGatherPrimDimN 1 {k} 0 {gl} := by simpa only [List.length_cons,List.length_nil] using hg.full_value",
        f" have hS : smFinal {out.sm_tid} = (bw_linear (smFinal {g.sm_tid}) (smFinal {x.sm_tid}) (smFinal {w.sm_tid})).1 := {hs} smStore"])
    for r,th in enumerate(hp):
        lines.append(f" have hP{r} : pmFinal {out.pm_tids[r]} = (bw_linear (pmFinal {g.pm_tids[r]}) (pmFinal {x.pm_tids[r]}) (pmFinal {w.pm_tids[0]})).1 := {th} pmStore")
    local_list="["+", ".join(f"(bw_linear (pmFinal {gt}) (pmFinal {xt}) (pmFinal {w.pm_tids[0]})).1" for gt,xt in zip(g.pm_tids,x.pm_tids))+"]"
    lines.extend([f" have hcomm := {c.lean_theorem} {k} {b} {s} {o} {i} {gl} {xl} (smFinal {x.sm_tid}) (pmFinal {w.pm_tids[0]})",
        "   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes hx.full_shape (hw.shard_shapes _ (by simp))",
        f" have hcommExplicit : (bw_linear (allGatherPrimDimN 1 {k} 0 {gl}) (smFinal {x.sm_tid}) (pmFinal {w.pm_tids[0]})).1 = allGatherPrimDimN 1 {k} 0 {local_list} := by simpa only [List.zipWith] using hcomm",
        f" have hV : smFinal {out.sm_tid} = allGatherPrimDimN 1 {k} 0 {ol} := by",
        "   rw [hS, hgV, hwEq, hcommExplicit]",
        "   rw ["+", ".join(f"← hP{r}" for r in range(k))+"]",
        f" have hFull : (smFinal {out.sm_tid}).shape = {xf} := by rw [hS]; exact bw_linear_3d_fst_shape {b} {s*k} {o} {i} _ _ _ hg.full_shape hx.full_shape hw.full_shape"])
    for r in range(k):
        lines.append(f" have hShape{r} : (pmFinal {out.pm_tids[r]}).shape = {xs} := by rw [hP{r}]; exact bw_linear_3d_fst_shape {b} {s} {o} {i} _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))")
    lines.extend([f" have hout : {out.fact_id}.Holds smFinal pmFinal := by",
        f"   change ShardedRel (smFinal {out.sm_tid}) {ol} 1 {xf} {xs}",
        "   refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }",
        "   · simpa only [List.length_cons,List.length_nil] using hV",
        "   · simp only [List.forall_mem_cons]; exact ⟨"+", ".join(f"hShape{r}" for r in range(k))+", List.forall_mem_nil _⟩",
        "   · simp only [List.length_cons,List.length_nil]; decide",
        " intro fact hfact",
        f" have hc : fact ∈ [{out.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{out.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        " simp only [List.mem_append] at hc", " rcases hc with fresh | old",
        " · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh; subst fact; exact hout",
        " · exact hframe fact old", "",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f" smNodes := {sn}",f" pmNodes := {pn}",
        f" sound := by intro a b h; have z := {segment_id}_sound a b h; unfold {sf} {pf} at z; exact z", ""])
    return "\n".join(lines)


def render_closed_k_rank_bw_linear_dx_segment(ir, relation, segment_id: str) -> str:
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

    row_rules = {
        "bw-linear-dx-row-reduction-k-rank",
    }
    view_rule_spec = get_closed_rule_spec("bw-view-joined")
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) not in (1, 2):
        raise ValueError("BW_linear dX reduction requires one transition and optional joined view")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    segment_transitions = tuple(transition_map[item] for item in segment.transition_ids)
    transition = next((item for item in segment_transitions
                       if item.rule_id in row_rules), None)
    view_transition = next((item for item in segment_transitions
                            if item.rule_id == view_rule_spec.rule_id), None)
    if transition is None or (len(segment_transitions) == 2 and view_transition is None):
        raise ValueError("BW_linear dX transition authority is missing")
    rule_spec = get_closed_rule_spec(transition.rule_id)
    rule = rule_spec.rule_id
    if transition.lean_theorem not in rule_spec.lean_theorems:
        raise ValueError("BW_linear dX row-reduction theorem identity mismatch")
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, transition.lean_theorem,
        rule_spec.certificate_type,
        lambda cert: (tuple(sorted(cert.input_facts)), (cert.output_fact,)),
    )
    if certificate.family != "row-reduction" or len(certificate.input_facts) != 3:
        raise ValueError("BW_linear dX certificate has wrong semantic family/arity")
    view_certificate = None
    if view_transition is not None:
        view_certificate = _select_exact_typed_certificate(
            relation, view_transition, view_rule_spec.rule_id,
            view_rule_spec.lean_theorems[0],
            view_rule_spec.certificate_type,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient, activation, weight = (
            records[source] for source in certificate.input_facts
        )
        output = records[certificate.output_fact]
        view_input = records[view_certificate.input_fact] if view_certificate else None
        view_output = records[view_certificate.output_fact] if view_certificate else None
    except KeyError as exc:
        raise ValueError("BW_linear dX relation fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {gradient.fact_id, activation.fact_id, weight.fact_id}
    fresh = {output.fact_id}
    if view_input is not None:
        required.add(view_input.fact_id); fresh.add(view_output.fact_id)
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids):
        raise ValueError("BW_linear dX pre/post facts are not live")
    if not set(after.fact_ids) <= (fresh | set(before.fact_ids)):
        raise ValueError("BW_linear dX post-state introduces an unproved fact")

    k = len(gradient.pm_tids)
    if (k == 0 or certificate.rank_count != k
            or certificate.output_layout != "reduction" or certificate.gather_dim is not None
            or gradient.kind != "sharded" or gradient.gather_dim != 2
            or activation.kind != "joined" or activation.pm_tids != ()
            or activation.joined_pm_tid is None
            or weight.kind != "sharded" or weight.gather_dim != 0
            or output.kind != "reduction" or len(output.pm_tids) != k
            or activation.shard_shape != activation.full_shape
            or output.shard_shape != output.full_shape
            or len(gradient.full_shape) != 3 or len(gradient.shard_shape) != 3
            or len(activation.full_shape) != 3
            or len(weight.full_shape) != 2 or len(weight.shard_shape) != 2
            or gradient.full_shape[:2] != activation.full_shape[:2]
            or gradient.shard_shape[:2] != activation.full_shape[:2]
            or output.full_shape != activation.full_shape
            or gradient.full_shape[2] != gradient.shard_shape[2] * k
            or weight.full_shape != (gradient.full_shape[2], activation.full_shape[2])
            or weight.shard_shape != (gradient.shard_shape[2], activation.full_shape[2])
            or len(weight.pm_tids) != k
            or any(x <= 0 for x in (*activation.full_shape, gradient.shard_shape[2]))):
        raise ValueError("BW_linear dX row-reduction metadata is not exact")

    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("BW_linear dX footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    if (not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("BW_linear dX writers are outside the complete frame")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    if certificate.sm_step_id != f"sm:{transition.sm_node_indices[0]}:0" or (
        certificate.pm_step_ids
        != tuple(f"pm:{index}:0" for index in transition.pm_node_indices)
    ):
        raise ValueError("BW_linear dX certificate footprint was tampered")
    if (sm_node.rank != 0 or sm_node.op != "BW_linear" or sm_node.params
            or len(sm_node.ins) != 3 or len(sm_node.outs) != 2
            or tuple(sm_node.ins) != (gradient.sm_tid, activation.sm_tid, weight.sm_tid)
            or sm_node.outs[0] != output.sm_tid):
        raise ValueError("BW_linear dX SM writer roles are not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("BW_linear dX PM writer ranks are not ordered")
    for rank, node in enumerate(pm_nodes):
        if (node.op != "BW_linear" or node.params or len(node.ins) != 3
                or len(node.outs) != 2
                or tuple(node.ins) != (
                    gradient.pm_tids[rank], activation.joined_pm_tid,
                    weight.pm_tids[rank],
                )
                or node.outs[0] != output.pm_tids[rank]):
            raise ValueError("BW_linear dX PM writer roles/order are not exact")
    view_sm_node = view_pm_node = None
    if view_transition is not None:
        if (view_input.kind != "joined" or view_output.kind != "joined"
                or view_input.full_shape != tuple(view_certificate.input_shape)
                or view_output.full_shape != tuple(view_certificate.target_shape)):
            raise ValueError("BW_linear/view joined metadata mismatch")
        view_sm_node = ir.sm_nodes[view_transition.sm_node_indices[0]]
        view_pm_node = ir.pm_nodes[view_transition.pm_node_indices[0]]
        for node in (view_sm_node, view_pm_node):
            if (node.op != "BW_view" or node.ins[0] not in (view_input.sm_tid, view_input.joined_pm_tid)
                    or node.outs[0] not in (view_output.sm_tid, view_output.joined_pm_tid)):
                raise ValueError("BW_linear/view writer mismatch")

    sm_nodes_name = f"{segment_id}_sm_nodes"
    pm_nodes_name = f"{segment_id}_pm_nodes"
    sm_final_name = f"{segment_id}_sm_final"
    pm_final_name = f"{segment_id}_pm_final"
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
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} =",
            f"      (bw_linear ({final} {node.ins[0]}) ({final} {node.ins[1]}) ({final} {node.ins[2]})).1 := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}",
            "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=(
                f"(bw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
                f"({{store}} {node.ins[2]})).1"
            ),
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_linear_fst_out {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.ins[2]} "
                f"{node.outs[0]} {node.outs[1]} (by native_decide)",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = writer(
        "hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
        sm_nodes_name, sm_frame, transition.sm_node_indices[0] - sm_start, sm_node,
    )
    pm_helpers = [
        writer(
            f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, index - pm_start, node,
        )
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
    ]
    view_sm_helper = view_pm_helper = None
    if view_transition is not None:
        def view_writer(name, graph, initial, final_name, nodes_name, frame, position, node):
            theorem_name=f"{segment_id}_{name}"; final=f"({final_name} {initial})"; shape=_shape_text(list(view_certificate.target_shape))
            lines.extend([f"private theorem {theorem_name} ({initial}:Store) : {final} {node.outs[0]} = fw_view {shape} ({final} {node.ins[0]}) := by",f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {final_name}; rfl"])
            helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=position,output_tid=node.outs[0],input_tids=(node.ins[0],),written_tids={tid for item in frame for tid in item.outs},expression=f"fw_view {shape} ({{store}} {node.ins[0]})",apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.ins[1]} {node.outs[0]}"])
            lines.extend(item[2:] if item.startswith("  ") else item for item in helper);lines.extend(["  exact hout",""]);return theorem_name
        view_sm_helper=view_writer("hViewSm",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,sm_frame,view_transition.sm_node_indices[0]-sm_start,view_sm_node)
        view_pm_helper=view_writer("hViewPm",ir.pm_graph_ref,"pmStore",pm_final_name,pm_nodes_name,pm_frame,view_transition.pm_node_indices[0]-pm_start,view_pm_node)

    glist = "[" + ", ".join(f"pmFinal {tid}" for tid in gradient.pm_tids) + "]"
    wlist = "[" + ", ".join(f"pmFinal {tid}" for tid in weight.pm_tids) + "]"
    olist = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]"
    contribution_list = "[" + ", ".join(
        f"(bw_linear (pmFinal {g}) (pmFinal {activation.joined_pm_tid}) (pmFinal {w})).1"
        for g, w in zip(gradient.pm_tids, weight.pm_tids)
    ) + "]"
    gfull, gshard = (_shape_text(list(x)) for x in (gradient.full_shape, gradient.shard_shape))
    wfull, wshard = (_shape_text(list(x)) for x in (weight.full_shape, weight.shard_shape))
    oshape = _shape_text(list(output.full_shape))
    lines.extend([
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
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} 2 {gfull} {gshard} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change smFinal {activation.sm_tid} = pmFinal {activation.joined_pm_tid} ∧",
        f"      (smFinal {activation.sm_tid}).shape = {_shape_text(list(activation.full_shape))} ∧",
        f"      (pmFinal {activation.joined_pm_tid}).shape = {_shape_text(list(activation.full_shape))} at hx",
        f"    have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {weight.sm_tid}) {wlist} 0 {wfull} {wshard} at hw",
        f"    have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 2 {k} 0 {glist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"    have hwValue : smFinal {weight.sm_tid} = allGatherPrimDimN 0 {k} 0 {wlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hw.full_value",
        f"    have hSmWriter : smFinal {sm_node.outs[0]} =",
        f"        (bw_linear (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) (smFinal {sm_node.ins[2]})).1 :=",
        f"      {sm_helper} smStore",
    ])
    if view_transition is not None:
        target_shape=_shape_text(list(view_certificate.target_shape));input_shape=_shape_text(list(view_certificate.input_shape))
        lines.extend([f"    have hvi : {view_input.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    have hvs := {view_sm_helper} smStore",f"    have hvp := {view_pm_helper} pmStore",f"    change smFinal {view_output.sm_tid} = fw_view {target_shape} (smFinal {view_input.sm_tid}) at hvs",f"    change pmFinal {view_output.joined_pm_tid} = fw_view {target_shape} (pmFinal {view_input.joined_pm_tid}) at hvp",f"    have houtView : {view_output.fact_id}.Holds smFinal pmFinal := by",f"      change smFinal {view_output.sm_tid} = pmFinal {view_output.joined_pm_tid} ∧ _ ∧ _","      rw [hvs, hvp]",f"      exact JoinedRel.fw_view {target_shape} {input_shape} hvi"])
    for rank, (helper, node) in enumerate(zip(pm_helpers, pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {node.outs[0]} =",
            f"        (bw_linear (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) (pmFinal {node.ins[2]})).1 :=",
            f"      {helper} pmStore",
            f"    have hgShape{rank} := hg.shard_shapes (pmFinal {gradient.pm_tids[rank]}) (by simp)",
            f"    have hwShape{rank} := hw.shard_shapes (pmFinal {weight.pm_tids[rank]}) (by simp)",
            f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {oshape} := by",
            f"      rw [hPmWriter{rank}]",
            f"      exact bw_linear_3d_fst_shape {gradient.shard_shape[0]} {gradient.shard_shape[1]} {gradient.shard_shape[2]} {activation.full_shape[2]} _ _ _",
            f"        hgShape{rank} hx.2.2 hwShape{rank}",
        ])
    hcomm_lines = _render_row_dx_commutation(
        name="hcomm", theorem=transition.lean_theorem, k=k,
        gradient=gradient, weight=weight,
        activation=f"pmFinal {activation.joined_pm_tid}",
        gradient_shapes="hg.shard_shapes", weight_shapes="hw.shard_shapes",
        activation_shape="hx.2.2")
    commute_name = "hcomm"
    lines.extend([
        *hcomm_lines,
        f"    have hOutValue : smFinal {output.sm_tid} = allReducePrim {k} 0 {olist} := by",
        f"      rw [hSmWriter, hgValue, hx.1, hwValue, {commute_name}]",
        "      rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
        f"    have hOutValueList : smFinal {output.sm_tid} =",
        f"        allReducePrim {olist}.length 0 {olist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hOutValue",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {oshape} := by",
        "      rw [hSmWriter]",
        f"      exact bw_linear_3d_fst_shape {gradient.full_shape[0]} {gradient.full_shape[1]} {gradient.full_shape[2]} {activation.full_shape[2]} _ _ _",
        "        hg.full_shape hx.2.1 hw.full_shape",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ReductionRel (smFinal {output.sm_tid}) {olist} {oshape}",
        "      refine {",
        "        full_value := hOutValueList", "        full_shape := hFullShape",
        "        contributions_nonempty := by simp",
        "        contribution_shapes := ?_", "        reduced_shape := ?_", "      }",
        "      · intro contribution hmem",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend(["        · subst contribution", f"          exact hOutShape{rank}"])
    publication=[output.fact_id]+([view_output.fact_id] if view_output else [])
    pub_list="["+", ".join(publication)+"]"
    fresh_lines=(["      rcases fresh with rfl | rfl","      · exact hout","      · exact houtView"] if view_output else ["      rcases fresh with rfl","      exact hout"])
    lines.extend([
        "      · rw [← hOutValueList]", "        exact hFullShape",
        "    intro fact hfact",
        f"    have covered : fact ∈ {pub_list} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {pub_list} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        *fresh_lines,
        "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    exact {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
