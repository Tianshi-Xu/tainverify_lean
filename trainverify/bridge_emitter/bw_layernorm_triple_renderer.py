"""Single-fold, same-writer BW_layernorm parameter projections (optional dX).

The historical public entry point is retained; the atomic component may publish
any nonempty subset containing dgamma or dbeta, at arbitrary positive K/b/s/d.
"""
from __future__ import annotations

import re


_FOUR_INPUT_WRITER_HELPER = """set_option maxHeartbeats 500000 in
private theorem abstract_four_input_middle_writer
    (g : GraphDecl) (fullnodes before after : List NodeDecl)
    (initialStore finalStore : Store) (target : NodeDecl)
    (in0 in1 in2 in3 output : Tid)
    (f : Tensor → Tensor → Tensor → Tensor → Tensor)
    (hnodes : fullnodes = before ++ [target] ++ after)
    (hfinal : finalStore = fullnodes.foldl (applyNodeDistributedFaithful g) initialStore)
    (happly : ∀ t, applyNodeDistributedFaithful g t target output =
      f (t in0) (t in1) (t in2) (t in3))
    (hAfterNil : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOutput : ∀ n ∈ after, output ∉ n.outs)
    (h0nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h0 : ∀ n ∈ target :: after, in0 ∉ n.outs)
    (h1nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h1 : ∀ n ∈ target :: after, in1 ∉ n.outs)
    (h2nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h2 : ∀ n ∈ target :: after, in2 ∉ n.outs)
    (h3nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h3 : ∀ n ∈ target :: after, in3 ∉ n.outs) :
    finalStore output = f (finalStore in0) (finalStore in1)
      (finalStore in2) (finalStore in3) := by
  have hfold : finalStore = (before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) initialStore :=
    hfinal.trans (congrArg (fun ns : List NodeDecl =>
      ns.foldl (applyNodeDistributedFaithful g) initialStore) hnodes)
  have hwriter := foldl_faithful_middle_writer g initialStore before after target output
    (fun t => f (t in0) (t in1) (t in2) (t in3)) happly hAfterNil hAfterOutput
  have hprefix : finalStore output = f
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in0)
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in1)
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in2)
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in3) :=
    (congrArg (fun st : Store => st output) hfold).trans hwriter
  have hread (tid : Tid) (hnil : ∀ n ∈ target :: after, n.outs ≠ [])
      (hnot : ∀ n ∈ target :: after, tid ∉ n.outs) :
      (before.foldl (applyNodeDistributedFaithful g) initialStore) tid = finalStore tid := by
    have hp : (before.foldl (applyNodeDistributedFaithful g) initialStore) tid =
        ((before ++ [target] ++ after).foldl (applyNodeDistributedFaithful g) initialStore) tid := by
      simpa only [List.append_assoc, List.singleton_append] using
        foldl_faithful_prefix_read_eq_final g initialStore before (target :: after) tid hnil hnot
    exact hp.trans (congrArg (fun st : Store => st tid) hfold).symm
  exact hprefix.trans (congrArg
    (fun v : Tensor × Tensor × Tensor × Tensor => f v.1 v.2.1 v.2.2.1 v.2.2.2)
    (congrArg₂ Prod.mk (hread in0 h0nil h0)
      (congrArg₂ Prod.mk (hread in1 h1nil h1)
        (congrArg₂ Prod.mk (hread in2 h2nil h2) (hread in3 h3nil h3)))))"""


def render_closed_k_rank_bw_layernorm_triple_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankBWLayernormDxCertificate, KRankBWLayernormParamReductionCertificate
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankBWLayernormDxCertificate, KRankBWLayernormParamReductionCertificate

    families = {
        "bw-layernorm-dx-dim1-k-rank": (0, "dx", ".1", KRankBWLayernormDxCertificate,
            "TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d"),
        "bw-layernorm-dgamma-sequence-reduction-k-rank": (1, "dgamma", ".2.1", KRankBWLayernormParamReductionCertificate,
            "TrainVerify.Denote.bw_layernorm_dgamma_sequence_reduction_rank3"),
        "bw-layernorm-dbeta-sequence-reduction-k-rank": (2, "dbeta", ".2.2", KRankBWLayernormParamReductionCertificate,
            "TrainVerify.Denote.bw_layernorm_dbeta_sequence_reduction_rank3"),
    }
    chain = relation.dependent_chain_plan
    if chain is None:
        raise ValueError("BW_layernorm projections require a closed chain")
    segments = [item for item in chain.segments if item.segment_id == segment_id]
    if len(segments) != 1 or not 1 <= len(segments[0].transition_ids) <= 3:
        raise ValueError("BW_layernorm requires one to three same-writer projections")
    segment = segments[0]
    transitions = []
    for tid in segment.transition_ids:
        matches = [item for item in relation.transition_specs if item.transition_id == tid]
        if len(matches) != 1:
            raise ValueError("BW_layernorm missing or ambiguous transition")
        transitions.append(matches[0])
    rules = [item.rule_id for item in transitions]
    if (len(set(rules)) != len(rules) or not set(rules) <= set(families)
            or not any(families[rule][0] != 0 for rule in rules)):
        raise ValueError("BW_layernorm parameter projection family set mismatch")

    def inputs(cert):
        return cert.gradient_fact, cert.activation_fact, cert.gamma_fact, cert.beta_fact

    selected = {}
    for transition in transitions:
        slot, name, projection, cert_type, theorem = families[transition.rule_id]
        cert = _select_exact_typed_certificate(
            relation, transition, transition.rule_id, theorem, cert_type,
            lambda c: (tuple(sorted(inputs(c))), (c.output_fact,)),
        )
        if slot and cert.projection != projection:
            raise ValueError("BW_layernorm parameter projection mismatch")
        selected[slot] = (transition, cert, name, projection, theorem)
    # Canonical projection order is independent of dependency-scheduler ordering.
    selected = dict(sorted(selected.items()))
    transition, certificate, _, _, _ = next(iter(selected.values()))
    if any(inputs(c) != inputs(certificate) for _, c, _, _, _ in selected.values()):
        raise ValueError("BW_layernorm projections do not share exact input facts")
    records = {r.source: r for r in chain.relation_facts}
    by_id = {r.fact_id: r for r in chain.relation_facts}
    authority = {a.fact_id: a for a in chain.authority_facts}
    if (len(records) != len(chain.relation_facts) or len(by_id) != len(chain.relation_facts)
            or len(authority) != len(chain.authority_facts) or set(by_id) & set(authority)):
        raise ValueError("BW_layernorm ambiguous fact identity")
    if chain.anchor_fact is not None:
        anchor = chain.anchor_fact
        if anchor.fact_id in by_id or (anchor.fact_id in authority and authority[anchor.fact_id] != anchor):
            raise ValueError("BW_layernorm ambiguous public anchor")
        authority[anchor.fact_id] = anchor
    try:
        gradient, activation, gamma, beta = (records[f] for f in inputs(certificate))
        outputs = {slot: records[c.output_fact] for slot, (_, c, _, _, _) in selected.items()}
        states = {item.state_id: item for item in chain.states}
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("BW_layernorm relation fact/state is not materialized") from exc
    if len(states) != len(chain.states):
        raise ValueError("BW_layernorm ambiguous state identity")
    required = {r.fact_id for r in (gradient, activation, gamma, beta)}
    fresh = {r.fact_id for r in outputs.values()}
    if (not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids)
            or fresh & set(before.fact_ids)
            or not set(after.fact_ids) <= fresh | set(before.fact_ids)):
        raise ValueError("BW_layernorm live pre/post state mismatch")
    k = certificate.rank_count
    if (type(k) is not int or k <= 0 or k != ir.pm_num_ranks
            or len(gradient.shard_shape) != 3):
        raise ValueError("BW_layernorm rank/shape authority mismatch")
    b, s, d = gradient.shard_shape
    if any(type(n) is not int or n <= 0 for n in (b, s, d)):
        raise ValueError("BW_layernorm dimensions must be positive integers")
    full, local, param = (b, s * k, d), (b, s, d), (d,)

    def source_tid(ref, side):
        initial = re.fullmatch(r"init:(0|[1-9][0-9]*)", ref)
        if initial:
            return int(initial[1])
        writer = re.fullmatch(r"(sm|pm):(0|[1-9][0-9]*):(0|[1-9][0-9]*)", ref)
        if writer is None or writer[1] != side:
            raise ValueError("BW_layernorm invalid source reference")
        nodes = ir.sm_nodes if side == "sm" else ir.pm_nodes
        index, slot = int(writer[2]), int(writer[3])
        if index >= len(nodes) or slot >= len(nodes[index].outs):
            raise ValueError("BW_layernorm source outside graph authority")
        return nodes[index].outs[slot]

    def check_record(record, kind, axis, full_shape, shard_shape, ranks):
        source = record.source
        if (record.kind != kind or source.layout != kind
                or record.gather_dim != axis or source.gather_dim != axis
                or record.full_shape != full_shape or record.shard_shape != shard_shape
                or len(record.pm_tids) != ranks or len(source.step_triple) != ranks + 1
                or record.metadata_tid is not None or record.metadata_region_id is not None
                or record.row_shard_shape is not None or record.source_tid_triples
                or record.joined_pm_tid is not None or source.source_step_triples
                or source.joined_pm_step is not None):
            raise ValueError("BW_layernorm source/record axes/shapes/cardinality mismatch")
        if (source_tid(source.step_triple[0], "sm") != record.sm_tid
                or tuple(source_tid(ref, "pm") for ref in source.step_triple[1:]) != record.pm_tids):
            raise ValueError("BW_layernorm source/record TID mismatch")

    for record in (gradient, activation):
        check_record(record, "sharded", 1, full, local, k)
    for record in (gamma, beta):
        kind, axis = ("reduction", None) if d == 1 else ("sharded", 0)
        check_record(record, kind, axis, param, param, 1)
        if record.source.step_triple != (f"init:{record.sm_tid}",) * 2:
            raise ValueError("BW_layernorm gamma/beta are not shared singleton init authority")
    sm_indices, pm_indices = transition.sm_node_indices, transition.pm_node_indices
    ss, se = segment.sm_range
    ps, pe = segment.pm_range
    if (len(sm_indices) != 1 or len(pm_indices) != k or len(set(pm_indices)) != k
            or not 0 <= ss <= se <= len(ir.sm_nodes) or not 0 <= ps <= pe <= len(ir.pm_nodes)
            or not set(sm_indices) <= set(range(ss, se)) or not set(pm_indices) <= set(range(ps, pe))):
        raise ValueError("BW_layernorm writer/frame cardinality mismatch")
    for slot, (t, c, _, _, _) in selected.items():
        output = outputs[slot]
        check_record(output, "sharded" if slot == 0 else "reduction", 1 if slot == 0 else None,
                     full if slot == 0 else param, local if slot == 0 else param, k)
        if (c.rank_count != k or t.sm_node_indices != sm_indices or t.pm_node_indices != pm_indices
                or c.sm_step_id != f"sm:{sm_indices[0]}:{slot}"
                or c.pm_step_ids != tuple(f"pm:{index}:{slot}" for index in pm_indices)
                or output.source.step_triple != (c.sm_step_id, *c.pm_step_ids)
                or len(set(output.pm_tids)) != k):
            raise ValueError("BW_layernorm projections do not own the same exact writers")
        if slot == 0 and (c.gather_dim != 1 or c.full_shape != full or c.shard_shape != local):
            raise ValueError("BW_layernorm dX shape certificate mismatch")
    sm_node = ir.sm_nodes[sm_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in pm_indices)

    def check_node(node, rank, ins, side):
        if (node.op != "BW_layernorm" or node.rank != rank
                or not (node.params is None or type(node.params) is list and node.params == [])
                or tuple(node.ins) != ins or len(node.outs) != 3 or len(set(node.outs)) != 3
                or any(node.outs[slot] != (out.sm_tid if side == "sm" else out.pm_tids[rank])
                       for slot, out in outputs.items())):
            raise ValueError("BW_layernorm writer rank/params/roles/projection mismatch")
    check_node(sm_node, 0, (gradient.sm_tid, activation.sm_tid, gamma.sm_tid, beta.sm_tid), "sm")
    for rank, node in enumerate(pm_nodes):
        check_node(node, rank, (gradient.pm_tids[rank], activation.pm_tids[rank],
                              gamma.pm_tids[0], beta.pm_tids[0]), "pm")
    sm_frame, pm_frame = list(ir.sm_nodes[ss:se]), list(ir.pm_nodes[ps:pe])

    def live_tids(fact_ids):
        sm, pm = set(), set()
        for fid in fact_ids:
            if fid in by_id:
                r = by_id[fid]
                sm.add(r.sm_tid)
                pm.update(r.pm_tids)
                if r.joined_pm_tid is not None:
                    pm.add(r.joined_pm_tid)
                if r.metadata_tid is not None:
                    sm.add(r.metadata_tid)
                    pm.add(r.metadata_tid)
                for ts, tp0, tp1 in r.source_tid_triples:
                    sm.add(ts)
                    pm.update((tp0, tp1))
            elif fid in authority:
                a = authority[fid]
                if a.kind == "tensor_shape" and a.side in ("sm", "pm"):
                    (sm if a.side == "sm" else pm).add(a.tid)
                elif a.kind == "tensor_eq" and a.left_side in ("sm", "pm") and a.right_side in ("sm", "pm"):
                    (sm if a.left_side == "sm" else pm).add(a.left_tid)
                    (sm if a.right_side == "sm" else pm).add(a.right_tid)
                elif a.kind == "gather":
                    sm.add(a.sm_tid)
                    pm.update((a.pm_rank0_tid, a.pm_rank1_tid))
                elif a.kind in ("packed_cu", "label_bound") and a.side in ("sm", "pm"):
                    (sm if a.side == "sm" else pm).add(a.tid)
                else:
                    raise ValueError("BW_layernorm unsupported live authority")
            else:
                raise ValueError("BW_layernorm unknown live fact (including public anchor)")
        return sm, pm

    pre_sm, pre_pm = live_tids(before.fact_ids)
    live_sm, live_pm = live_tids(set(before.fact_ids) | set(after.fact_ids))
    for frame, start, owned, pre, live, allowed in (
        (sm_frame, ss, set(sm_indices), pre_sm, live_sm, {r.sm_tid for r in outputs.values()}),
        (pm_frame, ps, set(pm_indices), pre_pm, live_pm, {tid for r in outputs.values() for tid in r.pm_tids}),
    ):
        for pos, node in enumerate(frame, start):
            if set(node.outs) & (pre if pos in owned else live):
                raise ValueError("BW_layernorm frame overwrites live relation/authority")
        for tid in allowed:
            if sum(tid in node.outs for node in frame) != 1:
                raise ValueError("BW_layernorm output has multiple writers")

    sn, pn, sf, pf = (f"{segment_id}_{suffix}" for suffix in ("sm_nodes", "pm_nodes", "sm_final", "pm_final"))
    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private def {sn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sf} (store : Store) : Store :=",
        f"  {sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"@[irreducible] private def {pf} (store : Store) : Store :=",
        f"  {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store", "",
    ]

    helper_name = f"{segment_id}_four_input_middle_writer"
    lines.extend(_FOUR_INPUT_WRITER_HELPER.replace("abstract_four_input_middle_writer", helper_name).splitlines())
    lines.append("")

    def writer(name, graph, final_name, nodes_name, frame, position, node, slot):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} store)"
        projection = selected[slot][3]
        apply_lemma = ("applyNode_bw_layernorm_dx_out", "applyNode_bw_layernorm_dw_out", "applyNode_bw_layernorm_db_out")[slot]
        side_conditions = ("", " (by native_decide)", " (by native_decide) (by native_decide)")[slot]
        expression = f"(bw_layernorm ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]}) ({{store}} {node.ins[3]})){projection}"
        lines.extend([
            f"private theorem {theorem_name} (store : Store) :",
            f"    {final} {node.outs[slot]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) store := by",
            f"    unfold {final_name}", "    rfl",
        ])
        prefix = f"({nodes_name}.take {position})"
        suffix = f"({nodes_name}.drop {position + 1})"
        split = f"{prefix} ++ [{_node_text(node)}] ++ {suffix}"
        lines.extend([
            f"  have hnodes : {nodes_name} = {split} := by native_decide",
            f"  exact {helper_name} {graph}",
            f"    {nodes_name} {prefix} {suffix}",
            f"    store {final} {_node_text(node)}",
            f"    {' '.join(map(str, node.ins))} {node.outs[slot]} (fun a b c d => (bw_layernorm a b c d){projection})",
            "    hnodes hfinal (by",
            "      intro t",
            "      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "      simp [applyNodeDistributed, applyNodeRingAttn]",
            f"      exact {apply_lemma} {graph} t {node.rank} {' '.join(map(str, (*node.ins, *node.outs)))}{side_conditions}",
            "    ) (by native_decide) (by native_decide)",
            "    (by native_decide) (by native_decide)",
            "    (by native_decide) (by native_decide)",
            "    (by native_decide) (by native_decide)",
            "    (by native_decide) (by native_decide)",
            "",
        ])
        return theorem_name

    sm_helpers, pm_helpers = {}, {}
    for slot, (_, _, name, _, _) in selected.items():
        sm_helpers[slot] = writer(f"hSm{name}", ir.sm_graph_ref, sf, sn, sm_frame, sm_indices[0] - ss, sm_node, slot)
        pm_helpers[slot] = [writer(f"hPm{name}{rank}", ir.pm_graph_ref, pf, pn, pm_frame, index - ps, node, slot)
                            for rank, (index, node) in enumerate(zip(pm_indices, pm_nodes))]
    vals = lambda record: "[" + ", ".join(f"pmFinal {tid}" for tid in record.pm_tids) + "]"
    shape = lambda sh: _shape_text(list(sh))
    gl, xl = vals(gradient), vals(activation)
    fs, ls, ds = shape(full), shape(local), shape(param)
    def parameter_relation(record):
        if record.kind == "reduction":
            return f"ReductionRel (smFinal {record.sm_tid}) {vals(record)} {ds}"
        return f"ShardedRel (smFinal {record.sm_tid}) {vals(record)} 0 {ds} {ds}"

    premises = [
        f"    (hg : ShardedRel (smFinal {gradient.sm_tid}) {gl} 1 {fs} {ls})",
        f"    (hx : ShardedRel (smFinal {activation.sm_tid}) {xl} 1 {fs} {ls})",
        f"    (hgamma : {parameter_relation(gamma)})",
        f"    (hbeta : {parameter_relation(beta)})",
    ]
    for slot, (_, _, name, projection, theorem) in selected.items():
        out, ol = outputs[slot], vals(outputs[slot])
        lines.extend([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {segment_id}_{name}_semantic (smFinal pmFinal : Store)", *premises,
            f"    (hSm : smFinal {out.sm_tid} = (bw_layernorm (smFinal {gradient.sm_tid}) (smFinal {activation.sm_tid}) (smFinal {gamma.sm_tid}) (smFinal {beta.sm_tid})){projection})",
        ])
        for rank in range(k):
            lines.append(f"    (hPm{rank} : pmFinal {out.pm_tids[rank]} = (bw_layernorm (pmFinal {gradient.pm_tids[rank]}) (pmFinal {activation.pm_tids[rank]}) (pmFinal {gamma.pm_tids[0]}) (pmFinal {beta.pm_tids[0]})){projection})")
        lines.extend([
            f"    : {out.fact_id}.Holds smFinal pmFinal := by",
            f"  have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 1 {k} 0 {gl} := by",
            "    simpa only [List.length_cons, List.length_nil] using hg.full_value",
            f"  have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN 1 {k} 0 {xl} := by",
            "    simpa only [List.length_cons, List.length_nil] using hx.full_value",
        ])
        for label, record in (("gamma", gamma), ("beta", beta)):
            shape_field = "contribution_shapes" if record.kind == "reduction" else "shard_shapes"
            lines.append(f"  have h{label}Shape : (pmFinal {record.pm_tids[0]}).shape = {ds} := h{label}.{shape_field} _ (by simp)")
            if record.kind == "reduction":
                lines.append(f"  have h{label}Value : smFinal {record.sm_tid} = pmFinal {record.pm_tids[0]} := h{label}.singleton_value")
                continue
            lines.extend([
                f"  have h{label}Value : smFinal {record.sm_tid} = pmFinal {record.pm_tids[0]} := by",
                f"    rw [h{label}.full_value]",
                "    simpa only [List.length_cons, List.length_nil] using",
                f"      (allGatherPrimDimN_singleton_eq 0 (pmFinal {record.pm_tids[0]}) (by",
                f"        rw [h{label}.shard_shapes _ (by simp)]; decide))",
            ])
        lines.extend([
            f"  have hComm := {theorem} {k} {b} {s} {d}",
            f"    {gl} {xl} (pmFinal {gamma.pm_tids[0]}) (pmFinal {beta.pm_tids[0]})",
            "    (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes",
        ])
        if slot:
            lines.append("    hgammaShape hbetaShape")
        target = f"allGatherPrimDimN 1 {k} 0 {ol}" if slot == 0 else f"tensorSum {ol}"
        lines.extend([
            f"  have hValue : smFinal {out.sm_tid} = {target} := by",
            "    rw [hSm, hgValue, hxValue, hgammaValue, hbetaValue, hComm]",
            "    simp only [List.zipWith]",
            "    rw [" + ", ".join(f"← hPm{rank}" for rank in range(k)) + "]",
        ])
        shape_lemma = ("bw_layernorm_dx_shape", "bw_layernorm_dw_shape", "bw_layernorm_db_shape")[slot]
        for rank in range(k):
            lines.extend([
                f"  have hShape{rank} : (pmFinal {out.pm_tids[rank]}).shape = {ls if slot == 0 else ds} := by",
                f"    rw [hPm{rank}, {shape_lemma} _ _ _ _ {d} [{s}, {b}] (by rw [hx.shard_shapes _ (by simp)]; rfl)]",
                "    exact " + ("hx.shard_shapes _ (by simp)" if slot == 0 else "hgammaShape" if slot == 1 else "hbetaShape"),
            ])
        lines.extend([
            f"  have hFull : (smFinal {out.sm_tid}).shape = {fs if slot == 0 else ds} := by",
            f"    rw [hSm, {shape_lemma} _ _ _ _ {d} [{s*k}, {b}] (by rw [hx.full_shape]; rfl)]",
            "    exact " + ("hx" if slot == 0 else "hgamma" if slot == 1 else "hbeta") + ".full_shape",
        ])
        if slot == 0:
            lines.extend([
                f"  change ShardedRel (smFinal {out.sm_tid}) {ol} 1 {fs} {ls}",
                "  refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }",
                "  · simpa only [List.length_cons, List.length_nil] using hValue",
                "  · simp only [List.forall_mem_cons]",
                "    exact ⟨" + ", ".join(f"hShape{r}" for r in range(k)) + ", List.forall_mem_nil _⟩",
                "  · simp only [List.length_cons, List.length_nil]", "    decide", "",
            ])
        else:
            lines.extend([
                f"  have hReduce : smFinal {out.sm_tid} = allReducePrim {ol}.length 0 {ol} := by",
                "    rw [hValue]", "    rfl",
                f"  change ReductionRel (smFinal {out.sm_tid}) {ol} {ds}",
                "  refine { full_value := hReduce, full_shape := hFull, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }",
                "  · simp only [List.forall_mem_cons]",
                "    exact ⟨" + ", ".join(f"hShape{r}" for r in range(k)) + ", List.forall_mem_nil _⟩",
                "  · rw [← hReduce]", "    exact hFull", "",
            ])

    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sf} smStore) ({pf} pmStore) := by",
        f"  let smFinal := {sf} smStore", f"  let pmFinal := {pf} pmStore",
        f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {sf} {pf}",
        f"    apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hstate <;> native_decide",
    ])
    for label, record, value_list, axis, full_text, local_text in (
        ("g", gradient, gl, 1, fs, ls), ("x", activation, xl, 1, fs, ls),
        ("gamma", gamma, vals(gamma), 0, ds, ds), ("beta", beta, vals(beta), 0, ds, ds),
    ):
        lines.extend([
            f"  have h{label} : {record.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            (f"  change {parameter_relation(record)} at h{label}" if label in ("gamma", "beta") else
             f"  change ShardedRel (smFinal {record.sm_tid}) {value_list} {axis} {full_text} {local_text} at h{label}"),
        ])
    for slot, (_, _, name, _, _) in selected.items():
        lines.extend([
            f"  have hout{slot} := {segment_id}_{name}_semantic smFinal pmFinal hg hx hgamma hbeta",
            f"    ({sm_helpers[slot]} smStore) " + " ".join(f"({h} pmStore)" for h in pm_helpers[slot]),
        ])
    fresh_text = "[" + ", ".join(r.fact_id for r in outputs.values()) + "]"
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ {fresh_text} ++ {before.state_id}.facts :=",
        f"    (show {after.state_id}.facts ⊆ {fresh_text} ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered", "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
    ])
    if len(outputs) == 1:
        lines.extend(["    subst fact", f"    exact hout{next(iter(outputs))}"])
    else:
        lines.append("    rcases fresh with " + " | ".join("rfl" for _ in outputs))
        lines.extend(f"    · exact hout{slot}" for slot in outputs)
    lines.extend([
        "  · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sn}", f"  pmNodes := {pn}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    have h := {segment_id}_sound smStore pmStore hstate",
        f"    unfold {sf} {pf} at h", "    exact h", "",
    ])
    return "\n".join(lines)
