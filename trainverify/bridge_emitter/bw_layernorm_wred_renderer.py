"""One atomic fold per store: shared LayerNorm triple and independent in-place WRED.

Projection semantics reuse the triple renderer's abstract four-input writer;
WRED reads the initial reduction authority and retires that overwritten fact.
"""
from __future__ import annotations
import re
try:
    from .bw_layernorm_triple_renderer import _FOUR_INPUT_WRITER_HELPER
except ImportError:
    from bw_layernorm_triple_renderer import _FOUR_INPUT_WRITER_HELPER

try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_bw_layernorm_wred_segment(ir, relation, segment_id: str) -> str:
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .closed_fact_sources import fact_tids, source_exact
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import (
            KRankBWLayernormDxCertificate, KRankBWLayernormParamReductionCertificate,
            KRankAllReduceReconstructionCertificate,
        )
    except ImportError:
        from closed_fact_sources import fact_tids, source_exact
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import (
            KRankBWLayernormDxCertificate, KRankBWLayernormParamReductionCertificate,
            KRankAllReduceReconstructionCertificate,
        )

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
    if len(segments) != 1 or len(segments[0].transition_ids) != 4:
        raise ValueError("BW_layernorm requires one to three same-writer projections")
    segment = segments[0]
    transitions = []
    for tid in segment.transition_ids:
        matches = [item for item in relation.transition_specs if item.transition_id == tid]
        if len(matches) != 1:
            raise ValueError("BW_layernorm missing or ambiguous transition")
        if matches[0].fact_only or matches[0].authority_requirements:
            raise ValueError("LayerNorm/WRED does not accept extra authority premises")
        transitions.append(matches[0])
    wreds = [t for t in transitions if t.rule_id == "cross-dp-wred-reconstruction-k-rank"]
    if len(wreds) != 1 or len({t.transition_id for t in relation.transition_specs}) != len(relation.transition_specs):
        raise ValueError("LayerNorm/WRED requires exact four transition identities")
    wt = wreds[0]
    wc = _select_exact_typed_certificate(relation, wt, wt.rule_id,
        "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",
        KRankAllReduceReconstructionCertificate, lambda c: ((c.input_fact,), (c.output_fact,)))
    transitions = [t for t in transitions if t is not wt]
    rules = [item.rule_id for item in transitions]
    if (len(set(rules)) != len(rules) or set(rules) != set(families)
            or not any(families[rule][0] != 0 for rule in rules)):
        raise ValueError("BW_layernorm parameter projection family set mismatch")

    def certificate_inputs(cert):
        return cert.gradient_fact, cert.activation_fact, cert.gamma_fact, cert.beta_fact

    selected = {}
    for transition in transitions:
        slot, name, projection, cert_type, theorem = families[transition.rule_id]
        cert = _select_exact_typed_certificate(
            relation, transition, transition.rule_id, theorem, cert_type,
            lambda c: (tuple(sorted(certificate_inputs(c))), (c.output_fact,)),
        )
        if slot and cert.projection != projection:
            raise ValueError("BW_layernorm parameter projection mismatch")
        selected[slot] = (transition, cert, name, projection, theorem)
    # Canonical projection order is independent of dependency-scheduler ordering.
    selected = dict(sorted(selected.items()))
    transition, certificate, _, _, _ = next(iter(selected.values()))
    if any(certificate_inputs(c) != certificate_inputs(certificate) for _, c, _, _, _ in selected.values()):
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
        wpre, wpost = records[wc.input_fact], records[wc.output_fact]
        gradient, activation, gamma, beta = (records[f] for f in certificate_inputs(certificate))
        outputs = {slot: records[c.output_fact] for slot, (_, c, _, _, _) in selected.items()}
        states = {item.state_id: item for item in chain.states}
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("BW_layernorm relation fact/state is not materialized") from exc
    if len(states) != len(chain.states):
        raise ValueError("BW_layernorm ambiguous state identity")
    required = {r.fact_id for r in (gradient, activation, gamma, beta, wpre)}
    fresh = {r.fact_id for r in (*outputs.values(), wpost)}
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

    sm_start, sm_end, pm_start, pm_end = ss, se, ps, pe
    wred_nodes = []
    for transition, cert, pre, post in [(wt, wc, wpre, wpost)]:
        if (transition.sm_node_indices != () or len(transition.pm_node_indices) != 1
                or cert.rank_count != len(pre.pm_tids) or pre.kind != "reduction"
                or post.kind != "joined" or post.sm_tid != pre.sm_tid
                or post.joined_pm_tid is None or post.full_shape != pre.full_shape):
            raise ValueError("BW_gelu/WRED relation authority mismatch")
        index = transition.pm_node_indices[0]
        if not (pm_start <= index < pm_end):
            raise ValueError("BW_gelu/WRED writer lies outside complete PM frame")
        node = ir.pm_nodes[index]
        if (node.rank != 0 or node.op != "CROSS_DP_WRED" or node.params
                or tuple(node.ins) != pre.pm_tids or node.outs != [node.ins[0]]
                or post.joined_pm_tid != node.outs[0]
                or cert.pm_allreduce_step != f"pm:{index}:0"):
            raise ValueError("BW_gelu/WRED literal writer mismatch")
        wred_nodes.append((index, node, pre, post))

    if (not chain.complete or ir.sm_num_ranks != 1 or wc.rank_count != k
            or wc.full_shape != wpre.full_shape or chain.anchor_fact is None
            or chain.anchor_fact.fact_id not in before.fact_ids
            or chain.anchor_fact.fact_id not in after.fact_ids
            or wpre.fact_id in after.fact_ids):
        raise ValueError("LayerNorm/WRED rank, retirement or public anchor mismatch")
    for state in (before, after):
        if len(set(state.fact_ids)) != len(state.fact_ids):
            raise ValueError("LayerNorm/WRED duplicate state facts")
    if (wpre.gather_dim is not None or wpost.gather_dim is not None
            or wpost.pm_tids or len(set(wpre.pm_tids)) != k
            or any(type(n) is not int or n <= 0 for n in wpre.full_shape)):
        raise ValueError("LayerNorm/WRED reduction/joined metadata mismatch")
    # Preserve the historical source-validation diagnostic prefix.
    for f in (gradient, activation, gamma, beta, wpre):
        source_exact(ir, f, ss, ps, context="BW_gelu/WRED")
    for f in (*outputs.values(), wpost):
        source_exact(ir, f, se, pe, context="BW_gelu/WRED")
    all_records = {**by_id, **authority}
    sm_writes = {t for n in sm_frame for t in n.outs}
    pm_writes = {t for n in pm_frame for t in n.outs}
    for fid in before.fact_ids:
        if fid not in all_records:
            raise ValueError("LayerNorm/WRED missing live fact")
        if fid == wpre.fact_id:
            continue
        st, pt = fact_tids(all_records[fid])
        if st & sm_writes or pt & pm_writes:
            raise ValueError("LayerNorm/WRED frame overwrites live authority")
    wi = wt.pm_node_indices[0]
    if (wpre.sm_tid in sm_writes
            or any(set(n.outs) & set(wpre.pm_tids) for n in ir.pm_nodes[ps:wi])
            or any(wpost.joined_pm_tid in n.outs for n in ir.pm_nodes[wi+1:pe])):
        raise ValueError("LayerNorm/WRED requires independent prior reduction authority")
    for nodes, tids in ((sm_frame, [o.sm_tid for o in outputs.values()]),
                        (pm_frame, [t for o in outputs.values() for t in o.pm_tids])):
        for tid in tids:
            if sum(tid in n.outs for n in nodes) != 1:
                raise ValueError("LayerNorm/WRED same-store output overwrite")

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

    frame_state_name = f"{segment_id}_frameable"
    frameable_ids = tuple(fid for fid in before.fact_ids if fid != wpre.fact_id)
    lines.extend([f"private def {frame_state_name} : RelationState where",
        f"  facts := [{', '.join(frameable_ids)}]", "  nonempty := by native_decide", ""])
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
    wred_helpers = []
    for ordinal, (index, node, pre, post) in enumerate(wred_nodes):
        name = f"{segment_id}_wred_writer_{ordinal}"
        position = index - ps
        prefix = f"({pn}.take {position})"
        suffix = f"({pn}.drop {position + 1})"
        inputs = "[" + ", ".join(str(tid) for tid in node.ins) + "]"
        lines.extend([
            f"private theorem {name} (pmStore : Store) :",
            f"    ({pf} pmStore) {node.outs[0]} = cross_dp_wred ({inputs}.map pmStore) := by",
            f"  have hfinal : {pf} pmStore = {pn}.foldl",
            f"      (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by",
            f"    unfold {pf}", "    rfl",
            f"  have hnodes : {pn} = {prefix} ++ [{_node_text(node)}] ++ {suffix} := by native_decide",
            f"  have hprefix : ({pf} pmStore) {node.outs[0]} =",
            f"      cross_dp_wred ({inputs}.map ({prefix}.foldl",
            f"        (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore)) := by",
            "    rw [hfinal, hnodes]",
            f"    exact foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix}",
            f"      {_node_text(node)} {node.outs[0]}",
            f"      (fun t => cross_dp_wred ({inputs}.map t)) (by",
            "        intro t",
            "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "          (hshuffle := by native_decide) (hunshuffle := by native_decide)",
            "          (hattn := by native_decide)]",
            "        unfold applyNodeDistributed",
            "        rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"        · exact applyNode_cross_dp_wred_out {ir.pm_graph_ref} t 0 {inputs} {node.outs[0]}",
            "        · native_decide", "        · native_decide",
            "      ) (by native_decide) (by native_decide)",
        ])
        read_names = []
        for rank, tid in enumerate(node.ins):
            read_name = f"hread{rank}"
            read_names.append(read_name)
            lines.extend([
                f"  have {read_name} : ({prefix}.foldl",
                f"      (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {tid} = pmStore {tid} :=",
                f"    foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
                f"      {prefix} pmStore {tid} (by native_decide) (by native_decide)",
            ])
        lines.extend(["  simp only [List.map] at hprefix ⊢",
                      f"  rw [{', '.join(read_names)}] at hprefix", "  exact hprefix", ""])
        wred_helpers.append(name)

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
        f"  have hFrameInitial : {frame_state_name}.Holds smStore pmStore := by",
        "    intro fact hfact",
        f"    exact hstate fact ((show {frame_state_name}.facts ⊆ {before.state_id}.facts by native_decide) hfact)",
        f"  have hframe : {frame_state_name}.Holds smFinal pmFinal := by",
        f"    unfold smFinal pmFinal {sf} {pf}",
        f"    apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hFrameInitial <;> native_decide",
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
    for ordinal, ((index, node, pre, post), helper) in enumerate(zip(wred_nodes, wred_helpers)):
        inputs = "[" + ", ".join(str(tid) for tid in node.ins) + "]"
        shape = _shape_text(list(pre.full_shape))
        hout = f"houtWred{ordinal}"
        lines.extend([
            f"  have hinWred{ordinal} : {pre.fact_id}.Holds smStore pmStore :=",
            f"    hstate {pre.fact_id} (by native_decide)",
            f"  change ReductionRel (smStore {pre.sm_tid}) ({inputs}.map pmStore) {shape} at hinWred{ordinal}",
            f"  have hWredWriter{ordinal} := {helper} pmStore",
            f"  change pmFinal {post.joined_pm_tid} = cross_dp_wred ({inputs}.map pmStore) at hWredWriter{ordinal}",
            f"  have hWredReduce{ordinal} : pmFinal {post.joined_pm_tid} =",
            f"      allReducePrim ({inputs}.map pmStore).length 0 ({inputs}.map pmStore) := by",
            f"    rw [hWredWriter{ordinal}]",
            "    exact cross_dp_wred_eq_allReducePrim _ (by simp)",
            f"  have hSmRead{ordinal} : smFinal {pre.sm_tid} = smStore {pre.sm_tid} := by",
            f"    unfold smFinal {sf}",
            f"    exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref}",
            f"      {sn} smStore {pre.sm_tid} (by native_decide) (by native_decide)",
            f"  have hJoined{ordinal} : smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} := by",
            f"    rw [hSmRead{ordinal}]",
            f"    exact hinWred{ordinal}.full_value.trans hWredReduce{ordinal}.symm",
            f"  have {hout} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"    change smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} ∧ _ ∧ _",
            f"    refine ⟨hJoined{ordinal}, ?_, ?_⟩",
            f"    · rw [hSmRead{ordinal}]", f"      exact hinWred{ordinal}.full_shape",
            f"    · rw [← hJoined{ordinal}, hSmRead{ordinal}]", f"      exact hinWred{ordinal}.full_shape",
        ])
    fresh_text = "[" + ", ".join(r.fact_id for r in (*outputs.values(), wpost)) + "]"
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ {fresh_text} ++ {frame_state_name}.facts :=",
        f"    (show {after.state_id}.facts ⊆ {fresh_text} ++ {frame_state_name}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered", "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
    ])
    if len(outputs) == 1:
        lines.extend(["    subst fact", f"    exact hout{next(iter(outputs))}"])
    else:
        lines.append("    rcases fresh with " + " | ".join("rfl" for _ in range(4)))
        lines.extend(f"    · exact hout{slot}" for slot in outputs)
        lines.append("    · exact houtWred0")
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
