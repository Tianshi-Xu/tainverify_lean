"""One-frame renderer for paired InnerChunk CE fst/snd projections."""
from __future__ import annotations

from dataclasses import asdict
import hashlib
import json


def _digest(certificate) -> str:
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        sort_keys=True, separators=(",", ":"),
    ).encode()).hexdigest()


def render_closed_ce_dual_projection_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import InnerChunkCEGatherCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import InnerChunkCEGatherCertificate

    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("dual CE renderer requires a complete closed chain")
    segments = [s for s in chain.segments if s.segment_id == segment_id]
    if len(segments) != 1 or len(segments[0].transition_ids) != 2:
        raise ValueError("dual CE component requires exactly two transitions")
    segment = segments[0]
    by_id = {t.transition_id: t for t in relation.transition_specs}
    transitions = tuple(by_id[x] for x in segment.transition_ids)
    certs = []
    for transition in transitions:
        matches = [
            c for c in relation.certificates
            if type(c) is InnerChunkCEGatherCertificate
            and c.rule_id == transition.rule_id
            and c.lean_theorem == transition.lean_theorem
            and _digest(c) == transition.certificate_digest
        ]
        if len(matches) != 1:
            raise ValueError("dual CE transition lacks one exact certificate")
        certs.append(matches[0])
    by_projection = {c.output_projection: (t, c) for t, c in zip(transitions, certs)}
    if set(by_projection) != {".fst", ".snd"} or len(by_projection) != 2:
        raise ValueError("dual CE projections are not exactly fst/snd")
    fst_t, fst_c = by_projection[".fst"]
    snd_t, snd_c = by_projection[".snd"]
    if fst_c.label_bound is None or snd_c.label_bound is not None:
        raise ValueError("dual CE label bound is not isolated to fst")

    sm_indices = set(fst_t.sm_node_indices) | set(snd_t.sm_node_indices)
    pm_indices = set(fst_t.pm_node_indices) | set(snd_t.pm_node_indices)
    if (len(sm_indices) != 1 or len(pm_indices) != 4
            or sm_indices != set(range(*segment.sm_range))
            or pm_indices != set(range(*segment.pm_range))):
        raise ValueError("dual CE writer union does not equal the atomic frame")
    sm_index = next(iter(sm_indices))
    common_pm = set(fst_t.pm_node_indices) & set(snd_t.pm_node_indices)
    if len(common_pm) != 2:
        raise ValueError("dual CE projections do not share exactly two PM CE writers")
    sm = ir.sm_nodes[sm_index]
    p0, p1 = sorted((ir.pm_nodes[i] for i in common_pm), key=lambda n: n.rank)
    fst_gather_index = next(iter(set(fst_t.pm_node_indices) - common_pm))
    snd_gather_index = next(iter(set(snd_t.pm_node_indices) - common_pm))
    fst_gather = ir.pm_nodes[fst_gather_index]
    snd_gather = ir.pm_nodes[snd_gather_index]
    if (sm.op != "FW_inner_chunk_ce" or p0.op != sm.op or p1.op != sm.op
            or (sm.rank, p0.rank, p1.rank) != (0, 0, 1)
            or fst_gather.ins != [p0.outs[0], p1.outs[0]]
            or snd_gather.ins != [p0.outs[1], p1.outs[1]]
            or fst_gather.outs != [sm.outs[0]] or snd_gather.outs != [sm.outs[1]]
            or any(g.op != "AllGatherPrim" or g.rank != 0 or g.params != [0]
                   for g in (fst_gather, snd_gather))):
        raise ValueError("dual CE node topology disagrees")

    records = {f.source: f for f in chain.relation_facts}
    fst_pres = [records[x] for x in fst_t.pre_facts]
    snd_pres = [records[x] for x in snd_t.pre_facts]
    activations = [f for f in fst_pres if f.kind == "ordinary"]
    chunks = [f for f in fst_pres if f.kind == "label_chunks"]
    snd_activations = [f for f in snd_pres if f.kind == "ordinary"]
    if len(activations) != 1 or len(chunks) != 1 or snd_activations != activations:
        raise ValueError("dual CE input relation roles disagree")
    activation, label_chunks = activations[0], chunks[0]
    fst_post = records[fst_t.post_facts[0]]
    snd_post = records[snd_t.post_facts[0]]
    if any(f.kind != "joined_ordinary" for f in (fst_post, snd_post)):
        raise ValueError("dual CE outputs are not joined ordinary")
    rows, hidden = activation.shard_shape
    weight, full_label = sm.ins[1], sm.ins[2]
    authority = list(chain.authority_facts)
    def one(kind, pred, label):
        found = [f for f in authority if f.kind == kind and pred(f)]
        if len(found) != 1:
            raise ValueError(f"dual CE {label} authority mismatch")
        return found[0]
    weight_eq = one("tensor_eq", lambda f: (f.left_side, f.left_tid, f.right_side, f.right_tid) == ("sm", weight, "pm", weight), "weight equality")
    weight_shape = one("tensor_shape", lambda f: (f.side, f.tid) == ("pm", weight), "weight shape")
    label_eq = one("tensor_eq", lambda f: (f.left_side, f.left_tid, f.right_side, f.right_tid) == ("sm", full_label, "pm", full_label), "label equality")
    label_shape = one("tensor_shape", lambda f: (f.side, f.tid) == ("pm", full_label), "label shape")
    vocab = weight_shape.shape[0]
    label_bound = one("label_bound", lambda f: (f.side, f.tid, f.length, f.upper_bound) == ("pm", full_label, rows * 2, vocab), "label bound")
    states = {s.state_id: s for s in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {activation.fact_id, label_chunks.fact_id, weight_eq.fact_id, weight_shape.fact_id,
                label_eq.fact_id, label_shape.fact_id, label_bound.fact_id}
    fresh = {fst_post.fact_id, snd_post.fact_id}
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids) or not set(after.fact_ids) <= set(before.fact_ids) | fresh:
        raise ValueError("dual CE liveness disagrees")

    sm_nodes = [ir.sm_nodes[i] for i in range(*segment.sm_range)]
    pm_nodes = [ir.pm_nodes[i] for i in range(*segment.pm_range)]
    sm_text = "[" + ", ".join(_node_text(n) for n in sm_nodes) + "]"
    pm_text = "[" + ", ".join(_node_text(n) for n in pm_nodes) + "]"
    sid = segment_id; sm_graph, pm_graph = ir.sm_graph_ref, ir.pm_graph_ref
    params = _shape_text(sm.params or [])
    zscale = f"((({params}.getD 1 0 : Nat) : Scalar))"
    full = _shape_text(activation.full_shape); shard = _shape_text(activation.shard_shape)
    out_full = _shape_text(fst_post.full_shape); out_shard = _shape_text(fst_post.shard_shape)
    wshape = _shape_text(weight_shape.shape); lshape = _shape_text(label_shape.shape)

    def ce_expr(store, node, output):
        projection = "fst" if output == 0 else "snd"
        return (f"(fw_inner_chunk_ce ({store} {node.ins[0]}) ({store} {node.ins[1]}) "
                f"({store} {node.ins[2]}) ((({store} {node.ins[1]}).shape.head?).getD 0) {zscale}).{projection}")

    def ce_writer(name, graph, store, final, nodes_name, nodes, node_index, output):
        pos = node_index - (segment.sm_range[0] if store == "smStore" else segment.pm_range[0])
        node = nodes[pos]; prefix_nodes = nodes[:pos]; suffix_nodes = nodes[pos + 1:]
        prefix = "[" + ", ".join(_node_text(n) for n in prefix_nodes) + "]"
        suffix = "[" + ", ".join(_node_text(n) for n in suffix_nodes) + "]"
        prefix_store = store if not prefix_nodes else f"{prefix}.foldl (applyNodeDistributedFaithful {graph}) {store}"
        lemma = "fst" if output == 0 else "snd"
        apply_lemma = (
            f"applyNode_fw_inner_chunk_ce_fst_out_1p {graph} t {node.rank} "
            f"{node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} {params}"
            if output == 0 else
            f"applyNode_fw_inner_chunk_ce_snd_out_1p {graph} t {node.rank} "
            f"{node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} "
            f"(by decide) (params := {params})"
        )
        lines = [f"    have {name} : {final} {node.outs[output]} = {ce_expr(store, node, output)} := by", "      calc",
                 f"        {final} {node.outs[output]} = {ce_expr(prefix_store, node, output)} := by",
                 f"          unfold {final} {nodes_name}",
                 f"          rw [show ({'[' + ', '.join(_node_text(n) for n in nodes) + ']'} : List NodeDecl) = {prefix} ++ [{_node_text(node)}] ++ {suffix} by native_decide]",
                 f"          exact foldl_faithful_middle_writer {graph} {store} {prefix} {suffix} {_node_text(node)} {node.outs[output]}",
                 f"            (fun t => {ce_expr('t', node, output)}) (by", "              intro t",
                 "              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
                 "                (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
                 "              unfold applyNodeDistributed", "              rw [if_neg (by decide)]",
                 "              rw [applyNodeRingAttn_eq_applyNode_of_not_ring]",
                 f"              · exact {apply_lemma}",
                 "              · decide", "              · decide", "            ) (by native_decide) (by native_decide)"]
        if prefix_nodes:
            lines.append(f"        _ = {ce_expr(store, node, output)} := by")
            for tid in dict.fromkeys(node.ins):
                lines.append(f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} {prefix} {store} {tid} (by native_decide) (by native_decide)]")
        else:
            lines.append("        _ = _ := rfl")
        return lines

    def gather_writer(name, gather_index, gather):
        pos = gather_index - segment.pm_range[0]; prefix_nodes = pm_nodes[:pos]; suffix_nodes = pm_nodes[pos + 1:]
        prefix = "[" + ", ".join(_node_text(n) for n in prefix_nodes) + "]"; suffix = "[" + ", ".join(_node_text(n) for n in suffix_nodes) + "]"
        tail = "[" + ", ".join(_node_text(n) for n in [gather, *suffix_nodes]) + "]"
        gt = _node_text(gather)
        return [f"    have {name} : pmFinal {gather.outs[0]} = allGatherPrimDimN 0 2 0 [pmFinal {gather.ins[0]}, pmFinal {gather.ins[1]}] := by",
                f"      have hw : pmFinal {gather.outs[0]} = allGatherPrimDimN 0 2 0 [({prefix}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[0]}, ({prefix}.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore) {gather.ins[1]}] := by",
                "        unfold pmFinal pmNodes",
                f"        rw [show ({pm_text} : List NodeDecl) = {prefix} ++ [{gt}] ++ {suffix} by native_decide]",
                f"        exact foldl_faithful_middle_writer {pm_graph} pmStore {prefix} {suffix} {gt} {gather.outs[0]}",
                f"          (fun t => allGatherPrimDimN 0 2 0 [t {gather.ins[0]}, t {gather.ins[1]}]) (by",
                "            intro t", "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
                "              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
                "            unfold applyNodeDistributed", "            rw [if_neg (by decide)]", "            rw [applyNodeRingAttn_eq_applyNode_of_not_ring]",
                f"            · exact applyNode_allGatherPrimDimN_out {pm_graph} t 0 [{gather.ins[0]}, {gather.ins[1]}] {gather.outs[0]} 0",
                "            · decide", "            · decide", "          ) (by native_decide) (by native_decide)",
                f"      have h0 := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore {prefix} {tail} {gather.ins[0]} (by native_decide) (by native_decide)",
                f"      have h1 := foldl_faithful_prefix_read_eq_final {pm_graph} pmStore {prefix} {tail} {gather.ins[1]} (by native_decide) (by native_decide)",
                "      change _ = pmFinal _ at h0 h1", "      rw [h0, h1] at hw", "      exact hw"]

    snd_core = f"{sid}_snd_core"
    core_lines = [
        "set_option maxHeartbeats 500000 in",
        f"private theorem {snd_core} (x0 x1 w y : Tensor)",
        f"    (h0 : x0.shape = {shard}) (h1 : x1.shape = {shard})",
        f"    (hw : w.shape = {wshape}) :",
        f"    (fw_inner_chunk_ce (allGatherPrimDimN 0 2 0 [x0, x1]) w y {vocab} {zscale}).snd =",
        f"      allGatherPrimDimN 0 2 0 [(fw_inner_chunk_ce x0 w y {vocab} {zscale}).snd,",
        f"        (fw_inner_chunk_ce x1 w y {vocab} {zscale}).snd] := by",
        f"  exact fw_inner_chunk_ce_snd_allGatherDim0_shards 2 {rows} {hidden} {vocab} {zscale}",
        "    [x0, x1] w y (by decide) (by decide) (by decide) (by decide) (by exact h0)",
        "    (by",
        "      intro r hr",
        "      have h : r = 0 ∨ r = 1 := by omega",
        "      rcases h with rfl | rfl",
        "      · simpa only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] using h0",
        "      · simpa only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] using h1)",
        "    hw",
        "",
    ]
    lines = core_lines + [f"private def {sid} :", f"    ClosedDepSegmentCertificate {sm_graph} {pm_graph} {before.state_id} {after.state_id} where",
             f"  smNodes := {sm_text}", f"  pmNodes := {pm_text}", "  sound := by", "    intro smStore pmStore hstate",
             f"    have hActivation : {activation.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
             f"    have hWeightEq : {weight_eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
             f"    have hWeightShape : {weight_shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
             f"    change GeneratedPatterns.Ordinary2Rel (smStore {sm.ins[0]}) (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) {full} {shard} at hActivation",
             f"    change smStore {weight} = pmStore {weight} at hWeightEq",
             f"    change (pmStore {weight}).shape = {wshape} at hWeightShape",
             f"    have hVocab : (((pmStore {weight}).shape.head?).getD 0) = {vocab} := by rw [hWeightShape]; rfl"]
    lines += [
        f"    have hPm0Labels : {ce_expr('pmStore',p0,1)} = {ce_expr('smStore',sm,1).replace('smStore '+str(sm.ins[0]), 'pmStore '+str(p0.ins[0])).replace('smStore '+str(weight), 'pmStore '+str(weight))} := by",
        "      exact RelationCompiler.inner_chunk_ce_snd_labels_independent _ _ _ _ _ _",
        f"    have hPm1Labels : {ce_expr('pmStore',p1,1)} = {ce_expr('smStore',sm,1).replace('smStore '+str(sm.ins[0]), 'pmStore '+str(p1.ins[0])).replace('smStore '+str(weight), 'pmStore '+str(weight))} := by",
        "      exact RelationCompiler.inner_chunk_ce_snd_labels_independent _ _ _ _ _ _",
        "    have hSCore : " + ce_expr("smStore",sm,1) + " = allGatherPrimDimN 0 2 0 [" + ce_expr("pmStore",p0,1) + ", " + ce_expr("pmStore",p1,1) + "] := by",
        "      rw [hPm0Labels, hPm1Labels, hWeightEq, hActivation.full_value, hVocab]",
        f"      rw [{snd_core} (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]})",
        f"        (pmStore {weight}) (smStore {full_label})",
        "        hActivation.rank0_shape hActivation.rank1_shape hWeightShape]",
        f"    let smNodes : List NodeDecl := {sm_text}",
        f"    let pmNodes : List NodeDecl := {pm_text}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {sm_graph}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pm_graph}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide",
        f"    have hChunks : {label_chunks.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hLabelEq : {label_eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hLabelShape : {label_shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    have hLabelBound : {label_bound.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"    change pmStore {p0.ins[2]} = chunkPrimDimN 0 2 0 (pmStore {full_label}) ∧ pmStore {p1.ins[2]} = chunkPrimDimN 0 2 1 (pmStore {full_label}) ∧ _ at hChunks",
        f"    change smStore {full_label} = pmStore {full_label} at hLabelEq",
        f"    change (pmStore {full_label}).shape = {lshape} at hLabelShape",
        f"    change (∀ i < {rows*2}, scalarToNat (valAt (pmStore {full_label}) i) < {vocab}) at hLabelBound",
    ]
    for output, suffix in ((0,"F"),(1,"S")):
        lines += ce_writer(f"hSm{suffix}", sm_graph, "smStore", "smFinal", "smNodes", sm_nodes, sm_index, output)
        lines += ce_writer(f"hP0{suffix}", pm_graph, "pmStore", "pmFinal", "pmNodes", pm_nodes, next(i for i in common_pm if ir.pm_nodes[i].rank==0), output)
        lines += ce_writer(f"hP1{suffix}", pm_graph, "pmStore", "pmFinal", "pmNodes", pm_nodes, next(i for i in common_pm if ir.pm_nodes[i].rank==1), output)
    lines += gather_writer("hGatherF", fst_gather_index, fst_gather)
    lines += gather_writer("hGatherS", snd_gather_index, snd_gather)
    lines += ["    have hFCore := GeneratedPatterns.fw_inner_chunk_ce_fst_allGather0_commute_2_of",
              f"      (pmStore {p0.ins[0]}) (pmStore {p1.ins[0]}) (pmStore {weight}) (pmStore {full_label})",
              f"      {rows} {hidden} {vocab} (by decide) (by decide) (by decide)",
              "      hActivation.rank0_shape hActivation.rank1_shape hWeightShape",
              "      (by simpa only [Nat.reduceMul] using hLabelShape) hLabelBound " + zscale]
    def output(name, post, output_index, core, gather_name):
        writer_suffix = "F" if output_index == 0 else "S"
        value_rewrites = (
            f"hSm{writer_suffix}, hP0{writer_suffix}, hP1{writer_suffix}, "
            "hWeightEq, hActivation.full_value, hLabelEq, hChunks.1, hChunks.2.1, hVocab"
            if output_index == 0 else
            f"hSm{writer_suffix}, hP0{writer_suffix}, hP1{writer_suffix}"
        )
        return [f"    have {name} : {post.fact_id}.Holds smFinal pmFinal := by",
                f"      change JoinedOrdinary2Rel (smFinal {sm.outs[output_index]}) (pmFinal {p0.outs[output_index]}) (pmFinal {p1.outs[output_index]}) (pmFinal {(fst_gather if output_index==0 else snd_gather).outs[0]}) {out_full} {out_shard}",
                f"      have hOrd : GeneratedPatterns.Ordinary2Rel (smFinal {sm.outs[output_index]}) (pmFinal {p0.outs[output_index]}) (pmFinal {p1.outs[output_index]}) {out_full} {out_shard} := by",
                "        refine { full_value := ?_, full_shape := ?_, rank0_shape := ?_, rank1_shape := ?_ }",
                f"        · rw [{value_rewrites}]",
                f"          exact {core}",
                f"        · rw [hSm{'F' if output_index==0 else 'S'}]", f"          exact fw_inner_chunk_ce_{'fst' if output_index==0 else 'snd'}_shape _ _ _ _ _ {rows*2} (by rw [hActivation.full_shape]; rfl)",
                f"        · rw [hP0{'F' if output_index==0 else 'S'}]", f"          exact fw_inner_chunk_ce_{'fst' if output_index==0 else 'snd'}_shape _ _ _ _ _ {rows} (by rw [hActivation.rank0_shape]; rfl)",
                f"        · rw [hP1{'F' if output_index==0 else 'S'}]", f"          exact fw_inner_chunk_ce_{'fst' if output_index==0 else 'snd'}_shape _ _ _ _ _ {rows} (by rw [hActivation.rank1_shape]; rfl)",
                f"      refine {{ toOrdinary2Rel := hOrd, joined_value := {gather_name}, public_value := ?_ }}",
                f"      exact hOrd.full_value.trans {gather_name}.symm"]
    lines += output("hOutF",fst_post,0,"hFCore","hGatherF")
    lines += output("hOutS",snd_post,1,"hSCore","hGatherS")
    lines += ["    intro fact hfact", f"    have covered : fact ∈ [{fst_post.fact_id}, {snd_post.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{fst_post.fact_id}, {snd_post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
              "    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
              "    rcases covered with (rfl | rfl) | old", "    · exact hOutF", "    · exact hOutS", "    · exact hframe fact old", ""]
    return "\n".join(lines)
