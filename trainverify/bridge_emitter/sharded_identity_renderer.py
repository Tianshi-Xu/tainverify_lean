"""Closed dynamic-K shape-identity view/reshape over ShardedRel."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict


def _digest(c):
    return hashlib.sha256(json.dumps({"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def render_closed_sharded_identity_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import get_closed_rule_spec
    chain = relation.dependent_chain_plan
    seg = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if seg is None or len(seg.transition_ids) != 1:
        raise ValueError("sharded identity requires one transition")
    t = {x.transition_id: x for x in relation.transition_specs}[seg.transition_ids[0]]
    spec = get_closed_rule_spec(t.rule_id)
    op = spec.op
    if op is None or t.lean_theorem not in spec.lean_theorems:
        raise ValueError("sharded identity theorem identity disagrees")
    matches = [c for c in relation.certificates if type(c) is spec.certificate_type
               and c.rule_id == t.rule_id and c.lean_theorem == t.lean_theorem
               and (c.input_fact,) == t.pre_facts and (c.output_fact,) == t.post_facts
               and _digest(c) == t.certificate_digest]
    if len(matches) != 1:
        raise ValueError("sharded identity lacks one exact certificate")
    c = matches[0]
    records = {f.source: f for f in chain.relation_facts}; states = {s.state_id: s for s in chain.states}
    pre, post = records[c.input_fact], records[c.output_fact]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    k = c.rank_count
    if (k <= 0 or k != ir.pm_num_ranks or pre.kind != "sharded" or post.kind != "sharded"
            or pre.gather_dim != post.gather_dim or len(pre.pm_tids) != k or len(post.pm_tids) != k
            or (pre.full_shape, pre.shard_shape) != (post.full_shape, post.shard_shape)
            or c.gather_dim != pre.gather_dim or tuple(c.full_shape) != pre.full_shape
            or tuple(c.shard_shape) != pre.shard_shape):
        raise ValueError("sharded identity relation metadata disagrees")
    if (len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != k
            or tuple(range(*seg.sm_range)) != t.sm_node_indices
            or tuple(range(*seg.pm_range)) != t.pm_node_indices):
        raise ValueError("sharded identity footprint is not exact 1xK")
    sm = ir.sm_nodes[t.sm_node_indices[0]]; pms = tuple(ir.pm_nodes[i] for i in t.pm_node_indices)
    nodes = (sm, *pms)
    if ((sm.rank, *(n.rank for n in pms)) != (0, *range(k))
            or any(n.op != op or len(n.ins) != 1 or len(n.outs) != 1 or not n.params for n in nodes)
            or (sm.ins[0], *(n.ins[0] for n in pms)) != (pre.sm_tid, *pre.pm_tids)
            or (sm.outs[0], *(n.outs[0] for n in pms)) != (post.sm_tid, *post.pm_tids)
            or tuple(sm.params) != pre.full_shape
            or any(tuple(n.params) != pre.shard_shape for n in pms)):
        raise ValueError("sharded identity writer topology disagrees")
    if (pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= set(before.fact_ids) | {post.fact_id}):
        raise ValueError("sharded identity liveness disagrees")
    sid = segment_id; smn=f"{sid}_smNodes"; pmn=f"{sid}_pmNodes"; smf=f"{sid}_smFinal"; pmf=f"{sid}_pmFinal"
    smt = _node_text(sm); pmts = tuple(_node_text(n) for n in pms)
    lines = [
        f"private def {smn} : List NodeDecl := [{smt}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(pmts)}]",
        f"@[irreducible] private def {smf} (s : Store) := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
    ]
    def writer(name, graph, store, final, nodes_name, frame, pos, node, target):
        prefix, suffix = frame[:pos], frame[pos+1:]
        if op == "FW_view":
            apply = f"exact applyNode_fw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.outs[0]}"
        else:
            apply = f"exact applyNode_fw_reshape_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {_shape_text(node.params)}"
        lines.extend([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {name} ({store} : Store) : ({final} {store}) {node.outs[0]} = fw_view {_shape_text(list(target))} ({store} {node.ins[0]}) := by",
            f"  unfold {final}", f"  simpa [{nodes_name}] using",
            f"    (foldl_faithful_unary_middle_writer {graph} {store} [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}] {_node_text(node)}",
            f"      {node.ins[0]} {node.outs[0]} (fun x => fw_view {_shape_text(list(target))} x) (by",
            "        intro t", "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "        simp [applyNodeDistributed, applyNodeRingAttn]", f"        {apply}",
            "      ) (by native_decide) (by native_decide) (by native_decide) (by native_decide))",
        ])
    writer(f"{sid}_smWriter", ir.sm_graph_ref, "smStore", smf, smn, (sm,), 0, sm, pre.full_shape)
    for rank,node in enumerate(pms):
        writer(f"{sid}_pmWriter{rank}", ir.pm_graph_ref, "pmStore", pmf, pmn, pms, rank, node, pre.shard_shape)
    full, shard = _shape_text(list(pre.full_shape)), _shape_text(list(pre.shard_shape))
    pre_list = "[" + ", ".join(f"pmStore {tid}" for tid in pre.pm_tids) + "]"
    post_list = "[" + ", ".join(f"({pmf} pmStore) {tid}" for tid in post.pm_tids) + "]"
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    unfold {smf} {pmf}", f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
        f"  have hin : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"  have hout : {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    change ShardedRel (smStore {pre.sm_tid}) {pre_list} {pre.gather_dim} {full} {shard} at hin",
        f"    have core := ShardedRel.fw_view_id hin",
        f"    change ShardedRel (({smf} smStore) {post.sm_tid}) {post_list} {post.gather_dim} {full} {shard}",
        f"    rw [{sid}_smWriter smStore, " + ", ".join(f"{sid}_pmWriter{r} pmStore" for r in range(k)) + "]",
        "    simpa only [List.map] using core",
        "  intro fact hfact",
        f"  have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
        "  rcases covered with rfl | old", "  · exact hout", "  · exact hframe fact old",
        f"private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {smn}", f"  pmNodes := {pmn}", "  sound := by",
        "    intro smStore pmStore hstate", f"    simpa only [{smf}, {pmf}] using {sid}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
