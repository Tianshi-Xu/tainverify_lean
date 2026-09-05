"""Atomic shared-writer renderer for ordinary and sharded identity reshape/view."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict


def _digest(certificate) -> str:
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        separators=(",", ":"), sort_keys=True,
    ).encode()).hexdigest()


def render_closed_mixed_identity_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import FrontierIdentityViewCertificate, KRankContiguousRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import FrontierIdentityViewCertificate, KRankContiguousRelationCertificate
    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("mixed identity requires one complete segment")
    segment = segments[0]
    if len(segment.transition_ids) != 2:
        raise ValueError("mixed identity requires two typed views")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    if len(by_id) != len(relation.transition_specs):
        raise ValueError("mixed identity transition identity is ambiguous")
    ordinary_t, sharded_t = (by_id[tid] for tid in segment.transition_ids)
    variants = {
        ("identity-reshape-ordinary-two-rank", "reshape-sharded-k-rank"): "FW_reshape",
        ("identity-view-ordinary-two-rank", "view-sharded-k-rank"): "FW_view",
    }
    op = variants.get((ordinary_t.rule_id, sharded_t.rule_id))
    if op is None:
        raise ValueError("mixed identity rule pair is unsupported")
    ordinary_cs = [c for c in relation.certificates if type(c) is FrontierIdentityViewCertificate
                   and c.rule_id == ordinary_t.rule_id and c.lean_theorem == ordinary_t.lean_theorem
                   and _digest(c) == ordinary_t.certificate_digest]
    sharded_cs = [c for c in relation.certificates if type(c) is KRankContiguousRelationCertificate
                  and c.rule_id == sharded_t.rule_id and c.lean_theorem == sharded_t.lean_theorem
                  and _digest(c) == sharded_t.certificate_digest
                  and c.input_fact == sharded_t.pre_facts[0]
                  and c.output_fact == sharded_t.post_facts[0]]
    if len(ordinary_cs) != 1 or len(sharded_cs) != 1:
        raise ValueError("mixed identity lacks exact typed certificates")
    ordinary_c, sharded_c = ordinary_cs[0], sharded_cs[0]
    if (
        ordinary_c.relation_kind != "ordinary"
        or ordinary_c.input_step_triple != ordinary_t.pre_facts[0].step_triple
        or ordinary_c.output_step_triple != ordinary_t.post_facts[0].step_triple
        or ordinary_t.lean_theorem != "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id"
        or sharded_t.lean_theorem != "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_view_id"
    ):
        raise ValueError("mixed identity theorem/fact identity disagrees")
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    if len(records) != len(chain.relation_facts) or len(states) != len(chain.states):
        raise ValueError("mixed identity fact/state identity is ambiguous")
    ordinary_pre, ordinary_post = records[ordinary_t.pre_facts[0]], records[ordinary_t.post_facts[0]]
    sharded_pre, sharded_post = records[sharded_t.pre_facts[0]], records[sharded_t.post_facts[0]]
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if (
        ordinary_pre.kind != "ordinary" or ordinary_post.kind != "ordinary"
        or sharded_pre.kind != "sharded" or sharded_post.kind != "sharded"
        or sharded_c.rank_count != 2 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2
        or sharded_pre.gather_dim != sharded_post.gather_dim
        or (ordinary_pre.sm_tid, ordinary_pre.pm_tids) != (sharded_pre.sm_tid, sharded_pre.pm_tids)
        or (ordinary_post.sm_tid, ordinary_post.pm_tids) != (sharded_post.sm_tid, sharded_post.pm_tids)
        or (ordinary_pre.full_shape, ordinary_pre.shard_shape) != (ordinary_post.full_shape, ordinary_post.shard_shape)
        or (sharded_pre.full_shape, sharded_pre.shard_shape) != (sharded_post.full_shape, sharded_post.shard_shape)
        or (ordinary_pre.full_shape, ordinary_pre.shard_shape) != (sharded_pre.full_shape, sharded_pre.shard_shape)
    ):
        raise ValueError("mixed identity relation payload disagrees")
    if (
        ordinary_t.sm_node_indices != sharded_t.sm_node_indices
        or ordinary_t.pm_node_indices != sharded_t.pm_node_indices
        or tuple(range(*segment.sm_range)) != ordinary_t.sm_node_indices
        or tuple(range(*segment.pm_range)) != ordinary_t.pm_node_indices
        or len(ordinary_t.sm_node_indices) != 1 or len(ordinary_t.pm_node_indices) != 2
    ):
        raise ValueError("mixed identity views do not share exact 1x2 writers")
    sm = ir.sm_nodes[ordinary_t.sm_node_indices[0]]
    pms = tuple(ir.pm_nodes[i] for i in ordinary_t.pm_node_indices)
    if (
        (sm.rank, pms[0].rank, pms[1].rank) != (0, 0, 1)
        or any(n.op != op or len(n.ins) != 1 or len(n.outs) != 1 or not n.params for n in (sm, *pms))
        or (sm.ins[0], pms[0].ins[0], pms[1].ins[0]) != (ordinary_pre.sm_tid, *ordinary_pre.pm_tids)
        or (sm.outs[0], pms[0].outs[0], pms[1].outs[0]) != (ordinary_post.sm_tid, *ordinary_post.pm_tids)
    ):
        raise ValueError("mixed identity writer topology disagrees")
    targets = (tuple(sm.params), tuple(pms[0].params), tuple(pms[1].params))
    if targets != (ordinary_post.full_shape, ordinary_post.shard_shape, ordinary_post.shard_shape):
        raise ValueError("mixed identity target shapes disagree")
    fresh = (ordinary_post.fact_id, sharded_post.fact_id)
    if (
        not {ordinary_pre.fact_id, sharded_pre.fact_id} <= set(before.fact_ids)
        or any(fid not in after.fact_ids for fid in fresh)
        or not set(after.fact_ids) <= set(before.fact_ids) | set(fresh)
    ):
        raise ValueError("mixed identity liveness disagrees")
    sid = segment_id
    smt, pmt = _node_text(sm), tuple(_node_text(n) for n in pms)
    full, shard = _shape_text(list(ordinary_post.full_shape)), _shape_text(list(ordinary_post.shard_shape))
    def app(node, graph):
        if op == "FW_reshape":
            return f"exact applyNode_fw_reshape_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {_shape_text(node.params)}"
        return f"exact applyNode_fw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.outs[0]}"
    def writer(name, graph, store, final, nodes_name, nodes, position, node, target):
        prefix, suffix = nodes[:position], nodes[position + 1:]
        target_text = _shape_text(list(target))
        return "\n".join([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {name} ({store} : Store) : ({final} {store}) {node.outs[0]} = fw_view {target_text} ({store} {node.ins[0]}) := by",
            f"  unfold {final}",
            f"  simpa [{nodes_name}] using",
            f"    (foldl_faithful_unary_middle_writer {graph} {store} [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}] {_node_text(node)}",
            f"      {node.ins[0]} {node.outs[0]} (fun x => fw_view {target_text} x) (by",
            "        intro t",
            "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "        simp [applyNodeDistributed, applyNodeRingAttn]",
            f"        {app(node, graph)}",
            "      ) (by native_decide) (by native_decide) (by native_decide) (by native_decide))",
        ])
    smn, pmn = f"{sid}_smNodes", f"{sid}_pmNodes"
    smf, pmf = f"{sid}_smFinal", f"{sid}_pmFinal"
    lines = [
        f"private def {smn} : List NodeDecl := [{smt}]",
        f"private def {pmn} : List NodeDecl := [{pmt[0]}, {pmt[1]}]",
        f"@[irreducible] private def {smf} (s : Store) := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
        writer(f"{sid}_smWriter", ir.sm_graph_ref, "smStore", smf, smn, (sm,), 0, sm, targets[0]),
        writer(f"{sid}_pm0Writer", ir.pm_graph_ref, "pmStore", pmf, pmn, pms, 0, pms[0], targets[1]),
        writer(f"{sid}_pm1Writer", ir.pm_graph_ref, "pmStore", pmf, pmn, pms, 1, pms[1], targets[2]),
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    unfold {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
        f"  have hOrd : {ordinary_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"  have hSh : {sharded_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"  have hOrdOut : {ordinary_post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {ordinary_pre.sm_tid}) (pmStore {ordinary_pre.pm_tids[0]}) (pmStore {ordinary_pre.pm_tids[1]}) {full} {shard} at hOrd",
        f"    have core := Ordinary2Rel.view_id hOrd",
        f"    change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {ordinary_post.sm_tid}) (({pmf} pmStore) {ordinary_post.pm_tids[0]}) (({pmf} pmStore) {ordinary_post.pm_tids[1]}) {full} {shard}",
        f"    rw [{sid}_smWriter smStore, {sid}_pm0Writer pmStore, {sid}_pm1Writer pmStore]",
        "    exact core",
        f"  have hShOut : {sharded_post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    change ShardedRel (smStore {sharded_pre.sm_tid}) [pmStore {sharded_pre.pm_tids[0]}, pmStore {sharded_pre.pm_tids[1]}] {sharded_pre.gather_dim} {full} {shard} at hSh",
        f"    have core := ShardedRel.fw_view_id hSh",
        f"    change ShardedRel (({smf} smStore) {sharded_post.sm_tid}) [({pmf} pmStore) {sharded_post.pm_tids[0]}, ({pmf} pmStore) {sharded_post.pm_tids[1]}] {sharded_post.gather_dim} {full} {shard}",
        f"    rw [{sid}_smWriter smStore, {sid}_pm0Writer pmStore, {sid}_pm1Writer pmStore]",
        "    exact core",
        "  intro fact hfact",
        f"  have covered : fact ∈ [{ordinary_post.fact_id}, {sharded_post.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{ordinary_post.fact_id}, {sharded_post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
        "  rcases covered with (rfl | rfl) | old",
        "  · exact hOrdOut", "  · exact hShOut", "  · exact hframe fact old",
        f"private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {smn}", f"  pmNodes := {pmn}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{smf}, {pmf}] using {sid}_sound smStore pmStore hstate",
        "",
    ]
    return "\n".join(lines)
