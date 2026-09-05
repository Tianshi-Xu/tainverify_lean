"""Atomic renderer for joined multiref projection aliases over a full PM frame."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict


def _digest(c):
    return hashlib.sha256(json.dumps({"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def render_closed_joined_multiref_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import MultirefAliasCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import MultirefAliasCertificate
    chain = relation.dependent_chain_plan
    segs = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segs) != 1:
        raise ValueError("joined multiref requires one complete segment")
    seg = segs[0]
    by_id = {t.transition_id: t for t in relation.transition_specs}
    transitions = tuple(by_id[x] for x in seg.transition_ids)
    if not transitions or any(t.rule_id != "multiref-projection-alias" or len(t.pre_facts) != 1
                              or len(t.post_facts) != 1 for t in transitions):
        raise ValueError("joined multiref requires positive alias views")
    typed = []
    for t in transitions:
        matches = [c for c in relation.certificates if type(c) is MultirefAliasCertificate
                   and c.rule_id == t.rule_id and c.lean_theorem == t.lean_theorem
                   and c.relation_kind == t.pre_facts[0].layout and c.input_step_triple == (*t.pre_facts[0].step_triple, t.pre_facts[0].joined_pm_step)
                   and c.output_step_triple == (*t.post_facts[0].step_triple, t.post_facts[0].joined_pm_step)
                   and _digest(c) == t.certificate_digest]
        if len(matches) != 1:
            raise ValueError("joined multiref lacks one exact alias certificate")
        typed.append((t, matches[0]))
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    rows = tuple((t, c, records[t.pre_facts[0]], records[t.post_facts[0]]) for t, c in typed)
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    pre_ids = {pre.fact_id for _t, _c, pre, _post in rows}
    if len(pre_ids) != 1:
        raise ValueError("joined multiref aliases do not share one input fact")
    sm_indices, pm_indices = tuple(range(*seg.sm_range)), tuple(range(*seg.pm_range))
    if len(sm_indices) != 1 or not pm_indices:
        raise ValueError("joined multiref frame shape is unsupported")
    sm = ir.sm_nodes[sm_indices[0]]
    pm_frame = tuple(ir.pm_nodes[i] for i in pm_indices)
    arity = len(sm.outs)
    if (sm.op != "FW_multiref" or len(sm.ins) != 1 or sm.params != [arity] or arity <= 0
            or tuple(n.rank for n in pm_frame) != tuple(range(len(pm_frame)))
            or any(n.op != "FW_multiref" or len(n.ins) != 1 or len(n.outs) != arity
                   or n.params != [arity] for n in pm_frame)):
        raise ValueError("joined multiref frame topology disagrees")
    for t, c, pre, post in rows:
        if (pre.kind not in {"joined", "joined_zigzag"} or post.kind != pre.kind
                or t.sm_node_indices != (sm_indices[0],) or len(t.pm_node_indices) != 1
                or t.pm_node_indices[0] not in pm_indices
                or pre.sm_tid != sm.ins[0] or pre.joined_pm_tid != ir.pm_nodes[t.pm_node_indices[0]].ins[0]
                or len(c.output_indices) != 2
                or any(not 0 <= projection < arity for projection in c.output_indices)
                or (post.sm_tid, post.joined_pm_tid) != (
                    sm.outs[c.output_indices[0]], ir.pm_nodes[t.pm_node_indices[0]].outs[c.output_indices[1]])
                or pre.full_shape != post.full_shape or pre.shard_shape != post.shard_shape
                or (pre.kind == "joined" and pre.full_shape != pre.shard_shape)
                or (pre.kind == "joined_zigzag" and (
                    pre.metadata_tid is None or post.metadata_tid != pre.metadata_tid or
                    pre.metadata_region_id != post.metadata_region_id or
                    pre.row_shard_shape != pre.shard_shape or post.row_shard_shape != post.shard_shape or
                    pre.full_shape != (2 * pre.shard_shape[0], *pre.shard_shape[1:]))) ):
            raise ValueError("joined multiref alias authority disagrees")
    fresh = tuple(post.fact_id for _t, _c, _pre, post in rows)
    if (not pre_ids <= set(before.fact_ids) or len(set(fresh)) != len(fresh)
            or any(fid not in after.fact_ids for fid in fresh)
            or not set(after.fact_ids) <= set(before.fact_ids) | set(fresh)):
        raise ValueError("joined multiref liveness disagrees")
    sid = segment_id
    smn, pmn = f"{sid}_smNodes", f"{sid}_pmNodes"
    smf, pmf = f"{sid}_smFinal", f"{sid}_pmFinal"
    sm_text, pm_texts = _node_text(sm), tuple(_node_text(n) for n in pm_frame)
    lines = [
        f"private def {smn} : List NodeDecl := [{sm_text}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(pm_texts)}]",
        f"@[irreducible] private def {smf} (s : Store) := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
    ]
    helpers = {}
    for row, (_t, cert, _pre, _post) in enumerate(rows):
        pair = tuple(cert.output_indices)
        if pair in helpers:
            continue
        names = []
        pm_index = _t.pm_node_indices[0]
        pm_node = ir.pm_nodes[pm_index]
        for label, graph, store, final, nodes_name, nodes, position, node, projection in (
            ("sm", ir.sm_graph_ref, "smStore", smf, smn, (sm,), 0, sm, pair[0]),
            ("pm", ir.pm_graph_ref, "pmStore", pmf, pmn, pm_frame, pm_index - seg.pm_range[0], pm_node, pair[1]),
        ):
            name = f"{sid}_{label}_{row}"; names.append(name)
            prefix, suffix = nodes[:position], nodes[position + 1:]
            lines.extend([
                "set_option maxHeartbeats 500000 in",
                f"private theorem {name} ({store} : Store) : ({final} {store}) {node.outs[projection]} = {store} {node.ins[0]} := by",
                f"  unfold {final}",
                f"  simpa [{nodes_name}] using",
                f"    (foldl_faithful_multiref_middle_writer {graph} {store}",
                f"      [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}]",
                f"      {node.rank} {node.ins[0]} {_shape_text(node.outs)} {arity} {node.outs[projection]}",
                "      rfl (by native_decide) (by native_decide) (by native_decide)",
                "      (by native_decide) (by native_decide))",
            ])
        helpers[pair] = tuple(names)
    pre = rows[0][2]
    shape = _shape_text(list(pre.full_shape))
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    unfold {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
        f"  have hin : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
    ])
    proof_names = []
    for row, (_t, cert, item_pre, post) in enumerate(rows):
        names = helpers[tuple(cert.output_indices)]
        name = f"hout{row}"; proof_names.append(name)
        lines.append(f"  have {name} : {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by")
        if post.kind == "joined":
            lines.extend([
                f"    change smStore {item_pre.sm_tid} = pmStore {item_pre.joined_pm_tid} ∧ (smStore {item_pre.sm_tid}).shape = {shape} ∧ (pmStore {item_pre.joined_pm_tid}).shape = {shape} at hin",
                f"    change ({smf} smStore) {post.sm_tid} = ({pmf} pmStore) {post.joined_pm_tid} ∧ (({smf} smStore) {post.sm_tid}).shape = {shape} ∧ (({pmf} pmStore) {post.joined_pm_tid}).shape = {shape}",
                f"    rw [{names[0]} smStore, {names[1]} pmStore]",
                "    exact hin",
            ])
        else:
            shard = _shape_text(list(item_pre.shard_shape))
            lines.extend([
                f"    have hmeta{row} : ({pmf} pmStore) {item_pre.metadata_tid} = pmStore {item_pre.metadata_tid} := by",
                f"      unfold {pmf}",
                f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} {pmn} pmStore {item_pre.metadata_tid} (by native_decide) (by native_decide)",
                f"    change JoinedZigzagRel (smStore {item_pre.sm_tid}) (pmStore {item_pre.joined_pm_tid}) (pmStore {item_pre.metadata_tid}) {shape} {shard} at hin",
                f"    change JoinedZigzagRel (({smf} smStore) {post.sm_tid}) (({pmf} pmStore) {post.joined_pm_tid}) (({pmf} pmStore) {post.metadata_tid}) {shape} {shard}",
                f"    rw [{names[0]} smStore, {names[1]} pmStore, hmeta{row}]",
                "    exact hin",
            ])
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ [{', '.join(fresh)}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{', '.join(fresh)}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
        "  rcases covered with fresh | old",
        "  · rcases fresh with " + " | ".join("rfl" for _ in fresh),
    ])
    lines.extend(f"    · exact {name}" for name in proof_names)
    lines.extend([
        "  · exact hframe fact old",
        f"private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {smn}", f"  pmNodes := {pmn}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{smf}, {pmf}] using {sid}_sound smStore pmStore hstate",
        "",
    ])
    return "\n".join(lines)
