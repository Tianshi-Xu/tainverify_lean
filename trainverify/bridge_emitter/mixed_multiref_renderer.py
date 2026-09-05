"""Atomic shared-writer renderer for sharded and ordinary multiref projections."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict


def _digest(certificate) -> str:
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        separators=(",", ":"), sort_keys=True,
    ).encode()).hexdigest()


def render_closed_mixed_multiref_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import KRankMultirefRelationCertificate, MultirefAliasCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import KRankMultirefRelationCertificate, MultirefAliasCertificate
    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("mixed multiref requires one complete segment")
    segment = segments[0]
    by_id = {t.transition_id: t for t in relation.transition_specs}
    if len(by_id) != len(relation.transition_specs):
        raise ValueError("mixed multiref transition authority is ambiguous")
    try:
        transitions = tuple(by_id[tid] for tid in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("mixed multiref names an unknown transition") from exc
    sharded_ts = tuple(t for t in transitions if t.rule_id == "multiref-sharded-k-rank")
    alias_ts = tuple(t for t in transitions if t.rule_id == "multiref-projection-alias")
    if not sharded_ts or not alias_ts or len(sharded_ts) + len(alias_ts) != len(transitions):
        raise ValueError("mixed multiref requires positive sharded and alias views")
    if any(len(t.pre_facts) != 1 or len(t.post_facts) != 1 for t in transitions):
        raise ValueError("mixed multiref transition arity disagrees")
    typed_k = [c for c in relation.certificates if type(c) is KRankMultirefRelationCertificate]
    sharded = []
    for transition in sharded_ts:
        candidates = [c for c in typed_k if
            c.rule_id == transition.rule_id and c.lean_theorem == transition.lean_theorem
            and c.input_fact == transition.pre_facts[0]
            and c.output_fact == transition.post_facts[0]
            and _digest(c) == transition.certificate_digest]
        if len(candidates) != 1:
            raise ValueError("mixed multiref lacks one exact sharded certificate")
        sharded.append(candidates[0])
    aliases = []
    typed_alias = [c for c in relation.certificates if type(c) is MultirefAliasCertificate]
    for transition in alias_ts:
        candidates = [c for c in typed_alias if
            c.rule_id == transition.rule_id and c.lean_theorem == transition.lean_theorem
            and c.relation_kind == transition.pre_facts[0].layout
            and c.input_step_triple == transition.pre_facts[0].step_triple
            and c.relation_kind == transition.post_facts[0].layout
            and c.output_step_triple == transition.post_facts[0].step_triple
            and _digest(c) == transition.certificate_digest]
        if len(candidates) != 1:
            raise ValueError("mixed multiref alias lacks one exact certificate")
        aliases.append(candidates[0])
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    if len(records) != len(chain.relation_facts) or len(states) != len(chain.states):
        raise ValueError("mixed multiref fact/state identity is ambiguous")
    try:
        sharded_rows = tuple((c, records[t.pre_facts[0]], records[t.post_facts[0]])
                             for t, c in zip(sharded_ts, sharded))
        ordinary_rows = tuple((c, records[t.pre_facts[0]], records[t.post_facts[0]])
                              for t, c in zip(alias_ts, aliases))
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("mixed multiref fact/state is unresolved") from exc
    sm_indices, pm_indices = tuple(range(*segment.sm_range)), tuple(range(*segment.pm_range))
    k = len(pm_indices)
    if len(sm_indices) != 1 or k != 2 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("mixed multiref frame is not exact 1xK")
    if any(t.sm_node_indices != sm_indices or t.pm_node_indices != pm_indices for t in transitions):
        raise ValueError("mixed multiref transitions do not share the exact frame")
    sm = ir.sm_nodes[sm_indices[0]]
    pms = tuple(ir.pm_nodes[i] for i in pm_indices)
    writers = (sm, *pms)
    arity = len(sm.outs)
    if (
        (sm.rank, *(n.rank for n in pms)) != (0, *range(k))
        or any(n.op != "FW_multiref" or len(n.ins) != 1 or len(n.outs) != arity
               or n.params != [arity] for n in writers)
        or arity <= 0
    ):
        raise ValueError("mixed multiref writer topology disagrees")
    sharded_pre_ids = {pre.fact_id for _c, pre, _post in sharded_rows}
    if len(sharded_pre_ids) != 1:
        raise ValueError("mixed multiref sharded views do not share one input")
    for kcert, sh_pre, sh_post in sharded_rows:
        if (
            sh_pre.kind != "sharded" or sh_post.kind != "sharded"
            or sh_pre.sm_tid != sm.ins[0] or sh_pre.pm_tids != tuple(n.ins[0] for n in pms)
            or kcert.rank_count != k or kcert.arity != arity
            or kcert.gather_dim != sh_pre.gather_dim
            or kcert.sm_step_id != f"sm:{sm_indices[0]}:{kcert.projection}"
            or kcert.pm_step_ids != tuple(f"pm:{index}:{projection}" for index, projection in zip(pm_indices, kcert.pm_projections))
            or not 0 <= kcert.projection < arity
            or len(kcert.pm_projections) != k
            or any(not 0 <= projection < arity for projection in kcert.pm_projections)
            or (sh_post.sm_tid, *sh_post.pm_tids) != (
                sm.outs[kcert.projection], *(node.outs[p] for node, p in zip(pms, kcert.pm_projections)))
            or sh_post.full_shape != sh_pre.full_shape or sh_post.shard_shape != sh_pre.shard_shape
        ):
            raise ValueError("mixed multiref sharded authority disagrees")
    sh_pre = sharded_rows[0][1]
    ordinary_pre_ids = {pre.fact_id for _c, pre, _post in ordinary_rows}
    if len(ordinary_pre_ids) != 1:
        raise ValueError("mixed multiref aliases do not share one ordinary input")
    for cert, pre, post in ordinary_rows:
        if (
            pre.kind != "ordinary" or post.kind != "ordinary"
            or pre.sm_tid != sm.ins[0] or pre.pm_tids != tuple(n.ins[0] for n in pms)
            or pre.full_shape != sh_pre.full_shape or pre.shard_shape != sh_pre.shard_shape
            or post.full_shape != pre.full_shape or post.shard_shape != pre.shard_shape
            or cert.arity != arity or len(cert.output_indices) != 3
            or any(not 0 <= projection < arity for projection in cert.output_indices)
            or (post.sm_tid, *post.pm_tids) != (
                sm.outs[cert.output_indices[0]], pms[0].outs[cert.output_indices[1]],
                pms[1].outs[cert.output_indices[2]])
        ):
            raise ValueError("mixed multiref ordinary alias authority disagrees")
    fresh = (*(post.fact_id for _c, _pre, post in sharded_rows),
             *(post.fact_id for _c, _pre, post in ordinary_rows))
    required_pre = {*sharded_pre_ids, *ordinary_pre_ids}
    if (
        not required_pre <= set(before.fact_ids)
        or any(fid not in after.fact_ids for fid in fresh)
        or len(set(fresh)) != len(fresh)
        or not set(after.fact_ids) <= set(before.fact_ids) | set(fresh)
    ):
        raise ValueError("mixed multiref liveness disagrees")

    sid = segment_id
    smn, pmn = f"{sid}_smNodes", f"{sid}_pmNodes"
    smf, pmf = f"{sid}_smFinal", f"{sid}_pmFinal"
    sm_text, pm_texts = _node_text(sm), tuple(_node_text(n) for n in pms)
    full, shard = _shape_text(list(sh_pre.full_shape)), _shape_text(list(sh_pre.shard_shape))
    lines = [
        f"private def {smn} : List NodeDecl := [{sm_text}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(pm_texts)}]",
        f"@[irreducible] private def {smf} (s : Store) := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
    ]
    needed = {tuple((c.projection, *c.pm_projections)) for c, _pre, _post in sharded_rows}
    needed |= {tuple(c.output_indices) for c in aliases}
    proof_names = {}
    for row, projections in enumerate(sorted(needed)):
        names = []
        for label, graph, store, final, nodes_name, nodes, position, node, projection in (
            ("sm", ir.sm_graph_ref, "smStore", smf, smn, (sm,), 0, sm, projections[0]),
            ("p0", ir.pm_graph_ref, "pmStore", pmf, pmn, pms, 0, pms[0], projections[1]),
            ("p1", ir.pm_graph_ref, "pmStore", pmf, pmn, pms, 1, pms[1], projections[2]),
        ):
            name = f"h_{label}_{row}"; names.append(name)
            prefix, suffix = nodes[:position], nodes[position + 1:]
            lines.extend([
                "set_option maxHeartbeats 500000 in",
                f"private theorem {sid}_{name} ({store} : Store) : ({final} {store}) {node.outs[projection]} = {store} {node.ins[0]} := by",
                f"  unfold {final}",
                f"  simpa [{nodes_name}] using",
                f"    (foldl_faithful_multiref_middle_writer {graph} {store}",
                f"      [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}]",
                f"      {node.rank} {node.ins[0]} {_shape_text(node.outs)} {arity} {node.outs[projection]}",
                "      rfl (by native_decide) (by native_decide) (by native_decide)",
                "      (by native_decide) (by native_decide))",
            ])
        proof_names[projections] = tuple(f"{sid}_{name}" for name in names)
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    unfold {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
    ])
    sharded_pre = sharded_rows[0][1]
    lines.append(f"  have hSh : {sharded_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)")
    ordinary_pre = ordinary_rows[0][1]
    lines.append(f"  have hOrd : {ordinary_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)")
    sharded_names = []
    for row, (kcert, pre, post) in enumerate(sharded_rows):
        projections = (kcert.projection, *kcert.pm_projections)
        names = proof_names[projections]
        outputs = [sm.outs[projections[0]], pms[0].outs[projections[1]], pms[1].outs[projections[2]]]
        name = f"hShOut{row}"; sharded_names.append(name)
        lines.extend([
            f"  have {name} : {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
            f"    change ShardedRel (smStore {pre.sm_tid}) [{', '.join(f'pmStore {tid}' for tid in pre.pm_tids)}] {pre.gather_dim} {full} {shard} at hSh",
            f"    change ShardedRel (({smf} smStore) {outputs[0]}) [({pmf} pmStore) {outputs[1]}, ({pmf} pmStore) {outputs[2]}] {pre.gather_dim} {full} {shard}",
            f"    rw [{names[0]} smStore, {names[1]} pmStore, {names[2]} pmStore]",
            "    exact hSh",
        ])
    ordinary_names = []
    for row, (cert, pre, post) in enumerate(ordinary_rows):
        projections = tuple(cert.output_indices); names = proof_names[projections]
        outputs = [sm.outs[projections[0]], pms[0].outs[projections[1]], pms[1].outs[projections[2]]]
        name = f"hOrdOut{row}"; ordinary_names.append(name)
        lines.extend([
            f"  have {name} : {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
            f"    change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_tids[0]}) (pmStore {pre.pm_tids[1]}) {full} {shard} at hOrd",
            f"    change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {outputs[0]}) (({pmf} pmStore) {outputs[1]}) (({pmf} pmStore) {outputs[2]}) {full} {shard}",
            f"    rw [{names[0]} smStore, {names[1]} pmStore, {names[2]} pmStore]",
            "    exact hOrd",
        ])
    proof_list = (*sharded_names, *ordinary_names)
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ [{', '.join(fresh)}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{', '.join(fresh)}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
        "  rcases covered with fresh | old",
        "  · rcases fresh with " + " | ".join("rfl" for _ in fresh),
    ])
    lines.extend(f"    · exact {name}" for name in proof_list)
    lines.extend([
        "  · exact hframe fact old",
        f"private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {smn}", f"  pmNodes := {pmn}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{smf}, {pmf}] using {sid}_sound smStore pmStore hstate",
        "",
    ])
    return "\n".join(lines)
