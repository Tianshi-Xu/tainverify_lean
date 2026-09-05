"""Atomic renderer for ordinary flatten, positive rank-3 RMS tuple, and CP2 projection."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict


def _digest(certificate) -> str:
    return hashlib.sha256(json.dumps(
        {"type": type(certificate).__name__, "fields": asdict(certificate)},
        separators=(",", ":"), sort_keys=True,
    ).encode()).hexdigest()


def render_closed_flatten_rms_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import (
            CP2OrdinaryToShardedCertificate,
            FrontierFlatten3DCertificate,
            FrontierRMSNormCertificate,
        )
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import (
            CP2OrdinaryToShardedCertificate,
            FrontierFlatten3DCertificate,
            FrontierRMSNormCertificate,
        )
    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("flatten/RMS requires one complete segment")
    segment = segments[0]
    by_id = {t.transition_id: t for t in relation.transition_specs}
    if len(by_id) != len(relation.transition_specs):
        raise ValueError("flatten/RMS transition identity is ambiguous")
    try:
        transitions = tuple(by_id[tid] for tid in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("flatten/RMS names an unknown transition") from exc
    rules = tuple(t.rule_id for t in transitions)
    adapter_present = rules[-1:] == ("ordinary-to-sharded-cp2-fw_reshape-output",)
    physical = transitions[:-1] if adapter_present else transitions
    if (
        len(physical) < 1 or physical[0].rule_id != "flatten-3d-ordinary-two-rank"
        or any(t.rule_id != "rms-norm-ordinary-two-rank" for t in physical[1:])
    ):
        raise ValueError("flatten/RMS family must be flatten + RMS tuple + optional adapter")
    expected_classes = [FrontierFlatten3DCertificate] + [FrontierRMSNormCertificate] * (len(physical) - 1)
    if adapter_present:
        expected_classes.append(CP2OrdinaryToShardedCertificate)
    certificates = []
    for transition, cls in zip(transitions, expected_classes):
        matches = [c for c in relation.certificates if type(c) is cls
                   and c.rule_id == transition.rule_id
                   and c.lean_theorem == transition.lean_theorem
                   and _digest(c) == transition.certificate_digest]
        if len(matches) != 1:
            raise ValueError("flatten/RMS transition lacks one exact typed certificate")
        certificates.append(matches[0])
    flatten_t, *tail = transitions
    flatten_c, *cert_tail = certificates
    adapter_t = tail[-1] if adapter_present else None
    adapter_c = cert_tail[-1] if adapter_present else None
    rms_ts = tuple(tail[:-1] if adapter_present else tail)
    rms_cs = tuple(cert_tail[:-1] if adapter_present else cert_tail)
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    if len(records) != len(chain.relation_facts) or len(states) != len(chain.states):
        raise ValueError("flatten/RMS fact/state identity is ambiguous")
    try:
        flat_pre = records[flatten_t.pre_facts[0]]
        flat_post = records[flatten_t.post_facts[0]]
        rms_rows = []
        for transition, cert in zip(rms_ts, rms_cs):
            rows = [records[source] for source in transition.pre_facts]
            activations = [row for row in rows if row.kind == "ordinary"]
            weights = [row for row in rows if row.kind == "joined"]
            if len(activations) != 1 or len(weights) != 1:
                raise ValueError("flatten/RMS typed RMS roles are ambiguous")
            rms_rows.append((transition, cert, activations[0], weights[0], records[transition.post_facts[0]]))
        adapter_post = None if adapter_t is None else records[adapter_t.post_facts[0]]
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("flatten/RMS facts/states are unresolved") from exc
    if (
        len(flatten_t.pre_facts) != 1 or len(flatten_t.post_facts) != 1
        or flat_pre.kind != "ordinary" or flat_post.kind != "ordinary"
        or flatten_t.lean_theorem != "TrainVerify.Denote.GeneratedPatterns.fw_view_allGather0_commute_cp2"
        or len(flat_pre.shard_shape) != 3 or len(flat_post.shard_shape) != 2
    ):
        raise ValueError("flatten/RMS flatten relation domain disagrees")
    rows, middle, hidden = flat_pre.shard_shape
    if (
        min(rows, middle, hidden) <= 0
        or flat_pre.full_shape != (rows * 2, middle, hidden)
        or flat_post.full_shape != (rows * 2, middle * hidden)
        or flat_post.shard_shape != (rows, middle * hidden)
    ):
        raise ValueError("flatten/RMS flatten shape contract disagrees")
    sm_indices, pm_indices = tuple(range(*segment.sm_range)), tuple(range(*segment.pm_range))
    if len(sm_indices) != len(physical) or len(pm_indices) != 2 * len(physical):
        raise ValueError("flatten/RMS complete frame cardinality disagrees")
    owned_sm = tuple(index for transition in physical for index in transition.sm_node_indices)
    owned_pm = tuple(index for transition in physical for index in transition.pm_node_indices)
    if set(owned_sm) != set(sm_indices) or set(owned_pm) != set(pm_indices):
        raise ValueError("flatten/RMS physical transitions do not exhaust the frame")
    if adapter_present and (
        not adapter_t.fact_only or adapter_t.sm_node_indices or adapter_t.pm_node_indices
        or adapter_c.input_fact != flatten_t.post_facts[0]
        or adapter_c.output_fact != adapter_t.post_facts[0]
        or adapter_t.lean_theorem !=
            "TrainVerify.Denote.RelationCompiler.ShardedRel.ofOrdinary2_dim0_rank2"
    ):
        raise ValueError("flatten/RMS CP2 adapter identity disagrees")
    sm_frame = tuple(ir.sm_nodes[i] for i in sm_indices)
    pm_frame = tuple(ir.pm_nodes[i] for i in pm_indices)
    if any(not node.outs for node in (*sm_frame, *pm_frame)):
        raise ValueError("flatten/RMS frame contains an outputless node")
    for transition in physical:
        for indices, frame, start in (
            (transition.sm_node_indices, sm_frame, segment.sm_range[0]),
            (transition.pm_node_indices, pm_frame, segment.pm_range[0]),
        ):
            for absolute in indices:
                position = absolute - start
                node = frame[position]
                if any(set(prefix.outs) & set(node.ins) for prefix in frame[:position]):
                    raise ValueError("flatten/RMS writer prefix overwrites a semantic input")
                if any(node.outs[0] in suffix.outs for suffix in frame[position + 1:]):
                    raise ValueError("flatten/RMS writer output has a later writer")
    fsm = ir.sm_nodes[flatten_t.sm_node_indices[0]]
    fpms = tuple(ir.pm_nodes[i] for i in flatten_t.pm_node_indices)
    if (
        len(flatten_t.sm_node_indices) != 1 or len(flatten_t.pm_node_indices) != 2
        or (fsm.rank, fpms[0].rank, fpms[1].rank) != (0, 0, 1)
        or any(n.op != "FW_reshape" or len(n.ins) != 1 or len(n.outs) != 1 for n in (fsm, *fpms))
        or tuple(fsm.params or ()) != flat_post.full_shape
        or tuple(fpms[0].params or ()) != flat_post.shard_shape
        or tuple(fpms[1].params or ()) != flat_post.shard_shape
        or (fsm.ins[0], fpms[0].ins[0], fpms[1].ins[0]) != (flat_pre.sm_tid, *flat_pre.pm_tids)
        or (fsm.outs[0], fpms[0].outs[0], fpms[1].outs[0]) != (flat_post.sm_tid, *flat_post.pm_tids)
    ):
        raise ValueError("flatten/RMS flatten writer authority disagrees")
    for transition, cert, pre, weight, post in rms_rows:
        sm = ir.sm_nodes[transition.sm_node_indices[0]]
        pms = tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
        if (
            len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != 2
            or transition.lean_theorem != "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core_3d"
            or pre.kind != "ordinary" or post.kind != "ordinary"
            or len(pre.shard_shape) != 3 or pre.full_shape != (pre.shard_shape[0] * 2, *pre.shard_shape[1:])
            or pre.full_shape != post.full_shape or pre.shard_shape != post.shard_shape
            or min(*pre.shard_shape) <= 0
            or weight.sm_tid != sm.ins[1] or weight.joined_pm_tid != sm.ins[1]
            or weight.full_shape != (pre.shard_shape[-1],)
            or (sm.rank, pms[0].rank, pms[1].rank) != (0, 0, 1)
            or any(n.op != "FW_rms_norm" or len(n.ins) != 2 or len(n.outs) != 1
                   or n.params not in (None, []) for n in (sm, *pms))
            or len({sm.ins[1], pms[0].ins[1], pms[1].ins[1]}) != 1
            or (sm.ins[0], pms[0].ins[0], pms[1].ins[0]) != (pre.sm_tid, *pre.pm_tids)
            or (sm.outs[0], pms[0].outs[0], pms[1].outs[0]) != (post.sm_tid, *post.pm_tids)
        ):
            raise ValueError("flatten/RMS rank-3 RMS authority disagrees")
    fresh_records = [flat_post, *(row[4] for row in rms_rows)]
    if adapter_post is not None:
        if (adapter_post.kind != "sharded" or adapter_post.sm_tid != flat_post.sm_tid
                or adapter_post.pm_tids != flat_post.pm_tids
                or adapter_post.full_shape != flat_post.full_shape
                or adapter_post.shard_shape != flat_post.shard_shape
                or adapter_post.gather_dim != 0):
            raise ValueError("flatten/RMS adapter output payload disagrees")
        fresh_records.append(adapter_post)
    required = {flat_pre.fact_id, *(row[2].fact_id for row in rms_rows), *(row[3].fact_id for row in rms_rows)}
    fresh_ids = tuple(record.fact_id for record in fresh_records)
    if (
        not required <= set(before.fact_ids)
        or len(set(fresh_ids)) != len(fresh_ids)
        or any(row[4].fact_id not in after.fact_ids for row in rms_rows)
        or (adapter_post is not None and adapter_post.fact_id not in after.fact_ids)
        or not set(after.fact_ids) <= set(before.fact_ids) | set(fresh_ids)
    ):
        raise ValueError("flatten/RMS state liveness disagrees")

    sid = segment_id
    smn, pmn = f"{sid}_smNodes", f"{sid}_pmNodes"
    smf, pmf = f"{sid}_smFinal", f"{sid}_pmFinal"
    lines = [
        f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {smf} (s : Store) := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
    ]

    def unary_helper(name, graph, store, final, nodes_name, frame, absolute, node, shape):
        position = absolute - (segment.sm_range[0] if store == "smStore" else segment.pm_range[0])
        prefix, suffix = frame[:position], frame[position + 1:]
        target = _shape_text(list(shape))
        lines.extend([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {name} ({store} : Store) : ({final} {store}) {node.outs[0]} = fw_view {target} ({store} {node.ins[0]}) := by",
            f"  unfold {final}",
            f"  simpa [{nodes_name}] using",
            f"    (foldl_faithful_unary_middle_writer {graph} {store}",
            f"      [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}] {_node_text(node)}",
            f"      {node.ins[0]} {node.outs[0]} (fun x => fw_view {target} x) (by",
            "        intro t",
            "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "        simp [applyNodeDistributed, applyNodeRingAttn]",
            f"        exact applyNode_fw_reshape_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]} {target}",
            "      ) (by native_decide) (by native_decide) (by native_decide) (by native_decide))",
        ])

    def rms_helper(name, graph, store, final, nodes_name, frame, absolute, node):
        position = absolute - (segment.sm_range[0] if store == "smStore" else segment.pm_range[0])
        prefix, suffix = frame[:position], frame[position + 1:]
        lines.extend([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {name} ({store} : Store) : ({final} {store}) {node.outs[0]} = fw_rms_norm ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            f"  unfold {final}",
            f"  simpa [{nodes_name}] using",
            f"    (foldl_faithful_binary_middle_writer {graph} {store}",
            f"      [{', '.join(_node_text(n) for n in prefix)}] [{', '.join(_node_text(n) for n in suffix)}] {_node_text(node)}",
            f"      {node.ins[0]} {node.ins[1]} {node.outs[0]} fw_rms_norm (by",
            "        intro t",
            "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "        simp [applyNodeDistributed, applyNodeRingAttn]",
            f"        exact applyNode_fw_rms_norm_out_1p {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            "      ) (by native_decide) (by native_decide) (by native_decide)",
            "      (by native_decide) (by native_decide))",
        ])

    flat_helpers = (f"{sid}_flatSm", f"{sid}_flatP0", f"{sid}_flatP1")
    unary_helper(flat_helpers[0], ir.sm_graph_ref, "smStore", smf, smn, sm_frame,
                 flatten_t.sm_node_indices[0], fsm, flat_post.full_shape)
    for rank in range(2):
        unary_helper(flat_helpers[rank + 1], ir.pm_graph_ref, "pmStore", pmf, pmn, pm_frame,
                     flatten_t.pm_node_indices[rank], fpms[rank], flat_post.shard_shape)
    rms_helpers = []
    for number, (transition, _cert, _pre, _weight, _post) in enumerate(rms_rows):
        sm = ir.sm_nodes[transition.sm_node_indices[0]]
        pms = tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
        names = (f"{sid}_rms{number}Sm", f"{sid}_rms{number}P0", f"{sid}_rms{number}P1")
        rms_helper(names[0], ir.sm_graph_ref, "smStore", smf, smn, sm_frame,
                   transition.sm_node_indices[0], sm)
        for rank in range(2):
            rms_helper(names[rank + 1], ir.pm_graph_ref, "pmStore", pmf, pmn, pm_frame,
                       transition.pm_node_indices[rank], pms[rank])
        rms_helpers.append(names)
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    unfold {smf} {pmf}",
        f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",
        f"  have hFlatIn : {flat_pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
        f"  have hFlat : {flat_post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"    change GeneratedPatterns.Ordinary2Rel (smStore {flat_pre.sm_tid}) (pmStore {flat_pre.pm_tids[0]}) (pmStore {flat_pre.pm_tids[1]}) {_shape_text(list(flat_pre.full_shape))} {_shape_text(list(flat_pre.shard_shape))} at hFlatIn",
        f"    change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {flat_post.sm_tid}) (({pmf} pmStore) {flat_post.pm_tids[0]}) (({pmf} pmStore) {flat_post.pm_tids[1]}) {_shape_text(list(flat_post.full_shape))} {_shape_text(list(flat_post.shard_shape))}",
        f"    rw [{flat_helpers[0]} smStore, {flat_helpers[1]} pmStore, {flat_helpers[2]} pmStore]",
        "    refine ⟨?_, rfl, rfl, rfl⟩",
        "    rw [hFlatIn.full_value]",
        f"    exact GeneratedPatterns.fw_view_allGather0_commute_cp2 (pmStore {flat_pre.pm_tids[0]}) (pmStore {flat_pre.pm_tids[1]}) {rows} {middle} {hidden}",
        "      (by native_decide) (by native_decide) (by native_decide) hFlatIn.rank0_shape hFlatIn.rank1_shape",
    ])
    rms_proofs = []
    for number, ((transition, _cert, pre, weight, post), names) in enumerate(zip(rms_rows, rms_helpers)):
        sm = ir.sm_nodes[transition.sm_node_indices[0]]
        proof = f"hRms{number}"; rms_proofs.append(proof)
        lines.extend([
            f"  have hRmsIn{number} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"  have hWeightFact{number} : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"  unfold {weight.fact_id} RelationFact.Holds StoreSide.read at hWeightFact{number}",
            f"  have hWeight{number} : smStore {sm.ins[1]} = pmStore {sm.ins[1]} := hWeightFact{number}.1",
            f"  have {proof} : {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
            f"    change GeneratedPatterns.Ordinary2Rel (smStore {pre.sm_tid}) (pmStore {pre.pm_tids[0]}) (pmStore {pre.pm_tids[1]}) {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hRmsIn{number}",
            f"    have hcore := GeneratedPatterns.Ordinary2Rel.rms_norm_3d (shard := {pre.shard_shape[0]}) (middle := {pre.shard_shape[1]}) (hidden := {pre.shard_shape[2]}) hRmsIn{number} hWeight{number}",
            "      (by native_decide) (by native_decide) (by native_decide)",
            f"    change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {post.sm_tid}) (({pmf} pmStore) {post.pm_tids[0]}) (({pmf} pmStore) {post.pm_tids[1]}) {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
            f"    rw [{names[0]} smStore, {names[1]} pmStore, {names[2]} pmStore]",
            f"    exact hcore",
        ])
    adapter_proof = None
    if adapter_post is not None:
        adapter_proof = "hAdapter"
        lines.extend([
            f"  have hAdapter : {adapter_post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
            f"    change GeneratedPatterns.Ordinary2Rel (({smf} smStore) {flat_post.sm_tid}) (({pmf} pmStore) {flat_post.pm_tids[0]}) (({pmf} pmStore) {flat_post.pm_tids[1]}) {_shape_text(list(flat_post.full_shape))} {_shape_text(list(flat_post.shard_shape))} at hFlat",
            f"    change ShardedRel (({smf} smStore) {adapter_post.sm_tid}) [({pmf} pmStore) {adapter_post.pm_tids[0]}, ({pmf} pmStore) {adapter_post.pm_tids[1]}] 0 {_shape_text(list(adapter_post.full_shape))} {_shape_text(list(adapter_post.shard_shape))}",
            f"    exact {adapter_t.lean_theorem} (rows := {adapter_post.shard_shape[0]}) (width := {adapter_post.shard_shape[1]}) hFlat",
        ])
    proof_by_id = {flat_post.fact_id: "hFlat"}
    for row, proof in zip(rms_rows, rms_proofs):
        proof_by_id[row[4].fact_id] = proof
    if adapter_post is not None:
        proof_by_id[adapter_post.fact_id] = adapter_proof
    publish = tuple(record.fact_id for record in fresh_records)
    lines.extend([
        "  intro fact hfact",
        f"  have covered : fact ∈ [{', '.join(publish)}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{', '.join(publish)}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
        "  rcases covered with fresh | old",
        "  · rcases fresh with " + " | ".join("rfl" for _ in publish),
    ])
    lines.extend(f"    · exact {proof_by_id[fact_id]}" for fact_id in publish)
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
