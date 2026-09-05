"""Closed renderer for exact initial-alias two-way chunk boundaries."""
from __future__ import annotations


def render_closed_init_alias_chunk_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import InitAliasChunkCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import InitAliasChunkCertificate

    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("init-alias chunks require one complete segment")
    segment = segments[0]
    if len(segment.transition_ids) != 1:
        raise ValueError("init-alias chunks require one transition")
    transitions = [t for t in relation.transition_specs if t.transition_id == segment.transition_ids[0]]
    if len(transitions) != 1:
        raise ValueError("init-alias chunk transition identity is missing or duplicated")
    transition = transitions[0]
    certificates = [
        c for c in relation.certificates
        if type(c) is InitAliasChunkCertificate
        and c.rule_id == transition.rule_id
        and c.lean_theorem == transition.lean_theorem
        and (c.input_fact,) == transition.pre_facts
        and (c.output_fact,) == transition.post_facts
    ]
    if len(certificates) != 1:
        raise ValueError("init-alias chunks lack one exact certificate")
    cert = certificates[0]
    records = {fact.source: fact for fact in chain.relation_facts}
    states = {state.state_id: state for state in chain.states}
    if len(records) != len(chain.relation_facts) or len(states) != len(chain.states):
        raise ValueError("init-alias chunk framing identity is duplicated")
    try:
        pre = records[cert.input_fact]
        post = records[cert.output_fact]
        before = states[segment.pre_state_id]
        after = states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("init-alias chunk framing is unresolved") from exc
    dim = cert.gather_dim
    if (
        dim < 0
        or pre.kind != "joined"
        or post.kind not in {"chunked", "sharded"}
        or post.gather_dim != dim
        or pre.sm_tid != cert.sm_tid
        or post.sm_tid != cert.sm_tid
        or cert.seed_pm_tid != cert.sm_tid
        or not cert.alias_steps
        or pre.source.joined_pm_step != cert.alias_steps[0]
        or tuple(pre.full_shape) != cert.full_shape
    ):
        raise ValueError("init-alias chunk relation metadata disagrees")
    if (
        len(post.pm_tids) != 2
        or tuple(post.full_shape) != cert.full_shape
        or tuple(post.shard_shape) != cert.shard_shape
        or len(cert.full_shape) != len(cert.shard_shape)
        or not 0 <= dim < len(cert.shard_shape)
        or cert.full_shape != tuple(
            value * 2 if axis == dim else value
            for axis, value in enumerate(cert.shard_shape)
        )
        or cert.lean_theorem != (
            "TrainVerify.Denote.RelationCompiler.ChunkedRel.of_chunks_two"
            if post.kind == "chunked" else
            "TrainVerify.Denote.RelationCompiler.ShardedRel.of_chunks_two"
        )
    ):
        raise ValueError("init-alias chunk theorem domain disagrees")
    if tuple(range(*segment.sm_range)) or transition.sm_node_indices:
        raise ValueError("init-alias chunks unexpectedly own SM nodes")
    frame_indices = tuple(range(*segment.pm_range))
    writer_indices = tuple(transition.pm_node_indices)
    if len(writer_indices) != 2 or not set(writer_indices) <= set(frame_indices):
        raise ValueError("init-alias chunks require two in-frame PM writers")
    if cert.chunk_steps != tuple(f"pm:{index}:0" for index in writer_indices):
        raise ValueError("init-alias chunk writer steps disagree")
    nodes = tuple(ir.pm_nodes[index] for index in frame_indices)
    writers = tuple(ir.pm_nodes[index] for index in writer_indices)
    source_tid = pre.joined_pm_tid
    for rank, node in enumerate(writers):
        if (
            node.rank != rank or node.op != "ChunkPrim" or node.params != [dim]
            or node.ins != [source_tid] or node.outs != [post.pm_tids[rank]]
        ):
            raise ValueError("init-alias chunk writer signature disagrees")
    live = {source_tid, *post.pm_tids}
    for index, node in zip(frame_indices, nodes):
        if index not in writer_indices and set(node.outs) & live:
            raise ValueError("init-alias chunk frame overwrites live authority")
    if source_tid in {tid for node in nodes for tid in node.outs}:
        raise ValueError("init-alias chunk frame overwrites its full input")
    if pre.fact_id not in before.fact_ids or not set(after.fact_ids) <= set(before.fact_ids) | {post.fact_id}:
        raise ValueError("init-alias chunk liveness disagrees")

    sid = segment_id
    pmn, pmf = f"{sid}_pmNodes", f"{sid}_pmFinal"
    full, shard = _shape_text(list(cert.full_shape)), _shape_text(list(cert.shard_shape))
    lines = [
        "end",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in nodes)}]",
        "noncomputable section",
        f"@[irreducible] private def {pmf} (s : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_source (pmStore : Store) : ({pmf} pmStore) {source_tid} = pmStore {source_tid} := by",
        f"  unfold {pmf}",
        f"  exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} {pmn} pmStore {source_tid} (by native_decide) (by native_decide)",
    ]
    for rank, (absolute, node) in enumerate(zip(writer_indices, writers)):
        position = absolute - segment.pm_range[0]
        lines.extend([
            "set_option maxHeartbeats 500000 in",
            f"private theorem {sid}_writer{rank} (pmStore : Store) :",
            f"    ({pmf} pmStore) {node.outs[0]} = chunkPrimDimN {dim} 2 {rank} (pmStore {source_tid}) := by",
            f"  unfold {pmf}",
            f"  rw [show {pmn} = ({pmn}.take {position}) ++ [{_node_text(node)}] ++ ({pmn}.drop {position + 1}) by native_decide]",
            f"  exact foldl_faithful_chunk_middle_writer {ir.pm_graph_ref} pmStore",
            f"    ({pmn}.take {position}) ({pmn}.drop {position + 1})",
            f"    {rank} {source_tid} {node.outs[0]} {dim} rfl",
            "    (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        ])
    relation_name = "ChunkedRel" if post.kind == "chunked" else "ShardedRel"
    theorem = cert.lean_theorem
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {sid}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds smStore ({pmf} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds smStore ({pmf} pmStore) := by",
        f"    unfold {pmf}",
        f"    apply RelationState.Holds.fold_frame (smGraph := {ir.sm_graph_ref}) (pmGraph := {ir.pm_graph_ref}) [] {pmn} smStore pmStore hstate <;> native_decide",
        f"  have hpre : {pre.fact_id}.Holds smStore ({pmf} pmStore) := hframe _ (by native_decide)",
        f"  unfold {pre.fact_id} RelationFact.Holds StoreSide.read at hpre",
        f"  have hw0 := {sid}_writer0 pmStore",
        f"  have hw1 := {sid}_writer1 pmStore",
        f"  have hsource := {sid}_source pmStore",
        f"  have hc0 : ({pmf} pmStore) {post.pm_tids[0]} = chunkPrimDimN {dim} 2 0 (smStore {post.sm_tid}) := by rw [hw0, ← hsource, ← hpre.1]",
        f"  have hc1 : ({pmf} pmStore) {post.pm_tids[1]} = chunkPrimDimN {dim} 2 1 (smStore {post.sm_tid}) := by rw [hw1, ← hsource, ← hpre.1]",
        f"  have hs0 : (({pmf} pmStore) {post.pm_tids[0]}).shape = {shard} := by rw [hc0, chunkPrimDimN_shape {dim} 2 0 (smStore {post.sm_tid}) {full} hpre.2.1 (by omega)]; native_decide",
        f"  have hs1 : (({pmf} pmStore) {post.pm_tids[1]}).shape = {shard} := by rw [hc1, chunkPrimDimN_shape {dim} 2 1 (smStore {post.sm_tid}) {full} hpre.2.1 (by omega)]; native_decide",
        f"  have hout : {post.fact_id}.Holds smStore ({pmf} pmStore) := by",
        f"    unfold {post.fact_id} RelationFact.Holds",
        f"    change {relation_name} (smStore {post.sm_tid}) [({pmf} pmStore) {post.pm_tids[0]}, ({pmf} pmStore) {post.pm_tids[1]}] {dim} {full} {shard}",
        f"    exact {theorem} hpre.2.1 hs0 hs1 (by native_decide) (by native_decide) hc0 hc1",
        "  intro fact hfact",
        f"  have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered",
        "  rcases covered with rfl | old",
        "  · exact hout",
        "  · exact hframe fact old",
        f"private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        "  smNodes := []",
        f"  pmNodes := {pmn}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{pmf}, List.foldl_nil] using {sid}_sound smStore pmStore hstate",
        "",
    ])
    return "\n".join(lines)
