"""Heartbeat-safe sparse/full-frame dynamic-K GELU renderer."""
from __future__ import annotations


def render_closed_sparse_k_rank_gelu_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _shape_text, _render_mixed_final_value,
            _typed_certificate_digest,
        )
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (
            _node_text, _shape_text, _render_mixed_final_value,
            _typed_certificate_digest,
        )
        from relation_compiler import get_closed_rule_spec

    chain = relation.dependent_chain_plan
    segment = next(x for x in chain.segments if x.segment_id == segment_id)
    if len(segment.transition_ids) != 1:
        raise ValueError("sparse GELU requires one transition")
    transition = next(x for x in relation.transition_specs
                      if x.transition_id == segment.transition_ids[0])
    try:
        spec = get_closed_rule_spec(transition.rule_id)
    except ValueError as exc:
        raise ValueError("sparse GELU theorem identity mismatch") from exc
    if transition.lean_theorem not in spec.lean_theorems:
        raise ValueError("sparse GELU theorem identity mismatch")
    theorem = spec.lean_theorems[0]
    certs = [x for x in relation.certificates
             if type(x) is spec.certificate_type
             and x.rule_id == spec.rule_id
             and x.lean_theorem in spec.lean_theorems
             and x.op == spec.op
             and ((x.input_fact,), (x.output_fact,)) == (transition.pre_facts, transition.post_facts)
             and _typed_certificate_digest(x) == transition.certificate_digest]
    if len(certs) != 1:
        raise ValueError("sparse GELU requires one exact typed certificate")
    cert = certs[0]
    records = {x.source: x for x in chain.relation_facts}
    if len(records) != len(chain.relation_facts):
        raise ValueError("sparse GELU duplicate relation fact source")
    states = {x.state_id: x for x in chain.states}
    if len(states) != len(chain.states):
        raise ValueError("sparse GELU duplicate relation state id")
    pre, post = records[cert.input_fact], records[cert.output_fact]
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if set(after.fact_ids) - set(before.fact_ids) != {post.fact_id}:
        raise ValueError("sparse GELU post-state contains an unproved fact")
    k = cert.rank_count
    if (k <= 0 or pre.kind != "sharded" or post.kind != "sharded"
            or len(pre.pm_tids) != k or len(post.pm_tids) != k
            or pre.gather_dim != post.gather_dim
            or pre.full_shape != post.full_shape or pre.shard_shape != post.shard_shape):
        raise ValueError("sparse GELU relation metadata mismatch")
    sm_start,sm_end=segment.sm_range; pm_start,pm_end=segment.pm_range
    if (len(transition.sm_node_indices)!=1 or len(transition.pm_node_indices)!=k
            or not set(transition.sm_node_indices)<=set(range(sm_start,sm_end))
            or not set(transition.pm_node_indices)<=set(range(pm_start,pm_end))):
        raise ValueError("sparse GELU writer/frame partition mismatch")
    sm_node=ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes=tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
    if tuple(n.rank for n in pm_nodes) != tuple(range(k)):
        raise ValueError("sparse GELU writers do not have ordered ranks")
    if (sm_node.op != spec.op or len(sm_node.ins) != 1 or len(sm_node.outs) != 1
            or any(n.op != spec.op or len(n.ins) != 1 or len(n.outs) != 1 for n in pm_nodes)):
        raise ValueError("sparse GELU requires unary singleton-output FW_gelu writers")
    if sm_node.params or any(n.params for n in pm_nodes):
        raise ValueError("sparse GELU writers require no parameters")
    if (sm_node.rank != 0 or sm_node.ins != [pre.sm_tid] or sm_node.outs != [post.sm_tid]
            or tuple(n.ins[0] for n in pm_nodes) != tuple(pre.pm_tids)
            or tuple(n.outs[0] for n in pm_nodes) != tuple(post.pm_tids)):
        raise ValueError("sparse GELU writers disagree with ordered relation TIDs")
    sm_frame=list(ir.sm_nodes[sm_start:sm_end]); pm_frame=list(ir.pm_nodes[pm_start:pm_end])
    live_outputs={post.sm_tid,*post.pm_tids}
    if any(live_outputs.intersection(n.outs) for i,n in enumerate(ir.sm_nodes)
           if sm_start<=i<sm_end and i not in transition.sm_node_indices):
        raise ValueError("sparse GELU SM frame overwrites output")
    if any(live_outputs.intersection(n.outs) for i,n in enumerate(ir.pm_nodes)
           if pm_start<=i<pm_end and i not in transition.pm_node_indices):
        raise ValueError("sparse GELU PM frame overwrites output")

    shape=lambda x:_shape_text(list(x))
    sm_nodes_name=f"{segment_id}_smNodes"; pm_nodes_name=f"{segment_id}_pmNodes"
    sm_final_name=f"{segment_id}_smFinal"; pm_final_name=f"{segment_id}_pmFinal"
    lines=[
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", "",
    ]

    def add_writer(name,graph,initial,final_name,nodes_name,frame,pos,node):
        final=f"({final_name} {initial})"; theorem_name=f"{segment_id}_{name}"
        expr=f"fw_gelu ({{store}} {node.ins[0]})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper=_render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame, position=pos,
            output_tid=node.outs[0], input_tids=tuple(node.ins),
            written_tids={t for n in frame for t in n.outs}, expression=expr,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_fw_gelu_out {graph} t {node.rank} {node.ins[0]} {node.outs[0]}",
            ])
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout",""])
        return theorem_name

    sm_helper=add_writer("smWriter",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,
                         sm_frame,transition.sm_node_indices[0]-sm_start,sm_node)
    pm_helpers=[]
    for rank,(index,node) in enumerate(zip(transition.pm_node_indices,pm_nodes)):
        pm_helpers.append(add_writer(f"pmWriter{rank}",ir.pm_graph_ref,"pmStore",pm_final_name,
                                     pm_nodes_name,pm_frame,index-pm_start,node))

    input_list="["+", ".join(f"({pm_final_name} pmStore) {t}" for t in pre.pm_tids)+"]"
    output_list="["+", ".join(f"({pm_final_name} pmStore) {t}" for t in post.pm_tids)+"]"
    lines.extend([
        f"private theorem {segment_id}_out (smStore pmStore : Store)",
        f"    (hin : {pre.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore)) :",
        f"    {post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  change ShardedRel (({sm_final_name} smStore) {pre.sm_tid}) {input_list} {pre.gather_dim} {shape(pre.full_shape)} {shape(pre.shard_shape)} at hin",
        f"  have hSm := {sm_helper} smStore",
    ])
    for rank,helper in enumerate(pm_helpers): lines.append(f"  have hPm{rank} := {helper} pmStore")
    lines.extend([
        f"  have hcomm := {theorem} {post.gather_dim} {input_list}.length {input_list} {shape(post.shard_shape)}",
        "    (by simp) rfl",
        "    (by simp only [List.head?, Option.map, Option.getD]; exact hin.shard_shapes _ (by simp))",
        "    (by intro i hi; exact hin.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))",
        f"  unfold {post.fact_id} RelationFact.Holds",
        f"  change ShardedRel (({sm_final_name} smStore) {post.sm_tid}) {output_list} {post.gather_dim} {shape(post.full_shape)} {shape(post.shard_shape)}",
        "  constructor",
        "  · rw [hSm, hin.full_value, hcomm]",
        "    simp only [List.map, List.length_cons, List.length_nil]",
        f"    rw [{', '.join('← hPm'+str(r) for r in range(k))}]",
        "  · rw [hSm, fw_gelu_shape]", "    exact hin.full_shape",
        "  · simp", "  · exact hin.gather_dim_lt",
        "  · intro shard hmem", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "    rcases hmem with "+" | ".join(f"h{r}" for r in range(k)),
    ])
    for rank in range(k):
        lines.extend([
            "    · subst shard", f"      rw [hPm{rank}, fw_gelu_shape]",
            f"      exact hin.shard_shapes (({pm_final_name} pmStore) {pre.pm_tids[rank]}) (by simp)",
        ])
    lines.extend(["  · exact hin.shape_contract",""])

    lines.extend([
        f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    unfold {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "    · native_decide", "    · native_decide", "    · native_decide", "    · native_decide",
        f"  have hin := hframe {pre.fact_id} (by native_decide)",
        f"  have hout := {segment_id}_out smStore pmStore hin",
        "  intro fact hfact",
        f"  have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered", "  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh", "    rcases fresh with rfl", "    exact hout",
        "  · exact hframe fact old", "",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa only [{sm_final_name}, {pm_final_name}] using {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
