"""Sparse full-frame renderer for dynamic-K sharded LayerNorm."""
from __future__ import annotations


def render_closed_sparse_k_rank_layernorm_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _shape_text, _render_mixed_final_value,
            _select_exact_typed_certificate,
        )
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (
            _node_text, _shape_text, _render_mixed_final_value,
            _select_exact_typed_certificate,
        )
        from relation_compiler import get_closed_rule_spec

    chain = relation.dependent_chain_plan
    segment = next(x for x in chain.segments if x.segment_id == segment_id)
    if len(segment.transition_ids) != 1:
        raise ValueError("sparse LayerNorm requires one transition")
    transition = next(x for x in relation.transition_specs
                      if x.transition_id == segment.transition_ids[0])
    spec = get_closed_rule_spec(transition.rule_id)
    theorem = spec.lean_theorems[0]
    cert = _select_exact_typed_certificate(
        relation, transition, spec.rule_id, theorem, spec.certificate_type,
        lambda item: ((item.input_fact,), (item.output_fact,)),
    )
    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    pre, post = records[cert.input_fact], records[cert.output_fact]
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    k = cert.rank_count
    if (cert.op != spec.op or cert.gather_dim != 1 or k < 1
            or pre.kind != "sharded" or post.kind != "sharded"
            or pre.gather_dim != 1 or post.gather_dim != 1
            or len(pre.pm_tids) != k or len(post.pm_tids) != k
            or len(cert.external_tids) != 2 or len(cert.external_shapes) != 2
            or cert.external_facts):
        raise ValueError("sparse LayerNorm dynamic K/authority mismatch")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if (len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k
            or not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("sparse LayerNorm writer/frame partition mismatch")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
    external_tids = tuple(cert.external_tids)
    if (sm_node.op != spec.op or sm_node.rank != 0 or sm_node.params
            or sm_node.ins != [pre.sm_tid, *external_tids]
            or sm_node.outs != [post.sm_tid]
            or tuple(node.rank for node in pm_nodes) != tuple(range(k))
            or any(node.op != spec.op or node.params
                   or node.ins != [pre.pm_tids[rank], *external_tids]
                   or node.outs != [post.pm_tids[rank]]
                   for rank, node in enumerate(pm_nodes))):
        raise ValueError("sparse LayerNorm writer signatures mismatch")
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    live_outputs = {post.sm_tid, *post.pm_tids}
    if any(live_outputs.intersection(node.outs)
           for index, node in enumerate(ir.sm_nodes)
           if sm_start <= index < sm_end and index not in transition.sm_node_indices):
        raise ValueError("sparse LayerNorm SM frame overwrites output")
    if any(live_outputs.intersection(node.outs)
           for index, node in enumerate(ir.pm_nodes)
           if pm_start <= index < pm_end and index not in transition.pm_node_indices):
        raise ValueError("sparse LayerNorm PM frame overwrites output")

    authorities = chain.authority_facts
    external = []
    for tid, shape in zip(cert.external_tids, cert.external_shapes):
        eq = [x for x in authorities if x.kind == "tensor_eq" and
              (x.left_side,x.left_tid,x.right_side,x.right_tid)==("sm",tid,"pm",tid)]
        sh = [x for x in authorities if x.kind == "tensor_shape" and
              x.side=="pm" and x.tid==tid and tuple(x.shape)==tuple(shape)]
        if (len(eq)!=1 or len(sh)!=1
                or eq[0].fact_id not in before.fact_ids
                or sh[0].fact_id not in before.fact_ids):
            raise ValueError("sparse LayerNorm external authority mismatch")
        external.append((tid, tuple(shape), eq[0], sh[0]))

    sm_nodes_name=f"{segment_id}_smNodes"; pm_nodes_name=f"{segment_id}_pmNodes"
    sm_final_name=f"{segment_id}_smFinal"; pm_final_name=f"{segment_id}_pmFinal"
    shape=lambda x:_shape_text(list(x))
    lines=[
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", "",
    ]

    def add_writer(name, graph, initial, final_name, nodes_name, frame, pos, node):
        final=f"({final_name} {initial})"; theorem=f"{segment_id}_{name}"
        expr=(f"fw_layernorm ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
              f"({{store}} {node.ins[2]})")
        lines.extend([
            f"private theorem {theorem} ({initial} : Store) :",
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
                f"exact applyNode_fw_layernorm_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} []",
            ])
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper)
        lines.extend(["  exact hout",""])
        return theorem

    sm_helper=add_writer("smWriter",ir.sm_graph_ref,"smStore",sm_final_name,
                         sm_nodes_name,sm_frame,transition.sm_node_indices[0]-sm_start,sm_node)
    pm_helpers=[]
    for rank,(idx,node) in enumerate(zip(transition.pm_node_indices,pm_nodes)):
        pm_helpers.append(add_writer(f"pmWriter{rank}",ir.pm_graph_ref,"pmStore",pm_final_name,
                                     pm_nodes_name,pm_frame,idx-pm_start,node))

    in_list="["+", ".join(f"({pm_final_name} pmStore) {t}" for t in pre.pm_tids)+"]"
    out_list="["+", ".join(f"({pm_final_name} pmStore) {t}" for t in post.pm_tids)+"]"
    shard=tuple(pre.shard_shape); b,s,d=shard
    lines.extend([
        f"private theorem {segment_id}_out (smStore pmStore : Store)",
        f"    (hin : {pre.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore))",
    ])
    for i,(tid,sh,eq,sf) in enumerate(external):
        lines.extend([
            f"    (heq{i} : ({sm_final_name} smStore) {tid} = ({pm_final_name} pmStore) {tid})",
            f"    (hshape{i} : (({pm_final_name} pmStore) {tid}).shape = {shape(sh)})",
        ])
    lines.extend([
        f"    : {post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  change ShardedRel (({sm_final_name} smStore) {pre.sm_tid}) {in_list} 1 {shape(pre.full_shape)} {shape(pre.shard_shape)} at hin",
        f"  have hSm := {sm_helper} smStore",
    ])
    for rank,helper in enumerate(pm_helpers): lines.append(f"  have hPm{rank} := {helper} pmStore")
    lines.extend([
        f"  have hComm := {cert.lean_theorem} (K := {in_list}.length) (b := {b}) (s := {s}) (d := {d})",
        f"    (xs := {in_list}) (gamma := ({pm_final_name} pmStore) {external[0][0]})",
        f"    (beta := ({pm_final_name} pmStore) {external[1][0]}) (by simp) (by omega) (by omega) (by omega)",
        "    rfl (fun x hx => hin.shard_shapes x hx) hshape0 hshape1",
        f"  have hValue : ({sm_final_name} smStore) {post.sm_tid} = allGatherPrimDimN 1 {out_list}.length 0 {out_list} := by",
        "    rw [hSm]", "    rw [heq0, heq1, hin.full_value, hComm]",
        "    simp only [List.map, List.length_cons, List.length_nil]",
        f"    rw [{', '.join('← hPm'+str(r) for r in range(k))}]",
    ])
    for rank,node in enumerate(pm_nodes):
        lines.extend([
            f"  have hOutShape{rank} : (({pm_final_name} pmStore) {node.outs[0]}).shape = {shape(post.shard_shape)} := by",
            f"    rw [hPm{rank}]", "    unfold fw_layernorm",
            f"    rw [hin.shard_shapes (({pm_final_name} pmStore) {pre.pm_tids[rank]}) (by simp)]", "    rfl",
        ])
    lines.extend([
        f"  unfold {post.fact_id} RelationFact.Holds",
        f"  change ShardedRel (({sm_final_name} smStore) {post.sm_tid}) {out_list} 1 {shape(post.full_shape)} {shape(post.shard_shape)}",
        "  refine {", "    full_value := hValue", "    full_shape := ?_",
        "    shards_nonempty := by simp", "    gather_dim_lt := by native_decide",
        "    shard_shapes := ?_", "    shape_contract := by norm_num [List.set, List.getD]", "  }",
        "  · rw [hValue]",
        f"    rw [allGatherPrimDimN_shape 1 {out_list}.length {out_list} {shape(post.shard_shape)}]",
        "    · norm_num [List.set, List.getD]", "    · simp only [List.head?, Option.map, Option.getD]; exact hOutShape0",
        "  · intro shard hmem", "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "    rcases hmem with "+" | ".join("rfl" for _ in range(k)),
    ])
    for rank in range(k): lines.append(f"    · exact hOutShape{rank}")
    lines.append("")

    lines.extend([
        f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    unfold {sm_final_name} {pm_final_name}",
        f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "    · native_decide", "    · native_decide", "    · native_decide", "    · native_decide",
        f"  have hin := hframe {pre.fact_id} (by native_decide)",
    ])
    for i,(tid,sh,eq,sf) in enumerate(external):
        lines.extend([f"  have heq{i} := hframe {eq.fact_id} (by native_decide)",
                      f"  unfold {eq.fact_id} RelationFact.Holds at heq{i}",
                      f"  have hshape{i} := hframe {sf.fact_id} (by native_decide)",
                      f"  unfold {sf.fact_id} RelationFact.Holds at hshape{i}"])
    args=" ".join(["hin", *sum(([f"heq{i}",f"hshape{i}"] for i in range(len(external))),[])])
    lines.extend([
        f"  have hout := {segment_id}_out smStore pmStore {args}",
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
