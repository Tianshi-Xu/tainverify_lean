"""Closed sparse/full-frame renderer for typed BW_gelu sharding."""
from __future__ import annotations


def render_closed_k_rank_bw_gelu_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("bw-gelu-pointwise-sharded-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 1:
        raise ValueError("BW_gelu requires one atomic transition")
    transition = {item.transition_id: item for item in relation.transition_specs}.get(
        segment.transition_ids[0]
    )
    if transition is None:
        raise ValueError("BW_gelu transition authority is missing")
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda cert: (
            tuple(sorted((cert.gradient_fact, cert.activation_fact))),
            (cert.output_fact,),
        ),
    )
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient = records[certificate.gradient_fact]
        activation = records[certificate.activation_fact]
        output = records[certificate.output_fact]
    except KeyError as exc:
        raise ValueError("BW_gelu fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before,after = states[segment.pre_state_id],states[segment.post_state_id]
    if (not {gradient.fact_id,activation.fact_id} <= set(before.fact_ids)
            or output.fact_id not in after.fact_ids):
        raise ValueError("BW_gelu pre/post facts are not live")
    if not set(after.fact_ids) <= ({output.fact_id}|set(before.fact_ids)):
        raise ValueError("BW_gelu post-state introduces an unproved fact")
    k=len(output.pm_tids)
    if (k<=0 or certificate.rank_count!=k or certificate.gather_dim!=output.gather_dim
            or gradient.kind!="sharded" or activation.kind!="sharded" or output.kind!="sharded"
            or (gradient.full_shape,gradient.shard_shape,gradient.gather_dim)
               !=(activation.full_shape,activation.shard_shape,activation.gather_dim)
            or (output.full_shape,output.shard_shape,output.gather_dim)
               !=(activation.full_shape,activation.shard_shape,activation.gather_dim)
            or len(gradient.pm_tids)!=k or len(activation.pm_tids)!=k):
        raise ValueError("BW_gelu metadata is not exact")
    if len(transition.sm_node_indices)!=1 or len(transition.pm_node_indices)!=k:
        raise ValueError("BW_gelu footprint is not exact 1+K")
    sm_start,sm_end=segment.sm_range;pm_start,pm_end=segment.pm_range
    if (not set(transition.sm_node_indices)<=set(range(sm_start,sm_end))
            or not set(transition.pm_node_indices)<=set(range(pm_start,pm_end))):
        raise ValueError("BW_gelu writers are outside complete frame")
    sm_frame=list(ir.sm_nodes[sm_start:sm_end]);pm_frame=list(ir.pm_nodes[pm_start:pm_end])
    sm_node=ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes=tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    if (certificate.sm_step_id!=f"sm:{transition.sm_node_indices[0]}:0"
            or certificate.pm_step_ids!=tuple(f"pm:{i}:0" for i in transition.pm_node_indices)):
        raise ValueError("BW_gelu certificate footprint was tampered")
    if (sm_node.rank!=0 or sm_node.op!="BW_gelu" or sm_node.params
            or sm_node.ins!=[gradient.sm_tid,activation.sm_tid]
            or sm_node.outs!=[output.sm_tid]):
        raise ValueError("BW_gelu SM writer roles are not exact")
    if tuple(node.rank for node in pm_nodes)!=tuple(range(k)):
        raise ValueError("BW_gelu PM ranks are not ordered")
    for rank,node in enumerate(pm_nodes):
        if (node.op!="BW_gelu" or node.params
                or node.ins!=[gradient.pm_tids[rank],activation.pm_tids[rank]]
                or node.outs!=[output.pm_tids[rank]]):
            raise ValueError("BW_gelu PM writer roles/order are not exact")

    sm_nodes_name,pm_nodes_name=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes"
    sm_final_name,pm_final_name=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store","",
    ]
    def writer(name,graph,initial,final_name,nodes_name,frame,position,node):
        theorem_name=f"{segment_id}_{name}";final=f"({final_name} {initial})"
        expression=f"bw_gelu ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}","    rfl",
        ])
        helper=_render_mixed_final_value(
            name="hout",graph=graph,initial_store=initial,final_store=final,
            final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=position,
            output_tid=node.outs[0],input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_gelu_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            ])
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout",""]);return theorem_name
    sm_helper=writer("hSmWriter",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,
                     sm_frame,transition.sm_node_indices[0]-sm_start,sm_node)
    pm_helpers=tuple(writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pm_final_name,
                            pm_nodes_name,pm_frame,index-pm_start,node)
                     for r,(index,node) in enumerate(zip(transition.pm_node_indices,pm_nodes)))
    glist="["+", ".join(f"pmFinal {t}" for t in gradient.pm_tids)+"]"
    xlist="["+", ".join(f"pmFinal {t}" for t in activation.pm_tids)+"]"
    olist="["+", ".join(f"pmFinal {t}" for t in output.pm_tids)+"]"
    full=_shape_text(list(output.full_shape));shard=_shape_text(list(output.shard_shape));dim=output.gather_dim
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smFinal := {sm_final_name} smStore",f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "      · native_decide","      · native_decide","      · native_decide","      · native_decide",
        f"    have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} {dim} {full} {shard} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {activation.sm_tid}) {xlist} {dim} {full} {shard} at hx",
        f"    have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN {dim} {k} 0 {glist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"    have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN {dim} {k} 0 {xlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"    have hSmWriter : smFinal {output.sm_tid} = bw_gelu (smFinal {gradient.sm_tid}) (smFinal {activation.sm_tid}) :=",
        f"      {sm_helper} smStore",
    ])
    for rank,(helper,node) in enumerate(zip(pm_helpers,pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {output.pm_tids[rank]} = bw_gelu (pmFinal {gradient.pm_tids[rank]}) (pmFinal {activation.pm_tids[rank]}) :=",
            f"      {helper} pmStore",
            f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
            f"      rw [hPmWriter{rank}, bw_gelu_shape]",
            f"      exact hx.shard_shapes _ (by simp)",
        ])
    lines.extend([
        f"    have hcomm := {theorem} {dim} {k} {glist} {xlist} {shard}",
        "      (by omega) (by simp) (by simp)",
        "      (by simpa using hg.shard_shapes _ (by simp))",
        "      (by simpa using hx.shard_shapes _ (by simp))",
        "      (by intro i hi; exact hg.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))",
        "      (by intro i hi; exact hx.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))",
        f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {k} 0 {olist} := by",
        "      rw [hSmWriter, hgValue, hxValue, hcomm]",
        "      simp only [List.zipWith]",
        "      rw ["+", ".join(f"← hPmWriter{r}" for r in range(k))+"]",
        f"    have hOutValueList : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {olist}.length 0 {olist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hOutValue",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
        "      rw [hSmWriter, bw_gelu_shape]","      exact hx.full_shape",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {output.sm_tid}) {olist} {dim} {full} {shard}",
        "      refine {","        full_value := hOutValueList","        full_shape := hFullShape",
        "        shards_nonempty := by simp","        gather_dim_lt := hx.gather_dim_lt",
        "        shard_shapes := ?_","        shape_contract := by",
        "          simp only [List.length_cons, List.length_nil]","          native_decide","      }",
        "      intro piece hmem","      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with "+" | ".join(f"h{r}" for r in range(k)),
    ])
    for rank in range(k):
        lines.extend(["      · subst piece",f"        exact hOutShape{rank}"])
    lines.extend([
        "    intro fact hfact",f"    have covered : fact ∈ [{output.fact_id}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered","    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with rfl",
        "      exact hout","    · exact hframe fact old","","set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}",f"  pmNodes := {pm_nodes_name}","  sound := by",
        "    intro smStore pmStore hstate",f"    exact {segment_id}_sound smStore pmStore hstate","",
    ])
    return "\n".join(lines)
