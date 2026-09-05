"""Closed sparse/full-frame renderer for typed BW_multiref tensor sums."""
from __future__ import annotations


def render_closed_k_rank_bw_multiref_sum_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import get_closed_rule_spec
    spec=get_closed_rule_spec("bw-multiref-sum-sharded-k-rank");rule=spec.rule_id
    chain=relation.dependent_chain_plan
    segment=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if segment is None or len(segment.transition_ids)!=1:
        raise ValueError("BW_multiref sum requires one atomic transition")
    transition={t.transition_id:t for t in relation.transition_specs}.get(segment.transition_ids[0])
    if transition is None: raise ValueError("BW_multiref sum transition is missing")
    cert=_select_exact_typed_certificate(relation,transition,rule,spec.lean_theorems[0],
        spec.certificate_type,lambda c: (tuple(sorted(set(c.input_facts))), (c.output_fact,)))
    arity=len(cert.input_facts)
    records={r.source:r for r in chain.relation_facts}
    try: inputs=tuple(records[f] for f in cert.input_facts);output=records[cert.output_fact]
    except KeyError as exc: raise ValueError("BW_multiref sum fact is not materialized") from exc
    states={s.state_id:s for s in chain.states};before,after=states[segment.pre_state_id],states[segment.post_state_id]
    if not {r.fact_id for r in inputs}<=set(before.fact_ids) or output.fact_id not in after.fact_ids:
        raise ValueError("BW_multiref sum pre/post facts are not live")
    if not set(after.fact_ids)<=({output.fact_id}|set(before.fact_ids)):
        raise ValueError("BW_multiref sum post-state introduces an unproved fact")
    k=len(output.pm_tids)
    if (k<=0 or cert.rank_count!=k or arity<=0 or output.kind!="sharded"
            or cert.full_shape!=output.full_shape or cert.shard_shape!=output.shard_shape
            or cert.gather_dim!=output.gather_dim
            or len(output.shard_shape)!=3 or cert.gather_dim not in (1,2)
            or any(type(d) is not int or d<=0 for d in output.shard_shape)
            or output.full_shape!=tuple(d*k if i==cert.gather_dim else d for i,d in enumerate(output.shard_shape))
            or any(r.kind!="sharded" or len(r.pm_tids)!=k for r in inputs)
            or any((r.full_shape,r.shard_shape,r.gather_dim)!=(output.full_shape,output.shard_shape,output.gather_dim) for r in inputs)):
        raise ValueError("BW_multiref sum metadata is not exact")
    if len(transition.sm_node_indices)!=1 or len(transition.pm_node_indices)!=k:
        raise ValueError("BW_multiref sum footprint is not exact 1+K")
    ss,se=segment.sm_range;ps,pe=segment.pm_range
    if not set(transition.sm_node_indices)<=set(range(ss,se)) or not set(transition.pm_node_indices)<=set(range(ps,pe)):
        raise ValueError("BW_multiref sum writers are outside complete frame")
    sm_frame=list(ir.sm_nodes[ss:se]);pm_frame=list(ir.pm_nodes[ps:pe]);sm=ir.sm_nodes[transition.sm_node_indices[0]]
    pms=tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
    if cert.sm_step_id!=f"sm:{transition.sm_node_indices[0]}:0" or cert.pm_step_ids!=tuple(f"pm:{i}:0" for i in transition.pm_node_indices):
        raise ValueError("BW_multiref sum certificate footprint was tampered")
    if sm.rank!=0 or sm.op!="BW_multiref" or sm.params or tuple(sm.ins)!=tuple(r.sm_tid for r in inputs) or sm.outs!=[output.sm_tid]:
        raise ValueError("BW_multiref sum SM writer roles are not exact")
    if tuple(n.rank for n in pms)!=tuple(range(k)): raise ValueError("BW_multiref sum PM ranks are not ordered")
    for rank,n in enumerate(pms):
        if n.op!="BW_multiref" or n.params or tuple(n.ins)!=tuple(r.pm_tids[rank] for r in inputs) or n.outs!=[output.pm_tids[rank]]:
            raise ValueError("BW_multiref sum PM writer roles/order are not exact")
    smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=["set_option maxHeartbeats 500000 in",
           f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
           f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
           f"private def {smf} (store : Store) : Store :=",f"  {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
           f"private def {pmf} (store : Store) : Store :=",f"  {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store",""]
    def writer(name,graph,initial,fn,nn,frame,pos,node):
        tn=f"{segment_id}_{name}";final=f"({fn} {initial})";ins="["+", ".join(f"{{store}} {t}" for t in node.ins)+"]";expr=f"tensorSum {ins}"
        lines.extend([f"private theorem {tn} ({initial} : Store) :",f"    {final} {node.outs[0]} = {expr.format(store=final)} := by",
                      f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",f"    unfold {fn}","    rfl"])
        h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,
          position=pos,output_tid=node.outs[0],input_tids=tuple(node.ins),written_tids={t for x in frame for t in x.outs},expression=expr,
          apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                       "simp [applyNodeDistributed, applyNodeRingAttn]",
                       "simpa only [List.map] using "
                       f"(applyNode_bw_multiref_out {graph} t {node.rank} {_shape_text(node.ins)} {node.outs[0]})"])
        lines.extend(x[2:] if x.startswith("  ") else x for x in h);lines.extend(["  exact hout",""]);return tn
    sh=writer("hSmWriter",ir.sm_graph_ref,"smStore",smf,smn,sm_frame,transition.sm_node_indices[0]-ss,sm)
    ph=tuple(writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pm_frame,i-ps,n) for r,(i,n) in enumerate(zip(transition.pm_node_indices,pms)))
    lists=["["+", ".join(f"pmFinal {t}" for t in rec.pm_tids)+"]" for rec in inputs];olist="["+", ".join(f"pmFinal {t}" for t in output.pm_tids)+"]"
    full=_shape_text(list(output.full_shape));shard=_shape_text(list(output.shard_shape));dim=output.gather_dim
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store)",f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
      f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    let smFinal := {smf} smStore",f"    let pmFinal := {pmf} pmStore",
      f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",f"      unfold smFinal pmFinal {smf} {pmf}",f"      apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate",
      "      · native_decide","      · native_decide","      · native_decide","      · native_decide"])
    for j,(rec,lst) in enumerate(zip(inputs,lists)):
        lines.extend([f"    have hi{j} : {rec.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {rec.sm_tid}) {lst} {dim} {full} {shard} at hi{j}",
                      f"    have hv{j} : smFinal {rec.sm_tid} = allGatherPrimDimN {dim} {k} 0 {lst} := by","      simpa only [List.length_cons, List.length_nil] using hi"+str(j)+".full_value"])
    lines.extend([f"    have hSmWriter : smFinal {output.sm_tid} = tensorSum [{', '.join(f'smFinal {r.sm_tid}' for r in inputs)}] :=",f"      {sh} smStore"])
    for r,(helper,node) in enumerate(zip(ph,pms)):
        lines.extend([f"    have hPmWriter{r} : pmFinal {output.pm_tids[r]} = tensorSum [{', '.join(f'pmFinal {x.pm_tids[r]}' for x in inputs)}] :=",f"      {helper} pmStore",
                      f"    have hOutShape{r} : (pmFinal {output.pm_tids[r]}).shape = {shard} := by",f"      rw [hPmWriter{r}, tensorSum_shape]",f"      exact hi0.shard_shapes _ (by simp)"])
    lines.extend(render_multiref_gather_value(cert, inputs, output, lists, olist, shard))
    lines.extend([f"    have hOutValueList : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {olist}.length 0 {olist} := by",
                  "      simpa only [List.length_cons, List.length_nil] using hOutValue",f"    have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
                  "      rw [hSmWriter, tensorSum_shape]","      exact hi0.full_shape",f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
                  f"      change ShardedRel (smFinal {output.sm_tid}) {olist} {dim} {full} {shard}","      refine {","        full_value := hOutValueList","        full_shape := hFullShape",
                  "        shards_nonempty := by simp","        gather_dim_lt := hi0.gather_dim_lt","        shard_shapes := ?_","        shape_contract := by",
                  "          simp only [List.length_cons, List.length_nil]","          native_decide","      }","      intro piece hmem","      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
                  "      rcases hmem with "+" | ".join(f"h{r}" for r in range(k))])
    for r in range(k): lines.extend(["      · subst piece",f"        exact hOutShape{r}"])
    lines.extend(["    intro fact hfact",f"    have covered : fact ∈ [{output.fact_id}] ++ {before.state_id}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
                  "    simp only [List.mem_append] at covered","    rcases covered with fresh | old","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with rfl","      exact hout","    · exact hframe fact old","",
                  "set_option maxRecDepth 8192 in",f"private def {segment_id} :",f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by","    intro smStore pmStore hstate",f"    exact {segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)


def render_multiref_gather_value(cert, inputs, output, lists, olist, shard):
    """Shared value proof for singleton and atomic WRED frames."""
    k=cert.rank_count;dim=cert.gather_dim
    columns="["+", ".join(lists)+"]"
    cases=" | ".join("rfl" for _ in inputs)
    lines=[f"    have hcomm := {cert.lean_theorem} {dim} {k} {shard} {columns}",
        "      (by decide) (by simp) (by decide)",
        "      (by", "        intro xs hxs",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs",
        f"        rcases hxs with {cases} <;> rfl)",
        "      (by", "        intro xs hxs",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs",
        f"        rcases hxs with {cases}"]
    lines.extend(f"        · exact hi{j}.shard_shapes" for j in range(len(inputs)))
    lines[-1]+= ")"
    input_eq="rfl"
    for j in reversed(range(len(inputs))):
        input_eq=f"(congrArg₂ List.cons hv{j} {input_eq})"
    lines.extend([
        f"    have hInputs : [{', '.join(f'smFinal {r.sm_tid}' for r in inputs)}] =",
        f"        [{', '.join(f'allGatherPrimDimN {dim} {k} 0 {lst}' for lst in lists)}] :=",
        f"      {input_eq}",
        f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {k} 0 {olist} := by",
        "      rw [hSmWriter, hInputs]",
        "      rw ["+", ".join(f"hPmWriter{r}" for r in range(k))+"]",
        "      simpa [tensorSumRanks, List.ofFn_succ] using hcomm"])
    return lines
