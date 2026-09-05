"""Atomic shared-writer renderer for paired BW_matmul projections."""
from __future__ import annotations


def render_closed_shared_bw_matmul_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankBWMatmulCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankBWMatmulCertificate
    contracts={
      "bw-matmul-snd-g-sharded-rank4":(".2","snd-g-sharded","TrainVerify.Denote.bw_matmul_snd_split_1_4_8_8"),
      "bw-matmul-fst-contraction-reduction-rank4":(".1","fst-contraction-reduction","TrainVerify.Denote.bw_matmul_fst_split_dW_1_4_8_8"),
    }
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=2: raise ValueError("shared BW_matmul requires exactly two transitions")
    byid={t.transition_id:t for t in relation.transition_specs};ts=tuple(byid[x] for x in seg.transition_ids)
    if set(t.rule_id for t in ts)!=set(contracts): raise ValueError("shared BW_matmul family set is unsupported")
    certs=[]
    for t in ts:
      projection,family,theorem=contracts[t.rule_id]
      if t.lean_theorem!=theorem: raise ValueError("shared BW_matmul theorem identity mismatch")
      c=_select_exact_typed_certificate(relation,t,t.rule_id,theorem,KRankBWMatmulCertificate,
          lambda x:(tuple(sorted(x.input_facts)),(x.output_fact,)))
      if c.projection!=projection or c.family!=family: raise ValueError("shared BW_matmul projection/family mismatch")
      certs.append(c)
    cby={c.projection:c for c in certs};fst,snd=cby[".1"],cby[".2"]
    if fst.input_facts!=snd.input_facts or fst.rank_count!=4 or snd.rank_count!=4: raise ValueError("shared BW_matmul input/rank authority disagrees")
    recs={r.source:r for r in chain.relation_facts}
    try:g,x,y=(recs[f] for f in fst.input_facts);ofst=recs[fst.output_fact];osnd=recs[snd.output_fact]
    except KeyError as exc: raise ValueError("shared BW_matmul fact missing") from exc
    states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if not {g.fact_id,x.fact_id,y.fact_id}<=set(before.fact_ids) or not {ofst.fact_id,osnd.fact_id}<=set(after.fact_ids): raise ValueError("shared BW_matmul facts are not live")
    if not set(after.fact_ids)<=({ofst.fact_id,osnd.fact_id}|set(before.fact_ids)): raise ValueError("shared BW_matmul post-state introduces unproved fact")
    if (g.kind!="sharded" or g.gather_dim!=3 or y.kind!="sharded" or y.gather_dim!=3 or x.kind!="joined" or x.joined_pm_tid is None
        or ofst.kind!="reduction" or osnd.kind!="sharded" or osnd.gather_dim!=3 or len(g.pm_tids)!=4 or len(y.pm_tids)!=4 or len(osnd.pm_tids)!=4 or len(ofst.pm_tids)!=4
        or g.full_shape!=(1,4,8,8) or g.shard_shape!=(1,4,8,2) or y.full_shape!=(1,4,8,8) or y.shard_shape!=(1,4,8,2)
        or x.full_shape!=(1,4,8,8) or osnd.full_shape!=(1,4,8,8) or osnd.shard_shape!=(1,4,8,2) or ofst.full_shape!=(1,4,8,8)):
      raise ValueError("shared BW_matmul relation metadata is not exact")
    if any(t.sm_node_indices!=ts[0].sm_node_indices or t.pm_node_indices!=ts[0].pm_node_indices for t in ts): raise ValueError("shared BW_matmul transitions do not share exact writers")
    if len(ts[0].sm_node_indices)!=1 or len(ts[0].pm_node_indices)!=4: raise ValueError("shared BW_matmul footprint must be 1+4")
    ss,se=seg.sm_range;ps,pe=seg.pm_range;si=ts[0].sm_node_indices[0];pis=ts[0].pm_node_indices
    if (ss,se)!=(si,si+1) or tuple(range(ps,pe))!=pis: raise ValueError("shared BW_matmul full frame differs from writer footprint")
    sm=ir.sm_nodes[si];pms=tuple(ir.pm_nodes[i] for i in pis)
    if sm.rank!=0 or tuple(n.rank for n in pms)!=(0,1,2,3): raise ValueError("shared BW_matmul ranks are not ordered")
    writers=(sm,*pms)
    if any(n.op!="BW_matmul" or len(n.ins)!=3 or len(n.outs)!=2 or n.params for n in writers): raise ValueError("shared BW_matmul node syntax is invalid")
    if tuple(sm.ins)!=(g.sm_tid,x.sm_tid,y.sm_tid) or tuple(tuple(n.ins) for n in pms)!=tuple((g.pm_tids[r],x.joined_pm_tid,y.pm_tids[r]) for r in range(4)): raise ValueError("shared BW_matmul input roles disagree")
    if sm.outs!=(ofst.sm_tid,osnd.sm_tid) and sm.outs!=[ofst.sm_tid,osnd.sm_tid]: raise ValueError("shared BW_matmul SM outputs disagree")
    if tuple(tuple(n.outs) for n in pms)!=tuple((ofst.pm_tids[r],osnd.pm_tids[r]) for r in range(4)): raise ValueError("shared BW_matmul PM outputs disagree")
    for c,slot in ((fst,0),(snd,1)):
      if c.sm_step_id!=f"sm:{si}:{slot}" or c.pm_step_ids!=tuple(f"pm:{i}:{slot}" for i in pis): raise ValueError("shared BW_matmul certificate projection footprint was tampered")
    smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    sf=[sm];pf=list(pms);lines=[f"private def {smn} : List NodeDecl := [{_node_text(sm)}]",f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pms)}]",f"private def {smf} (s : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"private def {pmf} (s : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
    def helper(name,graph,initial,fn,nn,frame,pos,node,slot):
      tn=f"{segment_id}_{name}";final=f"({fn} {initial})";proj=".1" if slot==0 else ".2";expr=f"(bw_matmul ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){proj}"
      lines.extend([f"private theorem {tn} ({initial} : Store) : {final} {node.outs[slot]} = {expr.format(store=final)} := by",f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {fn}; rfl"])
      lemma="applyNode_bw_matmul_fst_out" if slot==0 else "applyNode_bw_matmul_snd_out"
      h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=node.outs[slot],input_tids=tuple(node.ins),written_tids={t for z in frame for t in z.outs},expression=expr,
        apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact {lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)"])
      lines.extend(z[2:] if z.startswith("  ") else z for z in h);lines.extend(["  exact hout",""]);return tn
    hs0=helper("hSmFst",ir.sm_graph_ref,"smStore",smf,smn,sf,0,sm,0);hs1=helper("hSmSnd",ir.sm_graph_ref,"smStore",smf,smn,sf,0,sm,1)
    hp0=[];hp1=[]
    for r,n in enumerate(pms): hp0.append(helper(f"hPmFst{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pf,r,n,0));hp1.append(helper(f"hPmSnd{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pf,r,n,1))
    gl="["+", ".join(f"pmFinal {t}" for t in g.pm_tids)+"]";yl="["+", ".join(f"pmFinal {t}" for t in y.pm_tids)+"]";fl="["+", ".join(f"pmFinal {t}" for t in ofst.pm_tids)+"]";sl="["+", ".join(f"pmFinal {t}" for t in osnd.pm_tids)+"]"
    full="[1, 4, 8, 8]";shard="[1, 4, 8, 2]"
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    let smFinal := {smf} smStore",f"    let pmFinal := {pmf} pmStore",f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",f"      unfold smFinal pmFinal {smf} {pmf}",f"      apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate","      · native_decide","      · native_decide","      · native_decide","      · native_decide",f"    have hg : {g.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {g.sm_tid}) {gl} 3 {full} {shard} at hg",f"    have hx : {x.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change smFinal {x.sm_tid} = pmFinal {x.joined_pm_tid} ∧ (smFinal {x.sm_tid}).shape = {full} ∧ (pmFinal {x.joined_pm_tid}).shape = {full} at hx",f"    have hy : {y.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {y.sm_tid}) {yl} 3 {full} {shard} at hy",f"    have hgValue : smFinal {g.sm_tid} = allGatherPrimDimN 3 4 0 {gl} := by simpa only [List.length_cons, List.length_nil] using hg.full_value",f"    have hyValue : smFinal {y.sm_tid} = allGatherPrimDimN 3 4 0 {yl} := by simpa only [List.length_cons, List.length_nil] using hy.full_value",f"    have hxTShape : (transpose2d (pmFinal {x.joined_pm_tid})).shape = {full} := transpose2d_shape_1_4_8_8 _ hx.2.2",f"    have hSmFst := {hs0} smStore",f"    have hSmSnd := {hs1} smStore",f"    change smFinal {sm.outs[0]} = batchedMatmul (smFinal {sm.ins[0]}) (transpose2d (smFinal {sm.ins[2]})) at hSmFst",f"    change smFinal {sm.outs[1]} = batchedMatmul (transpose2d (smFinal {sm.ins[1]})) (smFinal {sm.ins[0]}) at hSmSnd"])
    for r in range(4): lines.extend([f"    have hPmFst{r} := {hp0[r]} pmStore",f"    have hPmSnd{r} := {hp1[r]} pmStore",f"    change pmFinal {pms[r].outs[0]} = batchedMatmul (pmFinal {pms[r].ins[0]}) (transpose2d (pmFinal {pms[r].ins[2]})) at hPmFst{r}",f"    change pmFinal {pms[r].outs[1]} = batchedMatmul (transpose2d (pmFinal {pms[r].ins[1]})) (pmFinal {pms[r].ins[0]}) at hPmSnd{r}",f"    have hgShape{r} := hg.shard_shapes (pmFinal {g.pm_tids[r]}) (by simp)",f"    have hyShape{r} := hy.shard_shapes (pmFinal {y.pm_tids[r]}) (by simp)",f"    have hFstShape{r} : (pmFinal {ofst.pm_tids[r]}).shape = {full} := by rw [hPmFst{r}]; exact batchedMatmul_shape_1_4_8_2_1_4_2_8 _ _ hgShape{r} (transpose2d_shape_1_4_8_2 _ hyShape{r})",f"    have hSndShape{r} : (pmFinal {osnd.pm_tids[r]}).shape = {shard} := by rw [hPmSnd{r}]; exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ hxTShape hgShape{r}"])
    lines.extend([f"    have hsndComm := {snd.lean_theorem} (transpose2d (pmFinal {x.joined_pm_tid}))",*(f"      (pmFinal {t})" for t in g.pm_tids),"      hxTShape",*(f"      hgShape{r}" for r in range(4)),f"    have hSndValue : smFinal {osnd.sm_tid} = allGatherPrimDimN 3 4 0 {sl} := by","      rw [hSmSnd, hgValue, hx.1, hsndComm]","      rw ["+", ".join(f"← hPmSnd{r}" for r in range(4))+"]",f"    have hSndValueList : smFinal {osnd.sm_tid} = allGatherPrimDimN 3 {sl}.length 0 {sl} := by simpa only [List.length_cons, List.length_nil] using hSndValue",f"    have hSndFullShape : (smFinal {osnd.sm_tid}).shape = {full} := by rw [hSmSnd]; exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_8 _ hx.2.1) hg.full_shape",f"    have houtSnd : {osnd.fact_id}.Holds smFinal pmFinal := by",f"      change ShardedRel (smFinal {osnd.sm_tid}) {sl} 3 {full} {shard}","      refine { full_value := hSndValueList, full_shape := hSndFullShape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide }","      intro piece hmem","      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem","      rcases hmem with h0 | h1 | h2 | h3"])
    for r in range(4): lines.extend(["      · subst piece",f"        exact hSndShape{r}"])
    lines.extend([f"    have hfstComm := {fst.lean_theorem}",*(f"      (pmFinal {t})" for t in g.pm_tids),*(f"      (pmFinal {t})" for t in y.pm_tids),*(f"      hgShape{r}" for r in range(4)),*(f"      hyShape{r}" for r in range(4)),f"    have hFstValue : smFinal {ofst.sm_tid} = allReducePrim 4 0 {fl} := by","      rw [hSmFst, hgValue, hyValue, hfstComm]","      rw ["+", ".join(f"← hPmFst{r}" for r in range(4))+"]",f"    have hFstValueList : smFinal {ofst.sm_tid} = allReducePrim {fl}.length 0 {fl} := by simpa only [List.length_cons, List.length_nil] using hFstValue",f"    have hFstFullShape : (smFinal {ofst.sm_tid}).shape = {full} := by rw [hSmFst]; exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ hg.full_shape (transpose2d_shape_1_4_8_8 _ hy.full_shape)",f"    have houtFst : {ofst.fact_id}.Holds smFinal pmFinal := by",f"      change ReductionRel (smFinal {ofst.sm_tid}) {fl} {full}","      refine { full_value := hFstValueList, full_shape := hFstFullShape, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }","      · intro piece hmem","        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem","        rcases hmem with h0 | h1 | h2 | h3"])
    for r in range(4): lines.extend(["        · subst piece",f"          exact hFstShape{r}"])
    lines.extend(["      · rw [← hFstValueList]","        exact hFstFullShape","    intro fact hfact",f"    have covered : fact ∈ [{ofst.fact_id}, {osnd.fact_id}] ++ {before.state_id}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{ofst.fact_id}, {osnd.fact_id}] ++ {before.state_id}.facts by native_decide) hfact","    simp only [List.mem_append] at covered","    rcases covered with fresh | old","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with rfl | rfl","      · exact houtFst","      · exact houtSnd","    · exact hframe fact old","","set_option maxRecDepth 8192 in",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by intro smStore pmStore hstate; exact "+f"{segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)
