"""Atomic cross-axis renderer for transpose plus BW_softmax."""
from __future__ import annotations


def render_closed_transpose_bw_softmax_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankTransposeRelationCertificate, KRankBWSoftmaxCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankTransposeRelationCertificate, KRankBWSoftmaxCertificate
    trule="transpose-sharded-k-rank"
    softmax_contracts={
      "bw-softmax-sharded-dim1-rank4":("TrainVerify.Denote.softmaxBwd_split_dim1_4_1_4_8_8_g234",1,(1,1,8,8)),
      "bw-softmax-sharded-dim2-rank4":("TrainVerify.Denote.bw_softmax_distribute_allGatherPrimDimN_dim2_4_1_4_2_8_g164",2,(1,4,2,8)),
    }
    transpose_contracts={
      "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4":(2,(1,4,8,8),(1,4,2,8),1,(1,8,4,8),(1,2,4,8)),
      "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4":(3,(1,4,8,8),(1,4,8,2),3,(1,8,4,8),(1,8,4,2)),
    }
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=2: raise ValueError("transpose/BW_softmax requires two transitions")
    byid={t.transition_id:t for t in relation.transition_specs};ts=tuple(byid[x] for x in seg.transition_ids)
    t=next((z for z in ts if z.rule_id==trule),None);s=next((z for z in ts if z.rule_id in softmax_contracts),None)
    if s is None: raise ValueError("transpose/BW_softmax typed family mismatch")
    stheorem,soft_dim,soft_shard=softmax_contracts[s.rule_id];srule=s.rule_id
    if t is None or t.lean_theorem not in transpose_contracts or s.lean_theorem!=stheorem: raise ValueError("transpose/BW_softmax typed family mismatch")
    ttheorem=t.lean_theorem;tin_dim,tin_full,tin_shard,tout_dim,tout_full,tout_shard=transpose_contracts[ttheorem]
    tc=_select_exact_typed_certificate(relation,t,trule,ttheorem,KRankTransposeRelationCertificate,lambda c:((c.input_fact,),(c.output_fact,)))
    sc=_select_exact_typed_certificate(relation,s,srule,stheorem,KRankBWSoftmaxCertificate,lambda c:(tuple(sorted((c.gradient_fact,c.activation_fact))),(c.output_fact,)))
    rec={r.source:r for r in chain.relation_facts}
    try: ti,to=rec[tc.input_fact],rec[tc.output_fact];sg,sy,so=rec[sc.gradient_fact],rec[sc.activation_fact],rec[sc.output_fact]
    except KeyError as exc: raise ValueError("transpose/BW_softmax fact missing") from exc
    states={x.state_id:x for x in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if not {ti.fact_id,sg.fact_id,sy.fact_id}<=set(before.fact_ids) or not {to.fact_id,so.fact_id}<=set(after.fact_ids): raise ValueError("transpose/BW_softmax facts are not live")
    if not set(after.fact_ids)<=({to.fact_id,so.fact_id}|set(before.fact_ids)): raise ValueError("transpose/BW_softmax post-state introduces unproved fact")
    if (ti.kind!="sharded" or ti.gather_dim!=tin_dim or ti.full_shape!=tin_full or ti.shard_shape!=tin_shard
        or to.kind!="sharded" or to.gather_dim!=tout_dim or to.full_shape!=tout_full or to.shard_shape!=tout_shard
        or any(r.kind!="sharded" or r.gather_dim!=soft_dim or r.full_shape!=(1,4,8,8) or r.shard_shape!=soft_shard for r in (sg,sy,so))):
      raise ValueError("transpose/BW_softmax metadata is not exact")
    if tc.rank_count!=4 or sc.rank_count!=4 or sc.gather_dim!=soft_dim: raise ValueError("transpose/BW_softmax rank authority mismatch")
    tr_sm=t.sm_node_indices;tr_pm=t.pm_node_indices;sf_sm=s.sm_node_indices;sf_pm=s.pm_node_indices
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if (len(tr_sm),len(sf_sm),len(tr_pm),len(sf_pm))!=(1,1,4,4) or set(tr_sm)&set(sf_sm) or set(tr_pm)&set(sf_pm) or set(tr_sm)|set(sf_sm)!=set(range(ss,se)) or set(tr_pm)|set(sf_pm)!=set(range(ps,pe)):
      raise ValueError("transpose/BW_softmax footprints are not a disjoint complete partition")
    tn=ir.sm_nodes[tr_sm[0]];sn=ir.sm_nodes[sf_sm[0]];tp=tuple(ir.pm_nodes[i] for i in tr_pm);sp=tuple(ir.pm_nodes[i] for i in sf_pm)
    if tn.op!="BW_transpose" or len(tn.ins)!=2 or tn.outs!=[to.sm_tid] or tuple(tn.params)!=(1,2) or tn.ins[0]!=ti.sm_tid: raise ValueError("transpose SM writer is invalid")
    if tuple(n.rank for n in tp)!=(0,1,2,3) or any(n.op!="BW_transpose" or len(n.ins)!=2 or tuple(n.params)!=(1,2) or n.ins[0]!=ti.pm_tids[r] or n.outs!=[to.pm_tids[r]] for r,n in enumerate(tp)): raise ValueError("transpose PM writers are invalid")
    if sn.op!="BW_softmax" or tuple(sn.ins)!=(sg.sm_tid,sy.sm_tid) or sn.outs!=[so.sm_tid]: raise ValueError("BW_softmax SM writer is invalid")
    if tuple(n.rank for n in sp)!=(0,1,2,3) or any(n.op!="BW_softmax" or tuple(n.ins)!=(sg.pm_tids[r],sy.pm_tids[r]) or n.outs!=[so.pm_tids[r]] for r,n in enumerate(sp)): raise ValueError("BW_softmax PM writers are invalid")
    if tc.sm_step_id!=f"sm:{tr_sm[0]}:0" or tc.pm_step_ids!=tuple(f"pm:{i}:0" for i in tr_pm) or sc.sm_step_id!=f"sm:{sf_sm[0]}:0" or sc.pm_step_ids!=tuple(f"pm:{i}:0" for i in sf_pm): raise ValueError("transpose/BW_softmax certificate footprint was tampered")
    smframe=list(ir.sm_nodes[ss:se]);pmframe=list(ir.pm_nodes[ps:pe]);smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in smframe)}]",f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pmframe)}]",f"private def {smf} (z : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z",f"private def {pmf} (z : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z",""]
    def helper(name,graph,initial,fn,nn,frame,pos,node,kind):
      final=f"({fn} {initial})";out=node.outs[0]
      if kind=="transpose": expr=f"transposeAxes {node.params[0]} {node.params[1]} ({{store}} {node.ins[0]})";apply=f"exact applyNode_bw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {out} {node.params[0]} {node.params[1]}"
      else: expr=f"bw_softmax ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})";apply=f"exact applyNode_bw_softmax_out_g234 {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {out} {_shape_text(node.params or [])}"
      th=f"{segment_id}_{name}";lines.extend([f"private theorem {th} ({initial} : Store) : {final} {out} = {expr.format(store=final)} := by",f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {fn}; rfl"])
      h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=out,input_tids=tuple(node.ins[:1] if kind=="transpose" else node.ins),written_tids={u for n in frame for u in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",apply])
      lines.extend(z[2:] if z.startswith("  ") else z for z in h);lines.extend(["  exact hout",""]);return th
    htS=helper("hTransposeSm",ir.sm_graph_ref,"smStore",smf,smn,smframe,tr_sm[0]-ss,tn,"transpose");hsS=helper("hSoftmaxSm",ir.sm_graph_ref,"smStore",smf,smn,smframe,sf_sm[0]-ss,sn,"softmax")
    htP=[helper(f"hTransposePm{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"transpose") for r,(i,n) in enumerate(zip(tr_pm,tp))]
    hsP=[helper(f"hSoftmaxPm{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"softmax") for r,(i,n) in enumerate(zip(sf_pm,sp))]
    til="["+", ".join(f"pmFinal {u}" for u in ti.pm_tids)+"]";tol="["+", ".join(f"pmFinal {u}" for u in to.pm_tids)+"]";gl="["+", ".join(f"pmFinal {u}" for u in sg.pm_tids)+"]";yl="["+", ".join(f"pmFinal {u}" for u in sy.pm_tids)+"]";ol="["+", ".join(f"pmFinal {u}" for u in so.pm_tids)+"]"
    soft_shard_text=_shape_text(list(soft_shard));soft_shape_args=" ".join(str(x) for x in soft_shard[:3]);soft_fn="softmaxBwd" if soft_dim==1 else "bw_softmax"
    tin_shard_text=_shape_text(list(tin_shard));tout_full_text=_shape_text(list(tout_full));tout_shard_text=_shape_text(list(tout_shard))
    tin_symbolic=list(tin_shard);tin_symbolic[tin_dim]=f"{tin_shard[tin_dim]} * {til}.length";tin_symbolic_text="["+", ".join(map(str,tin_symbolic))+"]"
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    let smFinal := {smf} smStore",f"    let pmFinal := {pmf} pmStore",f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",f"      unfold smFinal pmFinal {smf} {pmf}",f"      apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate","      · native_decide","      · native_decide","      · native_decide","      · native_decide",f"    have hti : {ti.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {ti.sm_tid}) {til} {tin_dim} {tin_symbolic_text} {tin_shard_text} at hti",f"    have hg : {sg.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {sg.sm_tid}) {gl} {soft_dim} [1, 4, 8, 8] {soft_shard_text} at hg",f"    have hy : {sy.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {sy.sm_tid}) {yl} {soft_dim} [1, 4, 8, 8] {soft_shard_text} at hy",f"    have hTsm := {htS} smStore",f"    change smFinal {to.sm_tid} = transposeAxes 1 2 (smFinal {ti.sm_tid}) at hTsm",f"    have hSsm := {hsS} smStore",f"    change smFinal {so.sm_tid} = {soft_fn} (smFinal {sg.sm_tid}) (smFinal {sy.sm_tid}) at hSsm"])
    for r in range(4): lines.extend([f"    have hTpm{r} := {htP[r]} pmStore",f"    change pmFinal {to.pm_tids[r]} = transposeAxes 1 2 (pmFinal {ti.pm_tids[r]}) at hTpm{r}",f"    have hSpm{r} := {hsP[r]} pmStore",f"    change pmFinal {so.pm_tids[r]} = {soft_fn} (pmFinal {sg.pm_tids[r]}) (pmFinal {sy.pm_tids[r]}) at hSpm{r}",f"    have hgShape{r} := hg.shard_shapes (pmFinal {sg.pm_tids[r]}) (by simp)",f"    have hyShape{r} := hy.shard_shapes (pmFinal {sy.pm_tids[r]}) (by simp)",f"    have hSShape{r} : (pmFinal {so.pm_tids[r]}).shape = {soft_shard_text} := by rw [hSpm{r}]; exact bw_softmax_shape_d8_g234 _ _ {soft_shape_args} hyShape{r}"])
    lines.extend([f"    have htRaw := {tc.lean_theorem} hti",f"    have houtT : {to.fact_id}.Holds smFinal pmFinal := by",f"      change ShardedRel (smFinal {to.sm_tid}) {tol} {tout_dim} {tout_full_text} {tout_shard_text}","      rw [hTsm, "+", ".join(f"hTpm{r}" for r in range(4))+"]","      simpa using htRaw",f"    have hgValue : smFinal {sg.sm_tid} = allGatherPrimDimN {soft_dim} 4 0 {gl} := by simpa only [List.length_cons, List.length_nil] using hg.full_value",f"    have hyValue : smFinal {sy.sm_tid} = allGatherPrimDimN {soft_dim} 4 0 {yl} := by simpa only [List.length_cons, List.length_nil] using hy.full_value"])
    if soft_dim == 1:
      for name,rel,lst in (("g",sg,gl),("y",sy,yl)):
        for r in range(4): lines.extend([f"    have h{name}Chunk{r} : chunkPrimDimN 1 4 {r} (smFinal {rel.sm_tid}) = pmFinal {rel.pm_tids[r]} := by",f"      rw [h{name}Value]",f"      simpa [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8" ,*(f"        (pmFinal {u})" for u in rel.pm_tids),*(f"        (h{name}Shape{q})" for q in range(4)),f"        {r} (by omega))"])
      lines.extend([f"    have hcomm := {sc.lean_theorem} (smFinal {sg.sm_tid}) (smFinal {sy.sm_tid}) hg.full_shape hy.full_shape",f"    have hSValue : smFinal {so.sm_tid} = allGatherPrimDimN 1 4 0 {ol} := by","      rw [hSsm, hcomm]","      rw ["+", ".join(f"hSpm{r}, ← hgChunk{r}, ← hyChunk{r}" for r in range(4))+"]"])
    else:
      lines.extend([f"    have hcomm := {sc.lean_theorem}",*(f"      (pmFinal {u})" for u in sg.pm_tids),*(f"      (pmFinal {u})" for u in sy.pm_tids),*(f"      hgShape{r}" for r in range(4)),*(f"      hyShape{r}" for r in range(4)),f"    have hSValue : smFinal {so.sm_tid} = allGatherPrimDimN 2 4 0 {ol} := by","      rw [hSsm, hgValue, hyValue, hcomm]","      rw ["+", ".join(f"← hSpm{r}" for r in range(4))+"]"])
    lines.extend([f"    have hSValueList : smFinal {so.sm_tid} = allGatherPrimDimN {soft_dim} {ol}.length 0 {ol} := by simpa only [List.length_cons, List.length_nil] using hSValue",f"    have hSFullShape : (smFinal {so.sm_tid}).shape = [1, 4, 8, 8] := by rw [hSsm]; exact bw_softmax_shape_d8_g234 _ _ 1 4 8 hy.full_shape",f"    have hSShapes : ∀ z ∈ {ol}, z.shape = {soft_shard_text} := by","      simp only [List.forall_mem_cons]","      exact ⟨"+", ".join(f"hSShape{r}" for r in range(4))+", List.forall_mem_nil _⟩",f"    have houtS : {so.fact_id}.Holds smFinal pmFinal := by",f"      change ShardedRel (smFinal {so.sm_tid}) {ol} {soft_dim} [1, 4, 8, 8] {soft_shard_text}","      exact { full_value := hSValueList, full_shape := hSFullShape, shards_nonempty := List.cons_ne_nil _ _, gather_dim_lt := by native_decide, shard_shapes := hSShapes, shape_contract := by simp only [List.map, List.length_cons, List.length_nil]; native_decide }"])
    lines.extend(["    intro fact hfact",f"    have covered : fact ∈ [{to.fact_id}, {so.fact_id}] ++ {before.state_id}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{to.fact_id}, {so.fact_id}] ++ {before.state_id}.facts by native_decide) hfact","    simp only [List.mem_append] at covered","    rcases covered with fresh | old","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with rfl | rfl","      · exact houtT","      · exact houtS","    · exact hframe fact old","","set_option maxRecDepth 8192 in",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by intro smStore pmStore hstate; exact "+f"{segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)
