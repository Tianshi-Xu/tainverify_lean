"""Atomic shared-writer renderer for paired batch-sharded BW_matmul projections."""
from __future__ import annotations


def render_closed_paired_batch_bw_matmul_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import KRankBWMatmulCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import KRankBWMatmulCertificate
    contracts={
      ".1":"TrainVerify.Denote.bw_matmul_fst_split_dim1_4_1_4_8_8",
      ".2":"TrainVerify.Denote.bw_matmul_snd_split_batchdim1_1_4_8_8",
    }
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=2: raise ValueError("paired batch BW_matmul requires two transitions")
    byid={t.transition_id:t for t in relation.transition_specs};ts=tuple(byid[x] for x in seg.transition_ids);certs=[]
    for t in ts:
      if t.rule_id!="bw-matmul-batch-sharded-rank4": raise ValueError("paired batch BW_matmul rule mismatch")
      cands=[]
      for projection,theorem in contracts.items():
        if t.lean_theorem==theorem:
          c=_select_exact_typed_certificate(relation,t,t.rule_id,theorem,KRankBWMatmulCertificate,
              lambda x:(tuple(sorted(x.input_facts)),(x.output_fact,)))
          if c.projection!=projection or c.family!="batch-sharded": raise ValueError("paired batch BW_matmul certificate mismatch")
          cands.append(c)
      if len(cands)!=1: raise ValueError("paired batch BW_matmul theorem identity mismatch")
      certs.append(cands[0])
    cby={c.projection:c for c in certs};fst,snd=cby[".1"],cby[".2"]
    if fst.input_facts!=snd.input_facts or fst.rank_count!=4 or snd.rank_count!=4: raise ValueError("paired batch BW_matmul authority mismatch")
    recs={r.source:r for r in chain.relation_facts}
    try:g,x,y=(recs[f] for f in fst.input_facts);ofst=recs[fst.output_fact];osnd=recs[snd.output_fact]
    except KeyError as exc: raise ValueError("paired batch BW_matmul fact missing") from exc
    allrecs=(g,x,y,ofst,osnd);full=(1,4,8,8);shard=(1,1,8,8)
    if any(r.kind!="sharded" or r.gather_dim!=1 or len(r.pm_tids)!=4 or r.full_shape!=full or r.shard_shape!=shard for r in allrecs):
      raise ValueError("paired batch BW_matmul metadata mismatch")
    states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if not {g.fact_id,x.fact_id,y.fact_id}<=set(before.fact_ids) or not {ofst.fact_id,osnd.fact_id}<=set(after.fact_ids): raise ValueError("paired batch BW_matmul liveness mismatch")
    if not set(after.fact_ids)<=({ofst.fact_id,osnd.fact_id}|set(before.fact_ids)): raise ValueError("paired batch BW_matmul post-state mismatch")
    if any(t.sm_node_indices!=ts[0].sm_node_indices or t.pm_node_indices!=ts[0].pm_node_indices for t in ts): raise ValueError("paired batch BW_matmul writers are not shared")
    if len(ts[0].sm_node_indices)!=1 or len(ts[0].pm_node_indices)!=4: raise ValueError("paired batch BW_matmul footprint mismatch")
    ss,se=seg.sm_range;ps,pe=seg.pm_range;si=ts[0].sm_node_indices[0];pis=ts[0].pm_node_indices
    if (ss,se)!=(si,si+1) or tuple(range(ps,pe))!=pis: raise ValueError("paired batch BW_matmul frame mismatch")
    sm=ir.sm_nodes[si];pms=tuple(ir.pm_nodes[i] for i in pis);writers=(sm,*pms)
    if any(n.op!="BW_matmul" or len(n.ins)!=3 or len(n.outs)!=2 or n.params for n in writers): raise ValueError("paired batch BW_matmul node syntax mismatch")
    if tuple(sm.ins)!=(g.sm_tid,x.sm_tid,y.sm_tid) or tuple(tuple(n.ins) for n in pms)!=tuple((g.pm_tids[r],x.pm_tids[r],y.pm_tids[r]) for r in range(4)): raise ValueError("paired batch BW_matmul roles mismatch")
    if tuple(sm.outs)!=(ofst.sm_tid,osnd.sm_tid) or tuple(tuple(n.outs) for n in pms)!=tuple((ofst.pm_tids[r],osnd.pm_tids[r]) for r in range(4)): raise ValueError("paired batch BW_matmul outputs mismatch")
    for c,slot in ((fst,0),(snd,1)):
      if c.sm_step_id!=f"sm:{si}:{slot}" or c.pm_step_ids!=tuple(f"pm:{i}:{slot}" for i in pis): raise ValueError("paired batch BW_matmul projection footprint mismatch")
    smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[f"private def {smn} : List NodeDecl := [{_node_text(sm)}]",f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pms)}]",f"private def {smf} (s : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"private def {pmf} (s : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
    def helper(name,graph,initial,fn,nn,frame,pos,node,slot):
      tn=f"{segment_id}_{name}";final=f"({fn} {initial})";proj=".1" if slot==0 else ".2";expr=f"(bw_matmul ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){proj}";lemma="applyNode_bw_matmul_fst_out" if slot==0 else "applyNode_bw_matmul_snd_out"
      lines.extend([f"private theorem {tn} ({initial} : Store) : {final} {node.outs[slot]} = {expr.format(store=final)} := by",f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {fn}; rfl"])
      h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=node.outs[slot],input_tids=tuple(node.ins),written_tids={t for z in frame for t in z.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact {lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)"])
      lines.extend(z[2:] if z.startswith("  ") else z for z in h);lines.extend(["  exact hout",""]);return tn
    hs=[helper(f"hSm{slot}",ir.sm_graph_ref,"smStore",smf,smn,[sm],0,sm,slot) for slot in range(2)]
    hp=[[helper(f"hPm{slot}_{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,list(pms),r,n,slot) for r,n in enumerate(pms)] for slot in range(2)]
    def vals(rec):return "["+", ".join(f"pmFinal {t}" for t in rec.pm_tids)+"]"
    gl,xl,yl,fl,sl=map(vals,(g,x,y,ofst,osnd));F="[1, 4, 8, 8]";S="[1, 1, 8, 8]"
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f" let smFinal:={smf} smStore",f" let pmFinal:={pmf} pmStore",f" have hframe:{before.state_id}.Holds smFinal pmFinal:=by unfold smFinal pmFinal {smf} {pmf};apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide"])
    for name,rec,lst in (("g",g,gl),("x",x,xl),("y",y,yl)):
      lines.extend([f" have h{name}:{rec.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {rec.sm_tid}) {lst} 1 {F} {S} at h{name}",f" have h{name}V:smFinal {rec.sm_tid}=allGatherPrimDimN 1 4 0 {lst}:=by simpa only [List.length_cons,List.length_nil] using h{name}.full_value"])
      for r in range(4):
        lines.append(f" have h{name}S{r}:(pmFinal {rec.pm_tids[r]}).shape={S}:=h{name}.shard_shapes _ (by simp)")
      for r in range(4):
        lines.append(f" have h{name}C{r}:chunkPrimDimN 1 4 {r} (smFinal {rec.sm_tid})=pmFinal {rec.pm_tids[r]}:=by rw [h{name}V];simpa only [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_1_8_8_g232 "+" ".join(f"(pmFinal {t})" for t in rec.pm_tids)+f" {r} h{name}S0 h{name}S1 h{name}S2 h{name}S3 (by native_decide))")
    lines.extend([f" have hSmF:={hs[0]} smStore",f" have hSmS:={hs[1]} smStore",f" change smFinal {ofst.sm_tid}=batchedMatmul (smFinal {g.sm_tid}) (transpose2d (smFinal {y.sm_tid})) at hSmF",f" change smFinal {osnd.sm_tid}=batchedMatmul (transpose2d (smFinal {x.sm_tid})) (smFinal {g.sm_tid}) at hSmS"])
    for r,n in enumerate(pms):
      lines.extend([f" have hPmF{r}:={hp[0][r]} pmStore",f" have hPmS{r}:={hp[1][r]} pmStore",f" change pmFinal {ofst.pm_tids[r]}=batchedMatmul (pmFinal {g.pm_tids[r]}) (transpose2d (pmFinal {y.pm_tids[r]})) at hPmF{r}",f" change pmFinal {osnd.pm_tids[r]}=batchedMatmul (transpose2d (pmFinal {x.pm_tids[r]})) (pmFinal {g.pm_tids[r]}) at hPmS{r}",f" have hFS{r}:(pmFinal {ofst.pm_tids[r]}).shape={S}:=by rw [hPmF{r}];exact fw_matmul_shape_1_1_8_8 _ _ hgS{r} (transpose2d_shape_1_1_8_8 _ hyS{r})",f" have hSS{r}:(pmFinal {osnd.pm_tids[r]}).shape={S}:=by rw [hPmS{r}];exact fw_matmul_shape_1_1_8_8 _ _ (transpose2d_shape_1_1_8_8 _ hxS{r}) hgS{r}"])
    lines.extend([f" have hFC:={fst.lean_theorem} (smFinal {g.sm_tid}) (smFinal {y.sm_tid}) hg.full_shape hy.full_shape",f" have hFV:smFinal {ofst.sm_tid}=allGatherPrimDimN 1 4 0 {fl}:=by rw [hSmF,hFC,"+", ".join(f"hgC{r},hyC{r}" for r in range(4))+","+", ".join(f"←hPmF{r}" for r in range(4))+"]",f" have hSC:={snd.lean_theorem} (smFinal {x.sm_tid}) "+" ".join(f"(pmFinal {t})" for t in g.pm_tids)+" hx.full_shape "+" ".join(f"hgS{r}" for r in range(4)),f" have hSV:smFinal {osnd.sm_tid}=allGatherPrimDimN 1 4 0 {sl}:=by rw [hSmS,hgV,hSC,"+", ".join(f"hxC{r}" for r in range(4))+","+", ".join(f"←hPmS{r}" for r in range(4))+"]"])
    for tag,out,lst,shapes,smhyp in (("F",ofst,fl,"hFS","hSmF"),("S",osnd,sl,"hSS","hSmS")):
      lines.extend([f" have h{tag}VL:smFinal {out.sm_tid}=allGatherPrimDimN 1 {lst}.length 0 {lst}:=by simpa only [List.length_cons,List.length_nil] using h{tag}V",f" have h{tag}Full:(smFinal {out.sm_tid}).shape={F}:=by rw [{smhyp}];exact fw_matmul_shape_1_4_8_8 _ _ "+("hg.full_shape (transpose2d_shape_1_4_8_8 _ hy.full_shape)" if tag=="F" else "(transpose2d_shape_1_4_8_8 _ hx.full_shape) hg.full_shape"),f" have h{tag}Shapes:∀ z∈{lst},z.shape={S}:=by simp only [List.forall_mem_cons];exact ⟨"+", ".join(f"{shapes}{r}" for r in range(4))+",List.forall_mem_nil _⟩",f" have hout{tag}:{out.fact_id}.Holds smFinal pmFinal:=by exact {{full_value:=h{tag}VL,full_shape:=h{tag}Full,shards_nonempty:=List.cons_ne_nil _ _,gather_dim_lt:=by native_decide,shard_shapes:=h{tag}Shapes,shape_contract:=by simp only [List.map,List.length_cons,List.length_nil];native_decide}}"])
    lines.extend([" intro fact hfact",f" have hc:fact∈[{ofst.fact_id},{osnd.fact_id}]++{before.state_id}.facts:=by exact (show {after.state_id}.facts⊆[{ofst.fact_id},{osnd.fact_id}]++{before.state_id}.facts by native_decide) hfact"," simp only [List.mem_append] at hc"," rcases hc with fresh|old"," · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with rfl|rfl","   · exact houtF","   · exact houtS"," · exact hframe fact old","",f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f" smNodes:={smn}",f" pmNodes:={pmn}",f" sound:=by intro smStore pmStore hstate;exact {segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)
