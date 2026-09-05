"""Atomic inverse-order transpose / BW_linear dX / transpose renderer."""
from __future__ import annotations


def render_closed_transpose_linear_transpose_segment(ir, relation, segment_id: str) -> str:
 try:
  from .composer import _node_text,_render_mixed_final_value,_select_exact_typed_certificate,_shape_text
  from .relation_compiler import KRankTransposeRelationCertificate,KRankBWLinearDxCertificate,KRankBWLinearDwReductionCertificate
 except ImportError:
  from composer import _node_text,_render_mixed_final_value,_select_exact_typed_certificate,_shape_text
  from relation_compiler import KRankTransposeRelationCertificate,KRankBWLinearDxCertificate,KRankBWLinearDwReductionCertificate
 lr="bw-linear-dx-sequence-sharded-rank4";lcontracts={
  "TrainVerify.Denote.bw_linear_dx_dp_split_dim1_4_g169":((1,8,32),(1,2,32),(1,8,32),(1,2,32),(32,32),True),
  "TrainVerify.Denote.bw_linear_dx_dp_split_dim1_4_g143":((1,8,32),(1,2,32),(1,8,128),(1,2,128),(32,128),False),
 };tr="transpose-sharded-k-rank"
 tths={"TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4","TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4"}
 chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
 if seg is None or len(seg.transition_ids) not in (1,2,3,4):raise ValueError("sequence-linear requires dX, optional dW, and optional transpose pair")
 tm={t.transition_id:t for t in relation.transition_specs};ts=tuple(tm[x] for x in seg.transition_ids);lt=next((t for t in ts if t.rule_id==lr),None);dt=next((t for t in ts if t.rule_id=="bw-linear-dw-sequence-reduction-rank4"),None);tts=tuple(t for t in ts if t.rule_id==tr)
 lth=lt.lean_theorem if lt is not None else None;lspec=lcontracts.get(lth)
 if (lt is None or lspec is None
     or (len(tts) not in (0,2)) or (len(tts)==2 and {t.lean_theorem for t in tts}!=tths)
     or len(ts)!=1+(1 if dt else 0)+len(tts)):raise ValueError("transpose/linear typed family mismatch")
 lc=_select_exact_typed_certificate(relation,lt,lr,lth,KRankBWLinearDxCertificate,lambda c:(tuple(sorted(c.input_facts)),(c.output_fact,)));tcs=[]
 dc=None if dt is None else _select_exact_typed_certificate(relation,dt,"bw-linear-dw-sequence-reduction-rank4",dt.lean_theorem,KRankBWLinearDwReductionCertificate,lambda c:(tuple(sorted((c.gradient_fact,c.activation_fact,c.weight_fact))),(c.output_fact,)))
 if dc and (dt.lean_theorem not in {"TrainVerify.Denote.bw_linear_dw_dp_split_dim1_4_1_2_32_g170","TrainVerify.Denote.bw_linear_dw_dp_chunk_both_dim1_4_1_8_32_128_g144"} or set((dc.gradient_fact,dc.activation_fact,dc.weight_fact))!=set(lc.input_facts)):raise ValueError("transpose/linear dW authority mismatch")
 for t in tts:tcs.append((t,_select_exact_typed_certificate(relation,t,tr,t.lean_theorem,KRankTransposeRelationCertificate,lambda c:((c.input_fact,),(c.output_fact,)))))
 rs={r.source:r for r in chain.relation_facts}
 try:lg,lx,lw=(rs[f] for f in lc.input_facts);lo=rs[lc.output_fact];ldwo=rs[dc.output_fact] if dc else None;trs=[(t,c,rs[c.input_fact],rs[c.output_fact]) for t,c in tcs]
 except KeyError as exc:raise ValueError("transpose/linear/transpose fact missing") from exc
 states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
 fresh_ids={lo.fact_id,*[o.fact_id for _,_,_,o in trs]}|({ldwo.fact_id} if ldwo else set())
 if not {lg.fact_id,lx.fact_id,lw.fact_id,*[i.fact_id for _,_,i,_ in trs]}<=set(before.fact_ids) or not fresh_ids<=set(after.fact_ids):raise ValueError("transpose/linear/transpose liveness mismatch")
 if not set(after.fact_ids)<=(fresh_ids|set(before.fact_ids)):raise ValueError("transpose/linear/transpose post-state mismatch")
 gfull,gshard,xfull,xshard,wshape,needs_chunks=lspec
 if (lg.kind!="sharded" or lg.gather_dim!=1 or lg.full_shape!=gfull or lg.shard_shape!=gshard
     or lx.kind!="sharded" or lx.gather_dim!=1 or lx.full_shape!=xfull or lx.shard_shape!=xshard
     or lo.kind!="sharded" or lo.gather_dim!=1 or lo.full_shape!=xfull or lo.shard_shape!=xshard
     or lw.kind!="sharded" or lw.gather_dim!=0 or len(lw.pm_tids)!=1
     or lw.full_shape!=wshape or lw.shard_shape!=lw.full_shape
     or (ldwo and (ldwo.kind!="reduction" or ldwo.full_shape!=wshape or len(ldwo.pm_tids)!=4))):raise ValueError("transpose/linear metadata mismatch")
 ss,se=seg.sm_range;ps,pe=seg.pm_range
 sm_owned=tuple(lt.sm_node_indices)+tuple(i for t,_,_,_ in trs for i in t.sm_node_indices)
 pm_owned=tuple(lt.pm_node_indices)+tuple(i for t,_,_,_ in trs for i in t.pm_node_indices)
 sm_range=set(range(ss,se));pm_range=set(range(ps,pe))
 if (len(sm_owned)!=len(set(sm_owned)) or len(pm_owned)!=len(set(pm_owned))
     or not set(sm_owned)<=sm_range or not set(pm_owned)<=pm_range):raise ValueError("transpose/linear/transpose writer/frame partition mismatch")
 sm_frame_only=sm_range-set(sm_owned);pm_frame_only=pm_range-set(pm_owned)
 live_ids=set(before.fact_ids)|set(after.fact_ids);by_id={r.fact_id:r for r in chain.relation_facts}
 live_sm=set();live_pm=set()
 for fid in live_ids:
  record=by_id.get(fid)
  if record is None:continue
  live_sm.add(record.sm_tid);live_pm.update(record.pm_tids)
  if record.joined_pm_tid is not None:live_pm.add(record.joined_pm_tid)
  if record.metadata_tid is not None:live_sm.add(record.metadata_tid);live_pm.add(record.metadata_tid)
 authority={a.fact_id:a for a in chain.authority_facts}
 for fid in live_ids:
  fact=authority.get(fid)
  if fact is None:continue
  if fact.kind=="tensor_shape":(live_sm if fact.side=="sm" else live_pm).add(fact.tid)
  elif fact.kind=="tensor_eq":
   (live_sm if fact.left_side=="sm" else live_pm).add(fact.left_tid)
   (live_sm if fact.right_side=="sm" else live_pm).add(fact.right_tid)
  else:raise ValueError("transpose/linear/transpose unsupported live authority kind")
 if any(set(ir.sm_nodes[i].outs)&live_sm for i in sm_frame_only) or any(set(ir.pm_nodes[i].outs)&live_pm for i in pm_frame_only):raise ValueError("transpose/linear/transpose frame overwrites live authority")
 lnS=ir.sm_nodes[lt.sm_node_indices[0]];lnP=tuple(ir.pm_nodes[i] for i in lt.pm_node_indices)
 if dc and (dt.sm_node_indices!=lt.sm_node_indices or dt.pm_node_indices!=lt.pm_node_indices or dc.sm_step_id!=f"sm:{lt.sm_node_indices[0]}:1" or dc.pm_step_ids!=tuple(f"pm:{i}:1" for i in lt.pm_node_indices)):raise ValueError("transpose/linear dW shared-writer footprint mismatch")
 if tuple(lnS.ins)!=(lg.sm_tid,lx.sm_tid,lw.sm_tid) or lnS.outs[0]!=lo.sm_tid or (ldwo and lnS.outs[1]!=ldwo.sm_tid) or any(tuple(n.ins)!=(lg.pm_tids[r],lx.pm_tids[r],lw.pm_tids[0]) or n.outs[0]!=lo.pm_tids[r] or (ldwo and n.outs[1]!=ldwo.pm_tids[r]) for r,n in enumerate(lnP)):raise ValueError("transpose/linear writers mismatch")
 smframe=list(ir.sm_nodes[ss:se]);pmframe=list(ir.pm_nodes[ps:pe]);smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final";lines=[f"private def {smn}:List NodeDecl:=[{', '.join(_node_text(n) for n in smframe)}]",f"private def {pmn}:List NodeDecl:=[{', '.join(_node_text(n) for n in pmframe)}]",f"@[irreducible] private def {smf}(s:Store):Store:={smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"@[irreducible] private def {pmf}(s:Store):Store:={pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
 def helper(name,graph,initial,fn,nn,frame,pos,node,kind,slot=0):
  final=f"({fn} {initial})";out=node.outs[slot] if kind=="linear" else node.outs[0]
  if kind=="linear":expr=f"(bw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){'.1' if slot==0 else '.2'}";apply=f"exact {'applyNode_bw_linear_fst_out' if slot==0 else 'applyNode_bw_linear_snd_out'} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)";ins=tuple(node.ins)
  else:expr=f"transposeAxes {node.params[0]} {node.params[1]} ({{store}} {node.ins[0]})";apply=f"exact applyNode_bw_transposeAxes_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {out} {node.params[0]} {node.params[1]}";ins=(node.ins[0],)
  th=f"{segment_id}_{name}";lines.extend([f"private theorem {th}({initial}:Store):{final} {out}={expr.format(store=final)}:=by",f"  have hfinal:{final}={nn}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {fn};rfl"]);h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=out,input_tids=ins,written_tids={u for n in frame for u in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]","simp [applyNodeDistributed,applyNodeRingAttn]",apply]);lines.extend(z[2:] if z.startswith("  ") else z for z in h);lines.extend(["  exact hout",""]);return th
 hlS=helper("hLinearSm",ir.sm_graph_ref,"smStore",smf,smn,smframe,lt.sm_node_indices[0]-ss,lnS,"linear");hlP=[helper(f"hLinearPm{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"linear") for r,(i,n) in enumerate(zip(lt.pm_node_indices,lnP))];hdS=helper("hLinearDwSm",ir.sm_graph_ref,"smStore",smf,smn,smframe,lt.sm_node_indices[0]-ss,lnS,"linear",1) if dc else None;hdP=[helper(f"hLinearDwPm{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"linear",1) for r,(i,n) in enumerate(zip(lt.pm_node_indices,lnP))] if dc else [];ths=[]
 for j,(t,c,ri,ro) in enumerate(trs):
  ns=ir.sm_nodes[t.sm_node_indices[0]];np=tuple(ir.pm_nodes[i] for i in t.pm_node_indices);ths.append((t,c,ri,ro,ns,np,helper(f"hTr{j}Sm",ir.sm_graph_ref,"smStore",smf,smn,smframe,t.sm_node_indices[0]-ss,ns,"tr"),[helper(f"hTr{j}Pm{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"tr") for r,(i,n) in enumerate(zip(t.pm_node_indices,np))]))
 def vals(r):return "["+", ".join(f"pmFinal {u}" for u in r.pm_tids)+"]"
 lgl,lxl,lol=map(vals,(lg,lx,lo));ldwl=vals(ldwo) if ldwo else None;gf,gs,xf,xs,wf=map(lambda z:_shape_text(list(z)),(gfull,gshard,xfull,xshard,wshape));lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f" let smFinal:={smf} smStore",f" let pmFinal:={pmf} pmStore",f" have hframe:{before.state_id}.Holds smFinal pmFinal:=by unfold smFinal pmFinal {smf} {pmf};apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide"])
 for name,r,l,fulltxt,shardtxt in (("lg",lg,lgl,gf,gs),("lx",lx,lxl,xf,xs)):lines.extend([f" have h{name}:{r.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {r.sm_tid}) {l} 1 {fulltxt} {shardtxt} at h{name}",f" have h{name}V:smFinal {r.sm_tid}=allGatherPrimDimN 1 4 0 {l}:=by simpa only [List.length_cons,List.length_nil] using h{name}.full_value"])
 lines.extend([f" have hw:{lw.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {lw.sm_tid}) [pmFinal {lw.pm_tids[0]}] 0 {wf} {wf} at hw",f" have hwEq:smFinal {lw.sm_tid}=pmFinal {lw.pm_tids[0]}:=by rw [hw.full_value];exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)];native_decide)",f" have hLS:={hlS} smStore",f" change smFinal {lo.sm_tid}=(bw_linear (smFinal {lg.sm_tid}) (smFinal {lx.sm_tid}) (smFinal {lw.sm_tid})).1 at hLS"])
 if dc:lines.extend([f" have hDS:={hdS} smStore",f" change smFinal {ldwo.sm_tid}=(bw_linear (smFinal {lg.sm_tid}) (smFinal {lx.sm_tid}) (smFinal {lw.sm_tid})).2 at hDS"])
 for r in range(4):
  lines.extend([f" have hLP{r}:={hlP[r]} pmStore",f" change pmFinal {lo.pm_tids[r]}=(bw_linear (pmFinal {lg.pm_tids[r]}) (pmFinal {lx.pm_tids[r]}) (pmFinal {lw.pm_tids[0]})).1 at hLP{r}"])
  if dc:lines.extend([f" have hDP{r}:={hdP[r]} pmStore",f" change pmFinal {ldwo.pm_tids[r]}=(bw_linear (pmFinal {lg.pm_tids[r]}) (pmFinal {lx.pm_tids[r]}) (pmFinal {lw.pm_tids[0]})).2 at hDP{r}"])
  if needs_chunks:lines.append(f" have hxC{r}:chunkPrimDimN 1 4 {r} (smFinal {lx.sm_tid})=pmFinal {lx.pm_tids[r]}:=by rw [hlxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 {lxl} {r} (by omega) (by simp) hlx.shard_shapes)")
 if needs_chunks:
  hcall=f"{lc.lean_theorem} "+" ".join(f"(pmFinal {u})" for u in lg.pm_tids)+f" (smFinal {lx.sm_tid}) (pmFinal {lw.pm_tids[0]}) "+" ".join("(hlg.shard_shapes _ (by simp))" for _ in range(4))+" hlx.full_shape (hw.shard_shapes _ (by simp))"
  local_rw=", ".join(f"hLP{r},←hxC{r}" for r in range(4))
 else:
  hcall=f"{lc.lean_theorem} "+" ".join(f"(pmFinal {u})" for u in lg.pm_tids)+f" (smFinal {lx.sm_tid}) "+" ".join(f"(pmFinal {u})" for u in lx.pm_tids)+f" (pmFinal {lw.pm_tids[0]}) "+" ".join("(hlg.shard_shapes _ (by simp))" for _ in range(4))+" hlx.full_shape "+" ".join("(hlx.shard_shapes _ (by simp))" for _ in range(4))+" (hw.shard_shapes _ (by simp))"
  local_rw=", ".join(f"←hLP{r}" for r in range(4))
 lines.extend([f" have hLC:={hcall}",f" have hLV:smFinal {lo.sm_tid}=allGatherPrimDimN 1 4 0 {lol}:=by rw [hLS,hlgV,hwEq,hLC];rw [{local_rw}]",f" have hLVL:smFinal {lo.sm_tid}=allGatherPrimDimN 1 {lol}.length 0 {lol}:=by simpa only [List.length_cons,List.length_nil] using hLV",f" have hLFull:(smFinal {lo.sm_tid}).shape={xf}:=by rw [hLS];exact bw_linear_3d_fst_shape {gfull[0]} {gfull[1]} {gfull[2]} {xfull[2]} _ _ _ hlg.full_shape hlx.full_shape hw.full_shape"])
 for r in range(4):lines.append(f" have hLShape{r}:(pmFinal {lo.pm_tids[r]}).shape={xs}:=by rw [hLP{r}];exact bw_linear_3d_fst_shape {gshard[0]} {gshard[1]} {gshard[2]} {xshard[2]} _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))")
 lines.extend([f" have hLShapes:∀z∈{lol},z.shape={xs}:=by simp only [List.forall_mem_cons];exact ⟨hLShape0,hLShape1,hLShape2,hLShape3,List.forall_mem_nil _⟩",f" have houtL:{lo.fact_id}.Holds smFinal pmFinal:=by exact {{full_value:=hLVL,full_shape:=hLFull,shards_nonempty:=List.cons_ne_nil _ _,gather_dim_lt:=by native_decide,shard_shapes:=hLShapes,shape_contract:=by simp only [List.map,List.length_cons,List.length_nil];native_decide}}"])
 if dc:
  if dc.lean_theorem.endswith("g170"):
   dcall=dc.lean_theorem+" "+" ".join(f"(pmFinal {u})" for u in lg.pm_tids)+f" (smFinal {lx.sm_tid}) (pmFinal {lw.pm_tids[0]}) "+" ".join("(hlg.shard_shapes _ (by simp))" for _ in range(4))+" hlx.full_shape (hw.shard_shapes _ (by simp))"
   drewrite="hDS,hlgV,hwEq,hDC,"+", ".join(f"hDP{r},←hxC{r}" for r in range(4))
  else:
   for r in range(4):
    lines.append(f" have hgC{r}:chunkPrimDimN 1 4 {r} (smFinal {lg.sm_tid})=pmFinal {lg.pm_tids[r]}:=by rw [hlgV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 {lgl} {r} (by omega) (by simp) hlg.shard_shapes)")
    lines.append(f" have hxC{r}:chunkPrimDimN 1 4 {r} (smFinal {lx.sm_tid})=pmFinal {lx.pm_tids[r]}:=by rw [hlxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_128 {lxl} {r} (by omega) (by simp) hlx.shard_shapes)")
   dcall=f"{dc.lean_theorem} (smFinal {lg.sm_tid}) (smFinal {lx.sm_tid}) (pmFinal {lw.pm_tids[0]}) hlg.full_shape hlx.full_shape (hw.shard_shapes _ (by simp))"
   drewrite="hDS,hwEq,hDC,"+", ".join(f"hDP{r},←hgC{r},←hxC{r}" for r in range(4))
  lines.extend([f" have hDC:={dcall}",f" have hDsum:smFinal {ldwo.sm_tid}=tensorSum {ldwl}:=by rw [{drewrite}]",f" have hDReduce:smFinal {ldwo.sm_tid}=allReducePrim {ldwl}.length 0 {ldwl}:=by rw [hDsum];rfl",f" have hDFull:(smFinal {ldwo.sm_tid}).shape={wf}:=by rw [hDS];exact bw_linear_3d_snd_shape {gfull[0]} {gfull[1]} {gfull[2]} {xfull[2]} _ _ _ hlg.full_shape hlx.full_shape hw.full_shape"])
  for r in range(4):lines.append(f" have hDShape{r}:(pmFinal {ldwo.pm_tids[r]}).shape={wf}:=by rw [hDP{r}];exact bw_linear_3d_snd_shape {gshard[0]} {gshard[1]} {gshard[2]} {xshard[2]} _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))")
  lines.extend([f" have houtD:{ldwo.fact_id}.Holds smFinal pmFinal:=by",f"  change ReductionRel (smFinal {ldwo.sm_tid}) {ldwl} {wf}","  refine {full_value:=hDReduce,full_shape:=hDFull,contributions_nonempty:=by simp,contribution_shapes:=?_,reduced_shape:=?_}","  · intro z hz; simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with h0|h1|h2|h3","    · subst z;exact hDShape0","    · subst z;exact hDShape1","    · subst z;exact hDShape2","    · subst z;exact hDShape3","  · rw [←hDReduce];exact hDFull"])
 outs=[]
 for j,(t,c,ri,ro,ns,np,hs,hp) in enumerate(ths):
  il,ol=vals(ri),vals(ro);sd=list(ri.shard_shape);sd[ri.gather_dim]=f"{sd[ri.gather_dim]} * {il}.length";sym="["+", ".join(map(str,sd))+"]";lines.extend([f" have hti{j}:{ri.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {ri.sm_tid}) {il} {ri.gather_dim} {sym} {_shape_text(list(ri.shard_shape))} at hti{j}",f" have htS{j}:={hs} smStore",f" change smFinal {ro.sm_tid}=transposeAxes {c.parameters[0]} {c.parameters[1]} (smFinal {ri.sm_tid}) at htS{j}"])
  for r in range(4):lines.extend([f" have htP{j}_{r}:={hp[r]} pmStore",f" change pmFinal {ro.pm_tids[r]}=transposeAxes {c.parameters[0]} {c.parameters[1]} (pmFinal {ri.pm_tids[r]}) at htP{j}_{r}"])
  lines.extend([f" have htRaw{j}:={c.lean_theorem} hti{j}",f" have houtT{j}:{ro.fact_id}.Holds smFinal pmFinal:=by change ShardedRel (smFinal {ro.sm_tid}) {ol} {ro.gather_dim} {_shape_text(list(ro.full_shape))} {_shape_text(list(ro.shard_shape))};rw [htS{j},"+", ".join(f"htP{j}_{r}" for r in range(4))+f"];simpa using htRaw{j}"]);outs.append(f"houtT{j}")
 fresh=[lo.fact_id]+([ldwo.fact_id] if ldwo else [])+[ro.fact_id for _,_,_,ro,_,_,_,_ in ths];proofs=["houtL"]+(["houtD"] if ldwo else [])+outs;lines.extend([" intro fact hfact",f" have hc:fact∈[{','.join(fresh)}]++{before.state_id}.facts:=by exact (show {after.state_id}.facts⊆[{','.join(fresh)}]++{before.state_id}.facts by native_decide) hfact"," simp only [List.mem_append] at hc"," rcases hc with fresh|old",f" · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with "+"|".join("rfl" for _ in fresh),*(f"   · exact {x}" for x in proofs)," · exact hframe fact old","",f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f" smNodes:={smn}",f" pmNodes:={pmn}",f" sound:=by intro a b h;have z:={segment_id}_sound a b h;unfold {smf} {pmf} at z;exact z",""])
 return "\n".join(lines)
