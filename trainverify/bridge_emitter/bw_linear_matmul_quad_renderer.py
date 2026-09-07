"""Atomic inverse-axis renderer for dual BW_linear plus paired BW_matmul."""
from __future__ import annotations


def render_closed_bw_linear_matmul_quad_segment(ir,relation,segment_id):
 try:
  from .composer import _node_text,_render_mixed_final_value,_select_exact_typed_certificate
  from .relation_compiler import KRankBWLinearDxCertificate,KRankBWLinearDwReductionCertificate,KRankBWMatmulCertificate
 except ImportError:
  from composer import _node_text,_render_mixed_final_value,_select_exact_typed_certificate
  from relation_compiler import KRankBWLinearDxCertificate,KRankBWLinearDwReductionCertificate,KRankBWMatmulCertificate
 lr="bw-linear-dx-sequence-sharded-k-rank";dr="bw-linear-dw-sequence-reduction-rank4";mr="bw-matmul-batch-sharded-rank4";lth="TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3";dth="TrainVerify.Denote.bw_linear_dw_dp_split_dim1_4_1_2_32_g170";mths={".1":"TrainVerify.Denote.bw_matmul_fst_split_dim1_4_1_4_8_8",".2":"TrainVerify.Denote.bw_matmul_snd_split_batchdim1_1_4_8_8"}
 chain=relation.dependent_chain_plan;seg=next((z for z in chain.segments if z.segment_id==segment_id),None)
 if seg is None or len(seg.transition_ids)!=4: raise ValueError("dual BW_linear/matmul component requires four transitions")
 by={t.transition_id:t for t in relation.transition_specs};ts=tuple(by[x] for x in seg.transition_ids);lt=next((t for t in ts if t.rule_id==lr),None);dt=next((t for t in ts if t.rule_id==dr),None);mts=tuple(t for t in ts if t.rule_id==mr)
 if lt is None or dt is None or len(mts)!=2 or lt.lean_theorem!=lth or dt.lean_theorem!=dth: raise ValueError("dual BW_linear/matmul typed family mismatch")
 lc=_select_exact_typed_certificate(relation,lt,lr,lth,KRankBWLinearDxCertificate,lambda c:(tuple(sorted(c.input_facts)),(c.output_fact,)))
 dc=_select_exact_typed_certificate(relation,dt,dr,dth,KRankBWLinearDwReductionCertificate,lambda c:(tuple(sorted((c.gradient_fact,c.activation_fact,c.weight_fact))),(c.output_fact,)))
 if set((dc.gradient_fact,dc.activation_fact,dc.weight_fact))!=set(lc.input_facts): raise ValueError("dual BW_linear input authority disagrees")
 mcs=[]
 for t in mts:
  c=_select_exact_typed_certificate(relation,t,mr,t.lean_theorem,KRankBWMatmulCertificate,lambda x:(tuple(sorted(x.input_facts)),(x.output_fact,)))
  if c.projection not in mths or t.lean_theorem!=mths[c.projection] or c.family!="batch-sharded": raise ValueError("BW_matmul projection/theorem mismatch")
  mcs.append(c)
 mc={c.projection:c for c in mcs};mf,ms=mc[".1"],mc[".2"]
 if mf.input_facts!=ms.input_facts: raise ValueError("BW_matmul projections do not share inputs")
 rec={r.source:r for r in chain.relation_facts}
 try:lg,lx,lw=(rec[f] for f in lc.input_facts);lo=rec[lc.output_fact];ldwo=rec[dc.output_fact];mg,mx,my=(rec[f] for f in mf.input_facts);mfo=rec[mf.output_fact];mso=rec[ms.output_fact]
 except KeyError as exc: raise ValueError("BW_linear/matmul fact missing") from exc
 states={z.state_id:z for z in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
 if not {lg.fact_id,lx.fact_id,lw.fact_id,mg.fact_id,mx.fact_id,my.fact_id}<=set(before.fact_ids) or not {lo.fact_id,ldwo.fact_id,mfo.fact_id,mso.fact_id}<=set(after.fact_ids): raise ValueError("dual BW_linear/matmul facts are not live")
 if any(r.kind!="sharded" or r.gather_dim!=1 for r in (lg,lx,lo,mg,mx,my,mfo,mso)) or lw.kind!="sharded" or ldwo.kind!="reduction": raise ValueError("dual BW_linear/matmul layouts mismatch")
 if (lg.full_shape,lx.full_shape,lo.full_shape)!=( (1,8,32),)*3 or (lg.shard_shape,lx.shard_shape,lo.shard_shape)!=((1,2,32),)*3 or lw.full_shape!=(32,32) or ldwo.full_shape!=(32,32): raise ValueError("dual BW_linear shapes mismatch")
 if any(r.full_shape!=(1,4,8,8) or r.shard_shape!=(1,1,8,8) for r in (mg,mx,my,mfo,mso)): raise ValueError("BW_matmul batch shapes mismatch")
 if lc.rank_count!=4 or dc.rank_count!=4 or dc.shard_dim!=1 or len(ldwo.pm_tids)!=4 or mf.rank_count!=4 or ms.rank_count!=4: raise ValueError("dual BW_linear/matmul rank mismatch")
 ss,se=seg.sm_range;ps,pe=seg.pm_range
 if (dt.sm_node_indices!=lt.sm_node_indices or dt.pm_node_indices!=lt.pm_node_indices
     or dc.sm_step_id!=f"sm:{lt.sm_node_indices[0]}:1"
     or dc.pm_step_ids!=tuple(f"pm:{i}:1" for i in lt.pm_node_indices)):
  raise ValueError("BW_linear dW shared-writer footprint mismatch")
 if (any(t.sm_node_indices!=mts[0].sm_node_indices or t.pm_node_indices!=mts[0].pm_node_indices for t in mts)
     or set(lt.sm_node_indices)|set(mts[0].sm_node_indices)!=set(range(ss,se))
     or set(lt.pm_node_indices)|set(mts[0].pm_node_indices)!=set(range(ps,pe))):
  raise ValueError("BW_linear/matmul footprints do not partition frame")
 lnS=ir.sm_nodes[lt.sm_node_indices[0]];lnP=tuple(ir.pm_nodes[i] for i in lt.pm_node_indices);mnS=ir.sm_nodes[mts[0].sm_node_indices[0]];mnP=tuple(ir.pm_nodes[i] for i in mts[0].pm_node_indices);smframe=list(ir.sm_nodes[ss:se]);pmframe=list(ir.pm_nodes[ps:pe])
 if lnS.op!="BW_linear" or tuple(lnS.ins)!=(lg.sm_tid,lx.sm_tid,lw.sm_tid) or tuple(lnS.outs)!=(lo.sm_tid,ldwo.sm_tid) or tuple(n.rank for n in lnP)!=(0,1,2,3) or any(n.op!="BW_linear" or tuple(n.ins)!=(lg.pm_tids[r],lx.pm_tids[r],lw.pm_tids[0]) or tuple(n.outs)!=(lo.pm_tids[r],ldwo.pm_tids[r]) for r,n in enumerate(lnP)): raise ValueError("dual BW_linear writers mismatch")
 if mnS.op!="BW_matmul" or tuple(mnS.ins)!=(mg.sm_tid,mx.sm_tid,my.sm_tid) or tuple(mnS.outs)!=(mfo.sm_tid,mso.sm_tid) or tuple(n.rank for n in mnP)!=(0,1,2,3) or any(n.op!="BW_matmul" or tuple(n.ins)!=(mg.pm_tids[r],mx.pm_tids[r],my.pm_tids[r]) or tuple(n.outs)!=(mfo.pm_tids[r],mso.pm_tids[r]) for r,n in enumerate(mnP)): raise ValueError("BW_matmul writers mismatch")
 smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final";lines=[f"private def {smn}:List NodeDecl:=[{', '.join(_node_text(n) for n in smframe)}]",f"private def {pmn}:List NodeDecl:=[{', '.join(_node_text(n) for n in pmframe)}]",f"@[irreducible] private def {smf}(z:Store):Store:={smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z",f"@[irreducible] private def {pmf}(z:Store):Store:={pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z",""]
 def helper(name,graph,initial,fn,nn,frame,pos,node,kind,slot=0):
  final=f"({fn} {initial})";out=node.outs[slot]
  if kind=="linear": expr=f"(bw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){'.1' if slot==0 else '.2'}";lemma="applyNode_bw_linear_fst_out" if slot==0 else "applyNode_bw_linear_snd_out"
  else: expr=f"(bw_matmul ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){'.1' if slot==0 else '.2'}";lemma="applyNode_bw_matmul_fst_out" if slot==0 else "applyNode_bw_matmul_snd_out"
  th=f"{segment_id}_{name}";lines.extend([f"private theorem {th}({initial}:Store):{final} {out}={expr.format(store=final)}:=by",f"  have hfinal:{final}={nn}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {fn};rfl"])
  apply=f"exact {lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)"
  h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=out,input_tids=tuple(node.ins),written_tids={u for n in frame for u in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]","simp [applyNodeDistributed,applyNodeRingAttn]",apply])
  lines.extend(z[2:] if z.startswith("  ") else z for z in h);lines.extend(["  exact hout",""]);return th
 hlS=helper("hLinearSm",ir.sm_graph_ref,"smStore",smf,smn,smframe,lt.sm_node_indices[0]-ss,lnS,"linear");hlP=[helper(f"hLinearPm{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"linear") for r,(i,n) in enumerate(zip(lt.pm_node_indices,lnP))];hdS=helper("hLinearDwSm",ir.sm_graph_ref,"smStore",smf,smn,smframe,lt.sm_node_indices[0]-ss,lnS,"linear",1);hdP=[helper(f"hLinearDwPm{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"linear",1) for r,(i,n) in enumerate(zip(lt.pm_node_indices,lnP))];hmS=[helper(f"hMatmulSm{q}",ir.sm_graph_ref,"smStore",smf,smn,smframe,mts[0].sm_node_indices[0]-ss,mnS,"matmul",q) for q in (0,1)];hmP=[[helper(f"hMatmulPm{q}_{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"matmul",q) for r,(i,n) in enumerate(zip(mts[0].pm_node_indices,mnP))] for q in (0,1)]
 def lst(r): return "["+", ".join(f"pmFinal {u}" for u in r.pm_tids)+"]"
 lgl,lxl,lol,ldwl,mgl,mxl,myl,mfl,msl=map(lst,(lg,lx,lo,ldwo,mg,mx,my,mfo,mso))
 lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound(smStore pmStore:Store)(hstate:{before.state_id}.Holds smStore pmStore): {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f" let smFinal:={smf} smStore",f" let pmFinal:={pmf} pmStore",f" have hframe:{before.state_id}.Holds smFinal pmFinal:=by unfold smFinal pmFinal {smf} {pmf};apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide"])
 for name,r,l,full,shard in (("lg",lg,lgl,"[1,8,32]","[1,2,32]"),("lx",lx,lxl,"[1,8,32]","[1,2,32]"),("mg",mg,mgl,"[1,4,8,8]","[1,1,8,8]"),("mx",mx,mxl,"[1,4,8,8]","[1,1,8,8]"),("my",my,myl,"[1,4,8,8]","[1,1,8,8]")):
  lines.extend([f" have h{name}:{r.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {r.sm_tid}) {l} 1 {full} {shard} at h{name}",f" have h{name}V:smFinal {r.sm_tid}=allGatherPrimDimN 1 4 0 {l}:=by simpa only [List.length_cons,List.length_nil] using h{name}.full_value"])
 lines.extend([f" have hlw:{lw.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {lw.sm_tid}) [pmFinal {lw.pm_tids[0]}] 0 [32,32] [32,32] at hlw",f" have hlwEq : smFinal {lw.sm_tid} = pmFinal {lw.pm_tids[0]} := by rw [hlw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hlw.shard_shapes _ (by simp)]; native_decide)",f" have hLS:={hlS} smStore",f" change smFinal {lo.sm_tid} = (bw_linear (smFinal {lg.sm_tid}) (smFinal {lx.sm_tid}) (smFinal {lw.sm_tid})).1 at hLS",f" have hDS:={hdS} smStore",f" change smFinal {ldwo.sm_tid} = (bw_linear (smFinal {lg.sm_tid}) (smFinal {lx.sm_tid}) (smFinal {lw.sm_tid})).2 at hDS"])
 for r in range(4): lines.extend([f" have hLP{r}:={hlP[r]} pmStore",f" change pmFinal {lo.pm_tids[r]} = (bw_linear (pmFinal {lg.pm_tids[r]}) (pmFinal {lx.pm_tids[r]}) (pmFinal {lw.pm_tids[0]})).1 at hLP{r}",f" have hDP{r}:={hdP[r]} pmStore",f" change pmFinal {ldwo.pm_tids[r]} = (bw_linear (pmFinal {lg.pm_tids[r]}) (pmFinal {lx.pm_tids[r]}) (pmFinal {lw.pm_tids[0]})).2 at hDP{r}"])
 for q,o in ((0,mfo),(1,mso)):
  lines.extend([f" have hMS{q}:={hmS[q]} smStore",f" change smFinal {o.sm_tid}={'batchedMatmul (smFinal '+str(mg.sm_tid)+') (transpose2d (smFinal '+str(my.sm_tid)+'))' if q==0 else 'batchedMatmul (transpose2d (smFinal '+str(mx.sm_tid)+')) (smFinal '+str(mg.sm_tid)+')'} at hMS{q}"])
  for r in range(4): lines.extend([f" have hMP{q}_{r}:={hmP[q][r]} pmStore",f" change pmFinal {o.pm_tids[r]}={'batchedMatmul (pmFinal '+str(mg.pm_tids[r])+') (transpose2d (pmFinal '+str(my.pm_tids[r])+'))' if q==0 else 'batchedMatmul (transpose2d (pmFinal '+str(mx.pm_tids[r])+')) (pmFinal '+str(mg.pm_tids[r])+')'} at hMP{q}_{r}"])
 # chunk equalities for all sharded inputs
 for name,r,h,l,shape,roundth in (("lx",lx,"hlx",lxl,"[1,2,32]","chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32"),("mg",mg,"hmg",mgl,"[1,1,8,8]","chunk1_gather1_roundtrip_1_1_8_8"),("mx",mx,"hmx",mxl,"[1,1,8,8]","chunk1_gather1_roundtrip_1_1_8_8"),("my",my,"hmy",myl,"[1,1,8,8]","chunk1_gather1_roundtrip_1_1_8_8")):
  for q in range(4):
   if name=="lx": lines.extend([f" have h{name}C{q}:chunkPrimDimN 1 4 {q} (smFinal {r.sm_tid})=pmFinal {r.pm_tids[q]}:=by rw [h{name}V];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using ({roundth} {l} {q} (by omega) (by simp) (by intro z hz;exact h{name}.shard_shapes z hz))"])
   else: lines.extend([f" have h{name}C{q}:chunkPrimDimN 1 4 {q} (smFinal {r.sm_tid})=pmFinal {r.pm_tids[q]}:=by rw [h{name}V];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using ({roundth} "+" ".join(f"(pmFinal {u})" for u in r.pm_tids)+" "+" ".join(f"(h{name}.shard_shapes _ (by simp))" for _ in range(4))+f" {q} (by omega))"])
 lines.extend([f" have hLCraw:={lc.lean_theorem} 4 1 2 32 32 {lgl} {lxl} (smFinal {lx.sm_tid}) (pmFinal {lw.pm_tids[0]}) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hlg.shard_shapes hlx.shard_shapes hlx.full_shape (hlw.shard_shapes _ (by simp))", " have hLC := hLCraw", " simp only [List.zipWith] at hLC", f" have hLOV:smFinal {lo.sm_tid}=allGatherPrimDimN 1 4 0 {lol}:=by rw [hLS,hlgV,hlwEq,hLC];rw ["+", ".join(f"←hLP{r}" for r in range(4))+"]"])
 lines.extend([f" have hDC:={dc.lean_theorem} "+" ".join(f"(pmFinal {u})" for u in lg.pm_tids)+f" (smFinal {lx.sm_tid}) (pmFinal {lw.pm_tids[0]}) "+" ".join(f"(hlg.shard_shapes _ (by simp))" for _ in range(4))+" hlx.full_shape (hlw.shard_shapes _ (by simp))",f" have hDsum:smFinal {ldwo.sm_tid}=tensorSum {ldwl}:=by rw [hDS,hlgV,hlwEq,hDC];rw ["+", ".join(f"hDP{r},←hlxC{r}" for r in range(4))+"]",f" have hDReduce:smFinal {ldwo.sm_tid}=allReducePrim {ldwl}.length 0 {ldwl}:=by rw [hDsum];rfl"])
 # matmul theorem equalities
 lines.extend([f" have hMF:={mf.lean_theorem} (smFinal {mg.sm_tid}) (smFinal {my.sm_tid}) hmg.full_shape hmy.full_shape",f" have hMFV:smFinal {mfo.sm_tid}=allGatherPrimDimN 1 4 0 {mfl}:=by rw [hMS0,hMF];rw ["+", ".join(f"hMP0_{r},←hmgC{r},←hmyC{r}" for r in range(4))+"]",f" have hMS:={ms.lean_theorem} (smFinal {mx.sm_tid}) "+" ".join(f"(pmFinal {u})" for u in mg.pm_tids)+" hmx.full_shape "+" ".join(f"(hmg.shard_shapes _ (by simp))" for _ in range(4)),f" have hMSV:smFinal {mso.sm_tid}=allGatherPrimDimN 1 4 0 {msl}:=by rw [hMS1,hmgV,hMS];rw ["+", ".join(f"hMP1_{r},←hmxC{r}" for r in range(4))+"]"])
 # package three ShardedRel outputs
 for name,o,l,val,full,shard,shape_src in (("LO",lo,lol,"hLOV","[1,8,32]","[1,2,32]","hlx"),("MF",mfo,mfl,"hMFV","[1,4,8,8]","[1,1,8,8]","hmg"),("MS",mso,msl,"hMSV","[1,4,8,8]","[1,1,8,8]","hmg")):
  if name=="LO":
   full_proof="rw [hLS]; exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.full_shape hlw.full_shape"
   piece=lambda r:f"rw [hLP{r}]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))"
  elif name=="MF":
   full_proof="rw [hMS0]; exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ hmg.full_shape (transpose2d_shape_1_4_8_8 _ hmy.full_shape)"
   piece=lambda r:f"rw [hMP0_{r}]; exact fw_matmul_shape_1_1_8_8 _ _ (hmg.shard_shapes _ (by simp)) (transpose2d_shape_1_1_8_8 _ (hmy.shard_shapes _ (by simp)))"
  else:
   full_proof="rw [hMS1]; exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_8 _ hmx.full_shape) hmg.full_shape"
   piece=lambda r:f"rw [hMP1_{r}]; exact fw_matmul_shape_1_1_8_8 _ _ (transpose2d_shape_1_1_8_8 _ (hmx.shard_shapes _ (by simp))) (hmg.shard_shapes _ (by simp))"
  lines.extend([f" have h{name}VL:smFinal {o.sm_tid}=allGatherPrimDimN 1 {l}.length 0 {l}:=by simpa only [List.length_cons,List.length_nil] using {val}",f" have hout{name}:{o.fact_id}.Holds smFinal pmFinal:=by",f"  change ShardedRel (smFinal {o.sm_tid}) {l} 1 {full} {shard}",f"  refine {{full_value:=h{name}VL,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=?_,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}}",f"  · {full_proof}",f"  · intro piece hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h0|h1|h2|h3"])
  for r in range(4): lines.extend(["    · subst piece",f"      {piece(r)}"])
 lines.extend([f" have hDFullShape:(smFinal {ldwo.sm_tid}).shape=[32,32]:=by rw [hDS];exact bw_linear_3d_snd_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.full_shape hlw.full_shape",f" have houtDW:{ldwo.fact_id}.Holds smFinal pmFinal:=by",f"  change ReductionRel (smFinal {ldwo.sm_tid}) {ldwl} [32,32]","  refine {full_value:=hDReduce,full_shape:=hDFullShape,contributions_nonempty:=by simp,contribution_shapes:=?_,reduced_shape:=?_}","  · intro piece hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h0|h1|h2|h3"])
 for r in range(4): lines.extend(["    · subst piece",f"      rw [hDP{r}]",f"      exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))"])
 lines.extend(["  · rw [← hDReduce]","    exact hDFullShape"])
 lines.extend([" intro fact hfact",f" have covered:fact∈[{lo.fact_id},{ldwo.fact_id},{mfo.fact_id},{mso.fact_id}]++{before.state_id}.facts:=by exact (show {after.state_id}.facts⊆[{lo.fact_id},{ldwo.fact_id},{mfo.fact_id},{mso.fact_id}]++{before.state_id}.facts by native_decide) hfact"," simp only [List.mem_append] at covered"," rcases covered with fresh|old"," · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with rfl|rfl|rfl|rfl","   · exact houtLO","   · exact houtDW","   · exact houtMF","   · exact houtMS"," · exact hframe fact old","","set_option maxRecDepth 32768 in",f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f" smNodes:={smn}",f" pmNodes:={pmn}"," sound:=by intro smStore pmStore hstate; have h:= "+f"{segment_id}_sound smStore pmStore hstate; unfold "+smf+" "+pmf+" at h; exact h",""])
 return "\n".join(lines)
