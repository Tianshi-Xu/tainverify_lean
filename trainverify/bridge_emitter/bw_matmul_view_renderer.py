"""Atomic BW_matmul paired projections plus joined BW_view renderer."""
from __future__ import annotations


def render_closed_bw_matmul_view_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import KRankBWMatmulCertificate, JoinedBWViewCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import KRankBWMatmulCertificate, JoinedBWViewCertificate
    rules={
      "bw-matmul-fst-query-sharded-rank4":(".1","fst-query-sharded","TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4"),
      "bw-matmul-snd-contraction-reduction-rank4":(".2","snd-contraction-reduction","TrainVerify.Denote.bw_matmul_snd_split_dW_g197"),
    };vrule="bw-view-joined";vth="TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view"
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=3: raise ValueError("BW_matmul/view requires three transitions")
    tm={t.transition_id:t for t in relation.transition_specs};ts=tuple(tm[x] for x in seg.transition_ids);mc=[]
    for t in ts:
      if t.rule_id in rules:
        proj,fam,th=rules[t.rule_id]
        if t.lean_theorem!=th: raise ValueError("BW_matmul/view theorem mismatch")
        c=_select_exact_typed_certificate(relation,t,t.rule_id,th,KRankBWMatmulCertificate,lambda x:(tuple(sorted(x.input_facts)),(x.output_fact,)))
        if c.projection!=proj or c.family!=fam: raise ValueError("BW_matmul/view projection mismatch")
        mc.append((t,c))
    vt=next((t for t in ts if t.rule_id==vrule),None)
    if len(mc)!=2 or vt is None or vt.lean_theorem!=vth: raise ValueError("BW_matmul/view typed family mismatch")
    vc=_select_exact_typed_certificate(relation,vt,vrule,vth,JoinedBWViewCertificate,lambda x:((x.input_fact,),(x.output_fact,)))
    cb={c.projection:(t,c) for t,c in mc};ft,fc=cb[".1"];st,sc=cb[".2"]
    if fc.input_facts!=sc.input_facts: raise ValueError("BW_matmul/view input authority mismatch")
    rs={r.source:r for r in chain.relation_facts}
    try:g,x,y=(rs[f] for f in fc.input_facts);of=rs[fc.output_fact];os=rs[sc.output_fact];vi=rs[vc.input_fact];vo=rs[vc.output_fact]
    except KeyError as exc: raise ValueError("BW_matmul/view fact missing") from exc
    states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if not {g.fact_id,x.fact_id,y.fact_id,vi.fact_id}<=set(before.fact_ids) or not {of.fact_id,os.fact_id,vo.fact_id}<=set(after.fact_ids): raise ValueError("BW_matmul/view liveness mismatch")
    if not set(after.fact_ids)<=({of.fact_id,os.fact_id,vo.fact_id}|set(before.fact_ids)): raise ValueError("BW_matmul/view post-state mismatch")
    F=(1,4,8,8);S=(1,4,2,8)
    if any(r.kind!="sharded" or r.gather_dim!=2 or r.full_shape!=F or r.shard_shape!=S or len(r.pm_tids)!=4 for r in (g,x,of)): raise ValueError("BW_matmul/view sharded metadata mismatch")
    if y.kind!="joined" or y.full_shape!=F or y.joined_pm_tid is None or os.kind!="reduction" or os.full_shape!=F or len(os.pm_tids)!=4: raise ValueError("BW_matmul/view joined/reduction metadata mismatch")
    if vi.kind!="joined" or vo.kind!="joined" or vi.full_shape!=(1,8,4,8) or vo.full_shape!=(1,8,32): raise ValueError("BW_matmul/view view metadata mismatch")
    if ft.sm_node_indices!=st.sm_node_indices or ft.pm_node_indices!=st.pm_node_indices or len(ft.sm_node_indices)!=1 or len(ft.pm_node_indices)!=4: raise ValueError("BW_matmul/view shared footprint mismatch")
    ss,se=seg.sm_range;ps,pe=seg.pm_range;mi=ft.sm_node_indices[0];pis=ft.pm_node_indices
    if set(ft.sm_node_indices)|set(vt.sm_node_indices)!=set(range(ss,se)) or not (set(ft.pm_node_indices)|set(vt.pm_node_indices))<=set(range(ps,pe)): raise ValueError("BW_matmul/view frame coverage mismatch")
    mn=ir.sm_nodes[mi];pms=tuple(ir.pm_nodes[i] for i in pis);vnS=ir.sm_nodes[vt.sm_node_indices[0]];vnP=ir.pm_nodes[vt.pm_node_indices[0]]
    if tuple(mn.ins)!=(g.sm_tid,x.sm_tid,y.sm_tid) or tuple(mn.outs)!=(of.sm_tid,os.sm_tid): raise ValueError("BW_matmul/view SM roles mismatch")
    if tuple(tuple(n.ins) for n in pms)!=tuple((g.pm_tids[r],x.pm_tids[r],y.joined_pm_tid) for r in range(4)) or tuple(tuple(n.outs) for n in pms)!=tuple((of.pm_tids[r],os.pm_tids[r]) for r in range(4)): raise ValueError("BW_matmul/view PM roles mismatch")
    if any(n.op!="BW_matmul" or n.params or len(n.outs)!=2 for n in (mn,*pms)): raise ValueError("BW_matmul/view matmul syntax mismatch")
    if vnS.op!="BW_view" or vnP.op!="BW_view" or vnS.ins[0]!=vi.sm_tid or vnP.ins[0]!=vi.joined_pm_tid or vnS.outs!=[vo.sm_tid] or vnP.outs!=[vo.joined_pm_tid] or tuple(vnS.params)!=(1,8,32) or tuple(vnP.params)!=(1,8,32): raise ValueError("BW_matmul/view view syntax mismatch")
    semantic_pm=set(pis)|set(vt.pm_node_indices)
    for i in set(range(ps,pe))-semantic_pm:
      n=ir.pm_nodes[i]
      if n.op!="BW_view" or n.ins[0]!=vi.joined_pm_tid or n.outs!=[vo.joined_pm_tid] or tuple(n.params)!=(1,8,32): raise ValueError("BW_matmul/view frame-only view mismatch")
    smframe=list(ir.sm_nodes[ss:se]);pmframe=list(ir.pm_nodes[ps:pe]);smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[f"private def {smn}:List NodeDecl:=[{', '.join(_node_text(n) for n in smframe)}]",f"private def {pmn}:List NodeDecl:=[{', '.join(_node_text(n) for n in pmframe)}]",f"private def {smf}(s:Store):Store:={smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"private def {pmf}(s:Store):Store:={pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
    def helper(name,graph,initial,fn,nn,frame,pos,node,kind,slot=0):
      final=f"({fn} {initial})";out=node.outs[slot]
      if kind=="mat": expr=f"(bw_matmul ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){'.1' if slot==0 else '.2'}";lemma="applyNode_bw_matmul_fst_out" if slot==0 else "applyNode_bw_matmul_snd_out";apply=f"exact {lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)";ins=tuple(node.ins)
      else: expr=f"fw_view [1, 8, 32] ({{store}} {node.ins[0]})";apply=f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} [8, 32] {node.ins[0]} {node.ins[1]} {out}";ins=(node.ins[0],)
      th=f"{segment_id}_{name}";lines.extend([f"private theorem {th}({initial}:Store):{final} {out}={expr.format(store=final)}:=by",f"  have hfinal:{final}={nn}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {fn};rfl"])
      h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=out,input_tids=ins,written_tids={u for n in frame for u in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed,applyNodeRingAttn]",apply]);lines.extend(z[2:] if z.startswith("  ") else z for z in h);lines.extend(["  exact hout",""]);return th
    hmS=[helper(f"hMatSm{q}",ir.sm_graph_ref,"smStore",smf,smn,smframe,mi-ss,mn,"mat",q) for q in range(2)];hmP=[[helper(f"hMatPm{q}_{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,i-ps,n,"mat",q) for r,(i,n) in enumerate(zip(pis,pms))] for q in range(2)];hvS=helper("hViewSm",ir.sm_graph_ref,"smStore",smf,smn,smframe,vt.sm_node_indices[0]-ss,vnS,"view");hvP=helper("hViewPm",ir.pm_graph_ref,"pmStore",pmf,pmn,pmframe,vt.pm_node_indices[0]-ps,vnP,"view")
    def vals(r):return "["+", ".join(f"pmFinal {u}" for u in r.pm_tids)+"]"
    gl,xl,fl,sl=map(vals,(g,x,of,os));FF="[1, 4, 8, 8]";SS="[1, 4, 2, 8]"
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f" let smFinal:={smf} smStore",f" let pmFinal:={pmf} pmStore",f" have hframe:{before.state_id}.Holds smFinal pmFinal:=by unfold smFinal pmFinal {smf} {pmf};apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide"])
    for name,r,lst in (("g",g,gl),("x",x,xl)):
      lines.extend([f" have h{name}:{r.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {r.sm_tid}) {lst} 2 {FF} {SS} at h{name}",f" have h{name}V:smFinal {r.sm_tid}=allGatherPrimDimN 2 4 0 {lst}:=by simpa only [List.length_cons,List.length_nil] using h{name}.full_value"])
      for q in range(4):lines.append(f" have h{name}S{q}:(pmFinal {r.pm_tids[q]}).shape={SS}:=h{name}.shard_shapes _ (by simp)")
    lines.extend([f" have hy:{y.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change smFinal {y.sm_tid}=pmFinal {y.joined_pm_tid}∧(smFinal {y.sm_tid}).shape={FF}∧(pmFinal {y.joined_pm_tid}).shape={FF} at hy",f" have hvi:{vi.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" have hVF:={hvS} smStore",f" have hVP:={hvP} pmStore",f" change smFinal {vo.sm_tid}=fw_view [1,8,32] (smFinal {vi.sm_tid}) at hVF",f" change pmFinal {vo.joined_pm_tid}=fw_view [1,8,32] (pmFinal {vi.joined_pm_tid}) at hVP",f" have houtV:{vo.fact_id}.Holds smFinal pmFinal:=by change smFinal {vo.sm_tid}=pmFinal {vo.joined_pm_tid}∧_∧_;rw [hVF,hVP];exact JoinedRel.fw_view [1,8,32] [1,8,4,8] hvi"])
    lines.extend([f" have hMF:={hmS[0]} smStore",f" have hMS:={hmS[1]} smStore",f" change smFinal {of.sm_tid}=batchedMatmul (smFinal {g.sm_tid}) (transpose2d (smFinal {y.sm_tid})) at hMF",f" change smFinal {os.sm_tid}=batchedMatmul (transpose2d (smFinal {x.sm_tid})) (smFinal {g.sm_tid}) at hMS"])
    for r in range(4):lines.extend([f" have hPF{r}:={hmP[0][r]} pmStore",f" have hPS{r}:={hmP[1][r]} pmStore",f" change pmFinal {of.pm_tids[r]}=batchedMatmul (pmFinal {g.pm_tids[r]}) (transpose2d (pmFinal {y.joined_pm_tid})) at hPF{r}",f" change pmFinal {os.pm_tids[r]}=batchedMatmul (transpose2d (pmFinal {x.pm_tids[r]})) (pmFinal {g.pm_tids[r]}) at hPS{r}",f" have hFS{r}:(pmFinal {of.pm_tids[r]}).shape={SS}:=by rw [hPF{r}];exact fw_matmul_rank4_shape _ _ 1 4 2 8 8 hgS{r} (transpose2d_shape_1_4_8_8 _ hy.2.2)",f" have hRS{r}:(pmFinal {os.pm_tids[r]}).shape={FF}:=by rw [hPS{r}];exact fw_matmul_rank4_shape _ _ 1 4 8 2 8 (transpose2d_shape_1_4_2_8 _ hxS{r}) hgS{r}"])
    lines.extend([f" have hyT:transpose2d (smFinal {y.sm_tid})=transpose2d (pmFinal {y.joined_pm_tid})∧(transpose2d (smFinal {y.sm_tid})).shape={FF}∧(transpose2d (pmFinal {y.joined_pm_tid})).shape={FF}:=⟨congrArg transpose2d hy.1,transpose2d_shape_1_4_8_8 _ hy.2.1,transpose2d_shape_1_4_8_8 _ hy.2.2⟩",f" have hFT:=TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4 (K:=4) (b:=1) (h:=4) (q:=2) (k:=8) (m:=8) hg hyT (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by simp only [List.length_cons,List.length_nil])",f" have hFL:{of.fact_id}.Holds smFinal pmFinal:=by change ShardedRel (smFinal {of.sm_tid}) {fl} 2 {FF} {SS};rw [hMF,"+", ".join(f"hPF{r}" for r in range(4))+"];simpa only [List.map,List.length_cons,List.length_nil] using hFT",f" have hRC:={sc.lean_theorem} "+" ".join(f"(pmFinal {u})" for u in x.pm_tids+g.pm_tids)+" "+" ".join(f"hxS{r}" for r in range(4))+" "+" ".join(f"hgS{r}" for r in range(4)),f" have hRV:smFinal {os.sm_tid}=allReducePrim 4 0 {sl}:=by rw [hMS,hxV,hgV,hRC,"+", ".join(f"←hPS{r}" for r in range(4))+"]",f" have hRVL:smFinal {os.sm_tid}=allReducePrim {sl}.length 0 {sl}:=by simpa only [List.length_cons,List.length_nil] using hRV",f" have hRFull:(smFinal {os.sm_tid}).shape={FF}:=by rw [hMS];exact fw_matmul_rank4_shape _ _ 1 4 8 8 8 (transpose2d_shape_1_4_8_8 _ hx.full_shape) hg.full_shape",f" have hRShapes:∀z∈{sl},z.shape={FF}:=by simp only [List.forall_mem_cons];exact ⟨"+", ".join(f"hRS{r}" for r in range(4))+",List.forall_mem_nil _⟩",f" have houtR:{os.fact_id}.Holds smFinal pmFinal:=by exact {{full_value:=hRVL,full_shape:=hRFull,contributions_nonempty:=List.cons_ne_nil _ _,contribution_shapes:=hRShapes,reduced_shape:=by simp only [List.map];rw [←hRVL];exact hRFull}}"])
    lines.extend([" intro fact hfact",f" have hc:fact∈[{of.fact_id},{os.fact_id},{vo.fact_id}]++{before.state_id}.facts:=by exact (show {after.state_id}.facts⊆[{of.fact_id},{os.fact_id},{vo.fact_id}]++{before.state_id}.facts by native_decide) hfact"," simp only [List.mem_append] at hc"," rcases hc with fresh|old"," · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with rfl|rfl|rfl","   · exact hFL","   · exact houtR","   · exact houtV"," · exact hframe fact old","",f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f" smNodes:={smn}",f" pmNodes:={pmn}",f" sound:=by intro smStore pmStore h;exact {segment_id}_sound smStore pmStore h",""])
    return "\n".join(lines)
