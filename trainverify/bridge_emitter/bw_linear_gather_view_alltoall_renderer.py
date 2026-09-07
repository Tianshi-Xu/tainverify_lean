"""Atomic BW_linear dX / AllGather / joined BW_view / AllToAll renderer."""
from __future__ import annotations


def render_closed_bw_linear_gather_view_alltoall_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import (KRankBWLinearDxCertificate, KRankBWLinearDwColumnShardedCertificate,
            KRankAllGatherReconstructionCertificate, JoinedBWViewCertificate, KRankAllToAllRelationCertificate)
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import (KRankBWLinearDxCertificate, KRankBWLinearDwColumnShardedCertificate,
            KRankAllGatherReconstructionCertificate, JoinedBWViewCertificate, KRankAllToAllRelationCertificate)
    try:
        from .bw_linear_dx_column_renderer import column_dx_shape_spec, render_dynamic_column_commute, validate_column_dw_authority
        from .bw_linear_column_dual_renderer import render_dynamic_column_dw_commute
    except ImportError:
        from bw_linear_dx_column_renderer import column_dx_shape_spec, render_dynamic_column_commute, validate_column_dw_authority
        from bw_linear_column_dual_renderer import render_dynamic_column_dw_commute
    rules=("bw-linear-dx-column-sharded-k-rank","allgather-reconstruction-k-rank","bw-view-joined","alltoall-k-rank-layout-transport")
    dual_rules=("bw-linear-dx-column-sharded-k-rank","bw-linear-dw-input-column-sharded-k-rank","allgather-reconstruction-k-rank","bw-view-joined","alltoall-k-rank-layout-transport")
    thL="TrainVerify.Denote.bw_linear_dx_column_allGather_rank3"
    thG="TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"
    thV="TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view"
    thA="TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    chain=relation.dependent_chain_plan; seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids) not in (4,5): raise ValueError("mixed backward collective requires four transitions and optional shared dW")
    byid={t.transition_id:t for t in relation.transition_specs}; ts=tuple(byid[x] for x in seg.transition_ids)
    family=tuple(t.rule_id for t in ts)
    if family not in (rules,dual_rules): raise ValueError("mixed backward collective typed family mismatch")
    D=next((t for t in ts if t.rule_id=="bw-linear-dw-input-column-sharded-k-rank"),None)
    L=next(t for t in ts if t.rule_id==rules[0]);G=next(t for t in ts if t.rule_id==rules[1]);V=next(t for t in ts if t.rule_id==rules[2]);A=next(t for t in ts if t.rule_id==rules[3])
    if (L.lean_theorem,G.lean_theorem,V.lean_theorem,A.lean_theorem)!=(thL,thG,thV,thA): raise ValueError("mixed backward collective theorem identity mismatch")
    cL=_select_exact_typed_certificate(relation,L,rules[0],thL,KRankBWLinearDxCertificate,lambda c:(tuple(sorted(c.input_facts)),(c.output_fact,)))
    cD=None if D is None else _select_exact_typed_certificate(relation,D,dual_rules[1],D.lean_theorem,KRankBWLinearDwColumnShardedCertificate,lambda c:(tuple(sorted((c.gradient_fact,c.activation_fact,c.weight_fact))),(c.output_fact,)))
    if cD and D.lean_theorem!="TrainVerify.Denote.bw_linear_dw_column_allGather_rank3": raise ValueError("mixed backward dW theorem identity mismatch")
    cG=_select_exact_typed_certificate(relation,G,rules[1],thG,KRankAllGatherReconstructionCertificate,lambda c:((c.input_fact,),(c.output_fact,)))
    cV=_select_exact_typed_certificate(relation,V,rules[2],thV,JoinedBWViewCertificate,lambda c:((c.input_fact,),(c.output_fact,)))
    cA=_select_exact_typed_certificate(relation,A,rules[3],thA,KRankAllToAllRelationCertificate,lambda c:((c.input_fact,),(c.output_fact,)))
    rec={r.source:r for r in chain.relation_facts}
    grad,act,weight=(rec[x] for x in cL.input_facts); outL=rec[cL.output_fact]
    outD=rec[cD.output_fact] if cD else None
    if cD and (cD.gradient_fact,cD.activation_fact,cD.weight_fact)!=cL.input_facts: raise ValueError("mixed backward shared dX/dW inputs disagree")
    inG,outG=rec[cG.input_fact],rec[cG.output_fact]; inV,outV=rec[cV.input_fact],rec[cV.output_fact]; inA,outA=rec[cA.input_fact],rec[cA.output_fact]
    if outL.fact_id!=inA.fact_id or outG.fact_id!=inV.fact_id: raise ValueError("mixed backward internal dependency mismatch")
    states={s.state_id:s for s in chain.states}; before,after=states[seg.pre_state_id],states[seg.post_state_id]
    required={grad.fact_id,act.fact_id,weight.fact_id,inG.fact_id}
    proved={outL.fact_id,outG.fact_id,outA.fact_id,outV.fact_id}|({outD.fact_id} if outD else set())
    required_published={outA.fact_id,outV.fact_id}|({outD.fact_id} if outD else set())
    if not required<=set(before.fact_ids) or not required_published<=set(after.fact_ids): raise ValueError("mixed backward liveness mismatch")
    if not set(after.fact_ids)<=set(before.fact_ids)|proved: raise ValueError("mixed backward publication mismatch")
    k=cL.rank_count
    column_dx_shape_spec(grad,act,weight,outL,k)
    b,s=grad.full_shape[:2]
    if cL.family!="column-sharded" or cL.output_layout!="sharded" or cL.gather_dim!=2:
        raise ValueError("mixed backward column dX certificate layout mismatch")
    if cD:
        column_dx_shape_spec(grad,act,weight,outD,k,dw=True)
    if k!=4 or any(c.rank_count!=k for c in (cG,cA)) or (cD and cD.rank_count!=k) or ir.pm_num_ranks!=k: raise ValueError("mixed backward rank mismatch")
    if (grad.kind!="joined" or act.kind!="sharded" or act.gather_dim!=2 or weight.kind!="sharded" or weight.gather_dim!=1
        or outL.kind!="sharded" or outL.gather_dim!=2 or (outD and (outD.kind!="sharded" or outD.gather_dim!=1 or outD.full_shape!=weight.full_shape or outD.shard_shape!=weight.shard_shape)) or inG.kind!="sharded" or outG.kind!="joined" or outV.kind!="joined"
        or outA.kind!="sharded" or cA.input_gather_dim!=2 or cA.output_gather_dim!=1): raise ValueError("mixed backward metadata mismatch")
    ss,se=seg.sm_range;ps,pe=seg.pm_range;sf=list(ir.sm_nodes[ss:se]);pf=list(ir.pm_nodes[ps:pe])
    if tuple(L.sm_node_indices)!=(se-1,) or tuple(V.sm_node_indices)!=(ss,) or G.sm_node_indices or A.sm_node_indices: raise ValueError("mixed backward SM authority mismatch")
    if len(L.pm_node_indices)!=k or len(G.pm_node_indices)!=1 or len(V.pm_node_indices)!=1 or len(A.pm_node_indices)!=k: raise ValueError("mixed backward PM footprint mismatch")
    if (cL.sm_step_id!=f"sm:{L.sm_node_indices[0]}:0"
            or cL.pm_step_ids!=tuple(f"pm:{i}:0" for i in L.pm_node_indices)
            or not set(L.pm_node_indices)<=set(range(ps,pe))):
        raise ValueError("mixed backward column dX footprint mismatch")
    if (cG.gather_dim!=inG.gather_dim or cG.full_shape!=inG.full_shape
            or cG.shard_shape!=inG.shard_shape or outG.full_shape!=inG.full_shape
            or outG.sm_tid!=inG.sm_tid
            or cG.pm_allgather_step!=f"pm:{G.pm_node_indices[0]}:0"
            or len(inG.pm_tids)!=k):
        raise ValueError("mixed backward AllGather metadata mismatch")
    if (cA.input_gather_dim!=2 or cA.output_gather_dim!=1
            or cA.pm_step_ids!=tuple(f"pm:{i}:0" for i in A.pm_node_indices)
            or len(inA.pm_tids)!=k or len(outA.pm_tids)!=k
            or inA.sm_tid!=outA.sm_tid or inA.full_shape!=outA.full_shape):
        raise ValueError("mixed backward AllToAll metadata mismatch")
    for fact,dim in ((inG,cG.gather_dim),(inA,2),(outA,1)):
        shape=list(fact.shard_shape)
        if dim<0 or dim>=len(shape):
            raise ValueError("mixed backward collective tensor rank mismatch")
        shape[dim]*=k
        if tuple(shape)!=fact.full_shape:
            raise ValueError("mixed backward collective shape mismatch")
    nLs=ir.sm_nodes[L.sm_node_indices[0]]; nLp=tuple(ir.pm_nodes[i] for i in L.pm_node_indices)
    nG=ir.pm_nodes[G.pm_node_indices[0]]; nVs=ir.sm_nodes[V.sm_node_indices[0]]; nVp=ir.pm_nodes[V.pm_node_indices[0]]; nAp=tuple(ir.pm_nodes[i] for i in A.pm_node_indices)
    if cD and (D.sm_node_indices!=L.sm_node_indices or D.pm_node_indices!=L.pm_node_indices
            or cD.sm_step_id!=f"sm:{L.sm_node_indices[0]}:1"
            or cD.pm_step_ids!=tuple(f"pm:{i}:1" for i in L.pm_node_indices)):
        raise ValueError("mixed backward dW shared-writer footprint mismatch")
    if (nLs.op!="BW_linear" or nLs.rank!=0 or nLs.params or len(nLs.outs)!=2 or tuple(nLs.ins)!=(grad.sm_tid,act.sm_tid,weight.sm_tid) or nLs.outs[0]!=outL.sm_tid or (outD and nLs.outs[1]!=outD.sm_tid)
        or tuple(n.rank for n in nLp)!=tuple(range(k)) or any(n.op!="BW_linear" or n.params or len(n.outs)!=2 or tuple(n.ins)!=(grad.joined_pm_tid,act.pm_tids[r],weight.pm_tids[r]) or n.outs[0]!=outL.pm_tids[r] or (outD and n.outs[1]!=outD.pm_tids[r]) for r,n in enumerate(nLp))): raise ValueError("mixed backward BW_linear writers invalid")
    if nG.op!="AllGatherPrim" or tuple(nG.ins)!=inG.pm_tids or nG.outs!=[outG.joined_pm_tid] or tuple(nG.params)!=(inG.gather_dim,): raise ValueError("mixed backward AllGather writer invalid")
    target=tuple(cV.target_shape)
    if (cV.input_shape!=inV.full_shape or cV.target_shape!=outV.full_shape
            or cV.sm_step_id!=f"sm:{V.sm_node_indices[0]}:0"
            or cV.pm_step_id!=f"pm:{V.pm_node_indices[0]}:0"):
        raise ValueError("mixed backward BW_view certificate metadata mismatch")
    if nVs.op!="BW_view" or nVp.op!="BW_view" or nVs.ins[0]!=inV.sm_tid or nVp.ins[0]!=inV.joined_pm_tid or nVs.outs!=[outV.sm_tid] or nVp.outs!=[outV.joined_pm_tid] or tuple(nVs.params)!=target or tuple(nVp.params)!=target: raise ValueError("mixed backward BW_view writers invalid")
    if tuple(n.rank for n in nAp)!=tuple(range(k)) or any(n.op!="AllToAllPrim" or tuple(n.ins)!=inA.pm_tids or n.outs!=[outA.pm_tids[r]] or tuple(n.params)!=(2,1) for r,n in enumerate(nAp)): raise ValueError("mixed backward AllToAll writers invalid")
    if cD:
        validate_column_dw_authority(ir,chain,seg,D,grad,act,weight,outD)
    smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[f"private def {smn}:List NodeDecl:=[{', '.join(_node_text(n) for n in sf)}]",f"private def {pmn}:List NodeDecl:=[{', '.join(_node_text(n) for n in pf)}]",f"@[irreducible] private def {smf}(z:Store):Store:={smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z",f"@[irreducible] private def {pmf}(z:Store):Store:={pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z",""]
    def helper(name,side,node,index,kind,input_tids,shape=None,slot=0):
        graph=ir.sm_graph_ref if side=="sm" else ir.pm_graph_ref; initial="smStore" if side=="sm" else "pmStore"; fn=smf if side=="sm" else pmf; nn=smn if side=="sm" else pmn; frame=sf if side=="sm" else pf; start=ss if side=="sm" else ps; final=f"({fn} {initial})"
        if kind=="linear": expr=f"(bw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){'.1' if slot==0 else '.2'}"; apply=f"exact {'applyNode_bw_linear_fst_out' if slot==0 else 'applyNode_bw_linear_snd_out'} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)"
        elif kind=="gather": expr=f"allGatherPrimDimN {inG.gather_dim} {k} 0 ["+", ".join(f"{{store}} {u}" for u in inG.pm_tids)+"]"; apply=f"exact applyNode_allGatherPrimDimN_out {graph} t 0 [{', '.join(str(u) for u in inG.pm_tids)}] {node.outs[0]} {inG.gather_dim}"
        elif kind=="view": expr=f"fw_view {_shape_text(list(target))} ({{store}} {node.ins[0]})"; apply=f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.ins[1]} {node.outs[0]}"
        else:
            expr=f"allToAllPrimWithDims {graph}.numRanks {node.rank} ["+", ".join(f"{{store}} {u}" for u in inA.pm_tids)+f"] {cA.input_gather_dim} {cA.output_gather_dim}"
            apply=f"simpa only [List.map] using applyNode_allToAllPrimWithDims_out {graph} t {node.rank} [{', '.join(str(u) for u in inA.pm_tids)}] {node.outs[0]} {cA.input_gather_dim} {cA.output_gather_dim}"
        out_tid=node.outs[slot] if kind=="linear" else node.outs[0]
        th=f"{segment_id}_{name}";lines.extend([f"private theorem {th}({initial}:Store):{final} {out_tid}={expr.format(store=final)}:=by",f"  have hfinal:{final}={nn}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {fn};rfl"])
        body=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=index-start,output_tid=out_tid,input_tids=tuple(input_tids),written_tids={u for n in frame for u in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]","simp [applyNodeDistributed,applyNodeRingAttn]",apply])
        lines.extend(x[2:] if x.startswith("  ") else x for x in body);lines.extend(["  exact hout",""]);return th
    hLs=helper("hLinearSm","sm",nLs,L.sm_node_indices[0],"linear",nLs.ins);hLp=[helper(f"hLinearPm{r}","pm",n,L.pm_node_indices[r],"linear",n.ins) for r,n in enumerate(nLp)]
    hDs=helper("hLinearDwSm","sm",nLs,L.sm_node_indices[0],"linear",nLs.ins,slot=1) if cD else None
    hDp=[helper(f"hLinearDwPm{r}","pm",n,L.pm_node_indices[r],"linear",n.ins,slot=1) for r,n in enumerate(nLp)] if cD else []
    hG=helper("hGatherPm","pm",nG,G.pm_node_indices[0],"gather",nG.ins);hVs=helper("hViewSm","sm",nVs,V.sm_node_indices[0],"view",(nVs.ins[0],));hVp=helper("hViewPm","pm",nVp,V.pm_node_indices[0],"view",(nVp.ins[0],));hAp=[helper(f"hA2APm{r}","pm",n,A.pm_node_indices[r],"a2a",n.ins) for r,n in enumerate(nAp)]
    def vals(f): return "["+", ".join(f"pmFinal {u}" for u in f.pm_tids)+"]"
    xlist,wlist,olist=vals(act),vals(weight),vals(outL); dlist=vals(outD) if outD else None; af,ash,wf,wsh,of,osh=map(lambda x:_shape_text(list(x)),(act.full_shape,act.shard_shape,weight.full_shape,weight.shard_shape,outL.full_shape,outL.shard_shape))
    lines += [f"private theorem {segment_id}_dx_shape(g x w:Tensor)(o i:Nat)(hg:g.shape=[{b},{s},o])(hx:x.shape=[{b},{s},i])(hw:w.shape=[o,i]):(bw_linear g x w).1.shape=[{b},{s},i]:=bw_linear_3d_fst_shape {b} {s} o i g x w hg hx hw","set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f" let smFinal:={smf} smStore",f" let pmFinal:={pmf} pmStore",f" have hframe:{before.state_id}.Holds smFinal pmFinal:=by unfold smFinal pmFinal {smf} {pmf};apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",f" have hg:{grad.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change smFinal {grad.sm_tid}=pmFinal {grad.joined_pm_tid}∧(smFinal {grad.sm_tid}).shape={_shape_text(list(grad.full_shape))}∧(pmFinal {grad.joined_pm_tid}).shape={_shape_text(list(grad.full_shape))} at hg",f" have hx:{act.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {act.sm_tid}) {xlist} 2 {af} {ash} at hx",f" have hw:{weight.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {weight.sm_tid}) {wlist} 1 {wf} {wsh} at hw",f" have hxV:smFinal {act.sm_tid}=allGatherPrimDimN 2 4 0 {xlist}:=by simpa only [List.length_cons,List.length_nil] using hx.full_value",f" have hwV:smFinal {weight.sm_tid}=allGatherPrimDimN 1 4 0 {wlist}:=by simpa only [List.length_cons,List.length_nil] using hw.full_value",f" have hLs:={hLs} smStore",f" change smFinal {outL.sm_tid}=(bw_linear (smFinal {nLs.ins[0]}) (smFinal {nLs.ins[1]}) (smFinal {nLs.ins[2]})).1 at hLs"]
    for r in range(k): lines += [f" have hLp{r}:={hLp[r]} pmStore",f" change pmFinal {outL.pm_tids[r]}=(bw_linear (pmFinal {nLp[r].ins[0]}) (pmFinal {nLp[r].ins[1]}) (pmFinal {nLp[r].ins[2]})).1 at hLp{r}",f" have hxS{r}:=hx.shard_shapes (pmFinal {act.pm_tids[r]}) (by simp)",f" have hwS{r}:=hw.shard_shapes (pmFinal {weight.pm_tids[r]}) (by simp)",f" have hoS{r}:(pmFinal {outL.pm_tids[r]}).shape={osh}:=by rw [hLp{r}];exact {segment_id}_dx_shape _ _ _ {grad.full_shape[2]} {outL.shard_shape[2]} hg.2.2 hxS{r} hwS{r}"]
    if cD:
        lines += [f" have hDs:={hDs} smStore",f" change smFinal {outD.sm_tid}=(bw_linear (smFinal {nLs.ins[0]}) (smFinal {nLs.ins[1]}) (smFinal {nLs.ins[2]})).2 at hDs"]
        for r in range(k): lines += [f" have hDp{r}:={hDp[r]} pmStore",f" change pmFinal {outD.pm_tids[r]}=(bw_linear (pmFinal {nLp[r].ins[0]}) (pmFinal {nLp[r].ins[1]}) (pmFinal {nLp[r].ins[2]})).2 at hDp{r}",f" have hdS{r}:(pmFinal {outD.pm_tids[r]}).shape={wsh}:=by rw [hDp{r}];exact bw_linear_3d_snd_shape {b} {s} {grad.full_shape[2]} {act.shard_shape[2]} _ _ _ hg.2.2 hxS{r} hwS{r}"]
        lines += [line[3:].replace("hDwComm","hdcomm") for line in render_dynamic_column_dw_commute(D.lean_theorem,grad,act,weight)]
        lines += [f" have hdV:smFinal {outD.sm_tid}=allGatherPrimDimN 1 4 0 {dlist}:=by rw [hDs,hg.1,hxV,hwV,hdcomm];rw ["+", ".join(f"←hDp{r}" for r in range(k))+"]",f" have hdVL:smFinal {outD.sm_tid}=allGatherPrimDimN 1 {dlist}.length 0 {dlist}:=by simpa only [List.length_cons,List.length_nil] using hdV",f" have hdF:(smFinal {outD.sm_tid}).shape={wf}:=by rw [hDs];exact bw_linear_3d_snd_shape {b} {s} {grad.full_shape[2]} {act.full_shape[2]} _ _ _ hg.2.1 hx.full_shape hw.full_shape",f" have houtD:{outD.fact_id}.Holds smFinal pmFinal:=by",f"  change ShardedRel (smFinal {outD.sm_tid}) {dlist} 1 {wf} {wsh}","  refine {full_value:=hdVL,full_shape:=hdF,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=?_,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}","  intro shard hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs;rcases hs with h0|h1|h2|h3"]
        for r in range(k): lines += ["  · subst shard",f"    exact hdS{r}"]
    lines += [line[3:] for line in render_dynamic_column_commute(thL,grad,act,weight)]
    lines += [f" have hLV:smFinal {outL.sm_tid}=allGatherPrimDimN 2 4 0 {olist}:=by rw [hLs,hg.1,hwV,hcomm];rw ["+", ".join(f"←hLp{r}" for r in range(k))+"]",f" have hLVL:smFinal {outL.sm_tid}=allGatherPrimDimN 2 {olist}.length 0 {olist}:=by simpa only [List.length_cons,List.length_nil] using hLV",f" have hLF:(smFinal {outL.sm_tid}).shape={of}:=by rw [hLs];exact {segment_id}_dx_shape _ _ _ {grad.full_shape[2]} {outL.full_shape[2]} hg.2.1 hx.full_shape hw.full_shape",f" have hLShapes:∀ shard∈{olist},shard.shape={osh}:=by\n  simp only [List.forall_mem_cons]\n  exact ⟨"+", ".join(f"hoS{r}" for r in range(k))+", List.forall_mem_nil _⟩",f" have houtL:{outL.fact_id}.Holds smFinal pmFinal:=by exact {{full_value:=hLVL,full_shape:=hLF,shards_nonempty:=List.cons_ne_nil _ _,gather_dim_lt:=by native_decide,shard_shapes:=hLShapes,shape_contract:=by simp only [List.map, List.length_cons,List.length_nil];native_decide}}"]
    gl=vals(inG); gshape=_shape_text(list(inG.full_shape)); lines += [f" have hgi:{inG.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {inG.sm_tid}) {gl} {inG.gather_dim} {gshape} {_shape_text(list(inG.shard_shape))} at hgi",f" have hGw:={hG} pmStore",f" change pmFinal {outG.joined_pm_tid}=allGatherPrimDimN {inG.gather_dim} {k} 0 {gl} at hGw",f" have hGEq:smFinal {inG.sm_tid}=pmFinal {outG.joined_pm_tid}:=(ShardedRel.to_joined_allGather hgi).trans hGw.symm",f" have houtG:{outG.fact_id}.Holds smFinal pmFinal:=by exact ⟨hGEq,hgi.full_shape,by rw [←hGEq];exact hgi.full_shape⟩",f" have hVs:={hVs} smStore",f" change smFinal {outV.sm_tid}=fw_view {_shape_text(list(outV.full_shape))} (smFinal {inV.sm_tid}) at hVs",f" have hVp:={hVp} pmStore",f" change pmFinal {outV.joined_pm_tid}=fw_view {_shape_text(list(outV.full_shape))} (pmFinal {inV.joined_pm_tid}) at hVp",f" have houtV:{outV.fact_id}.Holds smFinal pmFinal:=by change smFinal {outV.sm_tid}=pmFinal {outV.joined_pm_tid}∧_∧_;rw [hVs,hVp];exact JoinedRel.fw_view {_shape_text(list(outV.full_shape))} {gshape} houtG"]
    al=vals(inA); aol=vals(outA); lines += []
    for r in range(k): lines += [f" have hA{r}:={hAp[r]} pmStore",f" change pmFinal {outA.pm_tids[r]}=allToAllPrimWithDims 4 {r} {al} 2 1 at hA{r}"]
    lines += [f" have hHead:(({al}.head?.map (fun t => t.shape)).getD [])={_shape_text(list(inA.shard_shape))}:=houtL.shard_shapes _ (by simp)",f" have hAV:smFinal {inA.sm_tid}=allGatherPrimDimN 2 4 0 {al}:=by simpa only [List.map,List.length_cons,List.length_nil] using houtL.full_value",f" have hGS:(allGatherPrimDimN 2 4 0 {al}).shape={_shape_text(list(inA.full_shape))}:=by rw [←hAV];exact houtL.full_shape",f" have hOd:1<(allGatherPrimDimN 2 4 0 {al}).shape.length:=by rw [hGS];native_decide",f" have hDv:(allGatherPrimDimN 2 4 0 {al}).shape.getD 1 0%4=0:=by rw [hGS];native_decide"]
    for r in range(k): lines += [f" have hAS{r}:(pmFinal {outA.pm_tids[r]}).shape={_shape_text(list(outA.shard_shape))}:=by rw [hA{r},allToAllPrimWithDims_shape 4 {r} {al} 2 1 {_shape_text(list(inA.shard_shape))} hHead (by native_decide)];native_decide"]
    lines += [f" have hOrd:{aol}=List.ofFn (fun r : Fin 4 => allToAllPrimWithDims 4 r.1 {al} 2 1):=by rw ["+", ".join(f"hA{r}" for r in range(k))+"];rfl",f" have hAC:allGatherPrimDimN 1 {aol}.length 0 {aol}=allGatherPrimDimN 2 4 0 {al}:=by rw [hOrd];simpa only [List.length_cons,List.length_nil,List.length_ofFn] using ({thA} 2 1 {al} (by simp) hOd hDv)",f" have hAShapes:∀ shard∈{aol},shard.shape={_shape_text(list(outA.shard_shape))}:=by\n  simp only [List.forall_mem_cons]\n  exact ⟨"+", ".join(f"hAS{r}" for r in range(k))+", List.forall_mem_nil _⟩",f" have houtA:{outA.fact_id}.Holds smFinal pmFinal:=by exact {{full_value:=by simp only [List.map];rw [hAC];exact hAV,full_shape:=houtL.full_shape,shards_nonempty:=List.cons_ne_nil _ _,gather_dim_lt:=by native_decide,shard_shapes:=hAShapes,shape_contract:=by simp only [List.map, List.length_cons,List.length_nil];native_decide}}"]
    fresh_facts=[outL.fact_id,outG.fact_id,outV.fact_id,outA.fact_id]+([outD.fact_id] if outD else [])
    fresh_proofs=["houtL","houtG","houtV","houtA"]+(["houtD"] if outD else [])
    fresh_list="["+", ".join(fresh_facts)+"]"
    lines += [" intro fact hfact",f" have hc:fact∈{fresh_list}++{before.state_id}.facts:=by exact (show {after.state_id}.facts⊆{fresh_list}++{before.state_id}.facts by native_decide) hfact"," simp only [List.mem_append] at hc"," rcases hc with fresh|old"," · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh","   rcases fresh with "+" | ".join("rfl" for _ in fresh_proofs),*(f"   · exact {proof}" for proof in fresh_proofs)," · exact hframe fact old","", "set_option maxRecDepth 32768 in",f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f" smNodes:={smn}",f" pmNodes:={pmn}",f" sound:=by intro smStore pmStore hstate;have h:={segment_id}_sound smStore pmStore hstate;unfold {smf} {pmf} at h;exact h",""]
    return "\n".join(lines)
