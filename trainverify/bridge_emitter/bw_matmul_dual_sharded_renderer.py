"""Atomic shared-writer renderer for dual-axis sharded BW_matmul projections."""
from __future__ import annotations


def render_closed_dual_sharded_bw_matmul_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import KRankBWMatmulCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import KRankBWMatmulCertificate
    contracts = {
        "bw-matmul-fst-y-sharded-rank4": (".1", "fst-y-sharded", "TrainVerify.Denote.bw_matmul_fst_split_1_4_8_8"),
        "bw-matmul-snd-x-sharded-rank4": (".2", "snd-x-sharded", "TrainVerify.Denote.bw_matmul_snd_split_dX_1_4_8_8"),
    }
    chain=relation.dependent_chain_plan; seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=2: raise ValueError("dual-sharded BW_matmul requires two transitions")
    tm={t.transition_id:t for t in relation.transition_specs}; ts=tuple(tm[x] for x in seg.transition_ids)
    if {t.rule_id for t in ts}!=set(contracts): raise ValueError("dual-sharded BW_matmul family set mismatch")
    certs=[]
    for t in ts:
        projection,family,theorem=contracts[t.rule_id]
        if t.lean_theorem!=theorem: raise ValueError("dual-sharded BW_matmul theorem mismatch")
        c=_select_exact_typed_certificate(relation,t,t.rule_id,theorem,KRankBWMatmulCertificate,lambda x:(tuple(sorted(x.input_facts)),(x.output_fact,)))
        if c.projection!=projection or c.family!=family: raise ValueError("dual-sharded BW_matmul projection mismatch")
        certs.append(c)
    cb={c.projection:c for c in certs}; fst,snd=cb[".1"],cb[".2"]
    if fst.input_facts!=snd.input_facts or fst.rank_count!=4 or snd.rank_count!=4: raise ValueError("dual-sharded BW_matmul authority disagrees")
    rs={r.source:r for r in chain.relation_facts}
    try: g,x,y=(rs[f] for f in fst.input_facts); ofst=rs[fst.output_fact]; osnd=rs[snd.output_fact]
    except KeyError as exc: raise ValueError("dual-sharded BW_matmul fact missing") from exc
    states={s.state_id:s for s in chain.states}; before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if not {g.fact_id,x.fact_id,y.fact_id}<=set(before.fact_ids) or not {ofst.fact_id,osnd.fact_id}<=set(after.fact_ids): raise ValueError("dual-sharded BW_matmul liveness mismatch")
    if not set(after.fact_ids)<=({ofst.fact_id,osnd.fact_id}|set(before.fact_ids)): raise ValueError("dual-sharded BW_matmul post-state mismatch")
    full=(1,4,8,8)
    if (g.kind!="joined" or g.joined_pm_tid is None or g.full_shape!=full
        or x.kind!="sharded" or x.gather_dim!=3 or x.full_shape!=full or x.shard_shape!=(1,4,8,2)
        or y.kind!="sharded" or y.gather_dim!=2 or y.full_shape!=full or y.shard_shape!=(1,4,2,8)
        or ofst.kind!="sharded" or ofst.gather_dim!=3 or ofst.full_shape!=full or ofst.shard_shape!=(1,4,8,2)
        or osnd.kind!="sharded" or osnd.gather_dim!=2 or osnd.full_shape!=full or osnd.shard_shape!=(1,4,2,8)
        or any(len(r.pm_tids)!=4 for r in (x,y,ofst,osnd))): raise ValueError("dual-sharded BW_matmul metadata mismatch")
    if any(t.sm_node_indices!=ts[0].sm_node_indices or t.pm_node_indices!=ts[0].pm_node_indices for t in ts): raise ValueError("dual-sharded BW_matmul writers differ")
    ss,se=seg.sm_range; ps,pe=seg.pm_range; si=ts[0].sm_node_indices[0]; pis=ts[0].pm_node_indices
    if (ss,se)!=(si,si+1) or tuple(range(ps,pe))!=pis: raise ValueError("dual-sharded BW_matmul frame mismatch")
    sm=ir.sm_nodes[si]; pms=tuple(ir.pm_nodes[i] for i in pis)
    if (tuple(sm.ins)!=(g.sm_tid,x.sm_tid,y.sm_tid) or tuple(sm.outs)!=(ofst.sm_tid,osnd.sm_tid)
        or tuple(n.rank for n in pms)!=(0,1,2,3)): raise ValueError("dual-sharded BW_matmul SM roles mismatch")
    for r,n in enumerate(pms):
        if n.op!="BW_matmul" or n.params or tuple(n.ins)!=(g.joined_pm_tid,x.pm_tids[r],y.pm_tids[r]) or tuple(n.outs)!=(ofst.pm_tids[r],osnd.pm_tids[r]): raise ValueError("dual-sharded BW_matmul PM roles mismatch")
    for c,slot in ((fst,0),(snd,1)):
        if c.sm_step_id!=f"sm:{si}:{slot}" or c.pm_step_ids!=tuple(f"pm:{i}:{slot}" for i in pis): raise ValueError("dual-sharded BW_matmul footprint tampered")
    smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes"; smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    sf=[sm];pf=list(pms);lines=[f"private def {smn}:List NodeDecl:=[{_node_text(sm)}]",f"private def {pmn}:List NodeDecl:=[{', '.join(_node_text(n) for n in pms)}]",f"@[irreducible] private def {smf}(s:Store):Store:={smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"@[irreducible] private def {pmf}(s:Store):Store:={pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
    def helper(name,graph,initial,fn,nn,frame,pos,node,slot):
        final=f"({fn} {initial})";proj=".1" if slot==0 else ".2";expr=f"(bw_matmul ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})){proj}";tn=f"{segment_id}_{name}"
        lines.extend([f"private theorem {tn}({initial}:Store):{final} {node.outs[slot]}={expr.format(store=final)}:=by",f"  have hfinal:{final}={nn}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {fn};rfl"])
        lemma="applyNode_bw_matmul_fst_out" if slot==0 else "applyNode_bw_matmul_snd_out"
        h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=node.outs[slot],input_tids=tuple(node.ins),written_tids={u for n in frame for u in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]","simp [applyNodeDistributed,applyNodeRingAttn]",f"exact {lemma} {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)"])
        lines.extend(z[2:] if z.startswith("  ") else z for z in h);lines.extend(["  exact hout",""]);return tn
    hs0=helper("hSmFst",ir.sm_graph_ref,"smStore",smf,smn,sf,0,sm,0);hs1=helper("hSmSnd",ir.sm_graph_ref,"smStore",smf,smn,sf,0,sm,1);hp0=[];hp1=[]
    for r,n in enumerate(pms):hp0.append(helper(f"hPmFst{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pf,r,n,0));hp1.append(helper(f"hPmSnd{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pf,r,n,1))
    xl="["+", ".join(f"pmFinal {u}" for u in x.pm_tids)+"]";yl="["+", ".join(f"pmFinal {u}" for u in y.pm_tids)+"]";fl="["+", ".join(f"pmFinal {u}" for u in ofst.pm_tids)+"]";sl="["+", ".join(f"pmFinal {u}" for u in osnd.pm_tids)+"]"
    F="[1,4,8,8]";XS="[1,4,8,2]";YS="[1,4,2,8]"
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound(smStore pmStore:Store)(hstate:{before.state_id}.Holds smStore pmStore):{after.state_id}.Holds ({smf} smStore) ({pmf} pmStore):=by",f" let smFinal:={smf} smStore",f" let pmFinal:={pmf} pmStore",f" have hframe:{before.state_id}.Holds smFinal pmFinal:=by unfold smFinal pmFinal {smf} {pmf};apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate <;> native_decide",f" have hg:{g.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change smFinal {g.sm_tid}=pmFinal {g.joined_pm_tid}∧(smFinal {g.sm_tid}).shape={F}∧(pmFinal {g.joined_pm_tid}).shape={F} at hg",f" have hx:{x.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {x.sm_tid}) {xl} 3 {F} {XS} at hx",f" have hy:{y.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f" change ShardedRel (smFinal {y.sm_tid}) {yl} 2 {F} {YS} at hy",f" have hxV:smFinal {x.sm_tid}=allGatherPrimDimN 3 4 0 {xl}:=by simpa only [List.length_cons,List.length_nil] using hx.full_value",f" have hyV:smFinal {y.sm_tid}=allGatherPrimDimN 2 4 0 {yl}:=by simpa only [List.length_cons,List.length_nil] using hy.full_value",f" have hSF:={hs0} smStore",f" have hSS:={hs1} smStore",f" change smFinal {ofst.sm_tid}=batchedMatmul (smFinal {g.sm_tid}) (transpose2d (smFinal {y.sm_tid})) at hSF",f" change smFinal {osnd.sm_tid}=batchedMatmul (transpose2d (smFinal {x.sm_tid})) (smFinal {g.sm_tid}) at hSS"])
    for r in range(4):lines.extend([f" have hPF{r}:={hp0[r]} pmStore",f" have hPS{r}:={hp1[r]} pmStore",f" change pmFinal {ofst.pm_tids[r]}=batchedMatmul (pmFinal {g.joined_pm_tid}) (transpose2d (pmFinal {y.pm_tids[r]})) at hPF{r}",f" change pmFinal {osnd.pm_tids[r]}=batchedMatmul (transpose2d (pmFinal {x.pm_tids[r]})) (pmFinal {g.joined_pm_tid}) at hPS{r}",f" have hxS{r}:=hx.shard_shapes (pmFinal {x.pm_tids[r]}) (by simp)",f" have hyS{r}:=hy.shard_shapes (pmFinal {y.pm_tids[r]}) (by simp)",f" have hfS{r}:(pmFinal {ofst.pm_tids[r]}).shape={XS}:=by rw [hPF{r}];exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ hg.2.2 (transpose2d_shape_1_4_2_8 _ hyS{r})",f" have hsS{r}:(pmFinal {osnd.pm_tids[r]}).shape={YS}:=by rw [hPS{r}];exact batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_2 _ hxS{r}) hg.2.2"])
    lines.extend([f" have hcF:={fst.lean_theorem} (pmFinal {g.joined_pm_tid}) "+" ".join(f"(pmFinal {u})" for u in y.pm_tids)+" hg.2.2 "+" ".join(f"hyS{r}" for r in range(4)),f" have hvF:smFinal {ofst.sm_tid}=allGatherPrimDimN 3 4 0 {fl}:=by rw [hSF,hg.1,hyV,hcF];rw ["+", ".join(f"←hPF{r}" for r in range(4))+"]",f" have hcS:={snd.lean_theorem} (pmFinal {g.joined_pm_tid}) "+" ".join(f"(pmFinal {u})" for u in x.pm_tids)+" hg.2.2 "+" ".join(f"hxS{r}" for r in range(4)),f" have hvS:smFinal {osnd.sm_tid}=allGatherPrimDimN 2 4 0 {sl}:=by rw [hSS,hg.1,hxV,hcS];rw ["+", ".join(f"←hPS{r}" for r in range(4))+"]"])
    def emit_fact(name,o,l,dim,sh,v,writer,fullshape,pieces):
        lines.extend([f" have {name}V:smFinal {o.sm_tid}=allGatherPrimDimN {dim} {l}.length 0 {l}:=by simpa only [List.length_cons,List.length_nil] using {v}",f" have {name}Full:(smFinal {o.sm_tid}).shape={F}:=by rw [{writer}];exact {fullshape}",f" have {name}:{o.fact_id}.Holds smFinal pmFinal:=by",f"  change ShardedRel (smFinal {o.sm_tid}) {l} {dim} {F} {sh}",f"  exact {{full_value:={name}V,full_shape:={name}Full,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=by intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with h0|h1|h2|h3 <;> subst z;exact {pieces}0;exact {pieces}1;exact {pieces}2;exact {pieces}3,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}}"])
    emit_fact("houtF",ofst,fl,3,XS,"hvF","hSF","batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ hg.2.1 (transpose2d_shape_1_4_8_8 _ hy.full_shape)","hfS")
    emit_fact("houtS",osnd,sl,2,YS,"hvS","hSS","batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_8 _ hx.full_shape) hg.2.1","hsS")
    lines.extend([" intro fact hfact",f" have hc:fact∈[{ofst.fact_id},{osnd.fact_id}]++{before.state_id}.facts:=by exact (show {after.state_id}.facts⊆[{ofst.fact_id},{osnd.fact_id}]++{before.state_id}.facts by native_decide) hfact"," simp only [List.mem_append] at hc"," rcases hc with fresh|old"," · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with rfl|rfl","   · exact houtF","   · exact houtS"," · exact hframe fact old","",f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f" smNodes:={smn}",f" pmNodes:={pmn}",f" sound:=by intro a b h;have z:={segment_id}_sound a b h;unfold {smf} {pmf} at z;exact z",""])
    return "\n".join(lines)
