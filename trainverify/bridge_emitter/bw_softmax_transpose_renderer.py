"""Independent BW_softmax dim1 and transpose dim2→dim1 in one atomic frame."""
from __future__ import annotations
import re


try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_bw_softmax_transpose_segment(ir, relation, segment_id: str) -> str:
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankTransposeRelationCertificate, KRankBWSoftmaxCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankTransposeRelationCertificate, KRankBWSoftmaxCertificate
    chain=relation.dependent_chain_plan
    seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    byid={t.transition_id:t for t in relation.transition_specs}
    if seg is None or len(seg.transition_ids)!=2 or len(byid)!=len(relation.transition_specs):raise ValueError("ambiguous atomic transitions")
    try:ts=tuple(byid[x] for x in seg.transition_ids)
    except KeyError as exc:raise ValueError("missing transition") from exc
    trule="transpose-sharded-k-rank";srule="bw-softmax-sharded-dim1-k-rank"
    ttheorem="TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4"
    stheorem="TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim1_rank4"
    if {t.rule_id for t in ts}!={trule,srule}:raise ValueError("wrong atomic family")
    t=next(t for t in ts if t.rule_id==trule);s=next(t for t in ts if t.rule_id==srule)
    tc=_select_exact_typed_certificate(relation,t,trule,ttheorem,KRankTransposeRelationCertificate,lambda c:((c.input_fact,),(c.output_fact,)))
    sc=_select_exact_typed_certificate(relation,s,srule,stheorem,KRankBWSoftmaxCertificate,lambda c:(tuple(sorted((c.gradient_fact,c.activation_fact))),(c.output_fact,)))
    rec={r.source:r for r in chain.relation_facts};byfid={r.fact_id:r for r in chain.relation_facts}
    if len(rec)!=len(chain.relation_facts) or len(byfid)!=len(rec):raise ValueError("ambiguous fact identity")
    try:ti,to,sg,sy,so=(rec[f] for f in (tc.input_fact,tc.output_fact,sc.gradient_fact,sc.activation_fact,sc.output_fact))
    except KeyError as exc:raise ValueError("missing materialized fact") from exc
    k=sc.rank_count
    if type(k) is not int or k<=0 or k!=ir.pm_num_ranks or tc.rank_count!=k:raise ValueError("rank authority mismatch")
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if not 0<=ss<=se<=len(ir.sm_nodes) or not 0<=ps<=pe<=len(ir.pm_nodes):raise ValueError("invalid frame")
    def source_tid(ref,side):
        m=re.fullmatch(r"init:(0|[1-9][0-9]*)",ref)
        if m:return int(m[1])
        m=re.fullmatch(r"(sm|pm):(0|[1-9][0-9]*):(0|[1-9][0-9]*)",ref)
        if m is None or m[1]!=side:raise ValueError("invalid source reference")
        nodes=ir.sm_nodes if side=="sm" else ir.pm_nodes
        index,slot=int(m[2]),int(m[3])
        if index>=len(nodes) or slot>=len(nodes[index].outs):raise ValueError("source outside graph")
        return nodes[index].outs[slot]
    def check_record(r,axis):
        f=r.source
        if (r.kind!="sharded" or f.layout!="sharded" or r.gather_dim!=axis or f.gather_dim!=axis
            or len(r.shard_shape)!=4 or any(type(v) is not int or v<=0 for v in r.shard_shape)
            or r.full_shape!=tuple(v*k if i==axis else v for i,v in enumerate(r.shard_shape))
            or len(r.pm_tids)!=k or len(f.step_triple)!=k+1 or len(set(r.pm_tids))!=k
            or r.metadata_tid is not None or r.metadata_region_id is not None or r.row_shard_shape is not None
            or r.source_tid_triples or r.joined_pm_tid is not None or f.source_step_triples or f.joined_pm_step is not None):raise ValueError("record axis/shape contract mismatch")
        if source_tid(f.step_triple[0],"sm")!=r.sm_tid or tuple(source_tid(z,"pm") for z in f.step_triple[1:])!=r.pm_tids:raise ValueError("source/record TID mismatch")
    for r,axis in ((ti,2),(to,1),(sg,1),(sy,1),(so,1)):check_record(r,axis)
    tin_dim,tout_dim,soft_dim=2,1,1
    tin_full,tin_shard,tout_full,tout_shard=ti.full_shape,ti.shard_shape,to.full_shape,to.shard_shape
    soft_shard=sy.shard_shape;soft_full_text=_shape_text(list(sy.full_shape))
    perm=lambda v:(v[0],v[2],v[1],v[3])
    if (tc.parameters!=(1,2) or tc.input_gather_dim!=2 or tc.output_gather_dim!=1
        or (tc.input_full_shape,tc.input_shard_shape,tc.output_full_shape,tc.output_shard_shape)!=(tin_full,tin_shard,tout_full,tout_shard)
        or perm(tin_full)!=tout_full or perm(tin_shard)!=tout_shard
        or sc.gather_dim!=1 or any((r.full_shape,r.shard_shape)!=(sy.full_shape,soft_shard) for r in (sg,so))):raise ValueError("certificate shape/axis mismatch")
    states={x.state_id:x for x in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    fresh={to.fact_id,so.fact_id}
    if (not {ti.fact_id,sg.fact_id,sy.fact_id}<=set(before.fact_ids) or not fresh<=set(after.fact_ids)
        or fresh&set(before.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh):raise ValueError("atomic fact liveness mismatch")
    tr_sm,tr_pm,sf_sm,sf_pm=t.sm_node_indices,t.pm_node_indices,s.sm_node_indices,s.pm_node_indices
    for tr,c,out in ((t,tc,to),(s,sc,so)):
        if (len(tr.sm_node_indices)!=1 or len(tr.pm_node_indices)!=k
            or tuple(sorted(set(tr.pm_node_indices)))!=tr.pm_node_indices
            or not set(tr.sm_node_indices)<=set(range(ss,se)) or not set(tr.pm_node_indices)<=set(range(ps,pe))
            or c.sm_step_id!=f"sm:{tr.sm_node_indices[0]}:0" or c.pm_step_ids!=tuple(f"pm:{p}:0" for p in tr.pm_node_indices)
            or out.source.step_triple!=(c.sm_step_id,*c.pm_step_ids)):raise ValueError("writer footprint mismatch")
    if set(tr_sm)&set(sf_sm) or set(tr_pm)&set(sf_pm):raise ValueError("overlapping semantic writers")
    tn=ir.sm_nodes[tr_sm[0]];sn=ir.sm_nodes[sf_sm[0]];tp=tuple(ir.pm_nodes[p] for p in tr_pm);sp=tuple(ir.pm_nodes[p] for p in sf_pm)
    def latest(ref,side,at):
        tid=source_tid(ref,side);nodes=ir.sm_nodes if side=="sm" else ir.pm_nodes
        writes=[(p,j) for p,n in enumerate(nodes[:at]) for j,u in enumerate(n.outs) if u==tid]
        expected=f"{side}:{writes[-1][0]}:{writes[-1][1]}" if writes else f"init:{tid}"
        if ref!=expected:raise ValueError("source is not latest before read")
    for tr,c,inputs,out,op in ((t,tc,(ti,),to,"BW_transpose"),(s,sc,(sg,sy),so,"BW_softmax")):
        for side,positions in (("sm",tr.sm_node_indices),("pm",tr.pm_node_indices)):
            nodes=ir.sm_nodes if side=="sm" else ir.pm_nodes
            for rank,p in enumerate(positions):
                n=nodes[p];ids=tuple(r.sm_tid if side=="sm" else r.pm_tids[rank] for r in inputs)
                if (n.op!=op or n.rank!=rank or tuple(n.params or [])!=c.parameters or len(n.ins)!=2
                    or tuple(n.ins[:len(inputs)])!=ids or n.outs!=[out.sm_tid if side=="sm" else out.pm_tids[rank]]):raise ValueError("writer roles/rank/params mismatch")
                for r in inputs:latest(r.source.step_triple[0 if side=="sm" else rank+1],side,p)
    authority={a.fact_id:a for a in chain.authority_facts}
    if chain.anchor_fact is not None:authority[chain.anchor_fact.fact_id]=chain.anchor_fact
    oldsm,oldpm=set(),set()
    for fid in before.fact_ids:
        if fid in byfid:
            r=byfid[fid];oldsm.add(r.sm_tid);oldpm.update(r.pm_tids)
            if r.joined_pm_tid is not None:oldpm.add(r.joined_pm_tid)
            if r.metadata_tid is not None:oldsm.add(r.metadata_tid);oldpm.add(r.metadata_tid)
            for a,b,c in r.source_tid_triples:oldsm.add(a);oldpm.update((b,c))
        elif fid in authority:
            a=authority[fid]
            if a.kind in ("tensor_shape","packed_cu","label_bound") and a.side in ("sm","pm"):(oldsm if a.side=="sm" else oldpm).add(a.tid)
            elif a.kind=="tensor_eq" and a.left_side in ("sm","pm") and a.right_side in ("sm","pm"):
                (oldsm if a.left_side=="sm" else oldpm).add(a.left_tid);(oldsm if a.right_side=="sm" else oldpm).add(a.right_tid)
            elif a.kind=="gather":oldsm.add(a.sm_tid);oldpm.update((a.pm_rank0_tid,a.pm_rank1_tid))
            else:raise ValueError("unsupported authority")
        else:raise ValueError("unknown live fact")
    for frame,old,outputs in ((ir.sm_nodes[ss:se],oldsm,{to.sm_tid,so.sm_tid}),(ir.pm_nodes[ps:pe],oldpm,set(to.pm_tids)|set(so.pm_tids))):
        if any(set(n.outs)&old for n in frame):raise ValueError("frame overwrites live authority")
        if any(sum(n.outs.count(u) for n in frame)!=1 for u in outputs):raise ValueError("output overwritten in frame")
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
    soft_shard_text=_shape_text(list(soft_shard));soft_shape_args=" ".join(str(x) for x in soft_shard[:3]);soft_fn="bw_softmax"
    tin_shard_text=_shape_text(list(tin_shard));tout_full_text=_shape_text(list(tout_full));tout_shard_text=_shape_text(list(tout_shard))
    tin_symbolic=list(tin_shard);tin_symbolic[tin_dim]=f"{tin_shard[tin_dim]} * {til}.length";tin_symbolic_text="["+", ".join(map(str,tin_symbolic))+"]"
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    let smFinal := {smf} smStore",f"    let pmFinal := {pmf} pmStore",f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",f"      unfold smFinal pmFinal {smf} {pmf}",f"      apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate","      · native_decide","      · native_decide","      · native_decide","      · native_decide",f"    have hti : {ti.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {ti.sm_tid}) {til} {tin_dim} {tin_symbolic_text} {tin_shard_text} at hti",f"    have hg : {sg.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {sg.sm_tid}) {gl} {soft_dim} {soft_full_text} {soft_shard_text} at hg",f"    have hy : {sy.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {sy.sm_tid}) {yl} {soft_dim} {soft_full_text} {soft_shard_text} at hy",f"    have hTsm := {htS} smStore",f"    change smFinal {to.sm_tid} = transposeAxes 1 2 (smFinal {ti.sm_tid}) at hTsm",f"    have hSsm := {hsS} smStore",f"    change smFinal {so.sm_tid} = {soft_fn} (smFinal {sg.sm_tid}) (smFinal {sy.sm_tid}) at hSsm"])
    for r in range(k): lines.extend([f"    have hTpm{r} := {htP[r]} pmStore",f"    change pmFinal {to.pm_tids[r]} = transposeAxes 1 2 (pmFinal {ti.pm_tids[r]}) at hTpm{r}",f"    have hSpm{r} := {hsP[r]} pmStore",f"    change pmFinal {so.pm_tids[r]} = {soft_fn} (pmFinal {sg.pm_tids[r]}) (pmFinal {sy.pm_tids[r]}) at hSpm{r}",f"    have hgShape{r} := hg.shard_shapes (pmFinal {sg.pm_tids[r]}) (by simp)",f"    have hyShape{r} := hy.shard_shapes (pmFinal {sy.pm_tids[r]}) (by simp)",f"    have hSShape{r} : (pmFinal {so.pm_tids[r]}).shape = {soft_shard_text} := by rw [hSpm{r}]; exact bw_softmax_shape_g199 _ _ {_shape_text(list(soft_shard[:3]))} {soft_shard[3]} hyShape{r}"])
    lines.extend([f"    have htRaw := {tc.lean_theorem} hti",f"    have houtT : {to.fact_id}.Holds smFinal pmFinal := by",f"      change ShardedRel (smFinal {to.sm_tid}) {tol} {tout_dim} {tout_full_text} {tout_shard_text}","      rw [hTsm, "+", ".join(f"hTpm{r}" for r in range(k))+"]","      simpa using htRaw",f"    have hgValue : smFinal {sg.sm_tid} = allGatherPrimDimN {soft_dim} {k} 0 {gl} := by simpa only [List.length_cons, List.length_nil] using hg.full_value",f"    have hyValue : smFinal {sy.sm_tid} = allGatherPrimDimN {soft_dim} {k} 0 {yl} := by simpa only [List.length_cons, List.length_nil] using hy.full_value"])

    soft_args=" ".join(map(str,soft_shard))
    lines.extend([f"    have hcomm := {sc.lean_theorem} {gl} {yl} {k} {soft_args}",
      "      (by omega) (by omega) (by omega) (by omega) (by omega)",
      "      (by simp) (by simp) hg.shard_shapes hy.shard_shapes",
      f"    have hSValue : smFinal {so.sm_tid} = allGatherPrimDimN {soft_dim} {k} 0 {ol} := by",
      "      rw [hSsm, hgValue, hyValue, hcomm]", "      simp only [List.zipWith]",
      "      rw ["+", ".join(f"← hSpm{r}" for r in range(k))+"]"])
    lines.extend([f"    have hSValueList : smFinal {so.sm_tid} = allGatherPrimDimN {soft_dim} {ol}.length 0 {ol} := by simpa only [List.length_cons, List.length_nil] using hSValue",f"    have hSFullShape : (smFinal {so.sm_tid}).shape = {soft_full_text} := by rw [hSsm]; exact bw_softmax_shape_g199 _ _ {_shape_text(list(sy.full_shape[:3]))} {soft_shard[3]} hy.full_shape",f"    have hSShapes : ∀ z ∈ {ol}, z.shape = {soft_shard_text} := by","      simp only [List.forall_mem_cons]","      exact ⟨"+", ".join(f"hSShape{r}" for r in range(k))+", List.forall_mem_nil _⟩",f"    have houtS : {so.fact_id}.Holds smFinal pmFinal := by",f"      change ShardedRel (smFinal {so.sm_tid}) {ol} {soft_dim} {soft_full_text} {soft_shard_text}","      exact { full_value := hSValueList, full_shape := hSFullShape, shards_nonempty := List.cons_ne_nil _ _, gather_dim_lt := by native_decide, shard_shapes := hSShapes, shape_contract := by simp only [List.map, List.length_cons, List.length_nil]; native_decide }"])
    lines.extend(["    intro fact hfact",f"    have covered : fact ∈ [{to.fact_id}, {so.fact_id}] ++ {before.state_id}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{to.fact_id}, {so.fact_id}] ++ {before.state_id}.facts by native_decide) hfact","    simp only [List.mem_append] at covered","    rcases covered with fresh | old","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with rfl | rfl","      · exact houtT","      · exact houtS","    · exact hframe fact old","","set_option maxRecDepth 8192 in",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by intro smStore pmStore hstate; exact "+f"{segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)
