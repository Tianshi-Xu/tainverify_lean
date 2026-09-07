"""List-indexed sequence dW, optionally sharing its frame with sequence dX."""
from __future__ import annotations
import re

RULE = "bw-linear-dw-sequence-reduction-k-rank"
THEOREM = "TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3"
DX_RULE = "bw-linear-dx-sequence-sharded-k-rank"
DX_THEOREM = "TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3"


def render_closed_bw_linear_dw_sequence_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import KRankBWLinearDwReductionCertificate, KRankBWLinearDxCertificate
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import KRankBWLinearDwReductionCertificate, KRankBWLinearDxCertificate
    chain = relation.dependent_chain_plan
    seg = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if seg is None or len(seg.transition_ids) not in (1, 2):
        raise ValueError("sequence dW requires dW and optional shared dX")
    tm = {t.transition_id:t for t in relation.transition_specs}
    if len(tm) != len(relation.transition_specs): raise ValueError("ambiguous transition identity")
    try: ts = tuple(tm[t] for t in seg.transition_ids)
    except KeyError as exc: raise ValueError("missing sequence transition") from exc
    selected = {}
    for t in ts:
        if t.rule_id == RULE:
            c = _select_exact_typed_certificate(relation,t,RULE,THEOREM,KRankBWLinearDwReductionCertificate,
                lambda c:(tuple(sorted((c.gradient_fact,c.activation_fact,c.weight_fact))),(c.output_fact,)))
            slot = 1; inputs = (c.gradient_fact,c.activation_fact,c.weight_fact)
            if c.shard_dim != 1: raise ValueError("sequence dW shard axis mismatch")
        elif t.rule_id == DX_RULE:
            c = _select_exact_typed_certificate(relation,t,DX_RULE,DX_THEOREM,KRankBWLinearDxCertificate,
                lambda c:(tuple(sorted(c.input_facts)),(c.output_fact,)))
            slot = 0; inputs = c.input_facts
            if c.family != "sequence-sharded" or c.gather_dim != 1 or c.output_layout != "sharded":
                raise ValueError("sequence dX semantic identity mismatch")
        else: raise ValueError("unsupported sequence projection")
        if slot in selected: raise ValueError("duplicate sequence projection")
        selected[slot] = (t,c,inputs)
    if 1 not in selected: raise ValueError("sequence dW is required")
    t,c,inputs = selected[1]
    records = {r.source:r for r in chain.relation_facts}
    by_id = {r.fact_id:r for r in chain.relation_facts}
    if len(records)!=len(chain.relation_facts) or len(by_id)!=len(records): raise ValueError("ambiguous relation identity")
    try:
        g,x,w = (records[f] for f in inputs)
        outputs = {slot:records[item[1].output_fact] for slot,item in selected.items()}
    except (KeyError,ValueError) as exc: raise ValueError("sequence fact missing") from exc
    k = c.rank_count
    if type(k) is not int or k<=0 or k!=ir.pm_num_ranks or len(g.shard_shape)!=3 or len(x.shard_shape)!=3:
        raise ValueError("sequence rank authority mismatch")
    b,s,o = g.shard_shape; i = x.shard_shape[2]
    if any(type(v) is not int or v<=0 for v in (b,s,o,i)): raise ValueError("sequence dimensions must be positive")
    def source_tid(ref,side):
        m=re.fullmatch(r"init:(0|[1-9][0-9]*)",ref)
        if m:return int(m[1])
        m=re.fullmatch(r"(sm|pm):(0|[1-9][0-9]*):(0|[1-9][0-9]*)",ref)
        if m is None or m[1]!=side:raise ValueError("invalid source reference")
        nodes=ir.sm_nodes if side=="sm" else ir.pm_nodes
        index,slot=int(m[2]),int(m[3])
        if index>=len(nodes) or slot>=len(nodes[index].outs):raise ValueError("source outside full graph")
        return nodes[index].outs[slot]
    def check_record(r,kind,axis,full,shard,n):
        f=r.source
        if (r.kind!=kind or f.layout!=kind or r.gather_dim!=axis or f.gather_dim!=axis
                or r.full_shape!=full or r.shard_shape!=shard or len(r.pm_tids)!=n
                or len(f.step_triple)!=n+1 or r.metadata_tid is not None or r.metadata_region_id is not None
                or r.row_shard_shape is not None or r.source_tid_triples or r.joined_pm_tid is not None
                or f.source_step_triples or f.joined_pm_step is not None):raise ValueError("source/record axis/shape mismatch")
        if source_tid(f.step_triple[0],"sm")!=r.sm_tid or tuple(source_tid(z,"pm") for z in f.step_triple[1:])!=r.pm_tids:
            raise ValueError("source/record TID mismatch")
    check_record(g,"sharded",1,(b,s*k,o),(b,s,o),k)
    check_record(x,"sharded",1,(b,s*k,i),(b,s,i),k)
    check_record(w,"sharded",0,(o,i),(o,i),1)
    if w.source.step_triple!=(f"init:{w.sm_tid}",)*2:raise ValueError("weight must be shared singleton initial authority")
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if (len(t.sm_node_indices)!=1 or len(t.pm_node_indices)!=k or len(set(t.pm_node_indices))!=k
            or not 0<=ss<=se<=len(ir.sm_nodes) or not 0<=ps<=pe<=len(ir.pm_nodes)
            or not set(t.sm_node_indices)<=set(range(ss,se)) or not set(t.pm_node_indices)<=set(range(ps,pe))):
        raise ValueError("sequence writer/frame footprint mismatch")
    for slot,(tr,cert,roles) in selected.items():
        out=outputs[slot]
        check_record(out,"reduction" if slot else "sharded",None if slot else 1,
            (o,i) if slot else (b,s*k,i),(o,i) if slot else (b,s,i),k)
        if (roles!=inputs or cert.rank_count!=k or tr.sm_node_indices!=t.sm_node_indices
                or tr.pm_node_indices!=t.pm_node_indices or cert.sm_step_id!=f"sm:{t.sm_node_indices[0]}:{slot}"
                or cert.pm_step_ids!=tuple(f"pm:{p}:{slot}" for p in t.pm_node_indices)
                or out.source.step_triple!=(cert.sm_step_id,*cert.pm_step_ids) or len(set(out.pm_tids))!=k):
            raise ValueError("sequence projections do not share exact roles/writers")
    states={z.state_id:z for z in chain.states}
    before,after=states[seg.pre_state_id],states[seg.post_state_id]
    fresh={r.fact_id for r in outputs.values()}
    if (not {g.fact_id,x.fact_id,w.fact_id}<=set(before.fact_ids) or not fresh<=set(after.fact_ids)
            or fresh & set(before.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh):raise ValueError("sequence liveness mismatch")
    sm=ir.sm_nodes[t.sm_node_indices[0]];pms=tuple(ir.pm_nodes[p] for p in t.pm_node_indices)
    def check_node(n,rank,ins,side):
        if (n.op!="BW_linear" or n.rank!=rank or not(n.params is None or type(n.params) is list and n.params==[])
                or tuple(n.ins)!=ins or len(n.outs)!=2 or len(set(n.outs))!=2
                or any(n.outs[slot]!=(r.sm_tid if side=="sm" else r.pm_tids[rank]) for slot,r in outputs.items())):
            raise ValueError("sequence writer rank/params/roles mismatch")
    check_node(sm,0,(g.sm_tid,x.sm_tid,w.sm_tid),"sm")
    for r,n in enumerate(pms):check_node(n,r,(g.pm_tids[r],x.pm_tids[r],w.pm_tids[0]),"pm")
    def check_read_source(ref,side,at):
        tid=source_tid(ref,side)
        nodes=ir.sm_nodes if side=="sm" else ir.pm_nodes
        writes=[(index,slot) for index,n in enumerate(nodes[:at])
                for slot,out in enumerate(n.outs) if out==tid]
        expected=f"init:{tid}"
        if writes:
            index,slot=writes[-1]
            if nodes[index].outs.count(tid)!=1:raise ValueError("ambiguous input producer")
            expected=f"{side}:{index}:{slot}"
        if ref!=expected:raise ValueError("input source is not the latest writer before its read point")
    for record in (g,x,w):
        check_read_source(record.source.step_triple[0],"sm",t.sm_node_indices[0])
        for rank,pos in enumerate(t.pm_node_indices):
            ref=record.source.step_triple[1 if record is w else rank+1]
            check_read_source(ref,"pm",pos)
    smframe=list(ir.sm_nodes[ss:se]);pmframe=list(ir.pm_nodes[ps:pe])
    authority={a.fact_id:a for a in chain.authority_facts}
    if chain.anchor_fact is not None:authority[chain.anchor_fact.fact_id]=chain.anchor_fact
    def live_tids(ids):
        ls,lp=set(),set()
        for fid in ids:
            if fid in by_id:
                r=by_id[fid];ls.add(r.sm_tid);lp.update(r.pm_tids)
                if r.joined_pm_tid is not None:lp.add(r.joined_pm_tid)
                if r.metadata_tid is not None:ls.add(r.metadata_tid);lp.add(r.metadata_tid)
                for a,b,c in r.source_tid_triples:ls.add(a);lp.update((b,c))
            elif fid in authority:
                a=authority[fid]
                if a.kind=="tensor_shape" and a.side in ("sm","pm"):(ls if a.side=="sm" else lp).add(a.tid)
                elif a.kind=="tensor_eq" and a.left_side in ("sm","pm") and a.right_side in ("sm","pm"):
                    (ls if a.left_side=="sm" else lp).add(a.left_tid);(ls if a.right_side=="sm" else lp).add(a.right_tid)
                elif a.kind=="gather":ls.add(a.sm_tid);lp.update((a.pm_rank0_tid,a.pm_rank1_tid))
                elif a.kind in ("packed_cu","label_bound") and a.side in ("sm","pm"):(ls if a.side=="sm" else lp).add(a.tid)
                else:raise ValueError("unsupported live authority")
            else:raise ValueError("unknown live fact")
        return ls,lp
    oldsm,oldpm=live_tids(before.fact_ids);livesm,livepm=live_tids(set(before.fact_ids)|set(after.fact_ids))
    for frame,start,owned,live,old,allowed in ((smframe,ss,set(t.sm_node_indices),livesm,oldsm,{r.sm_tid for r in outputs.values()}),
            (pmframe,ps,set(t.pm_node_indices),livepm,oldpm,{u for r in outputs.values() for u in r.pm_tids})):
        for pos,n in enumerate(frame,start):
            if set(n.outs)&(old| (live-(allowed if pos in owned else set()))):raise ValueError("frame overwrites live authority")
        if any(sum(tid in n.outs for n in frame)!=1 for tid in allowed):raise ValueError("output writer ambiguity")
    sn,pn,sf,pf=(f"{segment_id}_{z}" for z in ("sm_nodes","pm_nodes","sm_final","pm_final"))
    lines=[f"private def {sn} : List NodeDecl := [{', '.join(_node_text(n) for n in smframe)}]",f"private def {pn} : List NodeDecl := [{', '.join(_node_text(n) for n in pmframe)}]",
        f"@[irreducible] private def {sf} (s : Store) : Store := {sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",f"@[irreducible] private def {pf} (s : Store) : Store := {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
    def writer(name,graph,fn,nn,frame,pos,n,slot):
        final=f"({fn} store)";th=f"{segment_id}_{name}";expr=f"(bw_linear ({{store}} {n.ins[0]}) ({{store}} {n.ins[1]}) ({{store}} {n.ins[2]})).{slot+1}"
        lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {th} (store : Store) : {final} {n.outs[slot]} = {expr.format(store=final)} := by",f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) store := by unfold {fn}; rfl"])
        helper=_render_mixed_final_value(name="hout",graph=graph,initial_store="store",final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,position=pos,output_tid=n.outs[slot],input_tids=tuple(n.ins),written_tids={v for n in frame for v in n.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_bw_linear_{'snd' if slot else 'fst'}_out {graph} t {n.rank} {' '.join(map(str,(*n.ins,*n.outs)))} (by native_decide)"])
        lines.extend(z[2:] if z.startswith("  ") else z for z in helper);lines.extend(["  exact hout",""]);return th
    writers={slot:(writer(f"hSmWriter{slot}",ir.sm_graph_ref,sf,sn,smframe,t.sm_node_indices[0]-ss,sm,slot),[writer(f"hPmWriter{slot}_{r}",ir.pm_graph_ref,pf,pn,pmframe,p-ps,n,slot) for r,(p,n) in enumerate(zip(t.pm_node_indices,pms))]) for slot in selected}
    vals=lambda r:"["+", ".join(f"pmFinal {u}" for u in r.pm_tids)+"]"
    shape=lambda s:_shape_text(list(s))
    gl,xl=map(vals,(g,x));gf,gs,xf,xs,wf=map(shape,(g.full_shape,g.shard_shape,x.full_shape,x.shard_shape,w.full_shape))
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({sf} smStore) ({pf} pmStore) := by",f" let smFinal := {sf} smStore",f" let pmFinal := {pf} pmStore",f" have hframe : {before.state_id}.Holds smFinal pmFinal := by unfold smFinal pmFinal {sf} {pf}; apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hstate <;> native_decide"])
    for name,r,l,full,local,axis in (("g",g,gl,gf,gs,1),("x",x,xl,xf,xs,1),("w",w,vals(w),wf,wf,0)):
        lines.extend([f" have h{name} : {r.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f" change ShardedRel (smFinal {r.sm_tid}) {l} {axis} {full} {local} at h{name}"])
    lines.append(f" have hwEq : smFinal {w.sm_tid} = pmFinal {w.pm_tids[0]} := by rw [hw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)]; decide)")
    for name,r,l in (("g",g,gl),("x",x,xl)):
        lines.append(f" have h{name}V : smFinal {r.sm_tid} = allGatherPrimDimN 1 {k} 0 {l} := by simpa only [List.length_cons,List.length_nil] using h{name}.full_value")
    for slot,(_,cert,_) in selected.items():
        out=outputs[slot];ol=vals(out);hs,hp=writers[slot];suffix="snd" if slot else "fst";full=wf if slot else xf;local=wf if slot else xs
        lines.append(f" have hS{slot} : smFinal {out.sm_tid} = (bw_linear (smFinal {g.sm_tid}) (smFinal {x.sm_tid}) (smFinal {w.sm_tid})).{slot+1} := {hs} smStore")
        for r,th in enumerate(hp):lines.append(f" have hP{slot}_{r} : pmFinal {out.pm_tids[r]} = (bw_linear (pmFinal {g.pm_tids[r]}) (pmFinal {x.pm_tids[r]}) (pmFinal {w.pm_tids[0]})).{slot+1} := {th} pmStore")
        extra="" if slot else f"(smFinal {x.sm_tid}) "
        lines.extend([f" have hcomm{slot} := {cert.lean_theorem} {k} {b} {s} {o} {i} {gl} {xl} {extra}(pmFinal {w.pm_tids[0]})", "   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes "+("" if slot else "hx.full_shape ")+"(hw.shard_shapes _ (by simp))",f" simp only [List.zipWith] at hcomm{slot}"])
        value=f"tensorSum {ol}" if slot else f"allGatherPrimDimN 1 {k} 0 {ol}"
        lines.extend([f" have hV{slot} : smFinal {out.sm_tid} = {value} := by",f"   rw [hS{slot}, hgV, "+("hxV, " if slot else "")+f"hwEq, hcomm{slot}]","   rw ["+", ".join(f"← hP{slot}_{r}" for r in range(k))+"]",f" have hFull{slot} : (smFinal {out.sm_tid}).shape = {full} := by rw [hS{slot}]; exact bw_linear_3d_{suffix}_shape {b} {s*k} {o} {i} _ _ _ hg.full_shape hx.full_shape hw.full_shape"])
        for r in range(k):lines.append(f" have hShape{slot}_{r} : (pmFinal {out.pm_tids[r]}).shape = {local} := by rw [hP{slot}_{r}]; exact bw_linear_3d_{suffix}_shape {b} {s} {o} {i} _ _ _ (hg.shard_shapes _ (by simp)) (hx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))")
        shapes="simp only [List.forall_mem_cons]; exact ⟨"+", ".join(f"hShape{slot}_{r}" for r in range(k))+", List.forall_mem_nil _⟩"
        lines.append(f" have hout{slot} : {out.fact_id}.Holds smFinal pmFinal := by")
        if slot:
            lines.extend([f"   change ReductionRel (smFinal {out.sm_tid}) {ol} {wf}",f"   have hReduce : smFinal {out.sm_tid} = allReducePrim {ol}.length 0 {ol} := by rw [hV{slot}]; rfl",f"   refine {{ full_value := hReduce, full_shape := hFull{slot}, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }}",f"   · {shapes}",f"   · rw [← hReduce]; exact hFull{slot}"])
        else:
            lines.extend([f"   change ShardedRel (smFinal {out.sm_tid}) {ol} 1 {xf} {xs}",f"   refine {{ full_value := ?_, full_shape := hFull{slot}, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }}",f"   · simpa only [List.length_cons,List.length_nil] using hV{slot}",f"   · {shapes}","   · simp only [List.length_cons,List.length_nil]; decide"])
    freshtext=", ".join(outputs[q].fact_id for q in selected)
    lines.extend([" intro fact hfact",f" have hc : fact ∈ [{freshtext}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{freshtext}] ++ {before.state_id}.facts by native_decide) hfact"," simp only [List.mem_append] at hc"," rcases hc with fresh | old"," · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh","   rcases fresh with "+" | ".join("rfl" for _ in selected),*(f"   · exact hout{q}" for q in selected)," · exact hframe fact old","",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f" smNodes := {sn}",f" pmNodes := {pn}",f" sound := by intro a b h; have z := {segment_id}_sound a b h; unfold {sf} {pf} at z; exact z",""])
    return "\n".join(lines)
