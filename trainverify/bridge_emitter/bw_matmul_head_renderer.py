"""Head-sharded BW_matmul: exact one/two-projection full-frame replay."""
from __future__ import annotations


def render_closed_bw_matmul_head_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from .relation_compiler import get_closed_rule_spec, bw_matmul_head_shape_spec
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from relation_compiler import get_closed_rule_spec, bw_matmul_head_shape_spec
    spec=get_closed_rule_spec("bw-matmul-head-sharded-k-rank")
    chain=relation.dependent_chain_plan
    seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids) not in (1,2):
        raise ValueError("head BW_matmul requires one or two projections")
    tm={t.transition_id:t for t in relation.transition_specs};rs={r.source:r for r in chain.relation_facts}
    selected=[]
    for tid in seg.transition_ids:
        t=tm[tid]
        if t.lean_theorem not in spec.lean_theorems: raise ValueError("head BW_matmul theorem mismatch")
        c=_select_exact_typed_certificate(relation,t,spec.rule_id,t.lean_theorem,spec.certificate_type,
            lambda c:(tuple(sorted(c.input_facts)),(c.output_fact,)))
        if c.projection not in (".1",".2") or c.family!="head-sharded" or len(c.input_facts)!=3:
            raise ValueError("head BW_matmul projection/family mismatch")
        slot=int(c.projection[1])-1
        if t.lean_theorem!=spec.lean_theorems[slot]: raise ValueError("head BW_matmul theorem/projection mismatch")
        selected.append((t,c,slot,rs[c.output_fact]))
    if len({slot for _,_,slot,_ in selected})!=len(selected): raise ValueError("head BW_matmul repeated projection")
    t,c,_,_=selected[0];g,x,y=(rs[f] for f in c.input_facts);k=c.rank_count
    if k<1 or any(r.kind!="sharded" or r.gather_dim!=1 or r.source.layout!="sharded" or r.source.gather_dim!=1 or len(r.pm_tids)!=k for r in (g,x,y)):
        raise ValueError("head BW_matmul input metadata mismatch")
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if (len(t.sm_node_indices)!=1 or len(t.pm_node_indices)!=k
            or not set(t.sm_node_indices)<=set(range(ss,se)) or not set(t.pm_node_indices)<=set(range(ps,pe))):
        raise ValueError("head BW_matmul footprint mismatch")
    sm=ir.sm_nodes[t.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in t.pm_node_indices)
    if (sm.rank!=0 or tuple(p.rank for p in pms)!=tuple(range(k))
            or any(p.op!="BW_matmul" or p.params or len(p.ins)!=3 or len(p.outs)!=2 or len(set(p.outs))!=2 for p in (sm,*pms))
            or tuple(sm.ins)!=(g.sm_tid,x.sm_tid,y.sm_tid)
            or any(tuple(p.ins)!=(g.pm_tids[r],x.pm_tids[r],y.pm_tids[r]) for r,p in enumerate(pms))):
        raise ValueError("head BW_matmul writer roles/ranks mismatch")
    for tr,cert,slot,out in selected:
        if (cert.rank_count!=k or cert.input_facts!=c.input_facts
                or tr.sm_node_indices!=t.sm_node_indices or tr.pm_node_indices!=t.pm_node_indices
                or cert.sm_step_id!=f"sm:{t.sm_node_indices[0]}:{slot}"
                or cert.pm_step_ids!=tuple(f"pm:{i}:{slot}" for i in t.pm_node_indices)
                or out.kind!="sharded" or out.gather_dim!=1 or cert.output_fact.layout!="sharded" or cert.output_fact.gather_dim!=1 or len(out.pm_tids)!=k
                or sm.outs[slot]!=out.sm_tid or tuple(p.outs[slot] for p in pms)!=out.pm_tids):
            raise ValueError("head BW_matmul shared output authority mismatch")
        b,h,q,n,m=bw_matmul_head_shape_spec(k,(g.full_shape,x.full_shape,y.full_shape),
            (g.shard_shape,x.shard_shape,y.shard_shape),out.full_shape,out.shard_shape,cert.projection,out.kind)
    states={s.state_id:s for s in chain.states};before,after=states[seg.pre_state_id],states[seg.post_state_id]
    fresh=[out.fact_id for _,_,_,out in selected]
    if (not {g.fact_id,x.fact_id,y.fact_id}<=set(before.fact_ids) or not set(fresh)<=set(after.fact_ids)
            or not set(after.fact_ids)<=set(before.fact_ids)|set(fresh)):
        raise ValueError("head BW_matmul live-state mismatch")
    sf=ir.sm_nodes[ss:se];pf=ir.pm_nodes[ps:pe]
    sn,pn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[f"private def {sn}:List NodeDecl:=[{', '.join(_node_text(z) for z in sf)}]",
        f"private def {pn}:List NodeDecl:=[{', '.join(_node_text(z) for z in pf)}]",
        f"@[irreducible] private def {smf}(s:Store):Store:={sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf}(s:Store):Store:={pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s"]
    def writer(name,graph,initial,final_name,nodes_name,frame,index,node,slot):
        th=f"{segment_id}_{name}";final=f"({final_name} {initial})"
        expr=f"(bw_matmul ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) ({{store}} {node.ins[2]})).{slot+1}"
        lines.extend([f"private theorem {th}({initial}:Store):{final} {node.outs[slot]}={expr.format(store=final)}:=by",
            f"  have hfinal:{final}={nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {final_name};rfl"])
        helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",
            nodes_name=nodes_name,nodes=frame,position=index,output_tid=node.outs[slot],input_tids=tuple(node.ins),
            written_tids={tid for z in frame for tid in z.outs},expression=expr,
            apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]",
                "simp [applyNodeDistributed,applyNodeRingAttn]",
                f"exact applyNode_bw_matmul_{'fst' if slot==0 else 'snd'}_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} {node.outs[0]} {node.outs[1]} (by native_decide)"])
        lines.extend(z[2:] if z.startswith("  ") else z for z in helper);lines.append("  exact hout")
        return th
    helpers={}
    for _,_,slot,_ in selected:
        hs=writer(f"hSm{slot}",ir.sm_graph_ref,"smStore",smf,sn,sf,t.sm_node_indices[0]-ss,sm,slot)
        hp=[writer(f"hPm{slot}_{r}",ir.pm_graph_ref,"pmStore",pmf,pn,pf,index-ps,node,slot) for r,(index,node) in enumerate(zip(t.pm_node_indices,pms))]
        helpers[slot]=(hs,hp)
    lines.extend([f"private theorem {segment_id}_transpose_shape (t:Tensor)(a b c d:Nat)(ht:t.shape=[a,b,c,d]):(transpose2d t).shape=[a,b,d,c]:=by",
        "  simp only [transpose2d,ht,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Tensor.mkShape]",
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound(smStore pmStore:Store)(hstate:{before.state_id}.Holds smStore pmStore):{after.state_id}.Holds ({smf} smStore) ({pmf} pmStore):=by",
        f"  let smFinal:={smf} smStore",f"  let pmFinal:={pmf} pmStore",
        f"  have hframe:{before.state_id}.Holds smFinal pmFinal:=by unfold smFinal pmFinal {smf} {pmf};apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hstate <;> native_decide"])
    def vals(r):return "["+", ".join(f"pmFinal {tid}" for tid in r.pm_tids)+"]"
    for name,r in (("g",g),("x",x),("y",y)):
        lines.extend([f"  have h{name}:{r.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",
            f"  change ShardedRel (smFinal {r.sm_tid}) {vals(r)} 1 {_shape_text(list(r.full_shape))} {_shape_text(list(r.shard_shape))} at h{name}",
            f"  have h{name}V:smFinal {r.sm_tid}=allGatherPrimDimN 1 {k} 0 {vals(r)}:=by simpa only [List.length_cons,List.length_nil] using h{name}.full_value"])
    for _,cert,slot,out in selected:
        hs,hp=helpers[slot];ol=vals(out);full=_shape_text(list(out.full_shape));shard=_shape_text(list(out.shard_shape))
        lines.append(f"  have hS{slot}:smFinal {out.sm_tid}=(bw_matmul (smFinal {g.sm_tid}) (smFinal {x.sm_tid}) (smFinal {y.sm_tid})).{slot+1}:={hs} smStore")
        for rank in range(k):
            lines.append(f"  have hP{slot}_{rank}:pmFinal {out.pm_tids[rank]}=(bw_matmul (pmFinal {g.pm_tids[rank]}) (pmFinal {x.pm_tids[rank]}) (pmFinal {y.pm_tids[rank]})).{slot+1}:={hp[rank]} pmStore")
        for rank in range(k):
            lines.append(f"  simp only [bw_matmul,batchedMatmulBwd] at hP{slot}_{rank}")
        lines.extend([f"  have hC{slot}:={cert.lean_theorem} {k} {b} {h} {q} {n} {m} {vals(g)} {vals(x)} {vals(y)}",
            "    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hg.shard_shapes hx.shard_shapes hy.shard_shapes",
            f"  have hV{slot}:smFinal {out.sm_tid}=allGatherPrimDimN 1 {k} 0 {ol}:=by",
            f"    rw [hS{slot},hgV,hxV,hyV,hC{slot}]",
            "    simp only [List.zipWith,bw_matmul,batchedMatmulBwd]",
            "    rw ["+", ".join(f"←hP{slot}_{rank}" for rank in range(k))+"]"])
        def shape_proof(heads,gg,xx,yy):
            if slot==0:return f"fw_matmul_rank4_shape _ _ {b} {heads} {q} {m} {n} {gg} ({segment_id}_transpose_shape _ {b} {heads} {n} {m} {yy})"
            return f"fw_matmul_rank4_shape _ _ {b} {heads} {n} {q} {m} ({segment_id}_transpose_shape _ {b} {heads} {q} {n} {xx}) {gg}"
        lines.extend([f"  have hFull{slot}:(smFinal {out.sm_tid}).shape={full}:=by rw [hS{slot}];exact {shape_proof(h*k,'hg.full_shape','hx.full_shape','hy.full_shape')}",
            f"  have hout{slot}:{out.fact_id}.Holds smFinal pmFinal:=by",
            f"    change ShardedRel (smFinal {out.sm_tid}) {ol} 1 {full} {shard}",
            f"    refine {{full_value:=hV{slot},full_shape:=hFull{slot},shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}}",
            "    · intro piece hmem; simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem",
            "      rcases hmem with "+" | ".join(f"hh{rank}" for rank in range(k))])
        for rank in range(k):
            args=[f"(h{name}.shard_shapes (pmFinal {r.pm_tids[rank]}) (by simp))" for name,r in (("g",g),("x",x),("y",y))]
            lines.append(f"      · subst piece;rw [hP{slot}_{rank}];exact {shape_proof(h,*args)}")
        lines.append("    · simp only [List.length_cons,List.length_nil];native_decide")
    pub="["+", ".join(fresh)+"]"
    lines.extend(["  intro fact hfact",f"  have hc:fact∈{pub}++{before.state_id}.facts:=(show {after.state_id}.facts⊆{pub}++{before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc",
        "  rcases hc with "+("rfl | old" if len(selected)==1 else "(rfl | rfl) | old")])
    lines.extend(f"  · exact hout{slot}" for _,_,slot,_ in selected)
    lines.extend(["  · exact hframe fact old",f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes:={sn}",f"  pmNodes:={pn}",f"  sound:=by intro smStore pmStore h;have hh:={segment_id}_sound smStore pmStore h;unfold {smf} {pmf} at hh;exact hh",""])
    return "\n".join(lines)
