"""One-fold BW_view rank-4 to rank-3 sequence-sharding certificate."""
from __future__ import annotations


def render_closed_bw_view_flatten_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate, _render_mixed_final_value
        from relation_compiler import get_closed_rule_spec
    chain=relation.dependent_chain_plan
    seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=1:
        raise ValueError("BW_view flatten requires one atomic transition")
    tr={t.transition_id:t for t in relation.transition_specs}[seg.transition_ids[0]]
    axes={"bw-view-flatten-sequence-sharded-k-rank":1,"bw-view-flatten-head-sharded-k-rank":2,
          "fw-view-flatten-sequence-sharded-k-rank":1,"fw-view-flatten-head-sharded-k-rank":2}
    if tr.rule_id not in axes:
        raise ValueError("BW_view flatten rule is unsupported")
    dim=axes[tr.rule_id]
    spec=get_closed_rule_spec(tr.rule_id)
    arity=2 if spec.op=="BW_view" else 1
    c=_select_exact_typed_certificate(relation,tr,spec.rule_id,spec.lean_theorems[0],spec.certificate_type,
        lambda c:((c.input_fact,),(c.output_fact,)))
    records={r.source:r for r in chain.relation_facts}
    x,y=records[c.input_fact],records[c.output_fact]
    if any(r.source.layout!="sharded" or r.source.gather_dim!=dim for r in (x,y)):
        raise ValueError("view source/record axis mismatch")
    k=c.rank_count
    if k<1 or len(x.shard_shape)!=4:
        raise ValueError("BW_view flatten rank/shape domain mismatch")
    b,s,n,d=x.shard_shape
    full_in=(b,s*k,n,d) if dim==1 else (b,s,n*k,d)
    full_out=(b,s*k,n*d) if dim==1 else (b,s,n*k*d)
    if (any(v<=0 for v in (b,s,n,d)) or x.kind!="sharded" or y.kind!="sharded"
            or x.gather_dim!=dim or y.gather_dim!=dim
            or x.full_shape!=full_in or y.full_shape!=full_out or y.shard_shape!=(b,s,n*d)
            or len(x.pm_tids)!=k or len(y.pm_tids)!=k):
        raise ValueError("BW_view flatten exact shape/axis authority mismatch")
    states={st.state_id:st for st in chain.states}
    before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if (x.fact_id not in before.fact_ids or y.fact_id not in after.fact_ids
            or not set(after.fact_ids)<=set(before.fact_ids)|{y.fact_id}):
        raise ValueError("BW_view flatten pre/post liveness mismatch")
    if len(tr.sm_node_indices)!=1 or len(tr.pm_node_indices)!=k:
        raise ValueError("BW_view flatten exact 1+K footprint required")
    ss,se=seg.sm_range;ps,pe=seg.pm_range
    if (not set(tr.sm_node_indices)<=set(range(ss,se)) or not set(tr.pm_node_indices)<=set(range(ps,pe))
            or c.sm_step_id!=f"sm:{tr.sm_node_indices[0]}:0"
            or c.pm_step_ids!=tuple(f"pm:{i}:0" for i in tr.pm_node_indices)):
        raise ValueError("BW_view flatten writer footprint mismatch")
    sm=ir.sm_nodes[tr.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in tr.pm_node_indices)
    for node,rank,inp,out,shape in ((sm,0,x.sm_tid,y.sm_tid,y.full_shape),*(
            (node,r,x.pm_tids[r],y.pm_tids[r],y.shard_shape) for r,node in enumerate(pms))):
        if (node.rank!=rank or node.op!=spec.op or len(node.ins)!=arity or node.ins[0]!=inp
                or node.outs!=[out] or tuple(node.params)!=shape):
            raise ValueError("BW_view flatten writer roles/order/parameters mismatch")
    sf=ir.sm_nodes[ss:se];pf=ir.pm_nodes[ps:pe]
    sn,pn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes"
    smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[f"private def {sn}:List NodeDecl := [{', '.join(_node_text(node) for node in sf)}]",
        f"private def {pn}:List NodeDecl := [{', '.join(_node_text(node) for node in pf)}]",
        f"@[irreducible] private def {smf}(z:Store):Store := {sn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) z",
        f"@[irreducible] private def {pmf}(z:Store):Store := {pn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) z"]
    def writer(name,graph,initial,final_name,nodes_name,frame,index,node):
        theorem=f"{segment_id}_{name}";final=f"({final_name} {initial})"
        target=_shape_text(list(node.params));expr=f"fw_view {target} ({{store}} {node.ins[0]})"
        lines.extend([f"private theorem {theorem}({initial}:Store):{final} {node.outs[0]}={expr.format(store=final)}:=by",
            f"  have hfinal:{final}={nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {final_name};rfl"])
        helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,
            final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=index,output_tid=node.outs[0],
            input_tids=(node.ins[0],),written_tids={tid for item in frame for tid in item.outs},expression=expr,
            apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]",
                "simp [applyNodeDistributed,applyNodeRingAttn]",
                f"exact {'applyNode_bw_view_out' if arity==2 else 'applyNode_fw_view_out'} {graph} t {node.rank} {node.params[0]} {_shape_text(list(node.params[1:]))} {' '.join(str(tid) for tid in node.ins)} {node.outs[0]}"])
        lines.extend(line[2:] if line.startswith("  ") else line for line in helper)
        lines.append("  exact hout")
        return theorem
    hs=writer("hSmWriter",ir.sm_graph_ref,"smStore",smf,sn,sf,tr.sm_node_indices[0]-ss,sm)
    hp=[writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pmf,pn,pf,index-ps,node) for r,(index,node) in enumerate(zip(tr.pm_node_indices,pms))]
    xl="["+", ".join(f"pmFinal {tid}" for tid in x.pm_tids)+"]"
    yl="["+", ".join(f"pmFinal {tid}" for tid in y.pm_tids)+"]"
    xf,xs,yf,ys=(_shape_text(list(sh)) for sh in (x.full_shape,x.shard_shape,y.full_shape,y.shard_shape))
    lines.extend(["set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound(smStore pmStore:Store)(hstate:{before.state_id}.Holds smStore pmStore):",
        f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore):=by",
        f"    let smFinal:={smf} smStore",f"    let pmFinal:={pmf} pmStore",
        f"    have hframe:{before.state_id}.Holds smFinal pmFinal:=by",
        f"      unfold smFinal pmFinal {smf} {pmf}",
        f"      apply RelationState.Holds.fold_frame {sn} {pn} smStore pmStore hstate <;> native_decide",
        f"    have hx:{x.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {x.sm_tid}) {xl} {dim} {xf} {xs} at hx",
        f"    have hxV:smFinal {x.sm_tid}=allGatherPrimDimN {dim} {k} 0 {xl}:=by simpa only [List.length_cons,List.length_nil] using hx.full_value",
        f"    have hSm:smFinal {y.sm_tid}=fw_view {yf} (smFinal {x.sm_tid}):={hs} smStore"])
    for r in range(k):
        lines.append(f"    have hPm{r}:pmFinal {y.pm_tids[r]}=fw_view {ys} (pmFinal {x.pm_tids[r]}):={hp[r]} pmStore")
    lines.extend([f"    have hcomm:={c.lean_theorem} {k} {b} {s} {n} {d} {xl}",
        "      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes",
        f"    have hvalue:smFinal {y.sm_tid}=allGatherPrimDimN {dim} {k} 0 {yl}:=by",
        "      rw [hSm,hxV,hcomm]","      simp only [List.map]",
        "      rw ["+", ".join(f"← hPm{r}" for r in range(k))+"]",
        f"    have hout:{y.fact_id}.Holds smFinal pmFinal:=by",
        f"      change ShardedRel (smFinal {y.sm_tid}) {yl} {dim} {yf} {ys}",
        "      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}",
        "      · rw [hSm]; rfl",
        "      · intro piece hmem",
        "        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem",
        "        rcases hmem with "+" | ".join(f"h{r}" for r in range(k))])
    for r in range(k):
        lines.extend([f"        · subst piece; rw [hPm{r}]; rfl"])
    lines.extend(["      · simp only [List.length_cons,List.length_nil]; native_decide",
        "    intro fact hfact",
        f"    have covered:fact∈[{y.fact_id}]++{before.state_id}.facts:=by",
        f"      exact (show {after.state_id}.facts⊆[{y.fact_id}]++{before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered",
        "    rcases covered with rfl | old","    · exact hout","    · exact hframe fact old",
        f"private def {segment_id}:ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes:={sn}",f"  pmNodes:={pn}",f"  sound:=by intro smStore pmStore hstate; have h:={segment_id}_sound smStore pmStore hstate; unfold {smf} {pmf} at h; exact h",""])
    return "\n".join(lines)
