"""Single-fold renderer for BW_multiref sums plus in-place WRED tails."""
from __future__ import annotations


def render_closed_bw_multiref_wred_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankBWMultirefSumCertificate, KRankAllReduceReconstructionCertificate
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankBWMultirefSumCertificate, KRankAllReduceReconstructionCertificate
    rule="bw-multiref-sum-sharded-k-rank"
    contracts={
        (1,2):"TrainVerify.Denote.tensorSum_gather_dim1_4_1_2_32_g181",
        (1,3):"TrainVerify.Denote.tensorSum_triple_gather_dim1_4_1_8_32_g114",
        (2,2):"TrainVerify.Denote.tensorSum_pair_split_dim2_4_1_8_32",
    }
    chain=relation.dependent_chain_plan
    segment=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if segment is None or len(segment.transition_ids)<2:
        raise ValueError("BW_multiref/WRED requires producer plus positive tails")
    transition_map={t.transition_id:t for t in relation.transition_specs}
    transitions=tuple(transition_map[t] for t in segment.transition_ids)
    producers=tuple(t for t in transitions if t.rule_id==rule)
    wred_transitions=tuple(t for t in transitions if t.rule_id=="cross-dp-wred-reconstruction-k-rank")
    if len(producers)!=1 or not wred_transitions or len(transitions)!=1+len(wred_transitions):
        raise ValueError("BW_multiref/WRED family cardinality is malformed")
    transition=producers[0]
    typed=[c for c in relation.certificates if type(c) is KRankBWMultirefSumCertificate
           and c.rule_id==transition.rule_id and c.lean_theorem==transition.lean_theorem
           and tuple(sorted(c.input_facts))==transition.pre_facts and (c.output_fact,)==transition.post_facts]
    if transition.rule_id!=rule or len(typed)!=1:
        raise ValueError("BW_multiref sum requires one exact typed certificate")
    cert=typed[0];arity=len(cert.input_facts)
    if contracts.get((cert.gather_dim,arity))!=cert.lean_theorem:
        raise ValueError("BW_multiref sum theorem/axis/arity identity mismatch")
    wred_certs=[]
    for item in wred_transitions:
        wred_certs.append((item,_select_exact_typed_certificate(
            relation,item,"cross-dp-wred-reconstruction-k-rank",
            "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",
            KRankAllReduceReconstructionCertificate,
            lambda c: ((c.input_fact,), (c.output_fact,)))))
    records={r.source:r for r in chain.relation_facts}
    try:
        inputs=tuple(records[f] for f in cert.input_facts);output=records[cert.output_fact]
        wred_records=[(t,c,records[c.input_fact],records[c.output_fact]) for t,c in wred_certs]
    except KeyError as exc: raise ValueError("BW_multiref sum fact is not materialized") from exc
    states={s.state_id:s for s in chain.states};before,after=states[segment.pre_state_id],states[segment.post_state_id]
    required={r.fact_id for r in inputs}|{pre.fact_id for _,_,pre,_ in wred_records}
    fresh={output.fact_id}|{post.fact_id for _,_,_,post in wred_records}
    if not required<=set(before.fact_ids) or not fresh<=set(after.fact_ids):
        raise ValueError("BW_multiref sum pre/post facts are not live")
    if not set(after.fact_ids)<=(fresh|set(before.fact_ids)):
        raise ValueError("BW_multiref sum post-state introduces an unproved fact")
    k=len(output.pm_tids)
    if (k!=4 or cert.rank_count!=k or arity not in (2,3) or output.kind!="sharded"
            or any(r.kind!="sharded" or len(r.pm_tids)!=k for r in inputs)
            or any((r.full_shape,r.shard_shape,r.gather_dim)!=(output.full_shape,output.shard_shape,output.gather_dim) for r in inputs)):
        raise ValueError("BW_multiref sum metadata is not exact")
    if len(transition.sm_node_indices)!=1 or len(transition.pm_node_indices)!=k:
        raise ValueError("BW_multiref sum footprint is not exact 1+K")
    ss,se=segment.sm_range;ps,pe=segment.pm_range
    if not set(transition.sm_node_indices)<=set(range(ss,se)) or not set(transition.pm_node_indices)<=set(range(ps,pe)):
        raise ValueError("BW_multiref sum writers are outside complete frame")
    sm_frame=list(ir.sm_nodes[ss:se]);pm_frame=list(ir.pm_nodes[ps:pe]);sm=ir.sm_nodes[transition.sm_node_indices[0]]
    pms=tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
    if cert.sm_step_id!=f"sm:{transition.sm_node_indices[0]}:0" or cert.pm_step_ids!=tuple(f"pm:{i}:0" for i in transition.pm_node_indices):
        raise ValueError("BW_multiref sum certificate footprint was tampered")
    if sm.rank!=0 or sm.op!="BW_multiref" or sm.params or tuple(sm.ins)!=tuple(r.sm_tid for r in inputs) or sm.outs!=[output.sm_tid]:
        raise ValueError("BW_multiref sum SM writer roles are not exact")
    if tuple(n.rank for n in pms)!=tuple(range(k)): raise ValueError("BW_multiref sum PM ranks are not ordered")
    for rank,n in enumerate(pms):
        if n.op!="BW_multiref" or n.params or tuple(n.ins)!=tuple(r.pm_tids[rank] for r in inputs) or n.outs!=[output.pm_tids[rank]]:
            raise ValueError("BW_multiref sum PM writer roles/order are not exact")
    wred_nodes=[]
    for t,c,pre,post in wred_records:
        if (t.sm_node_indices!=() or len(t.pm_node_indices)!=1 or c.rank_count!=len(pre.pm_tids)
                or pre.kind!="reduction" or post.kind!="joined" or post.sm_tid!=pre.sm_tid
                or post.joined_pm_tid is None or post.full_shape!=pre.full_shape):
            raise ValueError("BW_multiref/WRED relation authority mismatch")
        index=t.pm_node_indices[0]
        if not ps<=index<pe: raise ValueError("BW_multiref/WRED writer outside frame")
        node=ir.pm_nodes[index]
        if (node.rank!=0 or node.op!="CROSS_DP_WRED" or node.params
                or tuple(node.ins)!=pre.pm_tids or node.outs!=[node.ins[0]]
                or post.joined_pm_tid!=node.outs[0] or c.pm_allreduce_step!=f"pm:{index}:0"):
            raise ValueError("BW_multiref/WRED literal writer mismatch")
        wred_nodes.append((index,node,pre,post))
    smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    frame_name=f"{segment_id}_frameable"
    retired={pre.fact_id for _,_,pre,_ in wred_records}
    frame_ids=tuple(f for f in before.fact_ids if f not in retired)
    lines=["set_option maxHeartbeats 500000 in",
           f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
           f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
           f"@[irreducible] private def {smf} (store : Store) : Store :=",f"  {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
           f"@[irreducible] private def {pmf} (store : Store) : Store :=",f"  {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store",
           f"private def {frame_name} : RelationState where",f"  facts := [{', '.join(frame_ids)}]","  nonempty := by native_decide",""]
    def writer(name,graph,initial,fn,nn,frame,pos,node):
        tn=f"{segment_id}_{name}";final=f"({fn} {initial})";ins="["+", ".join(f"{{store}} {t}" for t in node.ins)+"]";expr=f"tensorSum {ins}"
        lines.extend([f"private theorem {tn} ({initial} : Store) :",f"    {final} {node.outs[0]} = {expr.format(store=final)} := by",
                      f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",f"    unfold {fn}","    rfl"])
        h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,
          position=pos,output_tid=node.outs[0],input_tids=tuple(node.ins),written_tids={t for x in frame for t in x.outs},expression=expr,
          apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                       "simp [applyNodeDistributed, applyNodeRingAttn]",
                       "simpa only [List.map] using "
                       f"(applyNode_bw_multiref_out {graph} t {node.rank} {_shape_text(node.ins)} {node.outs[0]})"])
        lines.extend(x[2:] if x.startswith("  ") else x for x in h);lines.extend(["  exact hout",""]);return tn
    sh=writer("hSmWriter",ir.sm_graph_ref,"smStore",smf,smn,sm_frame,transition.sm_node_indices[0]-ss,sm)
    ph=tuple(writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pm_frame,i-ps,n) for r,(i,n) in enumerate(zip(transition.pm_node_indices,pms)))
    wred_helpers=[]
    for ordinal,(index,node,pre,post) in enumerate(wred_nodes):
        name=f"{segment_id}_wred_writer_{ordinal}";position=index-ps
        prefix=f"({pmn}.take {position})";suffix=f"({pmn}.drop {position+1})";ins="["+", ".join(str(t) for t in node.ins)+"]"
        lines.extend([f"private theorem {name} (pmStore : Store) :",f"    ({pmf} pmStore) {node.outs[0]} = cross_dp_wred ({ins}.map pmStore) := by",
          f"  have hfinal : {pmf} pmStore = {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by",f"    unfold {pmf}","    rfl",
          f"  have hnodes : {pmn} = {prefix} ++ [{_node_text(node)}] ++ {suffix} := by native_decide",
          f"  have hprefix : ({pmf} pmStore) {node.outs[0]} = cross_dp_wred ({ins}.map ({prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore)) := by",
          "    rw [hfinal, hnodes]",f"    exact foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix}",f"      {_node_text(node)} {node.outs[0]}",
          f"      (fun t => cross_dp_wred ({ins}.map t)) (by","        intro t","        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
          "        unfold applyNodeDistributed","        rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",f"        · exact applyNode_cross_dp_wred_out {ir.pm_graph_ref} t 0 {ins} {node.outs[0]}","        · native_decide","        · native_decide","      ) (by native_decide) (by native_decide)"])
        reads=[]
        for rank,tid in enumerate(node.ins):
            read=f"hread{ordinal}_{rank}";reads.append(read);lines.extend([f"  have {read} : ({prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {tid} = pmStore {tid} :=",f"    foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} {prefix} pmStore {tid} (by native_decide) (by native_decide)"])
        lines.extend(["  simp only [List.map] at hprefix ⊢",f"  rw [{', '.join(reads)}] at hprefix","  exact hprefix",""]);wred_helpers.append(name)
    lists=["["+", ".join(f"pmFinal {t}" for t in rec.pm_tids)+"]" for rec in inputs];olist="["+", ".join(f"pmFinal {t}" for t in output.pm_tids)+"]"
    full=_shape_text(list(output.full_shape));shard=_shape_text(list(output.shard_shape));dim=output.gather_dim
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store)",f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
      f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    let smFinal := {smf} smStore",f"    let pmFinal := {pmf} pmStore",
      f"    have hFrameInitial : {frame_name}.Holds smStore pmStore := by","      intro fact hfact",f"      exact hstate fact ((show {frame_name}.facts ⊆ {before.state_id}.facts by native_decide) hfact)",
      f"    have hframe : {frame_name}.Holds smFinal pmFinal := by",f"      unfold smFinal pmFinal {smf} {pmf}",f"      apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hFrameInitial",
      "      · native_decide","      · native_decide","      · native_decide","      · native_decide"])
    for j,(rec,lst) in enumerate(zip(inputs,lists)):
        lines.extend([f"    have hi{j} : {rec.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    change ShardedRel (smFinal {rec.sm_tid}) {lst} {dim} {full} {shard} at hi{j}",
                      f"    have hv{j} : smFinal {rec.sm_tid} = allGatherPrimDimN {dim} {k} 0 {lst} := by","      simpa only [List.length_cons, List.length_nil] using hi"+str(j)+".full_value"])
    lines.extend([f"    have hSmWriter : smFinal {output.sm_tid} = tensorSum [{', '.join(f'smFinal {r.sm_tid}' for r in inputs)}] :=",f"      {sh} smStore"])
    for r,(helper,node) in enumerate(zip(ph,pms)):
        lines.extend([f"    have hPmWriter{r} : pmFinal {output.pm_tids[r]} = tensorSum [{', '.join(f'pmFinal {x.pm_tids[r]}' for x in inputs)}] :=",f"      {helper} pmStore",
                      f"    have hOutShape{r} : (pmFinal {output.pm_tids[r]}).shape = {shard} := by",f"      rw [hPmWriter{r}, tensorSum_shape]",f"      exact hi0.shard_shapes _ (by simp)"])
    if arity == 2 and dim == 2:
        for j in range(arity):
            for r in range(k):
                lines.extend([
                    f"    have hChunk{j}_{r} : chunkPrimDimN {dim} {k} {r} (smFinal {inputs[j].sm_tid}) = pmFinal {inputs[j].pm_tids[r]} := by",
                    f"      rw [hv{j}]",
                    "      simpa only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] using",
                    f"        (chunkPrimDimN_allGatherPrimDimN_dim2_4_1_8_8 {lists[j]} {r} (by native_decide) (by simp only [List.length_cons, List.length_nil]) hi{j}.shard_shapes)",
                ])
        lines.extend([f"    have hcomm := {cert.lean_theorem} (smFinal {inputs[0].sm_tid}) (smFinal {inputs[1].sm_tid}) hi0.full_shape hi1.full_shape",
                      f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {k} 0 {olist} := by",
                      "      rw [hSmWriter, hcomm, "+", ".join(f"hChunk{j}_{r}" for j in range(arity) for r in range(k))+"]",
                      "      rw ["+", ".join(f"← hPmWriter{r}" for r in range(k))+"]"])
    elif arity == 2:
        lines.extend([f"    have hcomm := {cert.lean_theorem}",
                      *(f"      (pmFinal {t})" for rec in inputs for t in rec.pm_tids),
                      *(f"      (hi{j}.shard_shapes (pmFinal {inputs[j].pm_tids[r]}) (by simp))"
                        for j in range(arity) for r in range(k)),
                      f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {k} 0 {olist} := by",
                      "      rw [hSmWriter, hv0, hv1, hcomm]",
                      "      rw ["+", ".join(f"← hPmWriter{r}" for r in range(k))+"]"])
    else:
        for r in range(k):
            lines.extend([
                f"    have hChunk{r} : chunkPrimDimN {dim} {k} {r} (smFinal {inputs[2].sm_tid}) = pmFinal {inputs[2].pm_tids[r]} := by",
                "      rw [hv2]",
                f"      simpa only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] using",
                f"        (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 {lists[2]} {r} (by native_decide) (by simp only [List.length_cons, List.length_nil]) hi2.shard_shapes)",
            ])
        lines.extend([f"    have hcomm := {cert.lean_theorem}",
                      *(f"      (pmFinal {t})" for rec in inputs[:2] for t in rec.pm_tids),
                      f"      (smFinal {inputs[2].sm_tid})",
                      *(f"      (hi{j}.shard_shapes (pmFinal {inputs[j].pm_tids[r]}) (by simp))"
                        for j in range(2) for r in range(k)),
                      "      hi2.full_shape",
                      f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {k} 0 {olist} := by",
                      "      rw [hSmWriter, hv0, hv1, hcomm, "+", ".join(f"hChunk{r}" for r in range(k))+"]",
                      "      rw ["+", ".join(f"← hPmWriter{r}" for r in range(k))+"]"])
    lines.extend([f"    have hOutValueList : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {olist}.length 0 {olist} := by",
                  "      simpa only [List.length_cons, List.length_nil] using hOutValue",f"    have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
                  "      rw [hSmWriter, tensorSum_shape]","      exact hi0.full_shape",f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
                  f"      change ShardedRel (smFinal {output.sm_tid}) {olist} {dim} {full} {shard}","      refine {","        full_value := hOutValueList","        full_shape := hFullShape",
                  "        shards_nonempty := by simp","        gather_dim_lt := hi0.gather_dim_lt","        shard_shapes := ?_","        shape_contract := by",
                  "          simp only [List.length_cons, List.length_nil]","          native_decide","      }","      intro piece hmem","      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
                  "      rcases hmem with "+" | ".join(f"h{r}" for r in range(k))])
    for r in range(k): lines.extend(["      · subst piece",f"        exact hOutShape{r}"])
    fresh_names=["hout"]
    for ordinal,((index,node,pre,post),helper) in enumerate(zip(wred_nodes,wred_helpers)):
        ins="["+", ".join(str(t) for t in node.ins)+"]";shape=_shape_text(list(pre.full_shape));hout=f"houtWred{ordinal}"
        lines.extend([f"    have hinWred{ordinal} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
          f"    change ReductionRel (smStore {pre.sm_tid}) ({ins}.map pmStore) {shape} at hinWred{ordinal}",f"    have hWredWriter{ordinal} := {helper} pmStore",
          f"    change pmFinal {post.joined_pm_tid} = cross_dp_wred ({ins}.map pmStore) at hWredWriter{ordinal}",
          f"    have hWredReduce{ordinal} : pmFinal {post.joined_pm_tid} = allReducePrim ({ins}.map pmStore).length 0 ({ins}.map pmStore) := by",
          f"      rw [hWredWriter{ordinal}]","      exact cross_dp_wred_eq_allReducePrim _ (by simp)",
          f"    have hSmRead{ordinal} : smFinal {pre.sm_tid} = smStore {pre.sm_tid} := by",f"      unfold smFinal {smf}",
          f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref} {smn} smStore {pre.sm_tid} (by native_decide) (by native_decide)",
          f"    have hJoined{ordinal} : smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} := by",f"      rw [hSmRead{ordinal}]",f"      exact hinWred{ordinal}.full_value.trans hWredReduce{ordinal}.symm",
          f"    have {hout} : {post.fact_id}.Holds smFinal pmFinal := by",f"      change smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} ∧ _ ∧ _",f"      refine ⟨hJoined{ordinal}, ?_, ?_⟩",
          f"      · rw [hSmRead{ordinal}]",f"        exact hinWred{ordinal}.full_shape",f"      · rw [← hJoined{ordinal}, hSmRead{ordinal}]",f"        exact hinWred{ordinal}.full_shape"])
        fresh_names.append(hout)
    fresh_ids=[output.fact_id]+[post.fact_id for _,_,_,post in wred_records]
    lines.extend(["    intro fact hfact",f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {frame_name}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {frame_name}.facts by native_decide) hfact",
                  "    simp only [List.mem_append] at covered","    rcases covered with fresh | old","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with "+" | ".join("rfl" for _ in fresh_names),*(f"      · exact {name}" for name in fresh_names),"    · exact hframe fact old","",
                  "set_option maxRecDepth 8192 in",f"private def {segment_id} :",f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by","    intro smStore pmStore hstate",f"    have h := {segment_id}_sound smStore pmStore hstate",f"    unfold {smf} {pmf} at h","    exact h",""])
    return "\n".join(lines)
