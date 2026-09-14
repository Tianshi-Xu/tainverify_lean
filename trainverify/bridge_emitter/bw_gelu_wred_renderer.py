"""Atomic BW_gelu plus independent in-place WRED; captured DP1 reduction semantics only."""
from __future__ import annotations


def render_closed_bw_gelu_wred_segment(ir, relation, segment_id: str) -> str:
    try:
        from .closed_fact_sources import fact_tids, source_exact
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import get_closed_rule_spec, KRankAllReduceReconstructionCertificate
    except ImportError:
        from closed_fact_sources import fact_tids, source_exact
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import get_closed_rule_spec, KRankAllReduceReconstructionCertificate

    spec = get_closed_rule_spec("bw-gelu-pointwise-sharded-k-rank")
    rule = spec.rule_id
    theorem = spec.lean_theorems[0]
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 2:
        raise ValueError("BW_gelu/WRED requires two exact transitions")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    transitions = [transition_map[item] for item in segment.transition_ids]
    gelus = [item for item in transitions if item.rule_id == rule]
    wreds = [item for item in transitions if item.rule_id == "cross-dp-wred-reconstruction-k-rank"]
    if len(gelus) != 1 or len(wreds) != 1:
        raise ValueError("BW_gelu/WRED family mismatch")
    transition = gelus[0]
    wt = wreds[0]
    wc = _select_exact_typed_certificate(
        relation, wt, "cross-dp-wred-reconstruction-k-rank",
        "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",
        KRankAllReduceReconstructionCertificate,
        lambda c: ((c.input_fact,), (c.output_fact,)),
    )
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda cert: (
            tuple(sorted((cert.gradient_fact, cert.activation_fact))),
            (cert.output_fact,),
        ),
    )
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient = records[certificate.gradient_fact]
        activation = records[certificate.activation_fact]
        output = records[certificate.output_fact]
    except KeyError as exc:
        raise ValueError("BW_gelu fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before,after = states[segment.pre_state_id],states[segment.post_state_id]
    wpre, wpost = records[wc.input_fact], records[wc.output_fact]
    wred_records = [(wt, wc, wpre, wpost)]
    required = {gradient.fact_id, activation.fact_id, wpre.fact_id}
    fresh = {output.fact_id, wpost.fact_id}
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids):
        raise ValueError("BW_gelu/WRED pre/post facts are not live")
    if not set(after.fact_ids) <= fresh | set(before.fact_ids):
        raise ValueError("BW_gelu/WRED unproved publication")
    k=len(output.pm_tids)
    if (k<=0 or certificate.rank_count!=k or certificate.gather_dim!=output.gather_dim
            or gradient.kind!="sharded" or activation.kind!="sharded" or output.kind!="sharded"
            or (gradient.full_shape,gradient.shard_shape,gradient.gather_dim)
               !=(activation.full_shape,activation.shard_shape,activation.gather_dim)
            or (output.full_shape,output.shard_shape,output.gather_dim)
               !=(activation.full_shape,activation.shard_shape,activation.gather_dim)
            or len(gradient.pm_tids)!=k or len(activation.pm_tids)!=k):
        raise ValueError("BW_gelu metadata is not exact")
    if len(transition.sm_node_indices)!=1 or len(transition.pm_node_indices)!=k:
        raise ValueError("BW_gelu footprint is not exact 1+K")
    sm_start,sm_end=segment.sm_range;pm_start,pm_end=segment.pm_range
    if (not set(transition.sm_node_indices)<=set(range(sm_start,sm_end))
            or not set(transition.pm_node_indices)<=set(range(pm_start,pm_end))):
        raise ValueError("BW_gelu writers are outside complete frame")
    sm_frame=list(ir.sm_nodes[sm_start:sm_end]);pm_frame=list(ir.pm_nodes[pm_start:pm_end])
    sm_node=ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes=tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    if (certificate.sm_step_id!=f"sm:{transition.sm_node_indices[0]}:0"
            or certificate.pm_step_ids!=tuple(f"pm:{i}:0" for i in transition.pm_node_indices)):
        raise ValueError("BW_gelu certificate footprint was tampered")
    if (sm_node.rank!=0 or sm_node.op!="BW_gelu" or sm_node.params
            or sm_node.ins!=[gradient.sm_tid,activation.sm_tid]
            or sm_node.outs!=[output.sm_tid]):
        raise ValueError("BW_gelu SM writer roles are not exact")
    if tuple(node.rank for node in pm_nodes)!=tuple(range(k)):
        raise ValueError("BW_gelu PM ranks are not ordered")
    for rank,node in enumerate(pm_nodes):
        if (node.op!="BW_gelu" or node.params
                or node.ins!=[gradient.pm_tids[rank],activation.pm_tids[rank]]
                or node.outs!=[output.pm_tids[rank]]):
            raise ValueError("BW_gelu PM writer roles/order are not exact")

    wred_nodes = []
    for transition, cert, pre, post in wred_records:
        if (transition.sm_node_indices != () or len(transition.pm_node_indices) != 1
                or cert.rank_count != len(pre.pm_tids) or pre.kind != "reduction"
                or post.kind != "joined" or post.sm_tid != pre.sm_tid
                or post.joined_pm_tid is None or post.full_shape != pre.full_shape):
            raise ValueError("BW_gelu/WRED relation authority mismatch")
        index = transition.pm_node_indices[0]
        if not (pm_start <= index < pm_end):
            raise ValueError("BW_gelu/WRED writer lies outside complete PM frame")
        node = ir.pm_nodes[index]
        if (node.rank != 0 or node.op != "CROSS_DP_WRED" or node.params
                or tuple(node.ins) != pre.pm_tids or node.outs != [node.ins[0]]
                or post.joined_pm_tid != node.outs[0]
                or cert.pm_allreduce_step != f"pm:{index}:0"):
            raise ValueError("BW_gelu/WRED literal writer mismatch")
        wred_nodes.append((index, node, pre, post))

    if (not chain.complete or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k
            or wc.rank_count != k or wc.full_shape != wpre.full_shape
            or len(set(segment.transition_ids)) != 2
            or len(transition_map) != len(relation.transition_specs)
            or len(records) != len(chain.relation_facts) or len(states) != len(chain.states)
            or sum(s.segment_id == segment_id for s in chain.segments) != 1):
        raise ValueError("BW_gelu/WRED duplicate or malformed graph/certificate authority")
    if not (0 <= sm_start <= sm_end <= len(ir.sm_nodes) and 0 <= pm_start <= pm_end <= len(ir.pm_nodes)):
        raise ValueError("BW_gelu/WRED frame bounds are invalid")
    for state in (before, after):
        if len(state.fact_ids) != len(set(state.fact_ids)):
            raise ValueError("BW_gelu/WRED duplicate state facts")
    if (fresh & set(before.fact_ids) or wpre.fact_id in after.fact_ids
            or chain.anchor_fact.fact_id not in before.fact_ids
            or chain.anchor_fact.fact_id not in after.fact_ids):
        raise ValueError("BW_gelu/WRED retirement, freshness, or public anchor mismatch")
    for f in (gradient, activation, output):
        shape = list(f.shard_shape)
        if f.gather_dim is None or not 0 <= f.gather_dim < len(shape) or any(n <= 0 for n in shape):
            raise ValueError("BW_gelu/WRED invalid shard shape")
        shape[f.gather_dim] *= k
        if tuple(shape) != f.full_shape:
            raise ValueError("BW_gelu/WRED gather shape contract mismatch")
    for f in (gradient, activation, wpre):
        source_exact(ir, f, sm_start, pm_start, context="BW_gelu/WRED")
    for f in (output, wpost):
        source_exact(ir, f, sm_end, pm_end, context="BW_gelu/WRED")
    all_records = (*chain.relation_facts, *chain.authority_facts, chain.anchor_fact)
    by_id = {f.fact_id: f for f in all_records}
    if len(by_id) != len(all_records):
        raise ValueError("BW_gelu/WRED duplicate materialized fact IDs")
    sm_writes = {t for n in sm_frame for t in n.outs}
    pm_writes = {t for n in pm_frame for t in n.outs}
    for fid in before.fact_ids:
        if fid not in by_id:
            raise ValueError("BW_gelu/WRED missing frame fact")
        if fid == wpre.fact_id:
            continue
        st, pt = fact_tids(by_id[fid])
        if st & sm_writes or pt & pm_writes:
            raise ValueError("BW_gelu/WRED frame overwrites live authority")
    wi = wt.pm_node_indices[0]
    if (wpre.sm_tid in sm_writes
            or any(set(n.outs) & set(wpre.pm_tids) for n in ir.pm_nodes[pm_start:wi])
            or any(wpost.joined_pm_tid in n.outs for n in ir.pm_nodes[wi+1:pm_end])):
        raise ValueError("BW_gelu/WRED requires independent prior reduction authority")
    for side, nodes, tids in (("sm", sm_frame, (output.sm_tid,)), ("pm", pm_frame, output.pm_tids)):
        for tid in tids:
            if sum(tid in n.outs for n in nodes) != 1:
                raise ValueError("BW_gelu/WRED same-store output overwrite")
    transition = gelus[0]
    sm_nodes_name,pm_nodes_name=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes"
    sm_final_name,pm_final_name=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    frame_state_name = f"{segment_id}_frameable"
    frameable_ids = tuple(f for f in before.fact_ids if f != wpre.fact_id)
    lines=[
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store",
        f"private def {frame_state_name} : RelationState where",
        f"  facts := [{', '.join(frameable_ids)}]", "  nonempty := by native_decide", "",
    ]
    def writer(name,graph,initial,final_name,nodes_name,frame,position,node):
        theorem_name=f"{segment_id}_{name}";final=f"({final_name} {initial})"
        expression=f"bw_gelu ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}","    rfl",
        ])
        helper=_render_mixed_final_value(
            name="hout",graph=graph,initial_store=initial,final_store=final,
            final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=position,
            output_tid=node.outs[0],input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_gelu_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            ])
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout",""]);return theorem_name
    sm_helper=writer("hSmWriter",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,
                     sm_frame,transition.sm_node_indices[0]-sm_start,sm_node)
    pm_helpers=tuple(writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pm_final_name,
                            pm_nodes_name,pm_frame,index-pm_start,node)
                     for r,(index,node) in enumerate(zip(transition.pm_node_indices,pm_nodes)))
    wred_helpers = []
    for ordinal, (index, node, pre, post) in enumerate(wred_nodes):
        name = f"{segment_id}_wred_writer_{ordinal}"
        position = index - pm_start
        prefix = f"({pm_nodes_name}.take {position})"
        suffix = f"({pm_nodes_name}.drop {position + 1})"
        inputs = "[" + ", ".join(str(tid) for tid in node.ins) + "]"
        lines.extend([
            f"private theorem {name} (pmStore : Store) :",
            f"    ({pm_final_name} pmStore) {node.outs[0]} = cross_dp_wred ({inputs}.map pmStore) := by",
            f"  have hfinal : {pm_final_name} pmStore = {pm_nodes_name}.foldl",
            f"      (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by",
            f"    unfold {pm_final_name}", "    rfl",
            f"  have hnodes : {pm_nodes_name} = {prefix} ++ [{_node_text(node)}] ++ {suffix} := by native_decide",
            f"  have hprefix : ({pm_final_name} pmStore) {node.outs[0]} =",
            f"      cross_dp_wred ({inputs}.map ({prefix}.foldl",
            f"        (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore)) := by",
            "    rw [hfinal, hnodes]",
            f"    exact foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix}",
            f"      {_node_text(node)} {node.outs[0]}",
            f"      (fun t => cross_dp_wred ({inputs}.map t)) (by",
            "        intro t",
            "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "          (hshuffle := by native_decide) (hunshuffle := by native_decide)",
            "          (hattn := by native_decide)]",
            "        unfold applyNodeDistributed",
            "        rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"        · exact applyNode_cross_dp_wred_out {ir.pm_graph_ref} t 0 {inputs} {node.outs[0]}",
            "        · native_decide", "        · native_decide",
            "      ) (by native_decide) (by native_decide)",
        ])
        read_names = []
        for rank, tid in enumerate(node.ins):
            read_name = f"hread{rank}"
            read_names.append(read_name)
            lines.extend([
                f"  have {read_name} : ({prefix}.foldl",
                f"      (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {tid} = pmStore {tid} :=",
                f"    foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
                f"      {prefix} pmStore {tid} (by native_decide) (by native_decide)",
            ])
        lines.extend(["  simp only [List.map] at hprefix ⊢",
                      f"  rw [{', '.join(read_names)}] at hprefix", "  exact hprefix", ""])
        wred_helpers.append(name)

    glist="["+", ".join(f"pmFinal {t}" for t in gradient.pm_tids)+"]"
    xlist="["+", ".join(f"pmFinal {t}" for t in activation.pm_tids)+"]"
    olist="["+", ".join(f"pmFinal {t}" for t in output.pm_tids)+"]"
    full=_shape_text(list(output.full_shape));shard=_shape_text(list(output.shard_shape));dim=output.gather_dim
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smFinal := {sm_final_name} smStore",f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hFrameInitial : {frame_state_name}.Holds smStore pmStore := by",
        "      intro fact hfact",
        f"      exact hstate fact ((show {frame_state_name}.facts ⊆ {before.state_id}.facts by native_decide) hfact)",
        f"    have hframe : {frame_state_name}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hFrameInitial",
        "      · native_decide","      · native_decide","      · native_decide","      · native_decide",
        f"    have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} {dim} {full} {shard} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {activation.sm_tid}) {xlist} {dim} {full} {shard} at hx",
        f"    have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN {dim} {k} 0 {glist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"    have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN {dim} {k} 0 {xlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"    have hSmWriter : smFinal {output.sm_tid} = bw_gelu (smFinal {gradient.sm_tid}) (smFinal {activation.sm_tid}) :=",
        f"      {sm_helper} smStore",
    ])
    for rank,(helper,node) in enumerate(zip(pm_helpers,pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {output.pm_tids[rank]} = bw_gelu (pmFinal {gradient.pm_tids[rank]}) (pmFinal {activation.pm_tids[rank]}) :=",
            f"      {helper} pmStore",
            f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
            f"      rw [hPmWriter{rank}, bw_gelu_shape]",
            f"      exact hx.shard_shapes _ (by simp)",
        ])
    lines.extend([
        f"    have hcomm := {theorem} {dim} {k} {glist} {xlist} {shard}",
        "      (by omega) (by simp) (by simp)",
        "      (by simpa using hg.shard_shapes _ (by simp))",
        "      (by simpa using hx.shard_shapes _ (by simp))",
        "      (by intro i hi; exact hg.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))",
        "      (by intro i hi; exact hx.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))",
        f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {k} 0 {olist} := by",
        "      rw [hSmWriter, hgValue, hxValue, hcomm]",
        "      simp only [List.zipWith]",
        "      rw ["+", ".join(f"← hPmWriter{r}" for r in range(k))+"]",
        f"    have hOutValueList : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {olist}.length 0 {olist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hOutValue",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
        "      rw [hSmWriter, bw_gelu_shape]","      exact hx.full_shape",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {output.sm_tid}) {olist} {dim} {full} {shard}",
        "      refine {","        full_value := hOutValueList","        full_shape := hFullShape",
        "        shards_nonempty := by simp","        gather_dim_lt := hx.gather_dim_lt",
        "        shard_shapes := ?_","        shape_contract := by",
        "          simp only [List.length_cons, List.length_nil]","          native_decide","      }",
        "      intro piece hmem","      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with "+" | ".join(f"h{r}" for r in range(k)),
    ])
    for rank in range(k):
        lines.extend(["      · subst piece",f"        exact hOutShape{rank}"])
    fresh_names = ["hout"]
    for ordinal, ((index, node, pre, post), helper) in enumerate(zip(wred_nodes, wred_helpers)):
        inputs = "[" + ", ".join(str(tid) for tid in node.ins) + "]"
        shape = _shape_text(list(pre.full_shape))
        hout = f"houtWred{ordinal}"
        lines.extend([
            f"    have hinWred{ordinal} : {pre.fact_id}.Holds smStore pmStore :=",
            f"      hstate {pre.fact_id} (by native_decide)",
            f"    change ReductionRel (smStore {pre.sm_tid}) ({inputs}.map pmStore) {shape} at hinWred{ordinal}",
            f"    have hWredWriter{ordinal} := {helper} pmStore",
            f"    change pmFinal {post.joined_pm_tid} = cross_dp_wred ({inputs}.map pmStore) at hWredWriter{ordinal}",
            f"    have hWredReduce{ordinal} : pmFinal {post.joined_pm_tid} =",
            f"        allReducePrim ({inputs}.map pmStore).length 0 ({inputs}.map pmStore) := by",
            f"      rw [hWredWriter{ordinal}]",
            "      exact cross_dp_wred_eq_allReducePrim _ (by simp)",
            f"    have hSmRead{ordinal} : smFinal {pre.sm_tid} = smStore {pre.sm_tid} := by",
            f"      unfold smFinal {sm_final_name}",
            f"      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref}",
            f"        {sm_nodes_name} smStore {pre.sm_tid} (by native_decide) (by native_decide)",
            f"    have hJoined{ordinal} : smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} := by",
            f"      rw [hSmRead{ordinal}]",
            f"      exact hinWred{ordinal}.full_value.trans hWredReduce{ordinal}.symm",
            f"    have {hout} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} ∧ _ ∧ _",
            f"      refine ⟨hJoined{ordinal}, ?_, ?_⟩",
            f"      · rw [hSmRead{ordinal}]", f"        exact hinWred{ordinal}.full_shape",
            f"      · rw [← hJoined{ordinal}, hSmRead{ordinal}]", f"        exact hinWred{ordinal}.full_shape",
        ])
        fresh_names.append(hout)
    fresh_fact_ids = [output.fact_id, wpost.fact_id]
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_fact_ids)}] ++ {frame_state_name}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_fact_ids)}] ++ {frame_state_name}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with " + " | ".join("rfl" for _ in fresh_names),
        *(f"      · exact {name}" for name in fresh_names),
        "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    have h := {segment_id}_sound smStore pmStore hstate",
        f"    unfold {sm_final_name} {pm_final_name} at h",
        "    exact h", "",
    ])
    return "\n".join(lines)
