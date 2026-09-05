"""Single-fold renderer for shared BW_linear dX/dW projections and optional tails."""
from __future__ import annotations


def render_closed_k_rank_bw_linear_dual_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import (
            KRankBWLinearDxCertificate, KRankBWLinearDwShardedCertificate,
            KRankAllReduceReconstructionCertificate, JoinedBWViewCertificate,
        )
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import (
            KRankBWLinearDxCertificate, KRankBWLinearDwShardedCertificate,
            KRankAllReduceReconstructionCertificate, JoinedBWViewCertificate,
        )

    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) not in (2, 3):
        raise ValueError("dual BW_linear requires dX+dW and at most one optional tail")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    segment_transitions = tuple(transition_map[item] for item in segment.transition_ids)
    transition = next((item for item in segment_transitions
                       if item.rule_id == "bw-linear-dx-row-reduction-rank4"), None)
    dw_transition = next((item for item in segment_transitions
                          if item.rule_id == "bw-linear-dw-output-row-sharded-rank4"), None)
    allreduce_transition = next((item for item in segment_transitions
                                 if item.rule_id == "allreduce-reconstruction-k-rank"), None)
    view_transition = next((item for item in segment_transitions
                            if item.rule_id == "bw-view-joined"), None)
    known = {"bw-linear-dx-row-reduction-rank4", "bw-linear-dw-output-row-sharded-rank4",
             "allreduce-reconstruction-k-rank", "bw-view-joined"}
    if (transition is None or dw_transition is None
            or any(item.rule_id not in known for item in segment_transitions)
            or (allreduce_transition is not None and view_transition is not None)):
        raise ValueError("dual BW_linear transition authority is malformed")
    rule = "bw-linear-dx-row-reduction-rank4"
    theorem_table = {
        ((1, 8, 32), (1, 8, 8), (1, 8, 32), (32, 32), (8, 32), (1, 8, 32)):
            "TrainVerify.Denote.bw_linear_dx_tp_split_dim2_4_g134",
        ((1, 8, 128), (1, 8, 32), (1, 8, 32), (128, 32), (32, 32), (1, 8, 32)):
            "TrainVerify.Denote.bw_linear_dx_tp_split_dim2_4_g175",
        ((1, 8, 32), (1, 8, 8), (1, 8, 128), (32, 128), (8, 128), (1, 8, 128)):
            "TrainVerify.Denote.bw_linear_dx_tp_split_dim2_4_g178",
    }
    if transition.rule_id != rule or transition.lean_theorem not in theorem_table.values():
        raise ValueError("BW_linear dX row-reduction theorem identity mismatch")
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, transition.lean_theorem,
        KRankBWLinearDxCertificate,
        lambda cert: (tuple(sorted(cert.input_facts)), (cert.output_fact,)),
    )
    if certificate.family != "row-reduction" or len(certificate.input_facts) != 3:
        raise ValueError("BW_linear dX certificate has wrong semantic family/arity")
    dw_certificate = _select_exact_typed_certificate(
        relation, dw_transition, "bw-linear-dw-output-row-sharded-rank4",
        dw_transition.lean_theorem, KRankBWLinearDwShardedCertificate,
        lambda cert: (tuple(sorted((cert.gradient_fact, cert.activation_fact,
                                    cert.weight_fact))), (cert.output_fact,)),
    )
    if set((dw_certificate.gradient_fact, dw_certificate.activation_fact,
            dw_certificate.weight_fact)) != set(certificate.input_facts):
        raise ValueError("dual BW_linear dX/dW input authority disagrees")
    allreduce_certificate = None
    if allreduce_transition is not None:
        allreduce_certificate = _select_exact_typed_certificate(
            relation, allreduce_transition, "allreduce-reconstruction-k-rank",
            "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",
            KRankAllReduceReconstructionCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
    view_certificate = None
    if view_transition is not None:
        view_certificate = _select_exact_typed_certificate(
            relation, view_transition, "bw-view-joined",
            "TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view",
            JoinedBWViewCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient, activation, weight = (
            records[source] for source in certificate.input_facts
        )
        output = records[certificate.output_fact]
        dw_output = records[dw_certificate.output_fact]
        reduce_input = records[allreduce_certificate.input_fact] if allreduce_certificate else None
        reduce_output = records[allreduce_certificate.output_fact] if allreduce_certificate else None
        view_input = records[view_certificate.input_fact] if view_certificate else None
        view_output = records[view_certificate.output_fact] if view_certificate else None
    except KeyError as exc:
        raise ValueError("BW_linear dX relation fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {gradient.fact_id, activation.fact_id, weight.fact_id}
    fresh = {output.fact_id, dw_output.fact_id}
    if reduce_input is not None:
        required.add(reduce_input.fact_id); fresh.add(reduce_output.fact_id)
    if view_input is not None:
        required.add(view_input.fact_id); fresh.add(view_output.fact_id)
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids):
        raise ValueError("BW_linear dX pre/post facts are not live")
    if not set(after.fact_ids) <= (fresh | set(before.fact_ids)):
        raise ValueError("BW_linear dX post-state introduces an unproved fact")

    k = len(gradient.pm_tids)
    shape_key = (
        gradient.full_shape, gradient.shard_shape, activation.full_shape,
        weight.full_shape, weight.shard_shape, output.full_shape,
    )
    if (k != 4 or certificate.rank_count != k
            or certificate.output_layout != "reduction" or certificate.gather_dim is not None
            or gradient.kind != "sharded" or gradient.gather_dim != 2
            or activation.kind != "joined" or activation.pm_tids != ()
            or activation.joined_pm_tid is None
            or weight.kind != "sharded" or weight.gather_dim != 0
            or output.kind != "reduction" or len(output.pm_tids) != k
            or activation.shard_shape != activation.full_shape
            or output.shard_shape != output.full_shape
            or gradient.full_shape[:2] != activation.full_shape[:2]
            or output.full_shape != activation.full_shape
            or weight.full_shape != (gradient.full_shape[2], activation.full_shape[2])
            or weight.shard_shape != (gradient.shard_shape[2], activation.full_shape[2])
            or len(weight.pm_tids) != k
            or theorem_table.get(shape_key) != transition.lean_theorem):
        raise ValueError("BW_linear dX row-reduction metadata is not exact")
    if (dw_certificate.rank_count != k or dw_output.kind != "sharded"
            or dw_output.gather_dim != 0 or len(dw_output.pm_tids) != k
            or dw_output.full_shape != weight.full_shape
            or dw_output.shard_shape != weight.shard_shape):
        raise ValueError("BW_linear dW row-sharded metadata is not exact")
    if reduce_input is not None and (
            reduce_input.kind != "reduction" or reduce_output.kind != "joined"
            or reduce_output.sm_tid != reduce_input.sm_tid
            or reduce_output.full_shape != reduce_input.full_shape
            or reduce_output.joined_pm_tid is None):
        raise ValueError("dual BW_linear AllReduce metadata is not exact")

    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("BW_linear dX footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    if (not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("BW_linear dX writers are outside the complete frame")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    if certificate.sm_step_id != f"sm:{transition.sm_node_indices[0]}:0" or (
        certificate.pm_step_ids
        != tuple(f"pm:{index}:0" for index in transition.pm_node_indices)
    ):
        raise ValueError("BW_linear dX certificate footprint was tampered")
    if (dw_transition.sm_node_indices != transition.sm_node_indices
            or dw_transition.pm_node_indices != transition.pm_node_indices
            or dw_certificate.sm_step_id != f"sm:{transition.sm_node_indices[0]}:1"
            or dw_certificate.pm_step_ids
               != tuple(f"pm:{index}:1" for index in transition.pm_node_indices)):
        raise ValueError("BW_linear dW shared-writer footprint was tampered")
    if (sm_node.rank != 0 or sm_node.op != "BW_linear" or sm_node.params
            or len(sm_node.ins) != 3 or len(sm_node.outs) != 2
            or tuple(sm_node.ins) != (gradient.sm_tid, activation.sm_tid, weight.sm_tid)
            or sm_node.outs[0] != output.sm_tid or sm_node.outs[1] != dw_output.sm_tid):
        raise ValueError("BW_linear dX SM writer roles are not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("BW_linear dX PM writer ranks are not ordered")
    for rank, node in enumerate(pm_nodes):
        if (node.op != "BW_linear" or node.params or len(node.ins) != 3
                or len(node.outs) != 2
                or tuple(node.ins) != (
                    gradient.pm_tids[rank], activation.joined_pm_tid,
                    weight.pm_tids[rank],
                )
                or node.outs[0] != output.pm_tids[rank]
                or node.outs[1] != dw_output.pm_tids[rank]):
            raise ValueError("BW_linear dX PM writer roles/order are not exact")
    view_sm_node = view_pm_node = None
    if view_transition is not None:
        if (view_input.kind != "joined" or view_output.kind != "joined"
                or view_input.full_shape != tuple(view_certificate.input_shape)
                or view_output.full_shape != tuple(view_certificate.target_shape)):
            raise ValueError("BW_linear/view joined metadata mismatch")
        view_sm_node = ir.sm_nodes[view_transition.sm_node_indices[0]]
        view_pm_node = ir.pm_nodes[view_transition.pm_node_indices[0]]
        for node in (view_sm_node, view_pm_node):
            if (node.op != "BW_view" or node.ins[0] not in (view_input.sm_tid, view_input.joined_pm_tid)
                    or node.outs[0] not in (view_output.sm_tid, view_output.joined_pm_tid)):
                raise ValueError("BW_linear/view writer mismatch")
    reduce_node = None
    if allreduce_transition is not None:
        if (allreduce_transition.sm_node_indices != ()
                or len(allreduce_transition.pm_node_indices) != 1):
            raise ValueError("dual BW_linear AllReduce footprint is not sparse PM-only")
        reduce_index = allreduce_transition.pm_node_indices[0]
        reduce_node = ir.pm_nodes[reduce_index]
        if (not (pm_start <= reduce_index < pm_end) or reduce_node.rank != 0
                or reduce_node.op != "AllReducePrim" or reduce_node.params
                or tuple(reduce_node.ins) != tuple(reduce_input.pm_tids)
                or reduce_node.outs != [reduce_output.joined_pm_tid]
                or allreduce_certificate.pm_allreduce_step != f"pm:{reduce_index}:0"):
            raise ValueError("dual BW_linear AllReduce writer authority mismatch")

    sm_nodes_name = f"{segment_id}_sm_nodes"
    pm_nodes_name = f"{segment_id}_pm_nodes"
    sm_final_name = f"{segment_id}_sm_final"
    pm_final_name = f"{segment_id}_pm_final"
    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store",
        "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node, slot):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        projection = ".1" if slot == 0 else ".2"
        apply_lemma = "applyNode_bw_linear_fst_out" if slot == 0 else "applyNode_bw_linear_snd_out"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[slot]} =",
            f"      (bw_linear ({final} {node.ins[0]}) ({final} {node.ins[1]}) ({final} {node.ins[2]})){projection} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}",
            "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[slot], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=(
                f"(bw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
                f"({{store}} {node.ins[2]})){projection}"
            ),
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact {apply_lemma} {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.ins[2]} "
                f"{node.outs[0]} {node.outs[1]} (by native_decide)",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = writer(
        "hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
        sm_nodes_name, sm_frame, transition.sm_node_indices[0] - sm_start, sm_node, 0,
    )
    sm_dw_helper = writer(
        "hSmDwWriter", ir.sm_graph_ref, "smStore", sm_final_name,
        sm_nodes_name, sm_frame, transition.sm_node_indices[0] - sm_start, sm_node, 1,
    )
    pm_helpers = [
        writer(
            f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, index - pm_start, node, 0,
        )
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
    ]
    pm_dw_helpers = [
        writer(
            f"hPmDwWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, index - pm_start, node, 1,
        )
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
    ]
    reduce_helper = None
    if reduce_node is not None:
        final = f"({pm_final_name} pmStore)"
        reduce_inputs = "[" + ", ".join(str(tid) for tid in reduce_node.ins) + "]"
        expression = f"allReducePrim {len(reduce_node.ins)} 0 [" + ", ".join(
            f"{{store}} {tid}" for tid in reduce_node.ins
        ) + "]"
        reduce_helper = f"{segment_id}_hAllReduceWriter"
        lines.extend([
            f"private theorem {reduce_helper} (pmStore : Store) :",
            f"    {final} {reduce_node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {pm_nodes_name}.foldl",
            f"      (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by",
            f"    unfold {pm_final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=ir.pm_graph_ref, initial_store="pmStore", final_store=final,
            final_equality="hfinal", nodes_name=pm_nodes_name, nodes=pm_frame,
            position=allreduce_transition.pm_node_indices[0] - pm_start,
            output_tid=reduce_node.outs[0], input_tids=tuple(reduce_node.ins),
            written_tids={tid for item in pm_frame for tid in item.outs},
            expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "unfold applyNodeDistributed",
                "rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
                f"· exact applyNode_allReducePrim_out {ir.pm_graph_ref} t 0 {reduce_inputs} {reduce_node.outs[0]}",
                "· native_decide", "· native_decide",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
    view_sm_helper = view_pm_helper = None
    if view_transition is not None:
        def view_writer(name, graph, initial, final_name, nodes_name, frame, position, node):
            theorem_name=f"{segment_id}_{name}"; final=f"({final_name} {initial})"; shape=_shape_text(list(view_certificate.target_shape))
            lines.extend([f"private theorem {theorem_name} ({initial}:Store) : {final} {node.outs[0]} = fw_view {shape} ({final} {node.ins[0]}) := by",f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {final_name}; rfl"])
            helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=position,output_tid=node.outs[0],input_tids=(node.ins[0],),written_tids={tid for item in frame for tid in item.outs},expression=f"fw_view {shape} ({{store}} {node.ins[0]})",apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.ins[1]} {node.outs[0]}"])
            lines.extend(item[2:] if item.startswith("  ") else item for item in helper);lines.extend(["  exact hout",""]);return theorem_name
        view_sm_helper=view_writer("hViewSm",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,sm_frame,view_transition.sm_node_indices[0]-sm_start,view_sm_node)
        view_pm_helper=view_writer("hViewPm",ir.pm_graph_ref,"pmStore",pm_final_name,pm_nodes_name,pm_frame,view_transition.pm_node_indices[0]-pm_start,view_pm_node)

    glist = "[" + ", ".join(f"pmFinal {tid}" for tid in gradient.pm_tids) + "]"
    wlist = "[" + ", ".join(f"pmFinal {tid}" for tid in weight.pm_tids) + "]"
    olist = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]"
    dwlist = "[" + ", ".join(f"pmFinal {tid}" for tid in dw_output.pm_tids) + "]"
    gfull, gshard = (_shape_text(list(x)) for x in (gradient.full_shape, gradient.shard_shape))
    wfull, wshard = (_shape_text(list(x)) for x in (weight.full_shape, weight.shard_shape))
    oshape = _shape_text(list(output.full_shape))
    lines.extend([
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smFinal := {sm_final_name} smStore",
        f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} 2 {gfull} {gshard} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change smFinal {activation.sm_tid} = pmFinal {activation.joined_pm_tid} ∧",
        f"      (smFinal {activation.sm_tid}).shape = {_shape_text(list(activation.full_shape))} ∧",
        f"      (pmFinal {activation.joined_pm_tid}).shape = {_shape_text(list(activation.full_shape))} at hx",
        f"    have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {weight.sm_tid}) {wlist} 0 {wfull} {wshard} at hw",
        f"    have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 2 4 0 {glist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"    have hwValue : smFinal {weight.sm_tid} = allGatherPrimDimN 0 4 0 {wlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hw.full_value",
        f"    have hSmWriter : smFinal {sm_node.outs[0]} =",
        f"        (bw_linear (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) (smFinal {sm_node.ins[2]})).1 :=",
        f"      {sm_helper} smStore",
        f"    have hSmDwWriter : smFinal {sm_node.outs[1]} =",
        f"        (bw_linear (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) (smFinal {sm_node.ins[2]})).2 :=",
        f"      {sm_dw_helper} smStore",
    ])
    if view_transition is not None:
        target_shape=_shape_text(list(view_certificate.target_shape));input_shape=_shape_text(list(view_certificate.input_shape))
        lines.extend([f"    have hvi : {view_input.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    have hvs := {view_sm_helper} smStore",f"    have hvp := {view_pm_helper} pmStore",f"    change smFinal {view_output.sm_tid} = fw_view {target_shape} (smFinal {view_input.sm_tid}) at hvs",f"    change pmFinal {view_output.joined_pm_tid} = fw_view {target_shape} (pmFinal {view_input.joined_pm_tid}) at hvp",f"    have houtView : {view_output.fact_id}.Holds smFinal pmFinal := by",f"      change smFinal {view_output.sm_tid} = pmFinal {view_output.joined_pm_tid} ∧ _ ∧ _","      rw [hvs, hvp]",f"      exact JoinedRel.fw_view {target_shape} {input_shape} hvi"])
    for rank, (helper, node) in enumerate(zip(pm_helpers, pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {node.outs[0]} =",
            f"        (bw_linear (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) (pmFinal {node.ins[2]})).1 :=",
            f"      {helper} pmStore",
            f"    have hPmDwWriter{rank} : pmFinal {node.outs[1]} =",
            f"        (bw_linear (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) (pmFinal {node.ins[2]})).2 :=",
            f"      {pm_dw_helpers[rank]} pmStore",
            f"    have hgShape{rank} := hg.shard_shapes (pmFinal {gradient.pm_tids[rank]}) (by simp)",
            f"    have hwShape{rank} := hw.shard_shapes (pmFinal {weight.pm_tids[rank]}) (by simp)",
            f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {oshape} := by",
            f"      rw [hPmWriter{rank}]",
            f"      exact bw_linear_3d_fst_shape {gradient.shard_shape[0]} {gradient.shard_shape[1]} {gradient.shard_shape[2]} {activation.full_shape[2]} _ _ _",
            f"        hgShape{rank} hx.2.2 hwShape{rank}",
            f"    have hDwOutShape{rank} : (pmFinal {dw_output.pm_tids[rank]}).shape = {wshard} := by",
            f"      rw [hPmDwWriter{rank}]",
            f"      exact bw_linear_3d_snd_shape {gradient.shard_shape[0]} {gradient.shard_shape[1]} {gradient.shard_shape[2]} {activation.full_shape[2]} _ _ _",
            f"        hgShape{rank} hx.2.2 hwShape{rank}",
        ])
    lines.extend([
        f"    have hcomm := {transition.lean_theorem}",
        *(f"      (pmFinal {tid})" for tid in gradient.pm_tids),
        f"      (pmFinal {activation.joined_pm_tid})",
        *(f"      (pmFinal {tid})" for tid in weight.pm_tids),
        *(f"      hgShape{rank}" for rank in range(k)),
        "      hx.2.2",
        *(f"      hwShape{rank}" for rank in range(k)),
        f"    have hOutValue : smFinal {output.sm_tid} = allReducePrim 4 0 {olist} := by",
        "      rw [hSmWriter, hgValue, hx.1, hwValue, hcomm]",
        "      rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
        f"    have hOutValueList : smFinal {output.sm_tid} =",
        f"        allReducePrim {olist}.length 0 {olist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hOutValue",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {oshape} := by",
        "      rw [hSmWriter]",
        f"      exact bw_linear_3d_fst_shape {gradient.full_shape[0]} {gradient.full_shape[1]} {gradient.full_shape[2]} {activation.full_shape[2]} _ _ _",
        "        hg.full_shape hx.2.1 hw.full_shape",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ReductionRel (smFinal {output.sm_tid}) {olist} {oshape}",
        "      refine {",
        "        full_value := hOutValueList", "        full_shape := hFullShape",
        "        contributions_nonempty := by simp",
        "        contribution_shapes := ?_", "        reduced_shape := ?_", "      }",
        "      · intro contribution hmem",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend(["        · subst contribution", f"          exact hOutShape{rank}"])
    lines.extend([
        "      · rw [← hOutValueList]", "        exact hFullShape",
    ])
    if dw_transition.lean_theorem.endswith("bw_linear_dw_split_dim2_4_g119"):
        for rank in range(k):
            lines.extend([
                f"    have hGradChunk{rank} : chunkPrimDimN 2 4 {rank} (smFinal {gradient.sm_tid}) = pmFinal {gradient.pm_tids[rank]} := by",
                "      rw [hgValue]",
                f"      rw [chunkPrimDimN_allGatherPrimDimN_dim2_4_1_8_8 _ {rank} (by native_decide) (by simp) hg.shard_shapes]",
                "      simp [List.getD]",
            ])
        lines.extend([
            f"    have hDwComm := {dw_transition.lean_theorem}",
            f"      (smFinal {gradient.sm_tid}) (smFinal {activation.sm_tid}) (smFinal {weight.sm_tid})",
            *(f"      (pmFinal {tid})" for tid in weight.pm_tids),
            "      hg.full_shape hx.2.1 hw.full_shape",
            *(f"      hwShape{rank}" for rank in range(k)),
            f"    have hDwValue : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 4 0 {dwlist} := by",
            "      rw [hSmDwWriter, hDwComm, hx.1]",
            "      rw [" + ", ".join(f"hGradChunk{rank}" for rank in range(k)) + "]",
            "      rw [" + ", ".join(f"← hPmDwWriter{rank}" for rank in range(k)) + "]",
        ])
    elif dw_transition.lean_theorem.endswith("bw_linear_dw_osplit_dim2_4_1_8_8_g179"):
        lines.extend([
            f"    have hDwComm := {dw_transition.lean_theorem}",
            f"      (pmFinal {activation.joined_pm_tid})",
            *(f"      (pmFinal {tid})" for tid in gradient.pm_tids),
            *(f"      (pmFinal {tid})" for tid in weight.pm_tids),
            "      hx.2.2",
            *(f"      hgShape{rank}" for rank in range(k)),
            *(f"      hwShape{rank}" for rank in range(k)),
            f"    have hDwValue : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 4 0 {dwlist} := by",
            "      rw [hSmDwWriter, hgValue, hx.1, hwValue, hDwComm]",
            "      rw [" + ", ".join(f"← hPmDwWriter{rank}" for rank in range(k)) + "]",
        ])
    else:
        lines.extend([
            f"    have hDwComm := {dw_transition.lean_theorem}",
            *(f"      (pmFinal {tid})" for tid in gradient.pm_tids),
            f"      (pmFinal {activation.joined_pm_tid})",
            *(f"      (pmFinal {tid})" for tid in weight.pm_tids),
            *(f"      hgShape{rank}" for rank in range(k)),
            "      hx.2.2",
            *(f"      hwShape{rank}" for rank in range(k)),
            f"    have hDwValue : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 4 0 {dwlist} := by",
            "      rw [hSmDwWriter, hgValue, hx.1, hwValue, hDwComm]",
            "      rw [" + ", ".join(f"← hPmDwWriter{rank}" for rank in range(k)) + "]",
        ])
    lines.extend([
        f"    have hDwValueList : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 {dwlist}.length 0 {dwlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hDwValue",
        f"    have hDwFullShape : (smFinal {dw_output.sm_tid}).shape = {wfull} := by",
        "      rw [hSmDwWriter]",
        f"      exact bw_linear_3d_snd_shape {gradient.full_shape[0]} {gradient.full_shape[1]} {gradient.full_shape[2]} {activation.full_shape[2]} _ _ _",
        "        hg.full_shape hx.2.1 hw.full_shape",
        f"    have houtDw : {dw_output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {dw_output.sm_tid}) {dwlist} 0 {wfull} {wshard}",
        "      refine {", "        full_value := hDwValueList", "        full_shape := hDwFullShape",
        "        shards_nonempty := by simp", "        gather_dim_lt := by native_decide",
        "        shard_shapes := ?_", "        shape_contract := by simp", "      }",
        "      intro shard hmem",
        "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend(["      · subst shard", f"        exact hDwOutShape{rank}"])
    if reduce_input is not None:
        reduce_list = "[" + ", ".join(f"pmFinal {tid}" for tid in reduce_input.pm_tids) + "]"
        reduce_shape = _shape_text(list(reduce_input.full_shape))
        lines.extend([
            f"    have hred : {reduce_input.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"    change ReductionRel (smFinal {reduce_input.sm_tid}) {reduce_list} {reduce_shape} at hred",
            f"    have hReduceWriter := {reduce_helper} pmStore",
            f"    change pmFinal {reduce_output.joined_pm_tid} = allReducePrim {len(reduce_input.pm_tids)} 0 {reduce_list} at hReduceWriter",
            f"    have hReduceValue : smFinal {reduce_input.sm_tid} = allReducePrim {len(reduce_input.pm_tids)} 0 {reduce_list} := by",
            "      simpa only [List.length_cons, List.length_nil] using hred.full_value",
            f"    have hReduceJoined : smFinal {reduce_output.sm_tid} = pmFinal {reduce_output.joined_pm_tid} :=",
            "      hReduceValue.trans hReduceWriter.symm",
            f"    have houtReduce : {reduce_output.fact_id}.Holds smFinal pmFinal := by",
            f"      change smFinal {reduce_output.sm_tid} = pmFinal {reduce_output.joined_pm_tid} ∧ _ ∧ _",
            "      refine ⟨hReduceJoined, hred.full_shape, ?_⟩",
            "      rw [← hReduceJoined]", "      exact hred.full_shape",
        ])
    publication=[output.fact_id,dw_output.fact_id]+([reduce_output.fact_id] if reduce_output else [])+([view_output.fact_id] if view_output else [])
    pub_list="["+", ".join(publication)+"]"
    proof_names=["hout","houtDw"]+(["houtReduce"] if reduce_output else [])+(["houtView"] if view_output else [])
    fresh_lines=["      rcases fresh with " + " | ".join("rfl" for _ in proof_names)]
    fresh_lines.extend(f"      · exact {name}" for name in proof_names)
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ {pub_list} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {pub_list} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        *fresh_lines,
        "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    exact {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
