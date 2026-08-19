"""Atomic renderer for positive reduction-linear producers plus output linear."""
from __future__ import annotations


def render_closed_mixed_reduction_output_linear_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import (
            KRankOutputShardedLinearCertificate,
            KRankReductionLinearProducerCertificate,
        )
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import (
            KRankOutputShardedLinearCertificate,
            KRankReductionLinearProducerCertificate,
        )

    reduction_rule = "linear-reduction-producer-k-rank"
    output_rule = "linear-output-sharded-k-rank"
    reduction_theorem = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d"
    output_theorem = "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm"
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None:
        raise ValueError("unknown mixed reduction/output linear segment")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    try:
        transitions = tuple(transition_map[item] for item in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("mixed reduction/output linear transition is unresolved") from exc
    if len(transitions) < 2:
        raise ValueError("mixed reduction/output linear family requires a positive producer count")
    if (any(item.rule_id != reduction_rule for item in transitions[:-1])
            or transitions[-1].rule_id != output_rule):
        raise ValueError("mixed reduction/output linear family/order is malformed")

    reductions = tuple(
        _select_exact_typed_certificate(
            relation, transition, reduction_rule, reduction_theorem,
            KRankReductionLinearProducerCertificate,
            lambda cert: (
                tuple(sorted((cert.activation_fact, cert.weight_fact))),
                (cert.output_fact,),
            ),
        )
        for transition in transitions[:-1]
    )
    output = _select_exact_typed_certificate(
        relation, transitions[-1], output_rule, output_theorem,
        KRankOutputShardedLinearCertificate,
        lambda cert: (
            tuple(sorted((cert.activation_fact, cert.weight_fact))),
            (cert.output_fact,),
        ),
    )
    records = {item.source: item for item in chain.relation_facts}
    try:
        reduction_inputs = tuple((records[c.activation_fact], records[c.weight_fact]) for c in reductions)
        reduction_outputs = tuple(records[c.output_fact] for c in reductions)
        joined = records[output.activation_fact]
        output_weight = records[output.weight_fact]
        final_output = records[output.output_fact]
    except KeyError as exc:
        raise ValueError("mixed reduction/output linear fact is not materialized") from exc

    states = {item.state_id: item for item in chain.states}
    try:
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("mixed reduction/output linear state is not materialized") from exc
    required_pre = {
        record.fact_id
        for pair in reduction_inputs for record in pair
    } | {joined.fact_id, output_weight.fact_id}
    required_post = {record.fact_id for record in reduction_outputs} | {final_output.fact_id}
    if not required_pre <= set(before.fact_ids):
        raise ValueError("mixed reduction/output linear pre-state lacks exact input authority")
    if not required_post <= set(after.fact_ids):
        raise ValueError("mixed reduction/output linear post-state omits a produced fact")
    if not set(after.fact_ids) <= (required_post | set(before.fact_ids)):
        raise ValueError("mixed reduction/output linear post-state introduces an unproved fact")

    k = len(joined.pm_tids) if joined.kind == "sharded" else output.rank_count
    if joined.kind != "joined" or joined.pm_tids != () or joined.joined_pm_tid is None:
        raise ValueError("mixed reduction/output linear activation is not canonical joined authority")
    if k <= 0 or output.rank_count != k:
        raise ValueError("mixed reduction/output linear rank authority is empty or inconsistent")
    if (output_weight.kind != "sharded" or output_weight.gather_dim != 0
            or final_output.kind != "sharded" or final_output.gather_dim != 2
            or len(output_weight.pm_tids) != k or len(final_output.pm_tids) != k):
        raise ValueError("mixed reduction/output linear final roles are malformed")
    for cert, (activation, weight), produced in zip(reductions, reduction_inputs, reduction_outputs):
        if (cert.rank_count != k or activation.kind != "sharded" or activation.gather_dim != 2
                or weight.kind != "sharded" or weight.gather_dim != 1
                or produced.kind != "reduction" or len(activation.pm_tids) != k
                or len(weight.pm_tids) != k or len(produced.pm_tids) != k):
            raise ValueError("mixed reduction/output linear producer roles/ranks are malformed")
        if (tuple(activation.full_shape) != cert.activation_full_shape
                or tuple(activation.shard_shape) != cert.activation_shard_shape
                or tuple(weight.full_shape) != cert.weight_full_shape
                or tuple(weight.shard_shape) != cert.weight_shard_shape
                or tuple(produced.full_shape) != cert.output_shape
                or tuple(produced.shard_shape) != cert.output_shape
                or len(cert.activation_full_shape) != 3
                or cert.activation_chunk_dim != 2 or cert.weight_gather_dim != 1
                or cert.activation_full_shape[-1] != k * cert.activation_shard_shape[-1]
                or cert.weight_full_shape[1] != k * cert.weight_shard_shape[1]
                or cert.activation_shard_shape[-1] != cert.weight_shard_shape[1]
                or cert.output_shape != (*cert.activation_full_shape[:-1], cert.weight_full_shape[0])):
            raise ValueError("mixed reduction/output linear producer shapes disagree")
    if (tuple(joined.full_shape) != output.activation_shape
            or tuple(output_weight.full_shape) != output.weight_full_shape
            or tuple(output_weight.shard_shape) != output.weight_shard_shape
            or tuple(final_output.full_shape) != output.output_full_shape
            or tuple(final_output.shard_shape) != output.output_shard_shape):
        raise ValueError("mixed reduction/output linear output shapes disagree")

    sm_range = tuple(range(*segment.sm_range))
    pm_range = tuple(range(*segment.pm_range))
    sm_owned = tuple(index for transition in transitions for index in transition.sm_node_indices)
    pm_owned = tuple(index for transition in transitions for index in transition.pm_node_indices)
    if (len(set(sm_owned)) != len(sm_owned) or set(sm_owned) != set(sm_range)
            or len(set(pm_owned)) != len(pm_owned) or set(pm_owned) != set(pm_range)):
        raise ValueError("mixed reduction/output linear footprints do not exactly partition the component")
    for transition, cert in zip(transitions[:-1], reductions):
        expected_sm = (int(cert.sm_linear_step.split(":")[1]),)
        expected_pm = tuple(int(step.split(":")[1]) for step in cert.pm_linear_steps)
        if transition.sm_node_indices != expected_sm or transition.pm_node_indices != expected_pm:
            raise ValueError("mixed reduction/output linear producer footprint was tampered")
    expected_sm = (int(output.sm_step_id.split(":")[1]),)
    expected_pm = tuple(int(step.split(":")[1]) for step in output.pm_step_ids)
    if transitions[-1].sm_node_indices != expected_sm or transitions[-1].pm_node_indices != expected_pm:
        raise ValueError("mixed reduction/output linear output footprint was tampered")

    def validate_writers(transition, activation, weight, produced, *, joined_input=False):
        if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
            raise ValueError("mixed reduction/output linear writer cardinality is malformed")
        sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
        pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
        if (sm_node.rank != 0 or sm_node.op != "FW_linear" or sm_node.params
                or len(sm_node.ins) != 2 or sm_node.ins != [activation.sm_tid, weight.sm_tid]
                or sm_node.outs != [produced.sm_tid]):
            raise ValueError("mixed reduction/output linear SM roles were tampered")
        if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
            raise ValueError("mixed reduction/output linear PM rank order was tampered")
        for rank, node in enumerate(pm_nodes):
            activation_tid = activation.joined_pm_tid if joined_input else activation.pm_tids[rank]
            if (node.op != "FW_linear" or node.params or len(node.ins) != 2
                    or node.ins != [activation_tid, weight.pm_tids[rank]]
                    or node.outs != [produced.pm_tids[rank]]):
                raise ValueError("mixed reduction/output linear PM roles were tampered")

    for transition, pair, produced in zip(transitions[:-1], reduction_inputs, reduction_outputs):
        validate_writers(transition, pair[0], pair[1], produced)
    validate_writers(transitions[-1], joined, output_weight, final_output, joined_input=True)

    sm_nodes = tuple(ir.sm_nodes[index] for index in sm_range)
    pm_nodes = tuple(ir.pm_nodes[index] for index in pm_range)
    sm_pos = {index: index - segment.sm_range[0] for index in sm_range}
    pm_pos = {index: index - segment.pm_range[0] for index in pm_range}
    smg, pmg = ir.sm_graph_ref, ir.pm_graph_ref
    sid = segment.segment_id
    sm_name, pm_name = f"{sid}_sm_nodes", f"{sid}_pm_nodes"
    lines = [
        "set_option maxHeartbeats 1000000 in",
        f"private def {sm_name} : List NodeDecl := [{', '.join(_node_text(node) for node in sm_nodes)}]",
        f"private def {pm_name} : List NodeDecl := [{', '.join(_node_text(node) for node in pm_nodes)}]", "",
        f"set_option maxHeartbeats 1000000 in",
        f"private def {sid} : ClosedDepSegmentCertificate {smg} {pmg} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_name}", f"  pmNodes := {pm_name}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_name}",
        f"    let pmNodes : List NodeDecl := {pm_name}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {smg}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
    ]

    def fact_hyp(name, record, proposition):
        lines.extend([
            f"    have {name} : {record.fact_id}.Holds smStore pmStore := hstate {record.fact_id} (by native_decide)",
            f"    change {proposition} at {name}",
        ])

    def middle_writer(name, side, absolute_index, node):
        pos = sm_pos[absolute_index] if side == "sm" else pm_pos[absolute_index]
        graph = smg if side == "sm" else pmg
        store = "smStore" if side == "sm" else "pmStore"
        nodes = "smNodes" if side == "sm" else "pmNodes"
        final = "smFinal" if side == "sm" else "pmFinal"
        prefix = f"{nodes}.take {pos}"
        suffix = f"{nodes}.drop {pos + 1}"
        lines.extend([
            f"    have {name} : {final} {node.outs[0]} = fw_linear ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            "      calc",
            f"        {final} {node.outs[0]} = fw_linear (({prefix}).foldl (applyNodeDistributedFaithful {graph}) {store} {node.ins[0]}) (({prefix}).foldl (applyNodeDistributedFaithful {graph}) {store} {node.ins[1]}) := by",
            f"          change ({nodes}.foldl (applyNodeDistributedFaithful {graph}) {store}) {node.outs[0]} = _",
            f"          rw [show {nodes} = {prefix} ++ [{_node_text(node)}] ++ {suffix} by native_decide]",
            f"          apply foldl_faithful_middle_writer {graph} {store} ({prefix}) ({suffix}) {_node_text(node)} {node.outs[0]} (fun t => fw_linear (t {node.ins[0]}) (t {node.ins[1]}))",
            "          · intro t",
            "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
            "            unfold applyNodeDistributed",
            "            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"            · exact applyNode_fw_linear_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            "            · decide", "            · decide", "          · native_decide", "          · native_decide",
            f"        _ = fw_linear ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} ({prefix}) {store} {node.ins[0]} (by native_decide) (by native_decide)]",
            f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} ({prefix}) {store} {node.ins[1]} (by native_decide) (by native_decide)]",
        ])

    reduction_holds = []
    for producer, (cert, transition, pair, produced) in enumerate(
        zip(reductions, transitions[:-1], reduction_inputs, reduction_outputs)
    ):
        activation, weight = pair
        atids = "[" + ", ".join(str(tid) for tid in activation.pm_tids) + "]"
        wtids = "[" + ", ".join(str(tid) for tid in weight.pm_tids) + "]"
        otids = "[" + ", ".join(str(tid) for tid in produced.pm_tids) + "]"
        fact_hyp(
            f"hActivation{producer}", activation,
            f"ShardedRel (smStore {activation.sm_tid}) ({atids}.map pmStore) 2 {_shape_text(list(activation.full_shape))} {_shape_text(list(activation.shard_shape))}",
        )
        fact_hyp(
            f"hReductionWeight{producer}", weight,
            f"ShardedRel (smStore {weight.sm_tid}) ({wtids}.map pmStore) 1 {_shape_text(list(weight.full_shape))} {_shape_text(list(weight.shard_shape))}",
        )
        lines.extend([
            f"    let pmActivationTids{producer} : List Tid := {atids}",
            f"    let pmWeightTids{producer} : List Tid := {wtids}",
            f"    let pmOutputTids{producer} : List Tid := {otids}",
            f"    let rankCount{producer} := pmActivationTids{producer}.length",
        ])
        middle_writer(f"hReductionSm{producer}", "sm", transition.sm_node_indices[0], ir.sm_nodes[transition.sm_node_indices[0]])
        writer_names = []
        chunk_names = []
        shape_names = []
        b, seq, _inner = activation.full_shape
        shard = activation.shard_shape[-1]
        outdim = weight.full_shape[0]
        for rank, absolute_index in enumerate(transition.pm_node_indices):
            node = ir.pm_nodes[absolute_index]
            writer = f"hReductionPm{producer}_{rank}"
            chunk = f"hReductionChunk{producer}_{rank}"
            shape = f"hReductionShape{producer}_{rank}"
            middle_writer(writer, "pm", absolute_index, node)
            writer_names.append(writer); chunk_names.append(chunk); shape_names.append(shape)
            lines.extend([
                f"    have {chunk} : chunkPrim {k} {rank} (smStore {activation.sm_tid}) = pmStore {node.ins[0]} := by",
                f"      rw [hActivation{producer}.full_value]",
                f"      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d {k} {rank} {b} {seq} {shard} (pmActivationTids{producer}.map pmStore)",
                f"        (by simp [rankCount{producer}, pmActivationTids{producer}]) hActivation{producer}.shard_shapes",
                "        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
                f"      simpa [rankCount{producer}, pmActivationTids{producer}] using hcancel",
                f"    have {shape} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(produced.full_shape))} := by",
                f"      rw [{writer}]",
                f"      have ha := hActivation{producer}.shard_shapes (pmStore {node.ins[0]}) (by simp [pmActivationTids{producer}])",
                f"      have hw := hReductionWeight{producer}.shard_shapes (pmStore {node.ins[1]}) (by simp [pmWeightTids{producer}])",
                "      simp [fw_linear, ha, hw]", "      rfl",
            ])
        lines.extend([
            f"    have hReductionWeightGather{producer} : smStore {weight.sm_tid} = allGatherPrim rankCount{producer} 0 (pmWeightTids{producer}.map pmStore) := by",
            f"      change smStore {weight.sm_tid} = allGatherPrim {k} 0 ({wtids}.map pmStore)",
            f"      rw [hReductionWeight{producer}.full_value]",
            f"      have hhead : ((pmWeightTids{producer}.map pmStore).head?.map (fun t => t.shape)).getD [] = {_shape_text(list(weight.shard_shape))} := by",
            f"        simpa [pmWeightTids{producer}] using hReductionWeight{producer}.shard_shapes (pmStore {weight.pm_tids[0]}) (by simp [pmWeightTids{producer}])",
            f"      simpa [rankCount{producer}, pmActivationTids{producer}, pmWeightTids{producer}] using",
            f"        (allGatherPrimDimN_1_eq_allGatherPrim_2d {k} ({wtids}.map pmStore) {outdim} {shard} hhead (by native_decide) (by native_decide))",
            f"    have hReductionFullShape{producer} : (smFinal {produced.sm_tid}).shape = {_shape_text(list(produced.full_shape))} := by",
            f"      rw [hReductionSm{producer}]", f"      simp [fw_linear, hActivation{producer}.full_shape, hReductionWeight{producer}.full_shape]", "      rfl",
            f"    have hReductionValue{producer} : smFinal {produced.sm_tid} = allReducePrim (pmOutputTids{producer}.map pmFinal).length 0 (pmOutputTids{producer}.map pmFinal) := by",
            f"      rw [hReductionSm{producer}, hReductionWeightGather{producer}]",
            f"      have hComm := {reduction_theorem} {k} {b} {seq} {activation.full_shape[-1]} {outdim} {shard} (smStore {activation.sm_tid}) (pmWeightTids{producer}.map pmStore)",
            f"        hActivation{producer}.full_shape (by native_decide) (by simp [rankCount{producer}, pmActivationTids{producer}, pmWeightTids{producer}]) hReductionWeight{producer}.shard_shapes",
            "        (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        ])
        contributions = "[" + ", ".join(
            f"fw_linear (chunkPrim {k} {rank} (smStore {activation.sm_tid})) (pmStore {weight.pm_tids[rank]})"
            for rank in range(k)
        ) + "]"
        lines.extend([
            f"      have hContribs : List.ofFn (fun r : Fin {k} => fw_linear (chunkPrim {k} r.val (smStore {activation.sm_tid})) ((pmWeightTids{producer}.map pmStore).get ⟨r.val, by simpa [pmWeightTids{producer}] using r.isLt⟩)) = {contributions} := by rfl",
            "      rw [hContribs] at hComm",
            f"      simp [rankCount{producer}, pmActivationTids{producer}, pmWeightTids{producer}, pmOutputTids{producer}] at hComm ⊢",
            f"      rw [{', '.join(chunk_names)}] at hComm", "      rw [hComm]",
            f"      rw [{', '.join('← ' + name for name in writer_names)}]",
            f"    have hReductionOut{producer} : {produced.fact_id}.Holds smFinal pmFinal := by",
            f"      change ReductionRel (smFinal {produced.sm_tid}) (pmOutputTids{producer}.map pmFinal) {_shape_text(list(produced.full_shape))}",
            f"      refine {{ full_value := hReductionValue{producer}, full_shape := hReductionFullShape{producer}, contributions_nonempty := by simp [pmOutputTids{producer}], contribution_shapes := ?_, reduced_shape := ?_ }}",
            "      · intro contribution hmem",
            f"        simp only [pmOutputTids{producer}, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
            f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}",
        ])
        lines.extend(f"        · exact {name}" for name in shape_names)
        lines.extend([f"      · rw [← hReductionValue{producer}]", f"        exact hReductionFullShape{producer}"])
        reduction_holds.append(f"hReductionOut{producer}")

    fact_hyp(
        "hJoined", joined,
        f"smStore {joined.sm_tid} = pmStore {joined.joined_pm_tid} ∧ (smStore {joined.sm_tid}).shape = {_shape_text(list(joined.full_shape))} ∧ (pmStore {joined.joined_pm_tid}).shape = {_shape_text(list(joined.full_shape))}",
    )
    ow_tids = "[" + ", ".join(str(tid) for tid in output_weight.pm_tids) + "]"
    out_tids = "[" + ", ".join(str(tid) for tid in final_output.pm_tids) + "]"
    fact_hyp(
        "hOutputWeight", output_weight,
        f"ShardedRel (smStore {output_weight.sm_tid}) ({ow_tids}.map pmStore) 0 {_shape_text(list(output_weight.full_shape))} {_shape_text(list(output_weight.shard_shape))}",
    )
    output_transition = transitions[-1]
    middle_writer("hOutputSm", "sm", output_transition.sm_node_indices[0], ir.sm_nodes[output_transition.sm_node_indices[0]])
    output_writer_names = []
    output_shape_names = []
    b, seq, inner = joined.full_shape
    local_out = output_weight.shard_shape[0]
    for rank, absolute_index in enumerate(output_transition.pm_node_indices):
        node = ir.pm_nodes[absolute_index]
        writer = f"hOutputPm{rank}"; shape = f"hOutputShape{rank}"
        middle_writer(writer, "pm", absolute_index, node)
        output_writer_names.append(writer); output_shape_names.append(shape)
        lines.extend([
            f"    have {shape} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(final_output.shard_shape))} := by",
            f"      rw [{writer}]",
            f"      exact fw_linear_3d_shape {b} {seq} {inner} {local_out} _ _ hJoined.2.2 (hOutputWeight.shard_shapes _ (by simp))",
        ])
    lines.extend([
        f"    have hOutputComm := ({output_theorem} (K := ({ow_tids}.map pmStore).length) (b := {b}) (s := {seq}) (i := {inner}) (o := {local_out}) (x := pmStore {joined.joined_pm_tid}) (ws := {ow_tids}.map pmStore) (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by simp) hJoined.2.2 (fun w hw => hOutputWeight.shard_shapes w hw))",
        f"    have hOutputValue : smFinal {final_output.sm_tid} = allGatherPrimDimN 2 ({out_tids}.map pmFinal).length 0 ({out_tids}.map pmFinal) := by",
        "      rw [hOutputSm, hJoined.1, hOutputWeight.full_value, hOutputComm]",
        "      simp only [List.map, List.length_cons, List.length_nil]",
        f"      rw [{', '.join('← ' + name for name in output_writer_names)}]",
        f"    have hOutputFullShape : (smFinal {final_output.sm_tid}).shape = {_shape_text(list(final_output.full_shape))} := by",
        f"      rw [hOutputValue, allGatherPrimDimN_shape 2 ({out_tids}.map pmFinal).length ({out_tids}.map pmFinal) {_shape_text(list(final_output.shard_shape))}]",
        "      · simp only [List.map, List.length_cons, List.length_nil]", "        native_decide",
        f"      · simp only [List.map, List.head?, Option.map, Option.getD]; exact {output_shape_names[0]}",
        f"    have hOutputOut : {final_output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {final_output.sm_tid}) ({out_tids}.map pmFinal) 2 {_shape_text(list(final_output.full_shape))} {_shape_text(list(final_output.shard_shape))}",
        "      refine { full_value := hOutputValue, full_shape := hOutputFullShape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.map, List.length_cons, List.length_nil] <;> native_decide }",
        "      intro shard hmem", "      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
        f"      rcases hmem with {' | '.join('rfl' for _ in range(k))}",
    ])
    lines.extend(f"      · exact {name}" for name in output_shape_names)
    fresh_ids = [record.fact_id for record in reduction_outputs] + [final_output.fact_id]
    fresh_holds = reduction_holds + ["hOutputOut"]
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        f"      rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}",
    ])
    lines.extend(f"      · exact {name}" for name in fresh_holds)
    lines.extend(["    · exact hframe fact old", ""])
    return "\n".join(lines)
