"""Atomic renderer for a positive reduction-linear tuple and optional AllGather."""
from __future__ import annotations


def render_closed_k_rank_reduction_linear_tuple_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankReductionLinearProducerCertificate,
        )
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankReductionLinearProducerCertificate,
        )

    reduction_rule = "linear-reduction-producer-k-rank"
    reduction_theorem2 = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk"
    gather_rule = "allgather-reconstruction-k-rank"
    gather_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None:
        raise ValueError("unknown reduction-linear tuple segment")
    by_id = {item.transition_id: item for item in relation.transition_specs}
    if len(by_id) != len(relation.transition_specs):
        raise ValueError("reduction-linear tuple transition authority is duplicated")
    try:
        transitions = tuple(by_id[item] for item in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("reduction-linear tuple transition is unresolved") from exc
    has_gather = bool(transitions and transitions[-1].rule_id == gather_rule)
    reduction_transitions = transitions[:-1] if has_gather else transitions
    gather_transition = transitions[-1] if has_gather else None
    if not reduction_transitions or any(item.rule_id != reduction_rule for item in reduction_transitions):
        raise ValueError("reduction-linear tuple requires a positive producer prefix")
    if has_gather and (
        gather_transition.lean_theorem != gather_theorem
        or len(gather_transition.pre_facts) != 1
        or len(gather_transition.post_facts) != 1
    ):
        raise ValueError("reduction-linear tuple AllGather theorem/facts are malformed")

    reductions = tuple(
        _select_exact_typed_certificate(
            relation, transition, reduction_rule, transition.lean_theorem,
            KRankReductionLinearProducerCertificate,
            lambda cert: (tuple(sorted((cert.activation_fact, cert.weight_fact))), (cert.output_fact,)),
        )
        for transition in reduction_transitions
    )
    gather = None
    if has_gather:
        gather = _select_exact_typed_certificate(
            relation, gather_transition, gather_rule, gather_theorem,
            KRankAllGatherReconstructionCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )

    sources = tuple(item.source for item in chain.relation_facts)
    if len(sources) != len(set(sources)):
        raise ValueError("reduction-linear tuple relation authority is duplicated")
    records = {item.source: item for item in chain.relation_facts}
    try:
        inputs = tuple((records[cert.activation_fact], records[cert.weight_fact]) for cert in reductions)
        outputs = tuple(records[cert.output_fact] for cert in reductions)
        gather_pre = records[gather.input_fact] if gather is not None else None
        gather_post = records[gather.output_fact] if gather is not None else None
    except KeyError as exc:
        raise ValueError("reduction-linear tuple fact is not materialized") from exc

    states = {item.state_id: item for item in chain.states}
    if len(states) != len(chain.states):
        raise ValueError("reduction-linear tuple state authority is duplicated")
    try:
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("reduction-linear tuple framing state is not materialized") from exc
    if len(set(before.fact_ids)) != len(before.fact_ids) or len(set(after.fact_ids)) != len(after.fact_ids):
        raise ValueError("reduction-linear tuple framing contains duplicate facts")
    required_pre = {record.fact_id for pair in inputs for record in pair}
    required_post = {record.fact_id for record in outputs}
    if gather_pre is not None:
        required_pre.add(gather_pre.fact_id)
        required_post.add(gather_post.fact_id)
    if (
        not required_pre <= set(before.fact_ids)
        or not required_post <= set(after.fact_ids)
        or not set(after.fact_ids) <= set(before.fact_ids) | required_post
    ):
        raise ValueError("reduction-linear tuple pre/post framing is not exhaustive")

    k = int(reductions[0].rank_count)
    if k <= 0 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("reduction-linear tuple graph rank authority is malformed")
    for transition, cert, pair, output in zip(reduction_transitions, reductions, inputs, outputs):
        activation, weight = pair
        expected_theorem = reduction_theorem2 + ("_3d" if len(activation.full_shape) == 3 else "")
        if (
            cert.rank_count != k or transition.lean_theorem != expected_theorem
            or activation.kind != "sharded" or weight.kind != "sharded" or output.kind != "reduction"
            or len(activation.full_shape) not in (2, 3)
            or activation.gather_dim != len(activation.full_shape) - 1
            or weight.gather_dim != 1 or cert.activation_chunk_dim != activation.gather_dim
            or cert.weight_gather_dim != 1
            or len(activation.pm_tids) != k or len(weight.pm_tids) != k or len(output.pm_tids) != k
            or tuple(activation.full_shape) != cert.activation_full_shape
            or tuple(activation.shard_shape) != cert.activation_shard_shape
            or tuple(weight.full_shape) != cert.weight_full_shape
            or tuple(weight.shard_shape) != cert.weight_shard_shape
            or tuple(output.full_shape) != cert.output_shape
            or tuple(output.shard_shape) != cert.output_shape
            or activation.full_shape[-1] != k * activation.shard_shape[-1]
            or weight.full_shape[1] != k * weight.shard_shape[1]
            or activation.shard_shape[-1] != weight.shard_shape[1]
            or output.full_shape != (*activation.full_shape[:-1], weight.full_shape[0])
        ):
            raise ValueError("reduction-linear tuple producer role/shape/theorem authority is malformed")

    sm_range = tuple(range(*segment.sm_range))
    pm_range = tuple(range(*segment.pm_range))
    sm_owned = tuple(index for transition in transitions for index in transition.sm_node_indices)
    pm_owned = tuple(index for transition in transitions for index in transition.pm_node_indices)
    if (
        len(set(sm_owned)) != len(sm_owned) or set(sm_owned) != set(sm_range)
        or len(set(pm_owned)) != len(pm_owned) or set(pm_owned) != set(pm_range)
        or any(index < 0 or index >= len(ir.sm_nodes) for index in sm_owned)
        or any(index < 0 or index >= len(ir.pm_nodes) for index in pm_owned)
    ):
        raise ValueError("reduction-linear tuple footprints do not exactly partition graph authority")
    for transition, cert, pair, output in zip(reduction_transitions, reductions, inputs, outputs):
        activation, weight = pair
        expected_sm = (int(cert.sm_linear_step.split(":")[1]),)
        expected_pm = tuple(int(step.split(":")[1]) for step in cert.pm_linear_steps)
        if transition.sm_node_indices != expected_sm or transition.pm_node_indices != expected_pm:
            raise ValueError("reduction-linear tuple producer footprint was tampered")
        if len(expected_sm) != 1 or len(expected_pm) != k:
            raise ValueError("reduction-linear tuple producer cardinality is malformed")
        sm_node = ir.sm_nodes[expected_sm[0]]
        pm_nodes = tuple(ir.pm_nodes[index] for index in expected_pm)
        if (
            sm_node.rank != 0 or sm_node.op != "FW_linear" or sm_node.params
            or sm_node.ins != [activation.sm_tid, weight.sm_tid] or sm_node.outs != [output.sm_tid]
            or tuple(node.rank for node in pm_nodes) != tuple(range(k))
        ):
            raise ValueError("reduction-linear tuple SM/PM roles were tampered")
        for rank, node in enumerate(pm_nodes):
            if (
                node.op != "FW_linear" or node.params
                or node.ins != [activation.pm_tids[rank], weight.pm_tids[rank]]
                or node.outs != [output.pm_tids[rank]]
            ):
                raise ValueError("reduction-linear tuple PM roles were tampered")

    gather_node = None
    if gather is not None:
        if gather_transition.sm_node_indices or len(gather_transition.pm_node_indices) != 1:
            raise ValueError("reduction-linear tuple AllGather footprint is malformed")
        gather_index = gather_transition.pm_node_indices[0]
        gather_node = ir.pm_nodes[gather_index]
        dim = int(gather.gather_dim)
        reconstructed = list(gather_pre.shard_shape)
        if (
            gather.pm_allgather_step != f"pm:{gather_index}:0"
            or gather.rank_count != k or gather_node.op != "AllGatherPrim" or gather_node.rank != 0
            or tuple(gather_node.params or ()) != (dim,) or tuple(gather_node.ins) != gather_pre.pm_tids
            or len(gather_node.outs) != 1 or gather_pre.kind != "sharded" or gather_pre.gather_dim != dim
            or gather_post.kind != "joined" or gather_post.sm_tid != gather_pre.sm_tid
            or gather_post.joined_pm_tid != gather_node.outs[0] or len(gather_pre.pm_tids) != k
            or dim < 0 or dim >= len(reconstructed)
            or tuple(gather_pre.full_shape) != gather.full_shape
            or tuple(gather_pre.shard_shape) != gather.shard_shape
            or tuple(gather_post.full_shape) != gather.full_shape
        ):
            raise ValueError("reduction-linear tuple AllGather authority is malformed")
        reconstructed[dim] *= k
        if tuple(reconstructed) != tuple(gather_pre.full_shape):
            raise ValueError("reduction-linear tuple AllGather reconstruction is inexact")

    sm_nodes = tuple(ir.sm_nodes[index] for index in sm_range)
    pm_nodes = tuple(ir.pm_nodes[index] for index in pm_range)
    sm_pos = {index: index - segment.sm_range[0] for index in sm_range}
    pm_pos = {index: index - segment.pm_range[0] for index in pm_range}
    smg, pmg, sid = ir.sm_graph_ref, ir.pm_graph_ref, segment.segment_id
    sm_name, pm_name = f"{sid}_sm_nodes", f"{sid}_pm_nodes"
    lines = [
        "set_option maxHeartbeats 1000000 in",
        f"private def {sm_name} : List NodeDecl := [{', '.join(_node_text(node) for node in sm_nodes)}]",
        f"private def {pm_name} : List NodeDecl := [{', '.join(_node_text(node) for node in pm_nodes)}]", "",
        "set_option maxHeartbeats 1000000 in",
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

    def middle_linear(name, side, absolute_index, node):
        pos = sm_pos[absolute_index] if side == "sm" else pm_pos[absolute_index]
        graph, store, nodes, final = ((smg, "smStore", "smNodes", "smFinal") if side == "sm" else (pmg, "pmStore", "pmNodes", "pmFinal"))
        prefix, suffix = f"{nodes}.take {pos}", f"{nodes}.drop {pos + 1}"
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

    fresh = []
    for producer, (cert, transition, pair, output) in enumerate(zip(reductions, reduction_transitions, inputs, outputs)):
        activation, weight = pair
        atids = "[" + ", ".join(map(str, activation.pm_tids)) + "]"
        wtids = "[" + ", ".join(map(str, weight.pm_tids)) + "]"
        otids = "[" + ", ".join(map(str, output.pm_tids)) + "]"
        fact_hyp(f"hActivation{producer}", activation, f"ShardedRel (smStore {activation.sm_tid}) ({atids}.map pmStore) {activation.gather_dim} {_shape_text(list(activation.full_shape))} {_shape_text(list(activation.shard_shape))}")
        fact_hyp(f"hWeight{producer}", weight, f"ShardedRel (smStore {weight.sm_tid}) ({wtids}.map pmStore) 1 {_shape_text(list(weight.full_shape))} {_shape_text(list(weight.shard_shape))}")
        lines.extend([
            f"    let pmActivationTids{producer} : List Tid := {atids}",
            f"    let pmWeightTids{producer} : List Tid := {wtids}",
            f"    let pmOutputTids{producer} : List Tid := {otids}",
            f"    let rankCount{producer} := pmActivationTids{producer}.length",
        ])
        middle_linear(f"hSm{producer}", "sm", transition.sm_node_indices[0], ir.sm_nodes[transition.sm_node_indices[0]])
        writers, chunks, shapes = [], [], []
        dims = tuple(activation.full_shape)
        shard, outdim = activation.shard_shape[-1], weight.full_shape[0]
        cancel = "TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d" if len(dims) == 3 else "TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_2d"
        for rank, absolute_index in enumerate(transition.pm_node_indices):
            node = ir.pm_nodes[absolute_index]
            writer, chunk, shape = f"hPm{producer}_{rank}", f"hChunk{producer}_{rank}", f"hShape{producer}_{rank}"
            middle_linear(writer, "pm", absolute_index, node)
            writers.append(writer); chunks.append(chunk); shapes.append(shape)
            cancel_args = f"{k} {rank} " + " ".join(str(x) for x in dims[:-1]) + f" {shard}"
            positivity = " (by native_decide)" * (5 if len(dims) == 3 else 3)
            lines.extend([
                f"    have {chunk} : chunkPrim {k} {rank} (smStore {activation.sm_tid}) = pmStore {node.ins[0]} := by",
                f"      rw [hActivation{producer}.full_value]",
                f"      have hcancel := {cancel} {cancel_args} (pmActivationTids{producer}.map pmStore)",
                f"        (by simp [rankCount{producer}, pmActivationTids{producer}]) hActivation{producer}.shard_shapes{positivity}",
                f"      simpa [rankCount{producer}, pmActivationTids{producer}] using hcancel",
                f"    have {shape} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(output.full_shape))} := by",
                f"      rw [{writer}]",
                f"      have ha := hActivation{producer}.shard_shapes (pmStore {node.ins[0]}) (by simp [pmActivationTids{producer}])",
                f"      have hw := hWeight{producer}.shard_shapes (pmStore {node.ins[1]}) (by simp [pmWeightTids{producer}])",
                "      simp [fw_linear, ha, hw]", "      rfl",
            ])
        lines.extend([
            f"    have hWeightGather{producer} : smStore {weight.sm_tid} = allGatherPrim rankCount{producer} 0 (pmWeightTids{producer}.map pmStore) := by",
            f"      change smStore {weight.sm_tid} = allGatherPrim {k} 0 ({wtids}.map pmStore)",
            f"      rw [hWeight{producer}.full_value]",
            f"      have hhead : ((pmWeightTids{producer}.map pmStore).head?.map (fun t => t.shape)).getD [] = {_shape_text(list(weight.shard_shape))} := by",
            f"        simpa [pmWeightTids{producer}] using hWeight{producer}.shard_shapes (pmStore {weight.pm_tids[0]}) (by simp [pmWeightTids{producer}])",
            f"      simpa [rankCount{producer}, pmActivationTids{producer}, pmWeightTids{producer}] using",
            f"        (allGatherPrimDimN_1_eq_allGatherPrim_2d {k} ({wtids}.map pmStore) {outdim} {shard} hhead (by native_decide) (by native_decide))",
            f"    have hFullShape{producer} : (smFinal {output.sm_tid}).shape = {_shape_text(list(output.full_shape))} := by",
            f"      rw [hSm{producer}]", f"      simp [fw_linear, hActivation{producer}.full_shape, hWeight{producer}.full_shape]", "      rfl",
            f"    have hValue{producer} : smFinal {output.sm_tid} = allReducePrim (pmOutputTids{producer}.map pmFinal).length 0 (pmOutputTids{producer}.map pmFinal) := by",
            f"      rw [hSm{producer}, hWeightGather{producer}]",
        ])
        theorem = cert.lean_theorem
        if len(dims) == 3:
            b, seq, inner = dims
            lines.extend([
                f"      have hComm := {theorem} {k} {b} {seq} {inner} {outdim} {shard} (smStore {activation.sm_tid}) (pmWeightTids{producer}.map pmStore)",
                f"        hActivation{producer}.full_shape (by native_decide) (by simp [rankCount{producer}, pmActivationTids{producer}, pmWeightTids{producer}]) hWeight{producer}.shard_shapes",
                "        (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
            ])
        else:
            batch, inner = dims
            lines.extend([
                f"      have hComm := {theorem} {k} {batch} {inner} {outdim} {shard} (smStore {activation.sm_tid}) (pmWeightTids{producer}.map pmStore)",
                f"        hActivation{producer}.full_shape (by native_decide) (by simp [rankCount{producer}, pmActivationTids{producer}, pmWeightTids{producer}]) hWeight{producer}.shard_shapes",
                "        (by native_decide) (by native_decide)",
            ])
        contributions = "[" + ", ".join(f"fw_linear (chunkPrim {k} {rank} (smStore {activation.sm_tid})) (pmStore {weight.pm_tids[rank]})" for rank in range(k)) + "]"
        lines.extend([
            f"      have hContribs : List.ofFn (fun r : Fin {k} => fw_linear (chunkPrim {k} r.val (smStore {activation.sm_tid})) ((pmWeightTids{producer}.map pmStore).get ⟨r.val, by simpa [pmWeightTids{producer}] using r.isLt⟩)) = {contributions} := by rfl",
            "      rw [hContribs] at hComm",
            f"      simp [rankCount{producer}, pmActivationTids{producer}, pmWeightTids{producer}, pmOutputTids{producer}] at hComm ⊢",
            f"      rw [{', '.join(chunks)}] at hComm", "      rw [hComm]",
            f"      rw [{', '.join('← ' + name for name in writers)}]",
            f"    have hOut{producer} : {output.fact_id}.Holds smFinal pmFinal := by",
            f"      change ReductionRel (smFinal {output.sm_tid}) (pmOutputTids{producer}.map pmFinal) {_shape_text(list(output.full_shape))}",
            f"      refine {{ full_value := hValue{producer}, full_shape := hFullShape{producer}, contributions_nonempty := by simp [pmOutputTids{producer}], contribution_shapes := ?_, reduced_shape := ?_ }}",
            "      · intro contribution hmem",
            f"        simp only [pmOutputTids{producer}, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
            f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}",
        ])
        lines.extend(f"        · exact {name}" for name in shapes)
        lines.extend([f"      · rw [← hValue{producer}]", f"        exact hFullShape{producer}"])
        fresh.append((output.fact_id, f"hOut{producer}"))

    if gather is not None:
        dim = gather.gather_dim
        tids = "[" + ", ".join(map(str, gather_pre.pm_tids)) + "]"
        full, shard = _shape_text(list(gather_pre.full_shape)), _shape_text(list(gather_pre.shard_shape))
        pos = pm_pos[gather_transition.pm_node_indices[0]]
        prefix, suffix = f"(pmNodes.take {pos})", f"(pmNodes.drop {pos + 1})"
        lines.extend([
            f"    let gatherInputTids : List Tid := {tids}",
            "    let rankCount := gatherInputTids.length",
            f"    have hRankCount : rankCount = {k} := by native_decide",
            f"    have hRankGraph : rankCount = {pmg}.numRanks := by native_decide",
            f"    have hGatherBefore : gatherInputTids.map (({prefix}).foldl (applyNodeDistributedFaithful {pmg}) pmStore) = gatherInputTids.map pmStore := by",
            "      apply List.map_congr_left", "      intro tid htid",
            "      simp only [gatherInputTids, List.mem_cons, List.not_mem_nil, or_false] at htid",
            f"      rcases htid with {' | '.join(f'h{i}' for i in range(k))}",
        ])
        for tid in gather_pre.pm_tids:
            lines.extend(["      · subst tid", f"        exact foldl_applyNodeDistributedFaithful_at_not_written {pmg} {prefix} pmStore {tid} (by native_decide) (by native_decide)"])
        lines.extend([
            "    have hGatherFinal : gatherInputTids.map pmFinal = gatherInputTids.map pmStore := by",
            "      apply List.map_congr_left", "      intro tid htid",
            "      simp only [gatherInputTids, List.mem_cons, List.not_mem_nil, or_false] at htid",
            f"      rcases htid with {' | '.join(f'h{i}' for i in range(k))}",
        ])
        for tid in gather_pre.pm_tids:
            lines.extend(["      · subst tid", f"        exact foldl_applyNodeDistributedFaithful_at_not_written {pmg} pmNodes pmStore {tid} (by native_decide) (by native_decide)"])
        lines.extend([
            f"    have hGatherWriter : pmFinal {gather_node.outs[0]} = allGatherPrimDimN {dim} rankCount 0 (gatherInputTids.map pmFinal) := by",
            f"      change (pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore) {gather_node.outs[0]} = _",
            f"      rw [show pmNodes = {prefix} ++ [{_node_text(gather_node)}] ++ {suffix} by native_decide]",
            f"      rw [foldl_faithful_middle_writer {pmg} pmStore {prefix} {suffix} {_node_text(gather_node)} {gather_node.outs[0]} (fun t => allGatherPrimDimN {dim} rankCount 0 (gatherInputTids.map t))]",
            "      · rw [hGatherBefore, hGatherFinal]", "      · intro t",
            "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
            "        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]",
            "        rw [hRankGraph]",
            f"        simpa [gatherInputTids] using applyNode_allGatherPrimDimN_out {pmg} t 0 gatherInputTids {gather_node.outs[0]} {dim}",
            "      · native_decide", "      · native_decide",
            f"    have hinGather : {gather_pre.fact_id}.Holds smFinal pmFinal := hframe {gather_pre.fact_id} (by native_decide)",
            f"    change ShardedRel (smFinal {gather_pre.sm_tid}) (gatherInputTids.map pmFinal) {dim} {full} {shard} at hinGather",
            f"    have hJoined : smFinal {gather_pre.sm_tid} = pmFinal {gather_node.outs[0]} := ({gather_theorem} hinGather).trans hGatherWriter.symm",
            f"    have houtGather : {gather_post.fact_id}.Holds smFinal pmFinal := by",
            f"      change smFinal {gather_pre.sm_tid} = pmFinal {gather_node.outs[0]} ∧ (smFinal {gather_pre.sm_tid}).shape = {full} ∧ (pmFinal {gather_node.outs[0]}).shape = {full}",
            "      refine ⟨hJoined, hinGather.full_shape, ?_⟩", "      rw [← hJoined]", "      exact hinGather.full_shape",
        ])
        fresh.append((gather_post.fact_id, "houtGather"))

    fresh_ids = "[" + ", ".join(fid for fid, _ in fresh) + "]"
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ {fresh_ids} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {fresh_ids} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with new | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new",
        f"      rcases new with {' | '.join(f'h{i}' for i in range(len(fresh)))}",
    ])
    for _, proof in fresh:
        lines.extend(["      · subst fact", f"        exact {proof}"])
    lines.extend(["    · exact hframe fact old", ""])
    return "\n".join(lines)
