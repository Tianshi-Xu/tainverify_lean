"""Atomic renderer for independent K-rank LayerNorm and AllToAll axes."""
from __future__ import annotations


def render_closed_mixed_k_rank_layernorm_alltoall_segment(
    ir, relation, segment_id: str
) -> str:
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate
        from .relation_compiler import (
            KRankAllToAllRelationCertificate,
            KRankLocalRelationCertificate,
            TransitionAuthorityRequirement,
        )
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate
        from relation_compiler import (
            KRankAllToAllRelationCertificate,
            KRankLocalRelationCertificate,
            TransitionAuthorityRequirement,
        )

    layer_rule = "layernorm-sharded-k-rank-dim1"
    alltoall_rule = "alltoall-k-rank-layout-transport"
    layer_theorem = (
        "TrainVerify.Denote."
        "fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d"
    )
    alltoall_theorem = (
        "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    )
    expected_family = (layer_rule, alltoall_rule)

    chain = relation.dependent_chain_plan
    segments = [item for item in chain.segments if item.segment_id == segment_id]
    if len(segments) != 1:
        raise ValueError("mixed LayerNorm/AllToAll requires one exact component")
    segment = segments[0]
    if (
        len(segment.transition_ids) != 2
        or len(set(segment.transition_ids)) != 2
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll requires two distinct transitions"
        )
    transitions = []
    for transition_id in segment.transition_ids:
        matches = [
            item
            for item in relation.transition_specs
            if item.transition_id == transition_id
        ]
        if len(matches) != 1:
            raise ValueError(
                "mixed LayerNorm/AllToAll transition identity is not unique"
            )
        transitions.append(matches[0])
    transitions = tuple(transitions)
    if tuple(item.rule_id for item in transitions) != expected_family:
        raise ValueError(
            "mixed LayerNorm/AllToAll transition order is not registered"
        )
    expected_classes = (
        KRankLocalRelationCertificate.__name__,
        KRankAllToAllRelationCertificate.__name__,
    )
    for transition, class_name in zip(transitions, expected_classes):
        identity = transition.transition_id.split(":", 2)
        if (
            len(identity) != 3
            or identity[1] != class_name
            or identity[2] != transition.rule_id
        ):
            raise ValueError(
                "mixed LayerNorm/AllToAll certificate identity is malformed"
            )

    layer_transition, alltoall_transition = transitions
    layer_cert = _select_exact_typed_certificate(
        relation,
        layer_transition,
        layer_rule,
        layer_theorem,
        KRankLocalRelationCertificate,
        lambda cert: ((cert.input_fact,), (cert.output_fact,)),
    )
    alltoall_cert = _select_exact_typed_certificate(
        relation,
        alltoall_transition,
        alltoall_rule,
        alltoall_theorem,
        KRankAllToAllRelationCertificate,
        lambda cert: ((cert.input_fact,), (cert.output_fact,)),
    )
    if (
        layer_cert.op != "FW_layernorm"
        or layer_cert.gather_dim != 1
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll certificate roles are inconsistent"
        )
    expected_authority = tuple(
        requirement
        for tid, shape in zip(
            layer_cert.external_tids, layer_cert.external_shapes
        )
        for requirement in (
            TransitionAuthorityRequirement(
                "tensor_eq", ("sm", "pm"), (tid, tid)
            ),
            TransitionAuthorityRequirement(
                "tensor_shape", ("pm",), (tid,), shape
            ),
        )
    )
    if (
        layer_transition.authority_requirements != expected_authority
        or alltoall_transition.authority_requirements
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll transition authority is not exact"
        )

    sources = [record.source for record in chain.relation_facts]
    fact_ids = [record.fact_id for record in chain.relation_facts]
    if len(set(sources)) != len(sources) or len(set(fact_ids)) != len(fact_ids):
        raise ValueError("mixed LayerNorm/AllToAll relation facts are duplicated")
    records = {record.source: record for record in chain.relation_facts}
    try:
        layer_input = records[layer_cert.input_fact]
        layer_output = records[layer_cert.output_fact]
        alltoall_input = records[alltoall_cert.input_fact]
        final_output = records[alltoall_cert.output_fact]
    except KeyError as exc:
        raise ValueError(
            "mixed LayerNorm/AllToAll relation fact is unresolved"
        ) from exc

    states = [state for state in chain.states if state.state_id in {
        segment.pre_state_id, segment.post_state_id
    }]
    if len(states) != 2 or len({state.state_id for state in states}) != 2:
        raise ValueError("mixed LayerNorm/AllToAll state identity is not unique")
    state_map = {state.state_id: state for state in states}
    before = state_map[segment.pre_state_id]
    after = state_map[segment.post_state_id]
    if (
        len(set(before.fact_ids)) != len(before.fact_ids)
        or len(set(after.fact_ids)) != len(after.fact_ids)
        or layer_input.fact_id not in before.fact_ids
        or alltoall_input.fact_id not in before.fact_ids
        or layer_output.fact_id not in after.fact_ids
        or final_output.fact_id not in after.fact_ids
        or not set(after.fact_ids)
        <= ({layer_output.fact_id, final_output.fact_id} | set(before.fact_ids))
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll post-state publication is not exact"
        )

    k = len(layer_input.pm_tids)
    if (
        k <= 0
        or getattr(ir, "sm_num_ranks", 1) != 1
        or getattr(ir, "pm_num_ranks", k) != k
        or layer_cert.rank_count != k
        or alltoall_cert.rank_count != k
        or any(
            len(record.pm_tids) != k
            for record in (layer_input, layer_output, alltoall_input, final_output)
        )
        or any(
            len(set(record.pm_tids)) != k
            for record in (layer_input, layer_output, alltoall_input, final_output)
        )
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll rank authority is not a positive dynamic K"
        )
    idim = alltoall_cert.input_gather_dim
    odim = alltoall_cert.output_gather_dim
    if (
        any(
            record.kind != "sharded"
            for record in (layer_input, layer_output, alltoall_input, final_output)
        )
        or layer_input.gather_dim != 1
        or layer_output.gather_dim != 1
        or alltoall_input.gather_dim != idim
        or final_output.gather_dim != odim
        or layer_input.full_shape != layer_output.full_shape
        or layer_input.shard_shape != layer_output.shard_shape
        or alltoall_input.full_shape != final_output.full_shape
        or alltoall_input.sm_tid != final_output.sm_tid
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll relation shapes or roles disagree"
        )
    for record, dim in ((alltoall_input, idim), (final_output, odim)):
        if dim is None or not 0 <= dim < len(record.shard_shape):
            raise ValueError("mixed LayerNorm/AllToAll dimension is invalid")
        reconstructed = list(record.shard_shape)
        reconstructed[dim] *= k
        if tuple(reconstructed) != record.full_shape:
            raise ValueError(
                "mixed LayerNorm/AllToAll shape contract is invalid"
            )
    shard_shape = layer_input.shard_shape
    if (
        len(shard_shape) != 3
        or any(value <= 0 for value in shard_shape)
        or layer_input.full_shape[1] != shard_shape[1] * k
        or layer_input.full_shape[0] != shard_shape[0]
        or layer_input.full_shape[2] != shard_shape[2]
        or tuple(layer_cert.external_tids) == ()
        or tuple(layer_cert.external_shapes) != (
            (shard_shape[2],),
            (shard_shape[2],),
        )
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll LayerNorm shape authority is invalid"
        )
    if len(layer_cert.external_tids) != 2:
        raise ValueError(
            "mixed LayerNorm/AllToAll gamma/beta authority is malformed"
        )

    sm_range = tuple(range(*segment.sm_range))
    pm_range = tuple(range(*segment.pm_range))
    if (
        not sm_range
        or min(sm_range) < 0
        or max(sm_range) >= len(ir.sm_nodes)
        or not pm_range
        or min(pm_range) < 0
        or max(pm_range) >= len(ir.pm_nodes)
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll component range is outside the graph"
        )

    def step_indices(step_ids, side):
        result = []
        for step_id in step_ids:
            fields = step_id.split(":")
            if (
                len(fields) != 3
                or fields[0] != side
                or fields[2] != "0"
            ):
                raise ValueError(
                    "mixed LayerNorm/AllToAll writer reference is malformed"
                )
            try:
                result.append(int(fields[1]))
            except ValueError as exc:
                raise ValueError(
                    "mixed LayerNorm/AllToAll writer index is malformed"
                ) from exc
        return tuple(result)

    expected_layer_sm = step_indices((layer_cert.sm_step_id,), "sm")
    expected_layer_pm = step_indices(layer_cert.pm_step_ids, "pm")
    expected_alltoall_pm = step_indices(alltoall_cert.pm_step_ids, "pm")
    if (
        layer_transition.sm_node_indices != expected_layer_sm
        or layer_transition.pm_node_indices != expected_layer_pm
        or alltoall_transition.sm_node_indices != ()
        or alltoall_transition.pm_node_indices != expected_alltoall_pm
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll transition footprint was tampered"
        )
    sm_owned = (
        *layer_transition.sm_node_indices,
        *alltoall_transition.sm_node_indices,
    )
    pm_owned = (
        *layer_transition.pm_node_indices,
        *alltoall_transition.pm_node_indices,
    )
    if (
        len(set(sm_owned)) != len(sm_owned)
        or set(sm_owned) != set(sm_range)
        or len(set(pm_owned)) != len(pm_owned)
        or set(pm_owned) != set(pm_range)
        or len(sm_range) != 1
        or len(pm_range) != 2 * k
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll footprints do not exactly partition "
            "the atomic component"
        )

    sm_node = ir.sm_nodes[expected_layer_sm[0]]
    layer_pm_nodes = tuple(ir.pm_nodes[index] for index in expected_layer_pm)
    alltoall_nodes = tuple(
        ir.pm_nodes[index] for index in expected_alltoall_pm
    )
    gamma_tid, beta_tid = layer_cert.external_tids
    if (
        sm_node.rank != 0
        or sm_node.op != "FW_layernorm"
        or sm_node.ins != [layer_input.sm_tid, gamma_tid, beta_tid]
        or sm_node.outs != [layer_output.sm_tid]
        or sm_node.params
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll SM writer roles were tampered"
        )
    if tuple(node.rank for node in layer_pm_nodes) != tuple(range(k)) or any(
        node.op != "FW_layernorm"
        or node.ins != [layer_input.pm_tids[rank], gamma_tid, beta_tid]
        or node.outs != [layer_output.pm_tids[rank]]
        or node.params
        for rank, node in enumerate(layer_pm_nodes)
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll PM LayerNorm writers were tampered"
        )
    if tuple(node.rank for node in alltoall_nodes) != tuple(range(k)) or any(
        node.op != "AllToAllPrim"
        or node.ins != list(alltoall_input.pm_tids)
        or node.outs != [final_output.pm_tids[rank]]
        or node.params != [idim, odim]
        for rank, node in enumerate(alltoall_nodes)
    ):
        raise ValueError(
            "mixed LayerNorm/AllToAll collective writers were tampered"
        )
    all_outputs = [
        node.outs[0] for node in (sm_node, *layer_pm_nodes, *alltoall_nodes)
    ]
    if len(set(all_outputs)) != len(all_outputs):
        raise ValueError(
            "mixed LayerNorm/AllToAll writers publish duplicate TIDs"
        )

    authorities = tuple(chain.authority_facts)
    authority_ids = [item.fact_id for item in authorities]
    if len(set(authority_ids)) != len(authority_ids):
        raise ValueError(
            "mixed LayerNorm/AllToAll authority facts are duplicated"
        )
    external_rows = []
    for tid, shape in zip(
        layer_cert.external_tids, layer_cert.external_shapes
    ):
        equalities = [
            item
            for item in authorities
            if getattr(item, "kind", None) == "tensor_eq"
            and {
                (item.left_side, item.left_tid),
                (item.right_side, item.right_tid),
            }
            == {("sm", tid), ("pm", tid)}
        ]
        shapes = [
            item
            for item in authorities
            if getattr(item, "kind", None) == "tensor_shape"
            and item.side == "pm"
            and item.tid == tid
            and tuple(item.shape) == tuple(shape)
        ]
        if (
            len(equalities) != 1
            or len(shapes) != 1
            or equalities[0].fact_id not in before.fact_ids
            or shapes[0].fact_id not in before.fact_ids
        ):
            raise ValueError(
                "mixed LayerNorm/AllToAll external authority is not exact"
            )
        equality = equalities[0]
        reverse = equality.left_side == "pm"
        external_rows.append((tid, tuple(shape), equality, shapes[0], reverse))

    sm_nodes = tuple(ir.sm_nodes[index] for index in sm_range)
    pm_nodes = tuple(ir.pm_nodes[index] for index in pm_range)
    sm_pos = {index: index - segment.sm_range[0] for index in sm_range}
    pm_pos = {index: index - segment.pm_range[0] for index in pm_range}
    sid = segment.segment_id
    sm_nodes_name = f"{sid}_sm_nodes"
    pm_nodes_name = f"{sid}_pm_nodes"
    layer_input_values = (
        "[" + ", ".join(f"pmStore {tid}" for tid in layer_input.pm_tids) + "]"
    )
    layer_values = (
        "[" + ", ".join(f"pmFinal {tid}" for tid in layer_output.pm_tids) + "]"
    )
    alltoall_initial_values = (
        "[" + ", ".join(f"pmStore {tid}" for tid in alltoall_input.pm_tids) + "]"
    )
    alltoall_input_values = (
        "[" + ", ".join(f"pmFinal {tid}" for tid in alltoall_input.pm_tids) + "]"
    )
    output_values = (
        "[" + ", ".join(f"pmFinal {tid}" for tid in final_output.pm_tids) + "]"
    )
    input_tids = "[" + ", ".join(str(tid) for tid in alltoall_input.pm_tids) + "]"
    output_tids = "[" + ", ".join(str(tid) for tid in final_output.pm_tids) + "]"
    layer_full_shape = _shape_text(list(layer_output.full_shape))
    layer_shard_shape = _shape_text(list(layer_output.shard_shape))
    alltoall_full_shape = _shape_text(list(alltoall_input.full_shape))
    alltoall_input_shard_shape = _shape_text(list(alltoall_input.shard_shape))
    output_shard_shape = _shape_text(list(final_output.shard_shape))

    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := "
        f"[{', '.join(_node_text(node) for node in sm_nodes)}]",
        f"private def {pm_nodes_name} : List NodeDecl := "
        f"[{', '.join(_node_text(node) for node in pm_nodes)}]",
        "",
        f"private def {sid} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} "
        f"{ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}",
        f"  pmNodes := {pm_nodes_name}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_nodes_name}",
        f"    let pmNodes : List NodeDecl := {pm_nodes_name}",
        f"    let inputTids : List Tid := {input_tids}",
        f"    let outputTids : List Tid := {output_tids}",
        "    let rankCount := outputTids.length",
        f"    have hRankCount : rankCount = {ir.pm_graph_ref}.numRanks := by "
        "native_decide",
        f"    let smFinal := smNodes.foldl "
        f"(applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl "
        f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes "
        "smStore pmStore hstate",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
        f"    have hLayerIn : {layer_input.fact_id}.Holds smStore pmStore := "
        "hstate _ (by native_decide)",
        f"    change ShardedRel (smStore {layer_input.sm_tid}) {layer_input_values} "
        f"1 {layer_full_shape} {layer_shard_shape} at hLayerIn",
        f"    have hAllToAllIn : {alltoall_input.fact_id}.Holds smStore pmStore := "
        "hstate _ (by native_decide)",
        f"    change ShardedRel (smStore {alltoall_input.sm_tid}) "
        f"{alltoall_initial_values} {idim} {alltoall_full_shape} "
        f"{alltoall_input_shard_shape} at hAllToAllIn",
        f"    have hAllToAllInFinal : {alltoall_input.fact_id}.Holds "
        "smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {alltoall_input.sm_tid}) "
        f"{alltoall_input_values} {idim} {alltoall_full_shape} "
        f"{alltoall_input_shard_shape} at hAllToAllInFinal",
    ]
    for index, (tid, shape, equality, shape_fact, reverse) in enumerate(
        external_rows
    ):
        lines.extend([
            f"    have hExternalEqRaw{index} : {equality.fact_id}.Holds "
            "smStore pmStore := hstate _ (by native_decide)",
            f"    have hExternalEq{index} : smStore {tid} = pmStore {tid} := by",
        ])
        if reverse:
            lines.extend([
                f"      change pmStore {tid} = smStore {tid} at "
                f"hExternalEqRaw{index}",
                f"      exact hExternalEqRaw{index}.symm",
            ])
        else:
            lines.extend([
                f"      change smStore {tid} = pmStore {tid} at "
                f"hExternalEqRaw{index}",
                f"      exact hExternalEqRaw{index}",
            ])
        lines.extend([
            f"    have hExternalShape{index} : {shape_fact.fact_id}.Holds "
            "smStore pmStore := hstate _ (by native_decide)",
            f"    change (pmStore {tid}).shape = {_shape_text(list(shape))} "
            f"at hExternalShape{index}",
        ])

    def layer_writer(name, side, absolute_index, node):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        store = "smStore" if side == "sm" else "pmStore"
        nodes = "smNodes" if side == "sm" else "pmNodes"
        final = "smFinal" if side == "sm" else "pmFinal"
        pos = sm_pos[absolute_index] if side == "sm" else pm_pos[absolute_index]
        args = " ".join(f"({store} {tid})" for tid in node.ins)
        lines.extend([
            f"    have {name} : {final} {node.outs[0]} = "
            f"fw_layernorm {args} := by",
            f"      change ({nodes}.foldl (applyNodeDistributedFaithful "
            f"{graph}) {store}) {node.outs[0]} = _",
            f"      rw [show {nodes} = {nodes}.take {pos} ++ "
            f"[{_node_text(node)}] ++ {nodes}.drop {pos + 1} by native_decide]",
            f"      rw [foldl_faithful_middle_writer {graph} {store} "
            f"({nodes}.take {pos}) ({nodes}.drop {pos + 1}) "
            f"{_node_text(node)} {node.outs[0]} "
            f"(fun t => fw_layernorm (t {node.ins[0]}) "
            f"(t {node.ins[1]}) (t {node.ins[2]})) (by",
            "          intro t",
            "          rw "
            "[applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "            (hshuffle := by native_decide) "
            "(hunshuffle := by native_decide) "
            "(hattn := by native_decide)]",
            "          simp [applyNodeDistributed, applyNodeRingAttn]",
            f"          exact applyNode_fw_layernorm_out {graph} t "
            f"{node.rank} {node.ins[0]} {node.ins[1]} {node.ins[2]} "
            f"{node.outs[0]} []",
            "        ) (by native_decide) (by native_decide)]",
        ])
        for tid in node.ins:
            lines.append(
                "      rw "
                f"[foldl_applyNodeDistributedFaithful_at_not_written {graph} "
                f"({nodes}.take {pos}) {store} {tid} "
                "(by native_decide) (by native_decide)]"
            )

    layer_writer(
        "hLayerSm", "sm", expected_layer_sm[0], sm_node
    )
    for rank, (index, node) in enumerate(
        zip(expected_layer_pm, layer_pm_nodes)
    ):
        layer_writer(f"hLayerPm{rank}", "pm", index, node)

    batch, sequence, width = layer_input.shard_shape
    lines.extend([
        f"    have hLayerComm := ({layer_theorem} "
        f"(K := {layer_input_values}.length) (b := {batch}) "
        f"(s := {sequence}) (d := {width}) (xs := {layer_input_values}) "
        f"(gamma := pmStore {gamma_tid}) (beta := pmStore {beta_tid}) "
        "(by simp) (by omega) (by omega) (by omega) rfl "
        "(fun x hx => hLayerIn.shard_shapes x hx) "
        "hExternalShape0 hExternalShape1)",
        f"    have hLayerValue : smFinal {layer_output.sm_tid} = "
        f"allGatherPrimDimN 1 {layer_values}.length 0 {layer_values} := by",
        "      rw [hLayerSm, hExternalEq0, hExternalEq1, "
        "hLayerIn.full_value, hLayerComm]",
        "      simp only [List.map, List.length_cons, List.length_nil]",
        "      rw ["
        + ", ".join(f"← hLayerPm{rank}" for rank in range(k))
        + "]",
    ])
    layer_shape_names = []
    for rank, node in enumerate(layer_pm_nodes):
        shape_name = f"hLayerShape{rank}"
        layer_shape_names.append(shape_name)
        lines.extend([
            f"    have {shape_name} : (pmFinal {node.outs[0]}).shape = "
            f"{layer_shard_shape} := by",
            f"      rw [hLayerPm{rank}]",
            "      unfold fw_layernorm",
            f"      rw [hLayerIn.shard_shapes (pmStore "
            f"{layer_input.pm_tids[rank]}) (by simp)]",
            "      rfl",
        ])
    lines.extend([
        f"    have hLayerFullShape : (smFinal {layer_output.sm_tid}).shape = "
        f"{layer_full_shape} := by",
        f"      rw [hLayerValue, allGatherPrimDimN_shape 1 "
        f"{layer_values}.length {layer_values} {layer_shard_shape}]",
        "      · simp only [List.length_cons, List.length_nil]",
        "        native_decide",
        "      · simp only [List.head?, Option.map, Option.getD]",
        f"        exact {layer_shape_names[0]}",
        f"    have hLayerOut : {layer_output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {layer_output.sm_tid}) "
        f"{layer_values} 1 {layer_full_shape} {layer_shard_shape}",
        "      refine {",
        "        full_value := hLayerValue",
        "        full_shape := hLayerFullShape",
        "        shards_nonempty := by simp",
        "        gather_dim_lt := by native_decide",
        "        shard_shapes := ?_",
        "        shape_contract := by "
        "simp only [List.length_cons, List.length_nil] <;> native_decide",
        "      }",
        "      intro shard hmem",
        "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with " + " | ".join("rfl" for _ in range(k)),
    ])
    lines.extend(
        f"      · exact {shape_name}" for shape_name in layer_shape_names
    )
    lines.extend([
        "    let xs := inputTids.map pmFinal",
        f"    have hHead : ((xs.head?.map (fun t => t.shape)).getD []) = "
        f"{alltoall_input_shard_shape} := by",
        "      simp only [xs, inputTids, List.map, List.head?, Option.map, "
        "Option.getD]",
        f"      exact hAllToAllInFinal.shard_shapes "
        f"(pmFinal {alltoall_input.pm_tids[0]}) (by simp)",
        "    have hRankXs : rankCount = xs.length := by",
        "      simp [rankCount, outputTids, xs, inputTids]",
    ])

    alltoall_writer_names = []
    alltoall_shape_names = []
    for rank, (absolute_index, node) in enumerate(
        zip(expected_alltoall_pm, alltoall_nodes)
    ):
        pos = pm_pos[absolute_index]
        prefix = (
            f"((pmNodes.take {pos}).foldl "
            f"(applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore)"
        )
        for input_rank, tid in enumerate(alltoall_input.pm_tids):
            lines.extend([
                f"    have hInputPrefix{rank}_{input_rank} : "
                f"{prefix} {tid} = pmFinal {tid} := by",
                f"      have h := "
                f"foldl_applyNodeDistributedFaithful_at_not_written "
                f"{ir.pm_graph_ref} (pmNodes.drop {pos}) {prefix} {tid} "
                "(by native_decide) (by native_decide)",
                "      rw [← List.foldl_append, show "
                f"pmNodes.take {pos} ++ pmNodes.drop {pos} = pmNodes by "
                f"exact List.take_append_drop {pos} pmNodes] at h",
                "      exact h.symm",
            ])
        lines.extend([
            f"    have hInputs{rank} : inputTids.map {prefix} = xs := by",
            "      simp only [inputTids, xs, List.map]",
            "      rw ["
            + ", ".join(
                f"hInputPrefix{rank}_{input_rank}"
                for input_rank in range(k)
            )
            + "]",
        ])
        writer_name = f"hAllToAll{rank}"
        shape_name = f"hAllToAllShape{rank}"
        alltoall_writer_names.append(writer_name)
        alltoall_shape_names.append(shape_name)
        lines.extend([
            f"    have {writer_name} : pmFinal {node.outs[0]} = "
            f"allToAllPrimWithDims rankCount {rank} xs {idim} {odim} := by",
            f"      change (pmNodes.foldl (applyNodeDistributedFaithful "
            f"{ir.pm_graph_ref}) pmStore) {node.outs[0]} = _",
            f"      rw [show pmNodes = pmNodes.take {pos} ++ "
            f"[{_node_text(node)}] ++ pmNodes.drop {pos + 1} by "
            "native_decide]",
            f"      rw [foldl_faithful_middle_writer {ir.pm_graph_ref} "
            f"pmStore (pmNodes.take {pos}) (pmNodes.drop {pos + 1}) "
            f"{_node_text(node)} {node.outs[0]} "
            f"(fun t => allToAllPrimWithDims rankCount {rank} "
            f"(inputTids.map t) {idim} {odim})]",
            f"      · rw [hInputs{rank}]",
            "      · intro t",
            "        rw "
            "[applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "          (hshuffle := by native_decide) "
            "(hunshuffle := by native_decide) "
            "(hattn := by native_decide)]",
            "        simp only [applyNodeDistributedFaithful, "
            "applyNodeDistributed, applyNodeRingAttn]",
            "        rw [hRankCount]",
            f"        simpa [inputTids] using "
            f"applyNode_allToAllPrimWithDims_out {ir.pm_graph_ref} t "
            f"{rank} inputTids {node.outs[0]} {idim} {odim}",
            "      · native_decide",
            "      · native_decide",
            f"    have {shape_name} : (pmFinal {node.outs[0]}).shape = "
            f"{output_shard_shape} := by",
            f"      rw [{writer_name}, allToAllPrimWithDims_shape "
            f"rankCount {rank} xs {idim} {odim} {alltoall_input_shard_shape} "
            "hHead (by native_decide)]",
            "      native_decide",
        ])

    lines.extend([
        "    have hOrderedOutputs : outputTids.map pmFinal =",
        f"        List.ofFn (fun r : Fin rankCount => "
        f"allToAllPrimWithDims rankCount r.1 xs {idim} {odim}) := by",
        "      simp only [outputTids, rankCount, List.map]",
        "      rw [" + ", ".join(alltoall_writer_names) + "]",
        "      rfl",
        f"    have hGatherShape : "
        f"(allGatherPrimDimN {idim} rankCount 0 xs).shape = "
        f"{alltoall_full_shape} := by",
        "      rw [hRankXs]",
        "      calc",
        f"        _ = (smFinal {alltoall_input.sm_tid}).shape := "
        "congrArg (fun t => t.shape) hAllToAllInFinal.full_value.symm",
        "        _ = _ := hAllToAllInFinal.full_shape",
        f"    have hOdim : {odim} < "
        f"(allGatherPrimDimN {idim} rankCount 0 xs).shape.length := by",
        "      rw [hGatherShape]",
        "      native_decide",
        f"    have hDiv : "
        f"(allGatherPrimDimN {idim} rankCount 0 xs).shape.getD "
        f"{odim} 0 % rankCount = 0 := by",
        "      rw [hGatherShape]",
        "      native_decide",
        "    have hOdimXs := hOdim",
        "    have hDivXs := hDiv",
        "    rw [hRankXs] at hOdimXs hDivXs",
        f"    have hFinalOut : {final_output.fact_id}.Holds "
        "smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {final_output.sm_tid}) "
        f"{output_values} {odim} {alltoall_full_shape} {output_shard_shape}",
        "      refine {",
        "        full_value := ?_",
        "        full_shape := hAllToAllInFinal.full_shape",
        "        shards_nonempty := by simp",
        "        gather_dim_lt := by native_decide",
        "        shard_shapes := ?_",
        "        shape_contract := by "
        "simp only [List.length_cons, List.length_nil] <;> native_decide",
        "      }",
        "      · rw [show "
        f"{output_values} = outputTids.map pmFinal by rfl, "
        "hOrderedOutputs, List.length_ofFn]",
        f"        rw [hRankXs, {alltoall_theorem} {idim} {odim} xs "
        "(by simp [xs, inputTids]) hOdimXs hDivXs]",
        "        simp only [rankCount, outputTids, xs, inputTids, List.map, "
        "List.length_cons, List.length_nil]",
        "        exact hAllToAllInFinal.full_value",
        "      · intro shard hmem",
        "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "        rcases hmem with " + " | ".join("rfl" for _ in range(k)),
    ])
    lines.extend(
        f"        · exact {shape_name}"
        for shape_name in alltoall_shape_names
    )
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ [{layer_output.fact_id}, {final_output.fact_id}] ++ "
        f"{before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ "
        f"[{layer_output.fact_id}, {final_output.fact_id}] ++ {before.state_id}.facts by "
        "native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl | rfl",
        "      · exact hLayerOut",
        "      · exact hFinalOut",
        "    · exact hframe fact old",
        "",
    ])
    return "\n".join(lines)
