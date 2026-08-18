"""Closed renderer for dynamic-K row-parallel FW_linear reduction producers."""


def render_closed_k_rank_reduction_linear_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import KRankReductionLinearProducerCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import KRankReductionLinearProducerCertificate

    rule_id = "linear-reduction-producer-k-rank"
    chain = relation.dependent_chain_plan
    segment = next(item for item in chain.segments if item.segment_id == segment_id)
    transitions = {item.transition_id: item for item in relation.transition_specs}
    if len(segment.transition_ids) != 1:
        raise ValueError("K-rank linear reduction segment must contain one transition")
    transition = transitions[segment.transition_ids[0]]
    certificates = [
        item for item in relation.certificates
        if type(item) is KRankReductionLinearProducerCertificate
        and item.rule_id == rule_id
        and item.lean_theorem == transition.lean_theorem
        and set(transition.pre_facts) == {item.activation_fact, item.weight_fact}
        and transition.post_facts == (item.output_fact,)
    ]
    if transition.rule_id != rule_id or len(certificates) != 1:
        raise ValueError("K-rank linear reduction segment lacks one exact certificate")
    certificate = certificates[0]
    facts = {item.source: item for item in chain.relation_facts}
    activation = facts[certificate.activation_fact]
    weight = facts[certificate.weight_fact]
    output = facts[certificate.output_fact]
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if activation.kind != "sharded" or weight.kind != "sharded" or output.kind != "reduction":
        raise ValueError("K-rank linear reduction requires sharded/sharded/reduction facts")
    k = len(activation.pm_tids)
    theorem2 = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk"
    theorem = theorem2 + "_3d" if len(activation.full_shape) == 3 else theorem2
    if (k <= 0 or certificate.rank_count != k or len(weight.pm_tids) != k
            or len(output.pm_tids) != k or activation.gather_dim not in (1, 2)
            or weight.gather_dim != 1 or len(activation.full_shape) not in (2, 3)
            or certificate.activation_chunk_dim != activation.gather_dim
            or certificate.weight_gather_dim != 1 or transition.lean_theorem != theorem):
        raise ValueError("K-rank linear reduction rank/dimension/theorem contract disagrees")
    if (tuple(activation.full_shape) != tuple(certificate.activation_full_shape)
            or tuple(activation.shard_shape) != tuple(certificate.activation_shard_shape)
            or tuple(weight.full_shape) != tuple(certificate.weight_full_shape)
            or tuple(weight.shard_shape) != tuple(certificate.weight_shard_shape)
            or tuple(output.full_shape) != tuple(certificate.output_shape)
            or tuple(output.shard_shape) != tuple(certificate.output_shape)
            or activation.full_shape[-1] != k * activation.shard_shape[-1]
            or weight.full_shape[1] != k * weight.shard_shape[1]
            or activation.shard_shape[-1] != weight.shard_shape[1]
            or output.full_shape != (*activation.full_shape[:-1], weight.full_shape[0])):
        raise ValueError("K-rank linear reduction materialized shape contract fails")

    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_indices = tuple(range(*segment.sm_range))
    pm_indices = tuple(range(*segment.pm_range))
    if (len(sm_nodes) != 1 or len(pm_nodes) != k
            or transition.sm_node_indices != sm_indices
            or transition.pm_node_indices != pm_indices):
        raise ValueError("K-rank linear reduction must own exact one-SM plus K-PM writers")
    sm_node = sm_nodes[0]
    if (certificate.sm_linear_step != f"sm:{sm_indices[0]}:0"
            or certificate.pm_linear_steps != tuple(f"pm:{i}:0" for i in pm_indices)):
        raise ValueError("K-rank linear reduction certificate footprint is not exact")
    if (sm_node.rank != 0 or sm_node.op != "FW_linear"
            or sm_node.ins != [activation.sm_tid, weight.sm_tid]
            or sm_node.outs != [output.sm_tid] or sm_node.params):
        raise ValueError("K-rank linear reduction SM writer binding mismatch")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)) or any(
        node.op != "FW_linear"
        or node.ins != [activation.pm_tids[r], weight.pm_tids[r]]
        or node.outs != [output.pm_tids[r]] or node.params
        for r, node in enumerate(pm_nodes)
    ):
        raise ValueError("K-rank linear reduction PM writer binding/rank/order mismatch")

    list_text = lambda xs: "[" + ", ".join(str(x) for x in xs) + "]"
    sm_text = "[" + _node_text(sm_node) + "]"
    pm_text = "[" + ", ".join(_node_text(node) for node in pm_nodes) + "]"
    atids, wtids, otids = map(list_text, (activation.pm_tids, weight.pm_tids, output.pm_tids))
    afull, ashard = map(lambda x: _shape_text(list(x)), (activation.full_shape, activation.shard_shape))
    wfull, wshard = map(lambda x: _shape_text(list(x)), (weight.full_shape, weight.shard_shape))
    oshape = _shape_text(list(output.full_shape))
    dims = tuple(int(x) for x in activation.full_shape)
    shard, outdim = int(activation.shard_shape[-1]), int(weight.full_shape[0])
    smg, pmg = ir.sm_graph_ref, ir.pm_graph_ref
    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private def {segment.segment_id} :",
        f"    ClosedDepSegmentCertificate {smg} {pmg} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_text}", f"  pmNodes := {pm_text}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_text}",
        f"    let pmNodes : List NodeDecl := {pm_text}",
        f"    let pmActivationTids : List Tid := {atids}",
        f"    let pmWeightTids : List Tid := {wtids}",
        f"    let pmOutputTids : List Tid := {otids}",
        "    let rankCount := pmActivationTids.length",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {smg}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hActivation : {activation.fact_id}.Holds smStore pmStore := hstate {activation.fact_id} (by native_decide)",
        f"    change ShardedRel (smStore {activation.sm_tid}) (pmActivationTids.map pmStore) {activation.gather_dim} {afull} {ashard} at hActivation",
        f"    have hWeight : {weight.fact_id}.Holds smStore pmStore := hstate {weight.fact_id} (by native_decide)",
        f"    change ShardedRel (smStore {weight.sm_tid}) (pmWeightTids.map pmStore) 1 {wfull} {wshard} at hWeight",
        f"    have hSmWriter : smFinal {output.sm_tid} = fw_linear (smStore {activation.sm_tid}) (smStore {weight.sm_tid}) := by",
        "      unfold smFinal smNodes", "      simp only [List.foldl]",
        "      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
        "      unfold applyNodeDistributed",
        "      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
        f"      · exact applyNode_fw_linear_out {smg} smStore 0 {activation.sm_tid} {weight.sm_tid} {output.sm_tid}",
        "      · decide", "      · decide",
    ]
    writer_names, shape_names, chunk_names = [], [], []
    cancel = "TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d" if len(dims) == 3 else "TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_2d"
    for rank, node in enumerate(pm_nodes):
        hw, hs, hc = f"hPmWriter{rank}", f"hPmShape{rank}", f"hActivationChunk{rank}"
        writer_names.append(hw); shape_names.append(hs); chunk_names.append(hc)
        pre, post = f"(pmNodes.take {rank})", f"(pmNodes.drop {rank + 1})"
        lines += [
            f"    have {hw} : pmFinal {node.outs[0]} = fw_linear (pmStore {node.ins[0]}) (pmStore {node.ins[1]}) := by",
            "      calc",
            f"        pmFinal {node.outs[0]} = fw_linear ({pre}.foldl (applyNodeDistributedFaithful {pmg}) pmStore {node.ins[0]}) ({pre}.foldl (applyNodeDistributedFaithful {pmg}) pmStore {node.ins[1]}) := by",
            f"          change (pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore) {node.outs[0]} = _",
            f"          rw [show pmNodes = {pre} ++ [{_node_text(node)}] ++ {post} by native_decide]",
            f"          apply foldl_faithful_middle_writer {pmg} pmStore {pre} {post} {_node_text(node)} {node.outs[0]} (fun t => fw_linear (t {node.ins[0]}) (t {node.ins[1]}))",
            "          · intro t",
            "            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]",
            "            unfold applyNodeDistributed",
            "            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
            f"            · exact applyNode_fw_linear_out {pmg} t {rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            "            · decide", "            · decide", "          · native_decide", "          · native_decide",
            f"        _ = fw_linear (pmStore {node.ins[0]}) (pmStore {node.ins[1]}) := by",
            f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {pmg} {pre} pmStore {node.ins[0]} (by native_decide) (by native_decide)]",
            f"          rw [foldl_applyNodeDistributedFaithful_at_not_written {pmg} {pre} pmStore {node.ins[1]} (by native_decide) (by native_decide)]",
            f"    have {hc} : chunkPrim {k} {rank} (smStore {activation.sm_tid}) = pmStore {node.ins[0]} := by",
            "      rw [hActivation.full_value]",
        ]
        args = f"{k} {rank} " + " ".join(str(x) for x in dims[:-1]) + f" {shard}"
        lines += [
            f"      have hcancel := {cancel} {args} (pmActivationTids.map pmStore)",
            "        (by simp [rankCount, pmActivationTids]) hActivation.shard_shapes",
        ]
        lines += (["        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)"]
                  if len(dims) == 3 else ["        (by native_decide) (by native_decide) (by native_decide)"])
        lines += [
            "      simpa [rankCount, pmActivationTids] using hcancel",
            f"    have {hs} : (pmFinal {node.outs[0]}).shape = {oshape} := by",
            f"      rw [{hw}]",
            f"      have ha := hActivation.shard_shapes (pmStore {node.ins[0]}) (by simp [pmActivationTids])",
            f"      have hw := hWeight.shard_shapes (pmStore {node.ins[1]}) (by simp [pmWeightTids])",
            "      simp [fw_linear, ha, hw]", "      rfl",
        ]
    lines += [
        f"    have hWeightGather : smStore {weight.sm_tid} = allGatherPrim rankCount 0 (pmWeightTids.map pmStore) := by",
        f"      change smStore {weight.sm_tid} = allGatherPrim {k} 0 ({wtids}.map pmStore)",
        "      rw [hWeight.full_value]",
        f"      have hhead : ((pmWeightTids.map pmStore).head?.map (fun t => t.shape)).getD [] = {wshard} := by",
        f"        simpa [pmWeightTids] using hWeight.shard_shapes (pmStore {weight.pm_tids[0]}) (by simp [pmWeightTids])",
        "      simpa [rankCount, pmActivationTids, pmWeightTids] using",
        f"        (allGatherPrimDimN_1_eq_allGatherPrim_2d {k} ({wtids}.map pmStore) {outdim} {shard} hhead (by native_decide) (by native_decide))",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {oshape} := by",
        "      rw [hSmWriter]", "      simp [fw_linear, hActivation.full_shape, hWeight.full_shape]", "      rfl",
        f"    have hOutValue : smFinal {output.sm_tid} = allReducePrim (pmOutputTids.map pmFinal).length 0 (pmOutputTids.map pmFinal) := by",
        "      rw [hSmWriter, hWeightGather]",
    ]
    if len(dims) == 3:
        b, seq, inner = dims
        lines += [
            f"      have hComm := {theorem} {k} {b} {seq} {inner} {outdim} {shard} (smStore {activation.sm_tid}) (pmWeightTids.map pmStore)",
            "        hActivation.full_shape (by native_decide) (by simp [rankCount, pmActivationTids, pmWeightTids]) hWeight.shard_shapes",
            "        (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
        ]
    else:
        batch, inner = dims
        lines += [
            f"      have hComm := {theorem} {k} {batch} {inner} {outdim} {shard} (smStore {activation.sm_tid}) (pmWeightTids.map pmStore)",
            "        hActivation.full_shape (by native_decide) (by simp [rankCount, pmActivationTids, pmWeightTids]) hWeight.shard_shapes",
            "        (by native_decide) (by native_decide)",
        ]
    explicit_contributions = "[" + ", ".join(
        f"fw_linear (chunkPrim {k} {rank} (smStore {activation.sm_tid})) (pmStore {weight.pm_tids[rank]})"
        for rank in range(k)
    ) + "]"
    lines += [
        f"      have hContribs : List.ofFn (fun r : Fin {k} =>",
        f"          fw_linear (chunkPrim {k} r.val (smStore {activation.sm_tid}))",
        "            ((pmWeightTids.map pmStore).get ⟨r.val, by simpa [pmWeightTids] using r.isLt⟩)) =",
        f"          {explicit_contributions} := by",
        "        rfl",
        "      rw [hContribs] at hComm",
        "      simp [rankCount, pmActivationTids, pmWeightTids, pmOutputTids] at hComm ⊢",
        f"      rw [{', '.join(chunk_names)}] at hComm", "      rw [hComm]",
        f"      rw [{', '.join('← ' + x for x in writer_names)}]",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ReductionRel (smFinal {output.sm_tid}) (pmOutputTids.map pmFinal) {oshape}",
        "      refine {", "        full_value := hOutValue", "        full_shape := hFullShape",
        "        contributions_nonempty := by simp [pmOutputTids]", "        contribution_shapes := ?_",
        "        reduced_shape := ?_", "      }",
        "      · intro contribution hmem",
        "        simp only [pmOutputTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
    ]
    lines += ["        rcases hmem with " + " | ".join("rfl" for _ in shape_names)]
    for hs in shape_names:
        lines += ["        · exact " + hs]
    lines += [
        "      · rw [← hOutValue]", "        exact hFullShape",
        "    exact RelationState.Holds.mono_insert hframe hout (by native_decide)", "",
    ]
    return "\n".join(lines)
