"""Atomic PM-only renderer for positive AllToAll tuples plus exact AllGather."""


def render_closed_k_rank_alltoall_allgather_segment(ir, relation, segment_id):
    try:
        from .composer import (
            _membership_cases, _node_text, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankAllToAllRelationCertificate,
        )
    except ImportError:
        from composer import (
            _membership_cases, _node_text, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankAllToAllRelationCertificate,
        )
    _tid_list_text = lambda tids: "[" + ", ".join(str(tid) for tid in tids) + "]"

    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("mixed collective requires one complete closed segment")
    segment = segments[0]
    if len(segment.transition_ids) < 2 or len(set(segment.transition_ids)) != len(segment.transition_ids):
        raise ValueError("mixed collective requires a positive unique transition tuple")
    by_id = {}
    for transition in relation.transition_specs:
        by_id.setdefault(transition.transition_id, []).append(transition)
    transition_matches = [by_id.get(tid, ()) for tid in segment.transition_ids]
    if any(len(items) != 1 for items in transition_matches):
        raise ValueError("mixed collective transition authority is missing or duplicated")
    transitions = [items[0] for items in transition_matches]
    alltoalls, gather = transitions[:-1], transitions[-1]
    a_rule = "alltoall-k-rank-layout-transport"
    a_theorem = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    g_rule = "allgather-reconstruction-k-rank"
    g_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"
    if (not alltoalls
            or any(t.rule_id != a_rule or t.lean_theorem != a_theorem
                   or len(t.pre_facts) != 1 or len(t.post_facts) != 1 for t in alltoalls)
            or gather.rule_id != g_rule or gather.lean_theorem != g_theorem
            or len(gather.pre_facts) != 1 or len(gather.post_facts) != 1):
        raise ValueError("mixed collective transition order/theorem contract is malformed")

    a_certs = [
        _select_exact_typed_certificate(
            relation, transition, a_rule, a_theorem,
            KRankAllToAllRelationCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        ) for transition in alltoalls
    ]
    g_cert = _select_exact_typed_certificate(
        relation, gather, g_rule, g_theorem,
        KRankAllGatherReconstructionCertificate,
        lambda cert: ((cert.input_fact,), (cert.output_fact,)),
    )
    sources = [record.source for record in chain.relation_facts]
    if len(sources) != len(set(sources)):
        raise ValueError("mixed collective relation authority is duplicated")
    records = {record.source: record for record in chain.relation_facts}
    try:
        a_records = [(records[t.pre_facts[0]], records[t.post_facts[0]]) for t in alltoalls]
        g_pre, g_post = records[gather.pre_facts[0]], records[gather.post_facts[0]]
    except KeyError as exc:
        raise ValueError("mixed collective relation fact is not materialized") from exc
    states = {state.state_id: state for state in chain.states}
    if len(states) != len(chain.states):
        raise ValueError("mixed collective state authority is duplicated")
    try:
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("mixed collective framing state is not materialized") from exc
    if (len(set(before.fact_ids)) != len(before.fact_ids)
            or len(set(after.fact_ids)) != len(after.fact_ids)):
        raise ValueError("mixed collective framing contains duplicate facts")
    pre_ids = [pre.fact_id for pre, _ in a_records] + [g_pre.fact_id]
    post_ids = [post.fact_id for _, post in a_records] + [g_post.fact_id]
    if (any(fid not in before.fact_ids for fid in pre_ids)
            or any(fid not in after.fact_ids for fid in post_ids)
            or not set(after.fact_ids) <= set(before.fact_ids) | set(post_ids)):
        raise ValueError("mixed collective pre/post framing is not exhaustive")

    pm_indices = tuple(range(*segment.pm_range))
    owned = tuple(i for transition in transitions for i in transition.pm_node_indices)
    if (tuple(range(*segment.sm_range)) or any(t.sm_node_indices for t in transitions)
            or len(owned) != len(set(owned)) or set(owned) != set(pm_indices)
            or any(i < 0 or i >= len(ir.pm_nodes) for i in owned)):
        raise ValueError("mixed collective footprint does not exactly partition PM authority")
    k = int(g_cert.rank_count)
    if k < 2 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("mixed collective graph rank authority is malformed")

    if len(gather.pm_node_indices) != 1:
        raise ValueError("mixed collective AllGather footprint is not exact")
    g_index = gather.pm_node_indices[0]
    g_node = ir.pm_nodes[g_index]
    g_dim = int(g_cert.gather_dim)
    reconstructed = list(g_pre.shard_shape)
    if (g_cert.pm_allgather_step != f"pm:{g_index}:0"
            or g_node.op != "AllGatherPrim" or g_node.rank != 0
            or tuple(g_node.params or ()) != (g_dim,) or len(g_node.outs) != 1
            or tuple(g_node.ins) != g_pre.pm_tids or g_pre.kind != "sharded"
            or g_post.kind != "joined" or g_pre.gather_dim != g_dim
            or g_post.sm_tid != g_pre.sm_tid or g_post.joined_pm_tid != g_node.outs[0]
            or len(g_pre.pm_tids) != k or g_dim < 0 or g_dim >= len(reconstructed)
            or tuple(g_pre.full_shape) != tuple(g_cert.full_shape)
            or tuple(g_pre.shard_shape) != tuple(g_cert.shard_shape)
            or tuple(g_post.full_shape) != tuple(g_cert.full_shape)):
        raise ValueError("mixed collective AllGather authority is malformed")
    reconstructed[g_dim] *= k
    if tuple(reconstructed) != tuple(g_pre.full_shape):
        raise ValueError("mixed collective AllGather reconstruction is inexact")

    validated = []
    for number, (transition, cert, pair) in enumerate(zip(alltoalls, a_certs, a_records)):
        pre, post = pair
        indices = transition.pm_node_indices
        nodes = [ir.pm_nodes[i] for i in indices]
        idim, odim = int(cert.input_gather_dim), int(cert.output_gather_dim)
        if (len(indices) != k
                or tuple(cert.pm_step_ids) != tuple(f"pm:{i}:0" for i in indices)
                or pre.kind != "sharded" or post.kind != "sharded"
                or len(pre.pm_tids) != k or len(post.pm_tids) != k
                or cert.rank_count != k or pre.gather_dim != idim or post.gather_dim != odim
                or pre.sm_tid != post.sm_tid or pre.full_shape != post.full_shape
                or tuple(node.rank for node in nodes) != tuple(range(k))
                or any(node.op != "AllToAllPrim" or tuple(node.ins) != pre.pm_tids
                       or len(node.outs) != 1 or tuple(node.params or ()) != (idim, odim)
                       for node in nodes)
                or tuple(node.outs[0] for node in nodes) != post.pm_tids):
            raise ValueError("mixed collective AllToAll authority is malformed")
        for fact, dim in ((pre, idim), (post, odim)):
            expected = list(fact.shard_shape)
            if dim < 0 or dim >= len(expected):
                raise ValueError("mixed collective AllToAll dimension is invalid")
            expected[dim] *= k
            if tuple(expected) != tuple(fact.full_shape):
                raise ValueError("mixed collective AllToAll shape authority is malformed")
        validated.append((number, transition, cert, pre, post, nodes))

    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    pm_text = "[" + ", ".join(_node_text(node) for node in pm_nodes) + "]"
    lines = [
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        "  smNodes := []", f"  pmNodes := {pm_text}", "  sound := by",
        "    intro smStore pmStore hstate", "    let smNodes : List NodeDecl := []",
        f"    let pmNodes : List NodeDecl := {pm_text}",
        f"    let rankCount := {_tid_list_text(list(g_pre.pm_tids))}.length",
        f"    have hRankCount : rankCount = {ir.pm_graph_ref}.numRanks := by native_decide",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
    ]
    fresh = []
    for number, transition, cert, pre, post, nodes in validated:
        iname, oname, xname = f"inputTids{number}", f"outputTids{number}", f"xs{number}"
        idim, odim = cert.input_gather_dim, cert.output_gather_dim
        full = _shape_text(list(pre.full_shape))
        ishape, oshape = _shape_text(list(pre.shard_shape)), _shape_text(list(post.shard_shape))
        lines += [
            f"    let {iname} : List Tid := {_tid_list_text(list(pre.pm_tids))}",
            f"    let {oname} : List Tid := {_tid_list_text(list(post.pm_tids))}",
            f"    let {xname} := {iname}.map pmStore",
            f"    have hRankCountXs{number} : rankCount = {xname}.length := by simp [{iname}, {oname}, {xname}, rankCount]",
            f"    have hin{number} : {pre.fact_id}.Holds smStore pmStore := hstate {pre.fact_id} (by native_decide)",
            f"    change ShardedRel (smStore {pre.sm_tid}) {xname} {idim} {full} {ishape} at hin{number}",
            f"    have hHead{number} : (({xname}.head?.map (fun t => t.shape)).getD []) = {ishape} := by",
            f"      simp only [{xname}, {iname}, List.map, List.head?, Option.map, Option.getD]",
            f"      exact hin{number}.shard_shapes _ (by simp [{xname}, {iname}])",
        ]
        writers, shapes = [], []
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, nodes)):
            ordinal = index - segment.pm_range[0]
            prefix, suffix = f"(pmNodes.take {ordinal})", f"(pmNodes.drop {ordinal + 1})"
            writer, shape = f"hAllToAll{number}_{rank}", f"hAllToAllShape{number}_{rank}"
            writers.append(writer); shapes.append(shape)
            lines += [
                f"    have hInputs{number}_{rank} : {iname}.map (({prefix}).foldl",
                f"        (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) = {xname} := by",
                "      apply List.map_congr_left", "      intro tid htid",
                f"      simp only [{iname}, List.mem_cons, List.not_mem_nil, or_false] at htid",
                f"      rcases htid with {' | '.join(f'h{i}' for i in range(k))}",
            ]
            for tid in pre.pm_tids:
                lines += ["      · subst tid",
                    f"        exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
                    f"          {prefix} pmStore {tid} (by native_decide) (by native_decide)"]
            lines += [
                f"    have {writer} : pmFinal {node.outs[0]} = allToAllPrimWithDims rankCount {rank} {xname} {idim} {odim} := by",
                f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {node.outs[0]} = _",
                f"      rw [show pmNodes = {prefix} ++ [{_node_text(node)}] ++ {suffix} by native_decide]",
                f"      rw [foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix}",
                f"        {_node_text(node)} {node.outs[0]} (fun t => allToAllPrimWithDims rankCount {rank} ({iname}.map t) {idim} {odim})]",
                f"      · rw [hInputs{number}_{rank}]", "      · intro t",
                "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
                "          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
                "        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]",
                "        rw [hRankCount]",
                f"        simpa [{iname}] using applyNode_allToAllPrimWithDims_out {ir.pm_graph_ref} t {rank} {iname} {node.outs[0]} {idim} {odim}",
                "      · native_decide", "      · native_decide",
                f"    have {shape} : (pmFinal {node.outs[0]}).shape = {oshape} := by",
                f"      rw [{writer}, allToAllPrimWithDims_shape rankCount {rank} {xname} {idim} {odim} {ishape} hHead{number} (by native_decide)]",
                "      native_decide",
            ]
        hout = f"houtAllToAll{number}"; fresh.append((post.fact_id, hout))
        lines += [
            f"    have hOrdered{number} : {oname}.map pmFinal = List.ofFn (fun r : Fin rankCount => allToAllPrimWithDims rankCount r.1 {xname} {idim} {odim}) := by",
            f"      simp only [{oname}, rankCount, List.map]", f"      rw [{', '.join(writers)}]", "      rfl",
            f"    have hGatherShape{number} : (allGatherPrimDimN {idim} rankCount 0 {xname}).shape = {full} := by",
            f"      rw [hRankCountXs{number}, ← hin{number}.full_value]", f"      exact hin{number}.full_shape",
            f"    have hOdim{number} : {odim} < (allGatherPrimDimN {idim} rankCount 0 {xname}).shape.length := by rw [hGatherShape{number}]; native_decide",
            f"    have hDiv{number} : (allGatherPrimDimN {idim} rankCount 0 {xname}).shape.getD {odim} 0 % rankCount = 0 := by rw [hGatherShape{number}]; native_decide",
            f"    have {hout} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change ShardedRel (smFinal {post.sm_tid}) ({oname}.map pmFinal) {odim} {full} {oshape}",
            "      refine {", "        full_value := ?_", "        full_shape := ?_",
            f"        shards_nonempty := by simp [{oname}]", "        gather_dim_lt := by native_decide",
            "        shard_shapes := ?_", f"        shape_contract := by simp [{oname}]", "      }",
            "      · change smStore _ = _", f"        rw [hOrdered{number}, List.length_ofFn, hRankCountXs{number}]",
            f"        rw [{a_theorem} {idim} {odim} {xname} (by simp [{xname}, {iname}]) hOdim{number} hDiv{number}]",
            f"        exact hin{number}.full_value", f"      · exact hin{number}.full_shape",
            "      · intro shard hmem",
            f"        simp only [{oname}, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
        ]
        lines += _membership_cases(shapes, indent="        ")

    ginputs = _tid_list_text(list(g_pre.pm_tids))
    gfull, gshard = _shape_text(list(g_pre.full_shape)), _shape_text(list(g_pre.shard_shape))
    ordinal = g_index - segment.pm_range[0]
    prefix, suffix = f"(pmNodes.take {ordinal})", f"(pmNodes.drop {ordinal + 1})"
    lines += [
        f"    let gatherInputTids : List Tid := {ginputs}",
        f"    have hGatherBefore : gatherInputTids.map (({prefix}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) = gatherInputTids.map pmStore := by",
        "      apply List.map_congr_left", "      intro tid htid",
        "      simp only [gatherInputTids, List.mem_cons, List.not_mem_nil, or_false] at htid",
        f"      rcases htid with {' | '.join(f'h{i}' for i in range(k))}",
    ]
    for tid in g_pre.pm_tids:
        lines += ["      · subst tid",
            f"        exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
            f"          {prefix} pmStore {tid} (by native_decide) (by native_decide)"]
    lines += [
        "    have hGatherFinal : gatherInputTids.map pmFinal = gatherInputTids.map pmStore := by",
        "      apply List.map_congr_left", "      intro tid htid",
        "      simp only [gatherInputTids, List.mem_cons, List.not_mem_nil, or_false] at htid",
        f"      rcases htid with {' | '.join(f'h{i}' for i in range(k))}",
    ]
    for tid in g_pre.pm_tids:
        lines += ["      · subst tid",
            f"        exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
            f"          pmNodes pmStore {tid} (by native_decide) (by native_decide)"]
    lines += [
        f"    have hGatherWriter : pmFinal {g_node.outs[0]} = allGatherPrimDimN {g_dim} rankCount 0 (gatherInputTids.map pmFinal) := by",
        f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {g_node.outs[0]} = _",
        f"      rw [show pmNodes = {prefix} ++ [{_node_text(g_node)}] ++ {suffix} by native_decide]",
        f"      rw [foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix}",
        f"        {_node_text(g_node)} {g_node.outs[0]} (fun t => allGatherPrimDimN {g_dim} rankCount 0 (gatherInputTids.map t))]",
        "      · rw [hGatherBefore, hGatherFinal]", "      · intro t",
        "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
        "        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]",
        "        rw [hRankCount]",
        f"        simpa [gatherInputTids] using applyNode_allGatherPrimDimN_out {ir.pm_graph_ref} t 0 gatherInputTids {g_node.outs[0]} {g_dim}",
        "      · native_decide", "      · native_decide",
        f"    have hinGather : {g_pre.fact_id}.Holds smFinal pmFinal := hframe {g_pre.fact_id} (by native_decide)",
        f"    change ShardedRel (smFinal {g_pre.sm_tid}) (gatherInputTids.map pmFinal) {g_dim} {gfull} {gshard} at hinGather",
        f"    have hJoined : smFinal {g_pre.sm_tid} = pmFinal {g_node.outs[0]} := (ShardedRel.to_joined_allGather hinGather).trans hGatherWriter.symm",
        f"    have houtGather : {g_post.fact_id}.Holds smFinal pmFinal := by",
        f"      change smFinal {g_pre.sm_tid} = pmFinal {g_node.outs[0]} ∧ (smFinal {g_pre.sm_tid}).shape = {gfull} ∧ (pmFinal {g_node.outs[0]}).shape = {gfull}",
        "      refine ⟨hJoined, hinGather.full_shape, ?_⟩", "      rw [← hJoined]", "      exact hinGather.full_shape",
    ]
    fresh.append((g_post.fact_id, "houtGather"))
    fresh_list = "[" + ", ".join(fid for fid, _ in fresh) + "]"
    lines += [
        "    intro fact hfact", f"    have covered : fact ∈ {fresh_list} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {fresh_list} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with new | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new",
        f"      rcases new with {' | '.join(f'h{i}' for i in range(len(fresh)))}",
    ]
    for _, proof in fresh:
        lines += ["      · subst fact", f"        exact {proof}"]
    lines += ["    · exact hframe fact old", ""]
    return "\n".join(lines)
