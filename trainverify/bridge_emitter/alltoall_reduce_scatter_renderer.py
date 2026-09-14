"""Independent AllToAll and ReduceScatter transitions in one exact PM fold.

The real source has disjoint multi-output producer projections: neither
collective consumes the other. No internal dependency premise is introduced.
"""


try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_alltoall_reduce_scatter_segment(ir, relation, segment_id):
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .closed_fact_sources import fact_tids, source_exact
        from .composer import (
            _membership_cases, _node_text, _select_exact_typed_certificate,
            _shape_text, _render_mixed_final_value,
        )
        from .relation_compiler import KRankAllToAllRelationCertificate, KRankReduceScatterReconstructionCertificate
    except ImportError:
        from closed_fact_sources import fact_tids, source_exact
        from composer import (
            _membership_cases, _node_text, _select_exact_typed_certificate,
            _shape_text, _render_mixed_final_value,
        )
        from relation_compiler import KRankAllToAllRelationCertificate, KRankReduceScatterReconstructionCertificate

    tid_list_text = lambda tids: "[" + ", ".join(str(tid) for tid in tids) + "]"
    rule = "alltoall-k-rank-layout-transport"
    theorem = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [
        item for item in chain.segments if item.segment_id == segment_id
    ]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("AllToAll tuple requires one complete closed segment")
    segment = segments[0]
    if (not 0 <= segment.sm_range[0] <= segment.sm_range[1] <= len(ir.sm_nodes)
            or not 0 <= segment.pm_range[0] < segment.pm_range[1] <= len(ir.pm_nodes)):
        raise ValueError("atomic authority ranges are invalid")
    if not segment.transition_ids or len(set(segment.transition_ids)) != len(segment.transition_ids):
        raise ValueError("AllToAll tuple requires positive unique transitions")

    transitions_by_id = {}
    for transition in relation.transition_specs:
        transitions_by_id.setdefault(transition.transition_id, []).append(transition)
    matches = [transitions_by_id.get(item, ()) for item in segment.transition_ids]
    if any(len(items) != 1 for items in matches):
        raise ValueError("AllToAll tuple transition authority is missing or duplicated")
    transitions = [items[0] for items in matches]
    def pm_authority_key(transition):
        indices = tuple(transition.pm_node_indices)
        if not indices or indices != tuple(sorted(indices)) or len(set(indices)) != len(indices):
            raise ValueError("AllToAll tuple PM transition authority is malformed")
        return indices[0]

    if tuple(t.rule_id for t in transitions) != (rule, "reduce-scatter-reconstruction-k-rank"):
        raise ValueError("requires exact ordered AllToAll/ReduceScatter family")
    rt = transitions[1]
    rc = _select_exact_typed_certificate(relation, rt,
        "reduce-scatter-reconstruction-k-rank", "TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn",
        KRankReduceScatterReconstructionCertificate, lambda c: ((c.input_fact,), (c.output_fact,)))
    all_transitions = transitions
    first_writers = tuple(pm_authority_key(transition) for transition in transitions)
    if len(set(first_writers)) != len(first_writers):
        raise ValueError("AllToAll tuple PM transition orientation is ambiguous")
    expected_order = tuple(
        transition.transition_id
        for transition in sorted(transitions, key=pm_authority_key)
    )
    if segment.transition_ids != expected_order:
        raise ValueError("AllToAll tuple transition order is not exact")
    transitions = transitions[:1]
    if any(
        transition.rule_id != rule
        or transition.lean_theorem != theorem
        or len(transition.pre_facts) != 1
        or len(transition.post_facts) != 1
        for transition in transitions
    ):
        raise ValueError("AllToAll tuple transition theorem contract is malformed")
    certificates = [
        _select_exact_typed_certificate(
            relation, transition, rule, theorem,
            KRankAllToAllRelationCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
        for transition in transitions
    ]

    sources = [record.source for record in chain.relation_facts]
    if len(sources) != len(set(sources)):
        raise ValueError("AllToAll tuple relation authority is duplicated")
    records = {record.source: record for record in chain.relation_facts}
    try:
        fact_pairs = [
            (records[transition.pre_facts[0]], records[transition.post_facts[0]])
            for transition in transitions
        ]
    except KeyError as exc:
        raise ValueError("AllToAll tuple relation fact is not materialized") from exc
    states = {state.state_id: state for state in chain.states}
    if len(states) != len(chain.states):
        raise ValueError("AllToAll tuple state authority is duplicated")
    try:
        before = states[segment.pre_state_id]
        after = states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("AllToAll tuple framing state is not materialized") from exc
    if (
        len(set(before.fact_ids)) != len(before.fact_ids)
        or len(set(after.fact_ids)) != len(after.fact_ids)
    ):
        raise ValueError("AllToAll tuple framing contains duplicate facts")
    rpre, rpost = records[rc.input_fact], records[rc.output_fact]
    pre_ids = [pre.fact_id for pre, _ in fact_pairs] + [rpre.fact_id]
    post_ids = [post.fact_id for _, post in fact_pairs] + [rpost.fact_id]
    if (
        len(set(pre_ids)) != len(pre_ids)
        or len(set(post_ids)) != len(post_ids)
        or set(post_ids) & set(before.fact_ids)
        or any(fact_id not in before.fact_ids for fact_id in pre_ids)
        or any(fact_id not in after.fact_ids for fact_id in post_ids)
        or not set(after.fact_ids) <= set(before.fact_ids) | set(post_ids)
    ):
        raise ValueError("AllToAll tuple pre/post state publication is not exact")

    pm_indices = tuple(range(*segment.pm_range))
    owned = tuple(
        index for transition in all_transitions for index in transition.pm_node_indices
    )
    if (
        tuple(range(*segment.sm_range))
        or any(transition.sm_node_indices or transition.fact_only or transition.authority_requirements for transition in all_transitions)
        or len(owned) != len(set(owned))
        or set(owned) != set(pm_indices)
        or any(index < 0 or index >= len(ir.pm_nodes) for index in owned)
    ):
        raise ValueError("AllToAll tuple footprints do not exactly partition PM authority")

    k = int(certificates[0].rank_count)
    if k <= 0 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("AllToAll tuple graph rank authority is malformed")
    validated = []
    for number, (transition, certificate, pair) in enumerate(
        zip(transitions, certificates, fact_pairs)
    ):
        pre, post = pair
        indices = transition.pm_node_indices
        nodes = [ir.pm_nodes[index] for index in indices]
        input_dim = int(certificate.input_gather_dim)
        output_dim = int(certificate.output_gather_dim)
        if (
            len(indices) != k
            or tuple(certificate.pm_step_ids)
            != tuple(f"pm:{index}:0" for index in indices)
            or pre.kind != "sharded"
            or post.kind != "sharded"
            or len(pre.pm_tids) != k
            or len(post.pm_tids) != k
            or int(certificate.rank_count) != k
            or pre.gather_dim != input_dim
            or post.gather_dim != output_dim
            or pre.sm_tid != post.sm_tid
            or pre.full_shape != post.full_shape
            or tuple(node.rank for node in nodes) != tuple(range(k))
            or any(
                node.op != "AllToAllPrim"
                or tuple(node.ins) != pre.pm_tids
                or len(node.outs) != 1
                or tuple(node.params or ()) != (input_dim, output_dim)
                for node in nodes
            )
            or tuple(node.outs[0] for node in nodes) != post.pm_tids
        ):
            raise ValueError("AllToAll tuple writer authority is malformed")
        for fact, dimension in ((pre, input_dim), (post, output_dim)):
            expected = list(fact.shard_shape)
            if dimension < 0 or dimension >= len(expected):
                raise ValueError("AllToAll tuple gather dimension is invalid")
            expected[dimension] *= k
            if tuple(expected) != tuple(fact.full_shape):
                raise ValueError("AllToAll tuple shape authority is malformed")
        validated.append((number, transition, certificate, pre, post, nodes))

    dim=rc.scatter_dim
    if (rc.rank_count != k or rpre.kind != "reduction" or rpost.kind != "sharded"
            or rpre.gather_dim is not None or rpost.gather_dim != dim
            or rpre.sm_tid != rpost.sm_tid or len(rpre.pm_tids) != k or len(rpost.pm_tids) != k
            or rpre.full_shape != rc.full_shape or rpost.full_shape != rc.full_shape
            or rpost.shard_shape != rc.shard_shape or len(rt.pm_node_indices) != k
            or rc.pm_step_ids != tuple(f"pm:{i}:0" for i in rt.pm_node_indices)):
        raise ValueError("ReduceScatter metadata/ownership mismatch")
    expected=list(rpost.shard_shape)
    if dim < 0 or dim >= len(expected):raise ValueError("ReduceScatter axis invalid")
    expected[dim]*=k
    if tuple(expected)!=rpost.full_shape:raise ValueError("ReduceScatter shape contract mismatch")
    for rank,index in enumerate(rt.pm_node_indices):
        n=ir.pm_nodes[index]
        if (n.op!="ReduceScatterPrim" or n.rank!=rank or tuple(n.params or ())!=(dim,)
                or tuple(n.ins)!=rpre.pm_tids or tuple(n.outs)!=(rpost.pm_tids[rank],)):
            raise ValueError("ReduceScatter exact writer signature mismatch")
    # Preserve the historical source-validation diagnostic prefix.
    for pre,post in (*fact_pairs,(rpre,rpost)):
        source_exact(ir, pre, segment.sm_range[0], segment.pm_range[0], context="BW_gelu/WRED")
        source_exact(ir, post, segment.sm_range[1], segment.pm_range[1], context="BW_gelu/WRED")
    all_facts=(*chain.relation_facts,*chain.authority_facts)
    if chain.anchor_fact is not None:all_facts=(*all_facts,chain.anchor_fact)
    by_id={f.fact_id:f for f in all_facts}
    if len(by_id)!=len(all_facts):raise ValueError("duplicate materialized fact identity")
    writes=[tid for node in ir.pm_nodes[slice(*segment.pm_range)] for tid in node.outs]
    if len(set(writes))!=len(writes):raise ValueError("output overwritten within atomic fold")
    for fid in before.fact_ids:
        if fid not in by_id:raise ValueError("unresolved live authority")
        _,protected=fact_tids(by_id[fid])
        if protected & set(writes):raise ValueError("PM write overwrites live authority")

    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    pm_text = "[" + ", ".join(_node_text(node) for node in pm_nodes) + "]"
    lines = [
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        "  smNodes := []",
        f"  pmNodes := {pm_text}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        "    let smNodes : List NodeDecl := []",
        f"    let pmNodes : List NodeDecl := {pm_text}",
        f"    let pmTids : List Tid := {tid_list_text(list(fact_pairs[0][1].pm_tids))}",
        "    let rankCount := pmTids.length",
        f"    have hRankCount : rankCount = {ir.pm_graph_ref}.numRanks := by rfl",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
        "      · native_decide",
    ]
    fresh = []
    for number, transition, certificate, pre, post, nodes in validated:
        input_name = f"inputTids{number}"
        output_name = f"outputTids{number}"
        values_name = f"xs{number}"
        input_dim = certificate.input_gather_dim
        output_dim = certificate.output_gather_dim
        full_shape = _shape_text(list(pre.full_shape))
        input_shape = _shape_text(list(pre.shard_shape))
        output_shape = _shape_text(list(post.shard_shape))
        lines.extend([
            f"    let {input_name} : List Tid := {tid_list_text(list(pre.pm_tids))}",
            f"    let {output_name} : List Tid := {tid_list_text(list(post.pm_tids))}",
            f"    let {values_name} := {input_name}.map pmStore",
            f"    have hRankCountXs{number} : rankCount = {values_name}.length := by simp [pmTids, {input_name}, {output_name}, {values_name}, rankCount]",
            f"    have hin{number} : {pre.fact_id}.Holds smStore pmStore := hstate {pre.fact_id} (by native_decide)",
            f"    change ShardedRel (smStore {pre.sm_tid}) {values_name} {input_dim} {full_shape} {input_shape} at hin{number}",
            f"    have hHead{number} : (({values_name}.head?.map (fun t => t.shape)).getD []) = {input_shape} := by",
            f"      simp only [{values_name}, {input_name}, List.map, List.head?, Option.map, Option.getD]",
            f"      exact hin{number}.shard_shapes _ (by simp [{values_name}, {input_name}])",
        ])
        writer_names = []
        shape_names = []
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, nodes)):
            ordinal = index - segment.pm_range[0]
            prefix = f"(pmNodes.take {ordinal})"
            suffix = f"(pmNodes.drop {ordinal + 1})"
            writer_name = f"hAllToAll{number}_{rank}"
            shape_name = f"hAllToAllShape{number}_{rank}"
            writer_names.append(writer_name)
            shape_names.append(shape_name)
            lines.extend([
                f"    have hInputs{number}_{rank} : {input_name}.map (({prefix}).foldl",
                f"        (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) = {values_name} := by",
                "      apply List.map_congr_left",
                "      intro tid htid",
                f"      simp only [{input_name}, List.mem_cons, List.not_mem_nil, or_false] at htid",
                f"      rcases htid with {' | '.join(f'h{i}' for i in range(k))}",
            ])
            for tid in pre.pm_tids:
                lines.extend([
                    "      · subst tid",
                    f"        exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref}",
                    f"          {prefix} pmStore {tid} (by native_decide) (by native_decide)",
                ])
            lines.extend([
                f"    have {writer_name} : pmFinal {node.outs[0]} = allToAllPrimWithDims rankCount {rank} {values_name} {input_dim} {output_dim} := by",
                f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {node.outs[0]} = _",
                f"      rw [show pmNodes = {prefix} ++ [{_node_text(node)}] ++ {suffix} by native_decide]",
                f"      rw [foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix}",
                f"        {_node_text(node)} {node.outs[0]} (fun t => allToAllPrimWithDims rankCount {rank} ({input_name}.map t) {input_dim} {output_dim})]",
                f"      · rw [hInputs{number}_{rank}]",
                "      · intro t",
                "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
                "          (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]",
                "        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]",
                "        rw [hRankCount]",
                f"        simpa [{input_name}] using applyNode_allToAllPrimWithDims_out {ir.pm_graph_ref} t {rank} {input_name} {node.outs[0]} {input_dim} {output_dim}",
                "      · native_decide",
                "      · native_decide",
                f"    have {shape_name} : (pmFinal {node.outs[0]}).shape = {output_shape} := by",
                f"      rw [{writer_name}, allToAllPrimWithDims_shape rankCount {rank} {values_name} {input_dim} {output_dim} {input_shape} hHead{number} (by native_decide)]",
                "      native_decide",
            ])
        proof_name = f"houtAllToAll{number}"
        fresh.append((post.fact_id, proof_name))
        lines.extend([
            f"    have hOrdered{number} : {output_name}.map pmFinal = List.ofFn (fun r : Fin rankCount => allToAllPrimWithDims rankCount r.1 {values_name} {input_dim} {output_dim}) := by",
            f"      simp only [{output_name}, rankCount, List.map]",
            f"      rw [{', '.join(writer_names)}]",
            "      rfl",
            f"    have hGatherShape{number} : (allGatherPrimDimN {input_dim} rankCount 0 {values_name}).shape = {full_shape} := by",
            f"      rw [hRankCountXs{number}, ← hin{number}.full_value]",
            f"      exact hin{number}.full_shape",
            f"    have hOdim{number} : {output_dim} < (allGatherPrimDimN {input_dim} rankCount 0 {values_name}).shape.length := by rw [hGatherShape{number}]; native_decide",
            f"    have hDiv{number} : (allGatherPrimDimN {input_dim} rankCount 0 {values_name}).shape.getD {output_dim} 0 % rankCount = 0 := by rw [hGatherShape{number}]; native_decide",
            f"    have {proof_name} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change ShardedRel (smFinal {post.sm_tid}) ({output_name}.map pmFinal) {output_dim} {full_shape} {output_shape}",
            "      refine {",
            "        full_value := ?_",
            "        full_shape := ?_",
            f"        shards_nonempty := by simp [{output_name}]",
            "        gather_dim_lt := by native_decide",
            "        shard_shapes := ?_",
            f"        shape_contract := by simp [{output_name}]",
            "      }",
            "      · change smStore _ = _",
            f"        rw [hOrdered{number}, List.length_ofFn, hRankCountXs{number}]",
            f"        rw [{theorem} {input_dim} {output_dim} {values_name} (by simp [{values_name}, {input_name}]) hOdim{number} hDiv{number}]",
            f"        exact hin{number}.full_value",
            f"      · exact hin{number}.full_shape",
            "      · intro shard hmem",
            f"        simp only [{output_name}, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
        ])
        lines.extend(_membership_cases(shape_names, indent="        "))

    pre,post,c=rpre,rpost,rc
    contrib="["+", ".join(f"pmFinal {x}" for x in pre.pm_tids)+"]"
    outs="["+", ".join(f"pmFinal {x}" for x in post.pm_tids)+"]"
    full=_shape_text(list(c.full_shape));shard=_shape_text(list(c.shard_shape))
    lines.extend([f"    have hfinal : pmFinal = pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := rfl",
        f"    have hred : {pre.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ReductionRel (smStore {pre.sm_tid}) {contrib} {full} at hred"])
    for rank,index in enumerate(rt.pm_node_indices):
        node=ir.pm_nodes[index]
        expr=f"reduceScatterPrimDimN {dim} {ir.pm_graph_ref}.numRanks {rank} ["+", ".join("{store} "+str(t) for t in pre.pm_tids)+"]"
        lines.extend(_render_mixed_final_value(name=f"hw{rank}",graph=ir.pm_graph_ref,initial_store="pmStore",final_store="pmFinal",final_equality="hfinal",nodes_name="pmNodes",nodes=list(pm_nodes),position=index-segment.pm_range[0],output_tid=node.outs[0],input_tids=tuple(node.ins),written_tids=set(writes),expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_reduceScatterPrim_out {ir.pm_graph_ref} t {rank} {dim} {tid_list_text(pre.pm_tids)} {node.outs[0]}"]))
        lines.extend([f"    change pmFinal {post.pm_tids[rank]} = reduceScatterPrimDimN {dim} {k} {rank} {contrib} at hw{rank}",f"    have hredValue{rank} : smStore {pre.sm_tid} = allReducePrim {k} {rank} {contrib} := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value",f"    have hc{rank} : pmFinal {post.pm_tids[rank]} = chunkPrimDimN {dim} {k} {rank} (smStore {pre.sm_tid}) := by rw [hw{rank}]; unfold reduceScatterPrimDimN; rw [← hredValue{rank}]"])
    explicit_chunks="["+", ".join(f"chunkPrimDimN {dim} {k} {rank} (smStore {pre.sm_tid})"   for rank in range(k))+"]"
    lines.extend([f"    have hordered : {outs} = List.ofFn (fun r : Fin {k} => chunkPrimDimN {dim} {k} r.1 (smStore {pre.sm_tid})) := by",f"      change {outs} = {explicit_chunks}",f"      rw [{', '.join('hc'+str(r) for r in range(k))}]",f"    have hvalue : smStore {pre.sm_tid} = allGatherPrimDimN {dim} {outs}.length 0 {outs} := by",f"      rw [hordered]",f"      simp only [List.length_ofFn]","      symm",f"      exact allGatherPrimDimN_chunks_ofFn {dim} {k} (smStore {pre.sm_tid}) (by omega) (by rw [hred.full_shape]; native_decide) (by rw [hred.full_shape]; native_decide)"])
    for rank in range(k):lines.extend([f"    have hs{rank} : (pmFinal {post.pm_tids[rank]}).shape = {shard} := by",f"      rw [hc{rank}, chunkPrimDimN_shape {dim} {k} {rank} (smStore {pre.sm_tid}) {full} hred.full_shape (by omega)]","      native_decide"])
    lines.extend([f"    have hout : {post.fact_id}.Holds smStore pmFinal := by",f"      change ShardedRel (smStore {post.sm_tid}) {outs} {dim} {full} {shard}","      refine { full_value := hvalue, full_shape := hred.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp }","      intro x hx","      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx","      rcases hx with "+"   | ".join("rfl"   for _ in range(k))])
    for rank in range(k):lines.append(f"      · exact hs{rank}")
    fresh.append((post.fact_id,"hout"))

    fresh_list = "[" + ", ".join(fact_id for fact_id, _ in fresh) + "]"
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ {fresh_list} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {fresh_list} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with new | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new",
        f"      rcases new with {' | '.join(f'h{i}' for i in range(len(fresh)))}",
    ])
    for _, proof_name in fresh:
        lines.extend(["      · subst fact", f"        exact {proof_name}"])
    lines.extend(["    · exact hframe fact old", ""])
    return "\n".join(lines)
