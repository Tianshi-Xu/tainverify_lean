"""Atomic renderer for positive local-linear and AllToAll tuples."""
from __future__ import annotations


def render_closed_k_rank_local_linear_alltoall_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankAllToAllRelationCertificate, KRankLocalRelationCertificate
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankAllToAllRelationCertificate, KRankLocalRelationCertificate

    local_rule = "linear-sharded-k-rank-dim1"
    a2a_rule = "alltoall-k-rank-layout-transport"
    local_theorem = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
    a2a_theorem = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
    chain = relation.dependent_chain_plan
    found = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(found) != 1:
        raise ValueError("local-linear/AllToAll requires one complete closed segment")
    segment = found[0]
    by_id = {}
    for transition in relation.transition_specs:
        by_id.setdefault(transition.transition_id, []).append(transition)
    resolved = [by_id.get(tid, ()) for tid in segment.transition_ids]
    if not resolved or any(len(items) != 1 for items in resolved):
        raise ValueError("local-linear/AllToAll transition authority is missing or duplicated")
    transitions = [items[0] for items in resolved]
    split = next((i for i, t in enumerate(transitions) if t.rule_id == a2a_rule), len(transitions))
    locals_, a2as = transitions[:split], transitions[split:]
    if (not locals_ or not a2as
            or any(t.rule_id != local_rule or t.lean_theorem != local_theorem
                   or len(t.pre_facts) != 1 or len(t.post_facts) != 1 for t in locals_)
            or any(t.rule_id != a2a_rule or t.lean_theorem != a2a_theorem
                   or len(t.pre_facts) != 1 or len(t.post_facts) != 1 for t in a2as)):
        raise ValueError("local-linear/AllToAll ordered theorem contract is malformed")

    def topology_key(t):
        step = t.post_facts[0].step_triple[0].split(":")
        if len(step) != 3 or step[0] != "sm":
            raise ValueError("local-linear/AllToAll SM topology authority is malformed")
        try:
            sm_index = int(step[1])
        except ValueError as exc:
            raise ValueError("local-linear/AllToAll SM topology authority is malformed") from exc
        return sm_index, min(t.pm_node_indices) if t.pm_node_indices else -1

    expected = tuple(t.transition_id for t in (
        *sorted(locals_, key=topology_key), *sorted(a2as, key=topology_key)
    ))
    if segment.transition_ids != expected:
        raise ValueError("local-linear/AllToAll transition order is not SM-topology exact")

    local_certs = [
        _select_exact_typed_certificate(
            relation, t, local_rule, local_theorem, KRankLocalRelationCertificate,
            lambda c: ((c.input_fact,), (c.output_fact,)),
        ) for t in locals_
    ]
    a2a_certs = [
        _select_exact_typed_certificate(
            relation, t, a2a_rule, a2a_theorem, KRankAllToAllRelationCertificate,
            lambda c: ((c.input_fact,), (c.output_fact,)),
        ) for t in a2as
    ]
    sources = [r.source for r in chain.relation_facts]
    fact_ids = [r.fact_id for r in chain.relation_facts]
    if len(sources) != len(set(sources)) or len(fact_ids) != len(set(fact_ids)):
        raise ValueError("local-linear/AllToAll relation authority is duplicated")
    records = {r.source: r for r in chain.relation_facts}
    try:
        local_pairs = [(records[c.input_fact], records[c.output_fact]) for c in local_certs]
        a2a_pairs = [(records[c.input_fact], records[c.output_fact]) for c in a2a_certs]
    except KeyError as exc:
        raise ValueError("local-linear/AllToAll relation fact is not materialized") from exc
    states = {s.state_id: s for s in chain.states}
    if len(states) != len(chain.states):
        raise ValueError("local-linear/AllToAll state authority is duplicated")
    try:
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("local-linear/AllToAll framing state is not materialized") from exc
    if len(set(before.fact_ids)) != len(before.fact_ids) or len(set(after.fact_ids)) != len(after.fact_ids):
        raise ValueError("local-linear/AllToAll framing contains duplicate facts")
    local_post_ids = {post.fact_id for _, post in local_pairs}
    if any(pre.fact_id not in before.fact_ids for pre, _ in local_pairs):
        raise ValueError("local-linear input authority is not live")
    if any(pre.fact_id not in before.fact_ids and pre.fact_id not in local_post_ids for pre, _ in a2a_pairs):
        raise ValueError("AllToAll input is neither live nor locally produced")
    fresh_ids = tuple(dict.fromkeys([
        *(post.fact_id for _, post in local_pairs), *(post.fact_id for _, post in a2a_pairs)
    ]))
    if any(fact_id not in after.fact_ids for fact_id in fresh_ids):
        raise ValueError("local-linear/AllToAll fresh output is not published")
    if not set(after.fact_ids) <= set(before.fact_ids) | set(fresh_ids):
        raise ValueError("local-linear/AllToAll post-state introduces an unproved fact")

    k = int(local_certs[0].rank_count)
    if k <= 0 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("local-linear/AllToAll dynamic graph rank authority is malformed")
    if any(int(c.rank_count) != k for c in (*local_certs, *a2a_certs)):
        raise ValueError("local-linear/AllToAll certificates disagree with dynamic rank authority")
    sm_indices = tuple(range(*segment.sm_range))
    pm_indices = tuple(range(*segment.pm_range))
    sm_owned = tuple(i for t in transitions for i in t.sm_node_indices)
    pm_owned = tuple(i for t in transitions for i in t.pm_node_indices)
    if (len(sm_owned) != len(set(sm_owned)) or set(sm_owned) != set(sm_indices)
            or len(pm_owned) != len(set(pm_owned)) or set(pm_owned) != set(pm_indices)
            or any(i < 0 or i >= len(ir.sm_nodes) for i in sm_owned)
            or any(i < 0 or i >= len(ir.pm_nodes) for i in pm_owned)):
        raise ValueError("local-linear/AllToAll footprints are not disjoint and exhaustive")

    authorities = tuple(chain.authority_facts)
    authority_ids = [a.fact_id for a in authorities]
    if len(authority_ids) != len(set(authority_ids)):
        raise ValueError("local-linear/AllToAll authority facts are duplicated")
    validated_locals = []
    for number, (transition, cert, pair) in enumerate(zip(locals_, local_certs, local_pairs)):
        pre, post = pair
        if (cert.op != "FW_linear" or cert.gather_dim != 1
                or len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k
                or cert.sm_step_id != f"sm:{transition.sm_node_indices[0]}:0"
                or tuple(cert.pm_step_ids) != tuple(f"pm:{i}:0" for i in transition.pm_node_indices)
                or pre.kind != "sharded" or post.kind != "sharded"
                or pre.gather_dim != 1 or post.gather_dim != 1
                or len(pre.pm_tids) != k or len(post.pm_tids) != k
                or len(cert.external_tids) != 1 or len(cert.external_shapes) != 1):
            raise ValueError("local-linear typed authority is malformed")
        sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
        pm_nodes = [ir.pm_nodes[i] for i in transition.pm_node_indices]
        weight_tid = cert.external_tids[0]
        if (sm_node.rank != 0 or sm_node.op != "FW_linear" or sm_node.params
                or sm_node.ins != [pre.sm_tid, weight_tid] or sm_node.outs != [post.sm_tid]
                or tuple(n.rank for n in pm_nodes) != tuple(range(k))
                or any(n.op != "FW_linear" or n.params
                       or n.ins != [pre.pm_tids[r], weight_tid] or n.outs != [post.pm_tids[r]]
                       for r, n in enumerate(pm_nodes))):
            raise ValueError("local-linear writer roles/order are malformed")
        eqs = [a for a in authorities if getattr(a, "kind", None) == "tensor_eq"
               and a.left_side == "sm" and a.left_tid == weight_tid
               and a.right_side == "pm" and a.right_tid == weight_tid]
        shapes = [a for a in authorities if getattr(a, "kind", None) == "tensor_shape"
                  and a.side == "pm" and a.tid == weight_tid
                  and tuple(a.shape) == tuple(cert.external_shapes[0])]
        if (len(eqs) != 1 or len(shapes) != 1
                or eqs[0].fact_id not in before.fact_ids or shapes[0].fact_id not in before.fact_ids):
            raise ValueError("local-linear external equality/shape authority is not exact and live")
        if (len(pre.shard_shape) != 3 or any(v <= 0 for v in pre.shard_shape)
                or tuple(pre.full_shape) != (pre.shard_shape[0], pre.shard_shape[1] * k, pre.shard_shape[2])
                or tuple(post.shard_shape) != (pre.shard_shape[0], pre.shard_shape[1], cert.external_shapes[0][0])
                or tuple(post.full_shape) != (post.shard_shape[0], post.shard_shape[1] * k, post.shard_shape[2])
                or tuple(cert.external_shapes[0]) != (post.shard_shape[2], pre.shard_shape[2])):
            raise ValueError("local-linear shape authority is inconsistent")
        validated_locals.append((number, transition, cert, pre, post, sm_node, pm_nodes, eqs[0], shapes[0]))

    validated_a2as = []
    for number, (transition, cert, pair) in enumerate(zip(a2as, a2a_certs, a2a_pairs)):
        pre, post = pair
        nodes = [ir.pm_nodes[i] for i in transition.pm_node_indices]
        idim, odim = int(cert.input_gather_dim), int(cert.output_gather_dim)
        if (transition.sm_node_indices or len(transition.pm_node_indices) != k
                or tuple(cert.pm_step_ids) != tuple(f"pm:{i}:0" for i in transition.pm_node_indices)
                or pre.kind != "sharded" or post.kind != "sharded"
                or len(pre.pm_tids) != k or len(post.pm_tids) != k
                or pre.gather_dim != idim or post.gather_dim != odim
                or pre.sm_tid != post.sm_tid or pre.full_shape != post.full_shape
                or tuple(n.rank for n in nodes) != tuple(range(k))
                or any(n.op != "AllToAllPrim" or tuple(n.ins) != pre.pm_tids
                       or n.outs != [post.pm_tids[r]] or tuple(n.params or ()) != (idim, odim)
                       for r, n in enumerate(nodes))):
            raise ValueError("AllToAll writer authority is malformed")
        for fact, dim in ((pre, idim), (post, odim)):
            shape = list(fact.shard_shape)
            if dim < 0 or dim >= len(shape):
                raise ValueError("AllToAll gather dimension is invalid")
            shape[dim] *= k
            if tuple(shape) != tuple(fact.full_shape):
                raise ValueError("AllToAll shape authority is malformed")
        producer = next((row for row in validated_locals if row[4].fact_id == pre.fact_id), None)
        if producer is not None and max(producer[1].pm_node_indices) >= min(transition.pm_node_indices):
            raise ValueError("AllToAll executes before its local-linear producer")
        validated_a2as.append((number, transition, cert, pre, post, nodes, producer))

    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_pos = {i: i - segment.sm_range[0] for i in sm_indices}
    pm_pos = {i: i - segment.pm_range[0] for i in pm_indices}
    sm_name, pm_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    lines = [
        f"private def {sm_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_nodes)}]",
        f"private def {pm_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_nodes)}]", "",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_name}", f"  pmNodes := {pm_name}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_name}",
        f"    let pmNodes : List NodeDecl := {pm_name}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
    ]
    for number, _t, cert, pre, _post, _sm, _pms, eq, shape in validated_locals:
        values = ", ".join(f"pmStore {tid}" for tid in pre.pm_tids)
        lines += [
            f"    have hIn{number} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    change ShardedRel (smStore {pre.sm_tid}) [{values}] 1 {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hIn{number}",
            f"    have hWeightEq{number} : {eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    change smStore {cert.external_tids[0]} = pmStore {cert.external_tids[0]} at hWeightEq{number}",
            f"    have hWeightShape{number} : {shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    change (pmStore {cert.external_tids[0]}).shape = {_shape_text(list(cert.external_shapes[0]))} at hWeightShape{number}",
        ]

    def local_writer(name, side, absolute_index, node):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        store = "smStore" if side == "sm" else "pmStore"
        nodes = "smNodes" if side == "sm" else "pmNodes"
        final = "smFinal" if side == "sm" else "pmFinal"
        pos = sm_pos[absolute_index] if side == "sm" else pm_pos[absolute_index]
        lines.extend([
            f"    have {name} : {final} {node.outs[0]} = fw_linear ({store} {node.ins[0]}) ({store} {node.ins[1]}) := by",
            f"      change ({nodes}.foldl (applyNodeDistributedFaithful {graph}) {store}) {node.outs[0]} = _",
            f"      rw [show {nodes} = {nodes}.take {pos} ++ [{_node_text(node)}] ++ {nodes}.drop {pos + 1} by native_decide]",
            f"      rw [foldl_faithful_middle_writer {graph} {store} ({nodes}.take {pos}) ({nodes}.drop {pos + 1})",
            f"        {_node_text(node)} {node.outs[0]} (fun t => fw_linear (t {node.ins[0]}) (t {node.ins[1]})) (by",
            "          intro t",
            "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "          simp [applyNodeDistributed, applyNodeRingAttn]",
            f"          exact applyNode_fw_linear_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            "        ) (by native_decide) (by native_decide)]",
            f"      rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} ({nodes}.take {pos}) {store} {node.ins[0]} (by native_decide) (by native_decide),",
            f"        foldl_applyNodeDistributedFaithful_at_not_written {graph} ({nodes}.take {pos}) {store} {node.ins[1]} (by native_decide) (by native_decide)]",
        ])

    for number, transition, _c, _pre, _post, sm_node, rank_nodes, _eq, _shape in validated_locals:
        local_writer(f"hLocalSm{number}", "sm", transition.sm_node_indices[0], sm_node)
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, rank_nodes)):
            local_writer(f"hLocalPm{number}_{rank}", "pm", index, node)

    local_proofs = {}
    for number, _t, cert, pre, post, _sm, rank_nodes, _eq, _shape in validated_locals:
        b, seq, inner = pre.shard_shape
        width = post.shard_shape[2]
        inputs = "[" + ", ".join(f"pmStore {tid}" for tid in pre.pm_tids) + "]"
        outputs = "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]"
        lines += [
            f"    have hComm{number} := ({local_theorem} (K := {inputs}.length) (b := {b}) (s := {seq}) (i := {inner}) (o := {width}) (xs := {inputs}) (w := pmStore {cert.external_tids[0]}) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn{number}.shard_shapes x hx) hWeightShape{number})",
            f"    have hLocalValue{number} : smFinal {post.sm_tid} = allGatherPrimDimN 1 {outputs}.length 0 {outputs} := by",
            f"      rw [hLocalSm{number}, hWeightEq{number}, hIn{number}.full_value, hComm{number}]",
            "      simp only [List.map, List.length_cons, List.length_nil]",
            f"      rw [{', '.join(f'← hLocalPm{number}_{r}' for r in range(k))}]",
        ]
        shape_names = []
        for rank, node in enumerate(rank_nodes):
            name = f"hLocalShape{number}_{rank}"
            shape_names.append(name)
            lines += [
                f"    have {name} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by",
                f"      rw [hLocalPm{number}_{rank}]",
                f"      exact fw_linear_3d_shape {b} {seq} {inner} {width} _ _ (hIn{number}.shard_shapes _ (by simp)) hWeightShape{number}",
            ]
        proof = f"hLocalOut{number}"
        local_proofs[post.fact_id] = proof
        lines += [
            f"    have {proof} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change ShardedRel (smFinal {post.sm_tid}) {outputs} 1 {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
            f"      refine {{ full_value := hLocalValue{number}, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }}",
            f"      · rw [hLocalValue{number}, allGatherPrimDimN_shape 1 {outputs}.length {outputs} {_shape_text(list(post.shard_shape))}]",
            "        · simp only [List.length_cons, List.length_nil]", "          native_decide",
            f"        · simp only [List.head?, Option.map, Option.getD]; exact {shape_names[0]}",
            "      · intro shard hmem",
            "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}",
        ]
        lines += [f"        · exact {name}" for name in shape_names]

    a2a_proofs = {}
    for number, transition, cert, pre, post, rank_nodes, producer in validated_a2as:
        idim, odim = cert.input_gather_dim, cert.output_gather_dim
        input_tids = "[" + ", ".join(str(tid) for tid in pre.pm_tids) + "]"
        output_tids = "[" + ", ".join(str(tid) for tid in post.pm_tids) + "]"
        input_values = "[" + ", ".join(f"pmFinal {tid}" for tid in pre.pm_tids) + "]"
        output_values = "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]"
        if producer is None:
            lines.append(f"    have hA2AIn{number} : {pre.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)")
        else:
            lines.append(f"    have hA2AIn{number} : {pre.fact_id}.Holds smFinal pmFinal := {local_proofs[pre.fact_id]}")
        lines += [
            f"    change ShardedRel (smFinal {pre.sm_tid}) {input_values} {idim} {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hA2AIn{number}",
            f"    let inputTids{number} : List Tid := {input_tids}",
            f"    let outputTids{number} : List Tid := {output_tids}",
            f"    let rankCount{number} := outputTids{number}.length",
            f"    have hRankCount{number} : rankCount{number} = {ir.pm_graph_ref}.numRanks := by native_decide",
            f"    let xs{number} := inputTids{number}.map pmFinal",
            f"    have hHead{number} : ((xs{number}.head?.map (fun t => t.shape)).getD []) = {_shape_text(list(pre.shard_shape))} := by",
            f"      simp only [xs{number}, inputTids{number}, List.map, List.head?, Option.map, Option.getD]",
            f"      exact hA2AIn{number}.shard_shapes (pmFinal {pre.pm_tids[0]}) (by simp)",
            f"    have hRankXs{number} : rankCount{number} = xs{number}.length := by simp [rankCount{number}, outputTids{number}, xs{number}, inputTids{number}]",
        ]
        writer_names, shape_names = [], []
        for rank, (absolute_index, node) in enumerate(zip(transition.pm_node_indices, rank_nodes)):
            pos = pm_pos[absolute_index]
            prefix_store = f"((pmNodes.take {pos}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore)"
            for input_rank, tid in enumerate(pre.pm_tids):
                lines += [
                    f"    have hA2APrefix{number}_{rank}_{input_rank} : {prefix_store} {tid} = pmFinal {tid} := by",
                    f"      have h := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} (pmNodes.drop {pos}) {prefix_store} {tid} (by native_decide) (by native_decide)",
                    f"      rw [← List.foldl_append, show pmNodes.take {pos} ++ pmNodes.drop {pos} = pmNodes by exact List.take_append_drop {pos} pmNodes] at h",
                    "      exact h.symm",
                ]
            lines += [
                f"    have hA2AInputs{number}_{rank} : inputTids{number}.map {prefix_store} = xs{number} := by",
                f"      simp only [inputTids{number}, xs{number}, List.map]",
                f"      rw [{', '.join(f'hA2APrefix{number}_{rank}_{r}' for r in range(k))}]",
            ]
            writer, shape = f"hA2AWriter{number}_{rank}", f"hA2AShape{number}_{rank}"
            writer_names.append(writer); shape_names.append(shape)
            lines += [
                f"    have {writer} : pmFinal {node.outs[0]} = allToAllPrimWithDims rankCount{number} {rank} xs{number} {idim} {odim} := by",
                f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {node.outs[0]} = _",
                f"      rw [show pmNodes = pmNodes.take {pos} ++ [{_node_text(node)}] ++ pmNodes.drop {pos + 1} by native_decide]",
                f"      rw [foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore (pmNodes.take {pos}) (pmNodes.drop {pos + 1})",
                f"        {_node_text(node)} {node.outs[0]} (fun t => allToAllPrimWithDims rankCount{number} {rank} (inputTids{number}.map t) {idim} {odim})]",
                f"      · rw [hA2AInputs{number}_{rank}]",
                "      · intro t",
                "        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
                "          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]",
                f"        rw [hRankCount{number}]",
                f"        simpa [inputTids{number}] using applyNode_allToAllPrimWithDims_out {ir.pm_graph_ref} t {rank} inputTids{number} {node.outs[0]} {idim} {odim}",
                "      · native_decide", "      · native_decide",
                f"    have {shape} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by",
                f"      rw [{writer}, allToAllPrimWithDims_shape rankCount{number} {rank} xs{number} {idim} {odim} {_shape_text(list(pre.shard_shape))} hHead{number} (by native_decide)]",
                "      native_decide",
            ]
        lines += [
            f"    have hOrdered{number} : outputTids{number}.map pmFinal = List.ofFn (fun r : Fin rankCount{number} => allToAllPrimWithDims rankCount{number} r.1 xs{number} {idim} {odim}) := by",
            f"      simp only [outputTids{number}, rankCount{number}, List.map]",
            f"      rw [{', '.join(writer_names)}]", "      rfl",
            f"    have hGatherShape{number} : (allGatherPrimDimN {idim} rankCount{number} 0 xs{number}).shape = {_shape_text(list(pre.full_shape))} := by",
            f"      rw [hRankXs{number}]",
            f"      calc _ = (smFinal {pre.sm_tid}).shape := congrArg (fun t => t.shape) hA2AIn{number}.full_value.symm",
            f"           _ = _ := hA2AIn{number}.full_shape",
            f"    have hOdim{number} : {odim} < (allGatherPrimDimN {idim} rankCount{number} 0 xs{number}).shape.length := by rw [hGatherShape{number}]; native_decide",
            f"    have hDiv{number} : (allGatherPrimDimN {idim} rankCount{number} 0 xs{number}).shape.getD {odim} 0 % rankCount{number} = 0 := by rw [hGatherShape{number}]; native_decide",
            f"    have hOdimXs{number} := hOdim{number}", f"    have hDivXs{number} := hDiv{number}",
            f"    rw [hRankXs{number}] at hOdimXs{number} hDivXs{number}",
        ]
        proof = f"hA2AOut{number}"; a2a_proofs[post.fact_id] = proof
        lines += [
            f"    have {proof} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change ShardedRel (smFinal {post.sm_tid}) {output_values} {odim} {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
            f"      refine {{ full_value := ?_, full_shape := hA2AIn{number}.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }}",
            f"      · rw [show {output_values} = outputTids{number}.map pmFinal by rfl, hOrdered{number}, List.length_ofFn]",
            f"        rw [hRankXs{number}, {a2a_theorem} {idim} {odim} xs{number} (by simp [xs{number}, inputTids{number}]) hOdimXs{number} hDivXs{number}]",
            f"        simp only [rankCount{number}, outputTids{number}, xs{number}, inputTids{number}, List.map, List.length_cons, List.length_nil]",
            f"        exact hA2AIn{number}.full_value",
            "      · intro shard hmem", "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}",
        ]
        lines += [f"        · exact {name}" for name in shape_names]

    proof_by_fact = {**local_proofs, **a2a_proofs}
    lines += [
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        f"      rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}",
    ]
    lines += [f"      · exact {proof_by_fact[fact_id]}" for fact_id in fresh_ids]
    lines += ["    · exact hframe fact old", ""]
    return "\n".join(lines)
