"""Atomic renderer for a positive homogeneous tuple of local dim-1 linears."""
from __future__ import annotations


def render_closed_k_rank_local_linear_tuple_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import KRankLocalRelationCertificate
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import KRankLocalRelationCertificate

    rule = "linear-sharded-k-rank-dim1"
    theorem = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
    chain = relation.dependent_chain_plan
    found = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(found) != 1:
        raise ValueError("local-linear tuple requires one complete closed segment")
    segment = found[0]
    if len(segment.transition_ids) < 2 or len(set(segment.transition_ids)) != len(segment.transition_ids):
        raise ValueError("local-linear tuple requires positive unique transition authority")

    by_id = {}
    for transition in relation.transition_specs:
        by_id.setdefault(transition.transition_id, []).append(transition)
    resolved = [by_id.get(tid, ()) for tid in segment.transition_ids]
    if any(len(items) != 1 for items in resolved):
        raise ValueError("local-linear tuple transition authority is missing or duplicated")
    transitions = [items[0] for items in resolved]
    if any(t.rule_id != rule or t.lean_theorem != theorem
           or len(t.pre_facts) != 1 or len(t.post_facts) != 1 for t in transitions):
        raise ValueError("local-linear tuple theorem contract is malformed")
    certificates = [
        _select_exact_typed_certificate(
            relation, transition, rule, theorem, KRankLocalRelationCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
        for transition in transitions
    ]

    sources = [record.source for record in chain.relation_facts]
    if len(sources) != len(set(sources)):
        raise ValueError("local-linear tuple relation authority is duplicated")
    records = {record.source: record for record in chain.relation_facts}
    state_rows = {state.state_id: state for state in chain.states}
    if len(state_rows) != len(chain.states):
        raise ValueError("local-linear tuple state authority is duplicated")
    try:
        pairs = [(records[c.input_fact], records[c.output_fact]) for c in certificates]
        before, after = state_rows[segment.pre_state_id], state_rows[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("local-linear tuple fact/state is not materialized") from exc
    if any(pre.fact_id not in before.fact_ids for pre, _post in pairs):
        raise ValueError("local-linear tuple input authority is not live")
    fresh_ids = tuple(post.fact_id for _pre, post in pairs)
    if len(fresh_ids) != len(set(fresh_ids)) or not set(fresh_ids) <= set(after.fact_ids):
        raise ValueError("local-linear tuple output publication is malformed")
    if not set(after.fact_ids) <= set(before.fact_ids) | set(fresh_ids):
        raise ValueError("local-linear tuple post-state introduces an unproved fact")

    k_values = {c.rank_count for c in certificates}
    if len(k_values) != 1:
        raise ValueError("local-linear tuple certificates disagree on K")
    k = int(next(iter(k_values)))
    if k <= 0 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("local-linear tuple graph rank authority is malformed")

    sm_range = set(range(*segment.sm_range)); pm_range = set(range(*segment.pm_range))
    sm_owned = tuple(i for t in transitions for i in t.sm_node_indices)
    pm_owned = tuple(i for t in transitions for i in t.pm_node_indices)
    if (len(sm_owned) != len(set(sm_owned)) or len(pm_owned) != len(set(pm_owned))
            or not set(sm_owned) <= sm_range or not set(pm_owned) <= pm_range):
        raise ValueError("local-linear tuple writers overlap or leave the complete frame")

    authorities = tuple(chain.authority_facts)
    validated = []
    for number, (transition, cert, pair) in enumerate(zip(transitions, certificates, pairs)):
        pre, post = pair
        if (cert.op != "FW_linear" or cert.gather_dim != 1
                or len(transition.sm_node_indices) != 1
                or len(transition.pm_node_indices) != k
                or cert.sm_step_id != f"sm:{transition.sm_node_indices[0]}:0"
                or tuple(cert.pm_step_ids) != tuple(f"pm:{i}:0" for i in transition.pm_node_indices)
                or pre.kind != "sharded" or post.kind != "sharded"
                or pre.gather_dim != 1 or post.gather_dim != 1
                or len(pre.pm_tids) != k or len(post.pm_tids) != k
                or len(cert.external_tids) != 1 or len(cert.external_shapes) != 1):
            raise ValueError("local-linear tuple typed authority is malformed")
        sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
        pm_nodes = tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
        weight_tid = cert.external_tids[0]
        if (sm_node.rank != 0 or sm_node.op != "FW_linear" or sm_node.params
                or sm_node.ins != [pre.sm_tid, weight_tid] or sm_node.outs != [post.sm_tid]
                or tuple(node.rank for node in pm_nodes) != tuple(range(k))
                or any(node.op != "FW_linear" or node.params
                       or node.ins != [pre.pm_tids[rank], weight_tid]
                       or node.outs != [post.pm_tids[rank]]
                       for rank, node in enumerate(pm_nodes))):
            raise ValueError("local-linear tuple writer roles/order are malformed")
        eqs = [a for a in authorities if getattr(a, "kind", None) == "tensor_eq"
               and a.left_side == "sm" and a.left_tid == weight_tid
               and a.right_side == "pm" and a.right_tid == weight_tid]
        shapes = [a for a in authorities if getattr(a, "kind", None) == "tensor_shape"
                  and a.side == "pm" and a.tid == weight_tid
                  and tuple(a.shape) == tuple(cert.external_shapes[0])]
        if (len(eqs) != 1 or len(shapes) != 1
                or eqs[0].fact_id not in before.fact_ids
                or shapes[0].fact_id not in before.fact_ids):
            raise ValueError("local-linear tuple external authority is not exact and live")
        if (len(pre.shard_shape) != 3 or any(v <= 0 for v in pre.shard_shape)
                or tuple(pre.full_shape) != (pre.shard_shape[0], pre.shard_shape[1] * k, pre.shard_shape[2])
                or tuple(post.shard_shape) != (pre.shard_shape[0], pre.shard_shape[1], cert.external_shapes[0][0])
                or tuple(post.full_shape) != (post.shard_shape[0], post.shard_shape[1] * k, post.shard_shape[2])
                or tuple(cert.external_shapes[0]) != (post.shard_shape[2], pre.shard_shape[2])):
            raise ValueError("local-linear tuple shape authority is inconsistent")
        validated.append((number, transition, cert, pre, post, sm_node, pm_nodes, eqs[0], shapes[0]))

    sm_frame = ir.sm_nodes[slice(*segment.sm_range)]
    pm_frame = ir.pm_nodes[slice(*segment.pm_range)]
    sm_pos = {i: i - segment.sm_range[0] for i in range(*segment.sm_range)}
    pm_pos = {i: i - segment.pm_range[0] for i in range(*segment.pm_range)}
    sm_name, pm_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    lines = [
        f"private def {sm_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]", "",
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
    for number, _t, cert, pre, _post, _sm, _pms, eq, shape in validated:
        inputs = ", ".join(f"pmStore {tid}" for tid in pre.pm_tids)
        lines += [
            f"    have hIn{number} : {pre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    change ShardedRel (smStore {pre.sm_tid}) [{inputs}] 1 {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))} at hIn{number}",
            f"    have hWeightEq{number} : {eq.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    change smStore {cert.external_tids[0]} = pmStore {cert.external_tids[0]} at hWeightEq{number}",
            f"    have hWeightShape{number} : {shape.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)",
            f"    change (pmStore {cert.external_tids[0]}).shape = {_shape_text(list(cert.external_shapes[0]))} at hWeightShape{number}",
        ]

    def writer_lines(name, side, absolute_index, node):
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        store = "smStore" if side == "sm" else "pmStore"
        nodes = "smNodes" if side == "sm" else "pmNodes"
        final = "smFinal" if side == "sm" else "pmFinal"
        pos = sm_pos[absolute_index] if side == "sm" else pm_pos[absolute_index]
        return [
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
        ]

    for number, transition, _cert, _pre, _post, sm_node, pms, _eq, _shape in validated:
        lines += writer_lines(f"hLocalSm{number}", "sm", transition.sm_node_indices[0], sm_node)
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pms)):
            lines += writer_lines(f"hLocalPm{number}_{rank}", "pm", index, node)

    proof_names = {}
    for number, _transition, cert, pre, post, _sm, pms, _eq, _shape in validated:
        b, seq, inner = pre.shard_shape; out_width = post.shard_shape[2]
        inputs = "[" + ", ".join(f"pmStore {tid}" for tid in pre.pm_tids) + "]"
        outputs = "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]"
        lines += [
            f"    have hComm{number} := ({theorem} (K := {inputs}.length) (b := {b}) (s := {seq}) (i := {inner}) (o := {out_width}) (xs := {inputs}) (w := pmStore {cert.external_tids[0]}) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn{number}.shard_shapes x hx) hWeightShape{number})",
            f"    have hLocalValue{number} : smFinal {post.sm_tid} = allGatherPrimDimN 1 {outputs}.length 0 {outputs} := by",
            f"      rw [hLocalSm{number}, hWeightEq{number}, hIn{number}.full_value, hComm{number}]",
            "      simp only [List.map, List.length_cons, List.length_nil]",
            f"      rw [{', '.join(f'← hLocalPm{number}_{rank}' for rank in range(k))}]",
        ]
        shape_names = []
        for rank, node in enumerate(pms):
            shape_name = f"hLocalShape{number}_{rank}"; shape_names.append(shape_name)
            lines += [
                f"    have {shape_name} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by",
                f"      rw [hLocalPm{number}_{rank}]",
                f"      exact fw_linear_3d_shape {b} {seq} {inner} {out_width} _ _ (hIn{number}.shard_shapes _ (by simp)) hWeightShape{number}",
            ]
        proof_name = f"hLocalOut{number}"; proof_names[post.fact_id] = proof_name
        lines += [
            f"    have {proof_name} : {post.fact_id}.Holds smFinal pmFinal := by",
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

    lines += [
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        f"      rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}",
    ]
    lines += [f"      · exact {proof_names[fact_id]}" for fact_id in fresh_ids]
    lines += ["    · exact hframe fact old", ""]
    return "\n".join(lines)
