"""Atomic renderer for a positive local-linear and AllGather tuples."""
from __future__ import annotations


def render_closed_k_rank_local_linear_allgather_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankLocalRelationCertificate,
        )
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankLocalRelationCertificate,
        )

    local_rule = "linear-sharded-k-rank-dim1"
    gather_rule = "allgather-reconstruction-k-rank"
    local_theorem = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
    gather_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"

    chain = relation.dependent_chain_plan
    matches = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(matches) != 1:
        raise ValueError("local-linear/AllGather requires one complete closed segment")
    segment = matches[0]
    if len(segment.transition_ids) < 2 or len(set(segment.transition_ids)) != len(segment.transition_ids):
        raise ValueError("local-linear/AllGather requires a positive unique local tuple")
    by_id = {}
    for transition in relation.transition_specs:
        by_id.setdefault(transition.transition_id, []).append(transition)
    resolved = [by_id.get(tid, ()) for tid in segment.transition_ids]
    if any(len(items) != 1 for items in resolved):
        raise ValueError("local-linear/AllGather transition authority is missing or duplicated")
    transitions = [items[0] for items in resolved]
    split = next((i for i, t in enumerate(transitions) if t.rule_id == gather_rule), len(transitions))
    locals_, gathers = transitions[:split], transitions[split:]
    if (not locals_ or not gathers
            or any(t.rule_id != local_rule or t.lean_theorem != local_theorem
                   or len(t.pre_facts) != 1 or len(t.post_facts) != 1 for t in locals_)
            or any(t.rule_id != gather_rule or t.lean_theorem != gather_theorem
                   or len(t.pre_facts) != 1 or len(t.post_facts) != 1 for t in gathers)):
        raise ValueError("local-linear/AllGather ordered theorem contract is malformed")

    local_certs = [
        _select_exact_typed_certificate(
            relation, transition, local_rule, local_theorem,
            KRankLocalRelationCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
        for transition in locals_
    ]
    gather_certs = [_select_exact_typed_certificate(
        relation, t, gather_rule, gather_theorem,
        KRankAllGatherReconstructionCertificate,
        lambda cert: ((cert.input_fact,), (cert.output_fact,)),
    ) for t in gathers]

    sources = [record.source for record in chain.relation_facts]
    if len(sources) != len(set(sources)):
        raise ValueError("local-linear/AllGather relation authority is duplicated")
    records = {record.source: record for record in chain.relation_facts}
    try:
        local_pairs = [(records[c.input_fact], records[c.output_fact]) for c in local_certs]
        gather_pairs = [(records[c.input_fact], records[c.output_fact]) for c in gather_certs]
    except KeyError as exc:
        raise ValueError("local-linear/AllGather relation fact is not materialized") from exc
    state_rows = {state.state_id: state for state in chain.states}
    if len(state_rows) != len(chain.states):
        raise ValueError("local-linear/AllGather state authority is duplicated")
    try:
        before, after = state_rows[segment.pre_state_id], state_rows[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("local-linear/AllGather framing state is not materialized") from exc
    if (len(set(before.fact_ids)) != len(before.fact_ids)
            or len(set(after.fact_ids)) != len(after.fact_ids)):
        raise ValueError("local-linear/AllGather framing contains duplicate facts")
    local_post_ids = {post.fact_id for _, post in local_pairs}
    if any(pre.fact_id not in before.fact_ids for pre, _ in local_pairs):
        raise ValueError("local-linear input authority is not live")
    if any(pre.fact_id not in before.fact_ids and pre.fact_id not in local_post_ids for pre, _ in gather_pairs):
        raise ValueError("AllGather input is neither live nor produced by this component")
    fresh_ids = tuple(dict.fromkeys([*(post.fact_id for _, post in local_pairs), *(post.fact_id for _, post in gather_pairs)]))
    if any(post.fact_id not in after.fact_ids for _, post in gather_pairs):
        raise ValueError("AllGather joined result is not published")
    if not set(after.fact_ids) <= set(before.fact_ids) | set(fresh_ids):
        raise ValueError("local-linear/AllGather post-state introduces an unproved fact")

    k = int(gather_certs[0].rank_count)
    if k <= 0 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("local-linear/AllGather dynamic graph rank authority is malformed")
    if any(c.rank_count != k for c in (*local_certs, *gather_certs)):
        raise ValueError("local-linear certificates disagree with dynamic rank authority")

    sm_indices = tuple(range(*segment.sm_range))
    pm_indices = tuple(range(*segment.pm_range))
    sm_owned = tuple(index for t in transitions for index in t.sm_node_indices)
    pm_owned = tuple(index for t in transitions for index in t.pm_node_indices)
    if (len(sm_owned) != len(set(sm_owned)) or set(sm_owned) != set(sm_indices)
            or len(pm_owned) != len(set(pm_owned)) or set(pm_owned) != set(pm_indices)
            or any(index < 0 or index >= len(ir.sm_nodes) for index in sm_owned)
            or any(index < 0 or index >= len(ir.pm_nodes) for index in pm_owned)):
        raise ValueError("local-linear/AllGather footprints do not exactly partition both axes")
    if any(t.sm_node_indices or len(t.pm_node_indices) != 1 for t in gathers):
        raise ValueError("AllGather footprint is not exact")

    authorities = tuple(chain.authority_facts)
    validated_locals = []
    for number, (transition, cert, pair) in enumerate(zip(locals_, local_certs, local_pairs)):
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
            raise ValueError("local-linear typed authority is malformed")
        sm_index = transition.sm_node_indices[0]
        sm_node = ir.sm_nodes[sm_index]
        pm_nodes = [ir.pm_nodes[i] for i in transition.pm_node_indices]
        weight_tid = cert.external_tids[0]
        if (sm_node.rank != 0 or sm_node.op != "FW_linear" or sm_node.params
                or sm_node.ins != [pre.sm_tid, weight_tid] or sm_node.outs != [post.sm_tid]
                or tuple(node.rank for node in pm_nodes) != tuple(range(k))
                or any(node.op != "FW_linear" or node.params
                       or node.ins != [pre.pm_tids[rank], weight_tid]
                       or node.outs != [post.pm_tids[rank]]
                       for rank, node in enumerate(pm_nodes))):
            raise ValueError("local-linear writer roles/order are malformed")
        eqs = [a for a in authorities if (
            getattr(a, "kind", None) == "tensor_eq"
            and a.left_side == "sm" and a.left_tid == weight_tid
            and a.right_side == "pm" and a.right_tid == weight_tid
        )]
        shapes = [a for a in authorities if (
            getattr(a, "kind", None) == "tensor_shape"
            and a.side == "pm" and a.tid == weight_tid
            and tuple(a.shape) == tuple(cert.external_shapes[0])
        )]
        if (len(eqs) != 1 or len(shapes) != 1
                or eqs[0].fact_id not in before.fact_ids
                or shapes[0].fact_id not in before.fact_ids):
            raise ValueError("local-linear external equality/shape authority is not exact and live")
        if (len(pre.shard_shape) != 3 or any(value <= 0 for value in pre.shard_shape)
                or tuple(pre.full_shape) != (pre.shard_shape[0], pre.shard_shape[1] * k, pre.shard_shape[2])
                or tuple(post.shard_shape) != (pre.shard_shape[0], pre.shard_shape[1], cert.external_shapes[0][0])
                or tuple(post.full_shape) != (post.shard_shape[0], post.shard_shape[1] * k, post.shard_shape[2])
                or tuple(cert.external_shapes[0]) != (post.shard_shape[2], pre.shard_shape[2])):
            raise ValueError("local-linear shape authority is inconsistent")
        validated_locals.append((number, transition, cert, pre, post, sm_node, pm_nodes, eqs[0], shapes[0]))

    validated_gathers = []
    for gather, gather_cert, (gather_pre, joined) in zip(gathers, gather_certs, gather_pairs):
        gather_index = gather.pm_node_indices[0]
        gather_node = ir.pm_nodes[gather_index]
        reconstructed = list(gather_pre.shard_shape)
        dim = int(gather_cert.gather_dim)
        if (gather_cert.pm_allgather_step != f"pm:{gather_index}:0"
                or gather_node.rank != 0 or gather_node.op != "AllGatherPrim"
                or tuple(gather_node.params or ()) != (dim,)
                or tuple(gather_node.ins) != gather_pre.pm_tids
                or gather_node.outs != [joined.joined_pm_tid]
                or gather_pre.kind != "sharded" or gather_pre.gather_dim != dim
                or joined.kind != "joined" or joined.pm_tids != ()
                or joined.sm_tid != gather_pre.sm_tid
                or len(gather_pre.pm_tids) != k
                or dim < 0 or dim >= len(reconstructed)
                or tuple(gather_pre.full_shape) != tuple(gather_cert.full_shape)
                or tuple(gather_pre.shard_shape) != tuple(gather_cert.shard_shape)
                or tuple(joined.full_shape) != tuple(gather_cert.full_shape)):
            raise ValueError("AllGather reconstruction authority is malformed")
        reconstructed[dim] *= k
        if tuple(reconstructed) != tuple(gather_pre.full_shape):
            raise ValueError("AllGather reconstruction shape is inexact")
        producer_number = next(
            (number for number, _t, _c, _pre, post, *_rest in validated_locals
             if post.fact_id == gather_pre.fact_id),
            None,
        )
        if producer_number is not None:
            producer_indices = validated_locals[producer_number][1].pm_node_indices
            if any(index >= gather_index for index in producer_indices):
                raise ValueError("AllGather executes before its local-linear producer")

        validated_gathers.append((gather_index, gather_node, gather_pre, joined, dim, producer_number))

    # A source record is authority, not merely a cache of convenient TIDs.
    # Resolve against the latest writer at the store where its proof is read.
    def check_source(ref, side, tid, limit, rank=None):
        nodes = ir.sm_nodes if side == "sm" else ir.pm_nodes
        pieces = ref.split(":")
        if len(pieces) == 2 and pieces[0] == "init" and pieces[1].isdigit():
            if ref != f"init:{tid}":
                raise ValueError("relation source resolved TID disagrees")
            writer = -1
        elif (len(pieces) == 3 and pieces[0] == side
              and pieces[1].isdigit() and pieces[2].isdigit()):
            writer, output = int(pieces[1]), int(pieces[2])
            if (ref != f"{side}:{writer}:{output}" or not 0 <= writer < limit
                    or output >= len(nodes[writer].outs)
                    or nodes[writer].outs[output] != tid
                    or (rank is not None and nodes[writer].rank != rank)):
                raise ValueError("relation source writer/projection/rank is malformed")
        else:
            raise ValueError("relation source axis or reference is malformed")
        if any(tid in node.outs for node in nodes[writer + 1:limit]):
            raise ValueError("relation source is not the latest writer at its read point")

    used_records = {r.fact_id: r for pair in (*local_pairs, *gather_pairs) for r in pair}
    if len({r.fact_id for r in chain.relation_facts}) != len(chain.relation_facts):
        raise ValueError("relation fact IDs are duplicated")
    for record in used_records.values():
        source = record.source
        if (source.layout != record.kind or source.gather_dim != record.gather_dim
                or source.source_step_triples or record.source_tid_triples
                or record.metadata_tid is not None or record.metadata_region_id is not None):
            raise ValueError("relation source layout/axis disagrees with materialized record")
        initial = record.fact_id in before.fact_ids
        sm_limit = segment.sm_range[0 if initial else 1]
        pm_limit = segment.pm_range[0 if initial else 1]
        if len(source.step_triple) != 1 + len(record.pm_tids):
            raise ValueError("relation source ordered rank arity disagrees")
        check_source(source.step_triple[0], "sm", record.sm_tid, sm_limit, 0)
        for rank, (ref, tid) in enumerate(zip(source.step_triple[1:], record.pm_tids)):
            check_source(ref, "pm", tid, pm_limit, rank)
        if record.kind == "joined":
            if source.joined_pm_step is None or record.joined_pm_tid is None:
                raise ValueError("joined source is missing")
            check_source(source.joined_pm_step, "pm", record.joined_pm_tid, pm_limit, 0)
        elif source.joined_pm_step is not None or record.joined_pm_tid is not None:
            raise ValueError("sharded source has joined authority")

    # The existing proof frames the entire pre-state, and each new output is
    # observed in the same final store. Reject writes that invalidate either.
    protected = {"sm": set(), "pm": set()}
    record_by_id = {r.fact_id: r for r in chain.relation_facts}
    authority_by_id = {a.fact_id: a for a in authorities}
    if len(authority_by_id) != len(authorities) or set(record_by_id) & set(authority_by_id):
        raise ValueError("closed authority IDs are duplicated")
    for fact_id in before.fact_ids:
        if fact_id in record_by_id:
            r = record_by_id[fact_id]
            protected["sm"].add(r.sm_tid)
            protected["pm"].update(r.pm_tids)
            if r.joined_pm_tid is not None:
                protected["pm"].add(r.joined_pm_tid)
        elif fact_id in authority_by_id:
            a = authority_by_id[fact_id]
            if a.kind == "tensor_eq":
                protected[a.left_side].add(a.left_tid)
                protected[a.right_side].add(a.right_tid)
            elif a.kind == "tensor_shape":
                protected[a.side].add(a.tid)
            else:
                raise ValueError("unsupported live authority framing")
        elif fact_id != chain.anchor_fact.fact_id:
            raise ValueError("pre-state fact is not materialized")
    anchor = chain.anchor_fact
    if anchor.side not in protected:
        raise ValueError("anchor side is malformed")
    protected[anchor.side].add(anchor.tid)
    for side, nodes, bounds in (("sm", ir.sm_nodes, segment.sm_range), ("pm", ir.pm_nodes, segment.pm_range)):
        if any(protected[side].intersection(node.outs) for node in nodes[slice(*bounds)]):
            raise ValueError("component overwrites protected pre-state/anchor authority")

    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_pos = {index: index - segment.sm_range[0] for index in sm_indices}
    pm_pos = {index: index - segment.pm_range[0] for index in pm_indices}
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

    for number, _transition, cert, pre, _post, _sm, _pms, eq, shape in validated_locals:
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

    for number, transition, _cert, _pre, _post, sm_node, local_pm_nodes, _eq, _shape in validated_locals:
        lines += writer_lines(f"hLocalSm{number}", "sm", transition.sm_node_indices[0], sm_node)
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, local_pm_nodes)):
            lines += writer_lines(f"hLocalPm{number}_{rank}", "pm", index, node)

    for gather_number, (gather_index, gather_node, gather_pre, joined, dim, producer_number) in enumerate(validated_gathers):
        start = len(lines)
        gather_pos = pm_pos[gather_index]
        prefix = f"(pmNodes.take {gather_pos})"
        suffix = f"(pmNodes.drop {gather_pos + 1})"
        prefix_inputs = ", ".join(
            f"(({prefix}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {tid}"
            for tid in gather_pre.pm_tids
        )
        final_inputs = ", ".join(f"pmFinal {tid}" for tid in gather_pre.pm_tids)
        lines += [
            f"    have hGatherRaw : pmFinal {joined.joined_pm_tid} = allGatherPrimDimN {dim} {k} 0 [{prefix_inputs}] := by",
            f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined.joined_pm_tid} = _",
            "      conv_lhs =>",
            f"        rw [show pmNodes = {prefix} ++ [{_node_text(gather_node)}] ++ {suffix} by native_decide]",
            f"      rw [foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {prefix} {suffix}",
            f"        {_node_text(gather_node)} {joined.joined_pm_tid} (fun t => allGatherPrimDimN {dim} {k} 0 [{', '.join(f't {tid}' for tid in gather_pre.pm_tids)}]) (by",
            "          intro t",
            "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "          simp [applyNodeDistributed, applyNodeRingAttn]",
            f"          exact applyNode_allGatherPrimDimN_out {ir.pm_graph_ref} t 0 [{', '.join(str(tid) for tid in gather_pre.pm_tids)}] {joined.joined_pm_tid} {dim}",
            "        ) (by native_decide) (by native_decide)]",
        ]
        for rank, tid in enumerate(gather_pre.pm_tids):
            lines += [
                f"    have hGatherInputFinal{rank} : (({prefix}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {tid} = pmFinal {tid} := by",
                f"      have h := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} (pmNodes.drop {gather_pos}) (({prefix}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {tid} (by native_decide) (by native_decide)",
                f"      rw [← List.foldl_append, show {prefix} ++ pmNodes.drop {gather_pos} = pmNodes by exact List.take_append_drop {gather_pos} pmNodes] at h",
                "      exact h.symm",
            ]
        lines += [
            f"    have hGatherWriter : pmFinal {joined.joined_pm_tid} = allGatherPrimDimN {dim} {k} 0 [{final_inputs}] := by",
            "      rw [hGatherRaw]",
            f"      rw [{', '.join(f'hGatherInputFinal{rank}' for rank in range(k))}]",
        ]

        if len(gathers) > 1:
            lines[start:] = [line.replace("hGather", f"hGather{gather_number}_") for line in lines[start:]]

    local_proof_names = {}
    for number, _transition, cert, pre, post, _sm, local_pm_nodes, _eq, _shape in validated_locals:
        b, seq, inner = pre.shard_shape
        out_width = post.shard_shape[2]
        inputs = "[" + ", ".join(f"pmStore {tid}" for tid in pre.pm_tids) + "]"
        outputs = "[" + ", ".join(f"pmFinal {tid}" for tid in post.pm_tids) + "]"
        lines += [
            f"    have hComm{number} := ({local_theorem} (K := {inputs}.length) (b := {b}) (s := {seq}) (i := {inner}) (o := {out_width}) (xs := {inputs}) (w := pmStore {cert.external_tids[0]}) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn{number}.shard_shapes x hx) hWeightShape{number})",
            f"    have hLocalValue{number} : smFinal {post.sm_tid} = allGatherPrimDimN 1 {outputs}.length 0 {outputs} := by",
            f"      rw [hLocalSm{number}, hWeightEq{number}, hIn{number}.full_value, hComm{number}]",
            "      simp only [List.map, List.length_cons, List.length_nil]",
            f"      rw [{', '.join(f'← hLocalPm{number}_{rank}' for rank in range(k))}]",
        ]
        shape_names = []
        for rank, node in enumerate(local_pm_nodes):
            shape_name = f"hLocalShape{number}_{rank}"
            shape_names.append(shape_name)
            lines += [
                f"    have {shape_name} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by",
                f"      rw [hLocalPm{number}_{rank}]",
                f"      exact fw_linear_3d_shape {b} {seq} {inner} {out_width} _ _ (hIn{number}.shard_shapes _ (by simp)) hWeightShape{number}",
            ]
        proof_name = f"hLocalOut{number}"
        local_proof_names[post.fact_id] = proof_name
        lines += [
            f"    have {proof_name} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change ShardedRel (smFinal {post.sm_tid}) {outputs} 1 {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
            f"      refine {{ full_value := hLocalValue{number}, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }}",
            f"      · rw [hLocalValue{number}, allGatherPrimDimN_shape 1 {outputs}.length {outputs} {_shape_text(list(post.shard_shape))}]",
            "        · simp only [List.length_cons, List.length_nil]",
            "          native_decide",
            f"        · simp only [List.head?, Option.map, Option.getD]; exact {shape_names[0]}",
            "      · intro shard hmem",
            "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}",
        ]
        lines += [f"        · exact {name}" for name in shape_names]

    joined_proof_names = {}
    for gather_number, (gather_index, gather_node, gather_pre, joined, dim, producer_number) in enumerate(validated_gathers):
        final_inputs = ", ".join(f"pmFinal {tid}" for tid in gather_pre.pm_tids)
        start = len(lines)
        if producer_number is None:
            lines += [
                f"    have hGatherFinal : {gather_pre.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            ]
        else:
            lines += [
                f"    have hGatherFinal : {gather_pre.fact_id}.Holds smFinal pmFinal := hLocalOut{producer_number}",
            ]
        lines += [
            f"    change ShardedRel (smFinal {gather_pre.sm_tid}) [{final_inputs}] {dim} {_shape_text(list(gather_pre.full_shape))} {_shape_text(list(gather_pre.shard_shape))} at hGatherFinal",
            f"    have hJoinedValue : smFinal {joined.sm_tid} = pmFinal {joined.joined_pm_tid} := by",
            f"      rw [{gather_theorem} hGatherFinal]",
            "      simp only [List.length_cons, List.length_nil]",
            "      exact hGatherWriter.symm",
            f"    have hJoinedOut : {joined.fact_id}.Holds smFinal pmFinal := by",
            f"      change smFinal {joined.sm_tid} = pmFinal {joined.joined_pm_tid} ∧ (smFinal {joined.sm_tid}).shape = {_shape_text(list(joined.full_shape))} ∧ (pmFinal {joined.joined_pm_tid}).shape = {_shape_text(list(joined.full_shape))}",
            "      refine ⟨hJoinedValue, hGatherFinal.full_shape, ?_⟩",
            "      rw [← hJoinedValue]",
            "      exact hGatherFinal.full_shape",
        ]
        if len(gathers) > 1:
            lines[start:] = [line.replace("hGather", f"hGather{gather_number}_").replace("hJoined", f"hJoined{gather_number}_") for line in lines[start:]]
        joined_proof_names[joined.fact_id] = f"hJoined{gather_number}_Out" if len(gathers) > 1 else "hJoinedOut"
    lines += [
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        f"      rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}",
    ]
    proof_by_fact = {**local_proof_names, **joined_proof_names}
    lines += [f"      · exact {proof_by_fact[fact_id]}" for fact_id in fresh_ids]
    lines += ["    · exact hframe fact old", ""]
    return "\n".join(lines)
