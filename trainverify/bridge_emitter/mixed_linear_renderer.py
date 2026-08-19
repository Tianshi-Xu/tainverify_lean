"""Atomic closed renderer for the mixed K-rank linear/reconstruction tuple."""
from __future__ import annotations


def render_closed_mixed_k_rank_linear_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate
        from .relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankLocalRelationCertificate,
            KRankOutputShardedLinearCertificate,
        )
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate
        from relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankLocalRelationCertificate,
            KRankOutputShardedLinearCertificate,
        )

    local_rule = "linear-sharded-k-rank-dim1"
    gather_rule = "allgather-reconstruction-k-rank"
    output_rule = "linear-output-sharded-k-rank"
    local_theorem = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
    gather_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"
    output_theorem = "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm"
    family = (local_rule, local_rule, gather_rule, output_rule)

    chain = relation.dependent_chain_plan
    segment = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) != 4:
        raise ValueError("mixed K-rank linear renderer requires one exact four-transition component")
    transition_map = {t.transition_id: t for t in relation.transition_specs}
    try:
        transitions = tuple(transition_map[t] for t in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("mixed K-rank linear component has an unresolved transition") from exc
    if tuple(t.rule_id for t in transitions) != family:
        raise ValueError("mixed K-rank linear transition order is not the registered family tuple")

    local_certs = []
    for transition in transitions[:2]:
        local_certs.append(_select_exact_typed_certificate(
            relation, transition, local_rule, local_theorem,
            KRankLocalRelationCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        ))
    gather_cert = _select_exact_typed_certificate(
        relation, transitions[2], gather_rule, gather_theorem,
        KRankAllGatherReconstructionCertificate,
        lambda cert: ((cert.input_fact,), (cert.output_fact,)),
    )
    output_cert = _select_exact_typed_certificate(
        relation, transitions[3], output_rule, output_theorem,
        KRankOutputShardedLinearCertificate,
        lambda cert: (tuple(sorted((cert.activation_fact, cert.weight_fact))), (cert.output_fact,)),
    )
    certs = (*local_certs, gather_cert, output_cert)

    records = {r.source: r for r in chain.relation_facts}
    try:
        local_inputs = tuple(records[c.input_fact] for c in local_certs)
        local_outputs = tuple(records[c.output_fact] for c in local_certs)
        gather_input = records[gather_cert.input_fact]
        joined = records[gather_cert.output_fact]
        weight = records[output_cert.weight_fact]
        final_output = records[output_cert.output_fact]
    except KeyError as exc:
        raise ValueError("mixed K-rank linear fact is not materialized") from exc
    if output_cert.activation_fact != gather_cert.output_fact:
        raise ValueError("mixed K-rank output activation is not the exact reconstruction result")
    states = {s.state_id: s for s in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required_pre = {r.fact_id for r in (*local_inputs, gather_input, weight)}
    required_post = {r.fact_id for r in (*local_outputs, final_output)}
    if not required_pre <= set(before.fact_ids):
        raise ValueError("mixed K-rank linear input authority is not live")
    if not required_post <= set(after.fact_ids):
        raise ValueError("mixed K-rank linear retained outputs are not live")
    if joined.fact_id in after.fact_ids:
        raise ValueError("mixed K-rank joined intermediate must be consumed before post-state")
    if not set(after.fact_ids) <= (required_post | set(before.fact_ids)):
        raise ValueError("mixed K-rank linear post-state introduces an unproved fact")

    k = len(gather_input.pm_tids)
    if k <= 0:
        raise ValueError("mixed K-rank linear rank authority is empty")
    if any(c.rank_count != k for c in certs):
        raise ValueError("mixed K-rank linear certificates disagree with dynamic authority")
    if any(len(r.pm_tids) != k for r in (*local_inputs, *local_outputs, gather_input, weight, final_output)):
        raise ValueError("mixed K-rank linear ordered authority lengths disagree")
    if any(r.kind != "sharded" or r.gather_dim != 1 for r in (*local_inputs, *local_outputs, gather_input)):
        raise ValueError("mixed K-rank local/reconstruction facts require dim1 sharding")
    if joined.kind != "joined" or joined.pm_tids != () or joined.joined_pm_tid is None:
        raise ValueError("mixed K-rank reconstruction result is not canonical joined authority")
    if weight.kind != "sharded" or weight.gather_dim != 0 or final_output.kind != "sharded" or final_output.gather_dim != 2:
        raise ValueError("mixed K-rank output-linear facts have wrong roles")

    sm_range = tuple(range(*segment.sm_range))
    pm_range = tuple(range(*segment.pm_range))
    sm_owned = tuple(i for t in transitions for i in t.sm_node_indices)
    pm_owned = tuple(i for t in transitions for i in t.pm_node_indices)
    if len(set(sm_owned)) != len(sm_owned) or set(sm_owned) != set(sm_range):
        raise ValueError("mixed K-rank SM footprints do not exactly partition the atomic range")
    if len(set(pm_owned)) != len(pm_owned) or set(pm_owned) != set(pm_range):
        raise ValueError("mixed K-rank PM footprints do not exactly partition the atomic range")
    for transition, cert in zip(transitions, certs):
        expected_sm = (() if isinstance(cert, KRankAllGatherReconstructionCertificate)
                       else (int(cert.sm_step_id.split(":")[1]),))
        expected_pm = ((int(cert.pm_allgather_step.split(":")[1]),)
                       if isinstance(cert, KRankAllGatherReconstructionCertificate)
                       else tuple(int(s.split(":")[1]) for s in cert.pm_step_ids))
        if transition.sm_node_indices != expected_sm or transition.pm_node_indices != expected_pm:
            raise ValueError("mixed K-rank certificate footprint was tampered")

    sm_nodes = tuple(ir.sm_nodes[i] for i in sm_range)
    pm_nodes = tuple(ir.pm_nodes[i] for i in pm_range)
    sm_pos = {index: index - segment.sm_range[0] for index in sm_range}
    pm_pos = {index: index - segment.pm_range[0] for index in pm_range}

    def validate_linear(cert, pre, post, transition, *, joined_input=False, weight_input=None):
        sm_index = transition.sm_node_indices[0]
        sm = ir.sm_nodes[sm_index]
        pms = tuple(ir.pm_nodes[i] for i in transition.pm_node_indices)
        if sm.rank != 0 or sm.op != "FW_linear" or tuple(n.rank for n in pms) != tuple(range(k)):
            raise ValueError("mixed K-rank linear writer order/ranks were tampered")
        if any(n.op != "FW_linear" or n.params or len(n.ins) != 2 or len(n.outs) != 1 for n in (sm, *pms)):
            raise ValueError("mixed K-rank linear writer signature was tampered")
        if joined_input:
            if sm.ins != [joined.sm_tid, weight_input.sm_tid] or sm.outs != [post.sm_tid]:
                raise ValueError("mixed K-rank output-linear SM roles were tampered")
            if tuple(n.ins[0] for n in pms) != (joined.joined_pm_tid,) * k:
                raise ValueError("mixed K-rank joined activation role was tampered")
            if tuple(n.ins[1] for n in pms) != weight_input.pm_tids:
                raise ValueError("mixed K-rank output weight order was tampered")
        else:
            ext = cert.external_tids
            if len(ext) != 1 or len(cert.external_shapes) != 1:
                raise ValueError("mixed K-rank local external role certificate was tampered")
            if sm.ins != [pre.sm_tid, ext[0]] or sm.outs != [post.sm_tid]:
                raise ValueError("mixed K-rank local SM roles were tampered")
            if tuple(n.ins for n in pms) != tuple([pre.pm_tids[r], ext[0]] for r in range(k)):
                raise ValueError("mixed K-rank local PM roles/order were tampered")
        if tuple(n.outs[0] for n in pms) != post.pm_tids:
            raise ValueError("mixed K-rank linear output order was tampered")

    for c, pre, post, t in zip(local_certs, local_inputs, local_outputs, transitions[:2]):
        validate_linear(c, pre, post, t)
    validate_linear(output_cert, joined, final_output, transitions[3], joined_input=True, weight_input=weight)
    gather_index = transitions[2].pm_node_indices[0]
    gather_node = ir.pm_nodes[gather_index]
    if (gather_node.rank != 0 or gather_node.op != "AllGatherPrim"
            or gather_node.ins != list(gather_input.pm_tids)
            or gather_node.outs != [joined.joined_pm_tid]
            or gather_node.params != [1]):
        raise ValueError("mixed K-rank reconstruction writer role/order was tampered")

    # Exact shape authority required by the three existing singleton theorem obligations.
    for c, pre, post in zip(local_certs, local_inputs, local_outputs):
        if (pre.full_shape[1] != pre.shard_shape[1] * k or pre.full_shape[0] != pre.shard_shape[0]
                or pre.full_shape[2] != pre.shard_shape[2] or post.full_shape[1] != post.shard_shape[1] * k
                or tuple(c.external_shapes[0]) != (post.shard_shape[2], pre.shard_shape[2])):
            raise ValueError("mixed K-rank local shape authority is inconsistent")
    if (tuple(gather_input.full_shape) != tuple(gather_cert.full_shape)
            or tuple(gather_input.shard_shape) != tuple(gather_cert.shard_shape)
            or tuple(joined.full_shape) != tuple(gather_cert.full_shape)):
        raise ValueError("mixed K-rank reconstruction shapes disagree")
    if (tuple(joined.full_shape) != tuple(output_cert.activation_shape)
            or tuple(weight.full_shape) != tuple(output_cert.weight_full_shape)
            or tuple(weight.shard_shape) != tuple(output_cert.weight_shard_shape)
            or tuple(final_output.full_shape) != tuple(output_cert.output_full_shape)
            or tuple(final_output.shard_shape) != tuple(output_cert.output_shard_shape)):
        raise ValueError("mixed K-rank output-linear shapes disagree")

    sid = segment_id
    sm_nodes_name, pm_nodes_name = f"{sid}_sm_nodes", f"{sid}_pm_nodes"
    lines = [
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_nodes)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_nodes)}]", "",
        f"private def {sid} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}", "  sound := by",
        "    intro smStore pmStore hstate",
        f"    let smNodes : List NodeDecl := {sm_nodes_name}",
        f"    let pmNodes : List NodeDecl := {pm_nodes_name}",
        f"    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore",
        f"    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        "      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
    ]

    def fact_hyp(name, record, change):
        lines.extend([f"    have {name} : {record.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)", f"    change {change} at {name}"])

    for j, (c, pre) in enumerate(zip(local_certs, local_inputs)):
        fact_hyp(f"hLocalIn{j}", pre, f"ShardedRel (smStore {pre.sm_tid}) [{', '.join(f'pmStore {t}' for t in pre.pm_tids)}] 1 {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))}")
        eq_id = next(a.fact_id for a in chain.authority_facts if getattr(a, "left_tid", None) == c.external_tids[0] and getattr(a, "right_tid", None) == c.external_tids[0])
        shape_id = next(a.fact_id for a in chain.authority_facts if getattr(a, "tid", None) == c.external_tids[0] and tuple(getattr(a, "shape", ())) == tuple(c.external_shapes[0]))
        fact_hyp(f"hLocalEq{j}", type("R", (), {"fact_id": eq_id})(), f"smStore {c.external_tids[0]} = pmStore {c.external_tids[0]}")
        fact_hyp(f"hLocalShape{j}", type("R", (), {"fact_id": shape_id})(), f"(pmStore {c.external_tids[0]}).shape = {_shape_text(list(c.external_shapes[0]))}")
    fact_hyp("hGatherIn", gather_input, f"ShardedRel (smStore {gather_input.sm_tid}) [{', '.join(f'pmStore {t}' for t in gather_input.pm_tids)}] 1 {_shape_text(list(gather_input.full_shape))} {_shape_text(list(gather_input.shard_shape))}")
    fact_hyp("hWeight", weight, f"ShardedRel (smStore {weight.sm_tid}) [{', '.join(f'pmStore {t}' for t in weight.pm_tids)}] 0 {_shape_text(list(weight.full_shape))} {_shape_text(list(weight.shard_shape))}")

    def linear_writer(name, side, absolute_index, node, input_modes=("initial", "initial")):
        pos = sm_pos[absolute_index] if side == "sm" else pm_pos[absolute_index]
        graph = ir.sm_graph_ref if side == "sm" else ir.pm_graph_ref
        store, nodes, final = ("smStore", "smNodes", "smFinal") if side == "sm" else ("pmStore", "pmNodes", "pmFinal")
        prefix = f"(({nodes}.take {pos}).foldl (applyNodeDistributedFaithful {graph}) {store})"
        rhs_inputs = [f"{prefix} {node.ins[i]}" if input_modes[i] == "prefix" else f"{store} {node.ins[i]}" for i in range(2)]
        lines.extend([
            f"    have {name} : {final} {node.outs[0]} = fw_linear ({rhs_inputs[0]}) ({rhs_inputs[1]}) := by",
            f"      change ({nodes}.foldl (applyNodeDistributedFaithful {graph}) {store}) {node.outs[0]} = _",
            f"      rw [show {nodes} = {nodes}.take {pos} ++ [{_node_text(node)}] ++ {nodes}.drop {pos+1} by native_decide]",
            f"      rw [foldl_faithful_middle_writer {graph} {store} ({nodes}.take {pos}) ({nodes}.drop {pos+1})",
            f"        {_node_text(node)} {node.outs[0]} (fun t => fw_linear (t {node.ins[0]}) (t {node.ins[1]})) (by",
            "          intro t", "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "          simp [applyNodeDistributed, applyNodeRingAttn]",
            f"          exact applyNode_fw_linear_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            "        ) (by native_decide) (by native_decide)]",
        ])
        if "prefix" in input_modes:
            lines.append("      congr 2")
        if "prefix" not in input_modes:
            for i, mode in enumerate(input_modes):
                if mode == "initial":
                    lines.append(f"      rw [foldl_applyNodeDistributedFaithful_at_not_written {graph} ({nodes}.take {pos}) {store} {node.ins[i]} (by native_decide) (by native_decide)]")

    local_writer_names = []
    for j, (c, t) in enumerate(zip(local_certs, transitions[:2])):
        names = []
        linear_writer(f"hLocal{j}Sm", "sm", t.sm_node_indices[0], ir.sm_nodes[t.sm_node_indices[0]])
        names.append(f"hLocal{j}Sm")
        for r, index in enumerate(t.pm_node_indices):
            linear_writer(f"hLocal{j}Pm{r}", "pm", index, ir.pm_nodes[index]); names.append(f"hLocal{j}Pm{r}")
        local_writer_names.append(names)

    # Reconstruction writer over its actual middle prefix and complete suffix.
    gp = pm_pos[gather_index]
    lines.extend([
        f"    have hGatherWriter : pmFinal {joined.joined_pm_tid} = allGatherPrimDimN 1 {k} 0 [{', '.join(f'pmStore {t}' for t in gather_input.pm_tids)}] := by",
        f"      change (pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined.joined_pm_tid} = _",
        f"      rw [show pmNodes = pmNodes.take {gp} ++ [{_node_text(gather_node)}] ++ pmNodes.drop {gp+1} by native_decide]",
        f"      rw [foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore (pmNodes.take {gp}) (pmNodes.drop {gp+1})",
        f"        {_node_text(gather_node)} {joined.joined_pm_tid} (fun t => allGatherPrimDimN 1 {k} 0 [{', '.join(f't {x}' for x in gather_input.pm_tids)}]) (by",
        "          intro t", "          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
        "            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
        "          simp [applyNodeDistributed, applyNodeRingAttn]",
        f"          exact applyNode_allGatherPrimDimN_out {ir.pm_graph_ref} t 0 [{', '.join(str(x) for x in gather_input.pm_tids)}] {joined.joined_pm_tid} 1",
        "        ) (by native_decide) (by native_decide)]",
    ])
    for tid in gather_input.pm_tids:
        lines.append(f"      rw [foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} (pmNodes.take {gp}) pmStore {tid} (by native_decide) (by native_decide)]")

    # Output linear writers: PM activation is produced earlier in this same PM fold.
    out_t = transitions[3]
    linear_writer("hOutputSm", "sm", out_t.sm_node_indices[0], ir.sm_nodes[out_t.sm_node_indices[0]])
    for r, index in enumerate(out_t.pm_node_indices):
        linear_writer(f"hOutputPmRaw{r}", "pm", index, ir.pm_nodes[index], ("prefix", "initial"))
        pos = pm_pos[index]
        lines.extend([
            f"    have hJoinedPrefix{r} : ((pmNodes.take {pos}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined.joined_pm_tid} = pmFinal {joined.joined_pm_tid} := by",
            f"      have h := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} (pmNodes.drop {pos}) ((pmNodes.take {pos}).foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined.joined_pm_tid} (by native_decide) (by native_decide)",
            f"      rw [← List.foldl_append, show pmNodes.take {pos} ++ pmNodes.drop {pos} = pmNodes by exact List.take_append_drop {pos} pmNodes] at h",
            "      exact h.symm",
            f"    have hOutputPm{r} : pmFinal {final_output.pm_tids[r]} = fw_linear (pmFinal {joined.joined_pm_tid}) (pmStore {weight.pm_tids[r]}) := by",
            f"      rw [hOutputPmRaw{r}, hJoinedPrefix{r}]",
        ])

    # Reuse the exact two local singleton theorem obligations.
    for j, (c, pre, post, names) in enumerate(zip(local_certs, local_inputs, local_outputs, local_writer_names)):
        b, local_s, inner = pre.shard_shape; out_dim = post.shard_shape[2]
        pm_in = "[" + ", ".join(f"pmStore {t}" for t in pre.pm_tids) + "]"
        pm_out = "[" + ", ".join(f"pmFinal {t}" for t in post.pm_tids) + "]"
        lines.extend([
            f"    have hLocalComm{j} := ({local_theorem} (K := {pm_in}.length) (b := {b}) (s := {local_s}) (i := {inner}) (o := {out_dim}) (xs := {pm_in}) (w := pmStore {c.external_tids[0]}) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hLocalIn{j}.shard_shapes x hx) hLocalShape{j})",
            f"    have hLocalValue{j} : smFinal {post.sm_tid} = allGatherPrimDimN 1 {pm_out}.length 0 {pm_out} := by",
            f"      rw [{names[0]}, hLocalEq{j}, hLocalIn{j}.full_value, hLocalComm{j}]",
            "      simp only [List.map, List.length_cons, List.length_nil]",
            f"      rw [{', '.join('← '+n for n in names[1:])}]",
        ])
        shape_names = []
        for r, n in enumerate(names[1:]):
            sn = f"hLocalShapeOut{j}_{r}"; shape_names.append(sn)
            lines.extend([f"    have {sn} : (pmFinal {post.pm_tids[r]}).shape = {_shape_text(list(post.shard_shape))} := by", f"      rw [{n}]", f"      exact fw_linear_3d_shape {b} {local_s} {inner} {out_dim} _ _ (hLocalIn{j}.shard_shapes _ (by simp)) hLocalShape{j}"])
        lines.extend([
            f"    have hLocalOut{j} : {post.fact_id}.Holds smFinal pmFinal := by",
            f"      change ShardedRel (smFinal {post.sm_tid}) {pm_out} 1 {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
            "      refine { full_value := hLocalValue"+str(j)+", full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }",
            f"      · rw [hLocalValue{j}, allGatherPrimDimN_shape 1 {pm_out}.length {pm_out} {_shape_text(list(post.shard_shape))}]",
            "        · simp only [List.length_cons, List.length_nil]",
            "          native_decide", f"        · simp only [List.head?, Option.map, Option.getD]; exact {shape_names[0]}",
            "      · intro shard hmem", "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}",
        ])
        lines.extend(f"        · exact {sn}" for sn in shape_names)

    # Reuse exact reconstruction relation theorem at the shared final stores.
    lines.extend([
        f"    have hGatherFinal : {gather_input.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {gather_input.sm_tid}) [{', '.join(f'pmFinal {t}' for t in gather_input.pm_tids)}] 1 {_shape_text(list(gather_input.full_shape))} {_shape_text(list(gather_input.shard_shape))} at hGatherFinal",
        f"    have hGatherInputsFinal : [{', '.join(f'pmFinal {t}' for t in gather_input.pm_tids)}] = [{', '.join(f'pmStore {t}' for t in gather_input.pm_tids)}] := by",
    ])
    for tid in gather_input.pm_tids:
        lines.extend([f"      have h{tid} := foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore {tid} (by native_decide) (by native_decide)"])
    lines.append(f"      change [{', '.join(f'(pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {t}' for t in gather_input.pm_tids)}] = [{', '.join(f'pmStore {t}' for t in gather_input.pm_tids)}]")
    lines.append(f"      rw [{', '.join('h'+str(t) for t in gather_input.pm_tids)}]")
    lines.extend([
        f"    have hJoinedValue : smFinal {joined.sm_tid} = pmFinal {joined.joined_pm_tid} := by",
        f"      rw [{gather_theorem} hGatherFinal, hGatherInputsFinal]",
        "      simp only [List.length_cons, List.length_nil]",
        "      exact hGatherWriter.symm",
        f"    have hJoinedOut : {joined.fact_id}.Holds smFinal pmFinal := by",
        f"      change smFinal {joined.sm_tid} = pmFinal {joined.joined_pm_tid} ∧ (smFinal {joined.sm_tid}).shape = {_shape_text(list(joined.full_shape))} ∧ (pmFinal {joined.joined_pm_tid}).shape = {_shape_text(list(joined.full_shape))}",
        "      refine ⟨hJoinedValue, hGatherFinal.full_shape, ?_⟩", "      rw [← hJoinedValue]", "      exact hGatherFinal.full_shape",
    ])

    # Reuse exact output-sharded singleton theorem obligation.
    b, seq, inner = joined.full_shape; local_out = weight.shard_shape[0]
    pm_weights = "[" + ", ".join(f"pmStore {t}" for t in weight.pm_tids) + "]"
    pm_outputs = "[" + ", ".join(f"pmFinal {t}" for t in final_output.pm_tids) + "]"
    lines.extend([
        f"    have hOutputComm := ({output_theorem} (K := {pm_weights}.length) (b := {b}) (s := {seq}) (i := {inner}) (o := {local_out}) (x := pmFinal {joined.joined_pm_tid}) (ws := {pm_weights}) (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by simp) (by rw [← hJoinedValue]; exact hGatherFinal.full_shape) (fun w hw => hWeight.shard_shapes w hw))",
        f"    have hOutputValue : smFinal {final_output.sm_tid} = allGatherPrimDimN 2 {pm_outputs}.length 0 {pm_outputs} := by",
        "      rw [hOutputSm]",
        f"      have hSmAct : smStore {joined.sm_tid} = pmFinal {joined.joined_pm_tid} := by",
        f"        have h := foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref} smNodes smStore {joined.sm_tid} (by native_decide) (by native_decide)",
        "        rw [← h]", "        exact hJoinedValue",
        f"      rw [hSmAct, hWeight.full_value, hOutputComm]",
        "      simp only [List.map, List.length_cons, List.length_nil]",
        f"      rw [{', '.join('← hOutputPm'+str(r) for r in range(k))}]",
    ])
    output_shape_names=[]
    for r in range(k):
        sn=f"hOutputShape{r}"; output_shape_names.append(sn)
        lines.extend([f"    have {sn} : (pmFinal {final_output.pm_tids[r]}).shape = {_shape_text(list(final_output.shard_shape))} := by", f"      rw [hOutputPm{r}]", f"      exact fw_linear_3d_shape {b} {seq} {inner} {local_out} _ _ (by rw [← hJoinedValue]; exact hGatherFinal.full_shape) (hWeight.shard_shapes _ (by simp))"])
    lines.extend([
        f"    have hFinalOut : {final_output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {final_output.sm_tid}) {pm_outputs} 2 {_shape_text(list(final_output.full_shape))} {_shape_text(list(final_output.shard_shape))}",
        "      refine { full_value := hOutputValue, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }",
        f"      · rw [hOutputValue, allGatherPrimDimN_shape 2 {pm_outputs}.length {pm_outputs} {_shape_text(list(final_output.shard_shape))}]",
        "        · simp only [List.length_cons, List.length_nil]",
        "          native_decide", f"        · simp only [List.head?, Option.map, Option.getD]; exact {output_shape_names[0]}",
        "      · intro shard hmem", "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}",
    ])
    lines.extend(f"        · exact {sn}" for sn in output_shape_names)
    fresh = [local_outputs[0].fact_id, local_outputs[1].fact_id, joined.fact_id, final_output.fact_id]
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        "      rcases fresh with rfl | rfl | rfl | rfl",
        "      · exact hLocalOut0", "      · exact hLocalOut1", "      · exact hJoinedOut", "      · exact hFinalOut",
        "    · exact hframe fact old", "",
    ])
    return "\n".join(lines)
