"""One-fold renderer for authority-typed mixed linear transition sequences."""
from __future__ import annotations


def render_closed_mixed_linear_sequence_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankAllToAllRelationCertificate,
            KRankLocalRelationCertificate,
            KRankOutputShardedLinearCertificate,
            KRankReductionLinearProducerCertificate,
        )
    except ImportError:
        from composer import _node_text, _select_exact_typed_certificate, _shape_text
        from relation_compiler import (
            KRankAllGatherReconstructionCertificate,
            KRankAllToAllRelationCertificate,
            KRankLocalRelationCertificate,
            KRankOutputShardedLinearCertificate,
            KRankReductionLinearProducerCertificate,
        )

    contracts = {
        "linear-sharded-k-rank-dim1": (
            "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm",
            KRankLocalRelationCertificate,
            lambda c: ((c.input_fact,), (c.output_fact,)),
        ),
        "alltoall-k-rank-layout-transport": (
            "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn",
            KRankAllToAllRelationCertificate,
            lambda c: ((c.input_fact,), (c.output_fact,)),
        ),
        "linear-reduction-producer-k-rank": (
            "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d",
            KRankReductionLinearProducerCertificate,
            lambda c: (tuple(sorted((c.activation_fact, c.weight_fact))), (c.output_fact,)),
        ),
        "allgather-reconstruction-k-rank": (
            "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather",
            KRankAllGatherReconstructionCertificate,
            lambda c: ((c.input_fact,), (c.output_fact,)),
        ),
        "linear-output-sharded-k-rank": (
            "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm",
            KRankOutputShardedLinearCertificate,
            lambda c: (tuple(sorted((c.activation_fact, c.weight_fact))), (c.output_fact,)),
        ),
    }
    chain = relation.dependent_chain_plan
    found = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(found) != 1:
        raise ValueError("mixed linear sequence requires one complete closed segment")
    segment = found[0]
    by_id = {}
    for transition in relation.transition_specs:
        by_id.setdefault(transition.transition_id, []).append(transition)
    resolved = [by_id.get(tid, ()) for tid in segment.transition_ids]
    if not resolved or any(len(items) != 1 for items in resolved):
        raise ValueError("mixed linear sequence transition authority is missing or duplicated")
    transitions = tuple(items[0] for items in resolved)
    if any(t.rule_id not in contracts for t in transitions):
        raise ValueError("mixed linear sequence contains an unsupported transition class")
    if len(transitions) <= 1 or len({t.rule_id for t in transitions}) <= 1:
        raise ValueError("mixed linear sequence requires multiple transition classes")

    certs = []
    for transition in transitions:
        theorem, cls, facts = contracts[transition.rule_id]
        if transition.lean_theorem != theorem:
            raise ValueError("mixed linear sequence theorem authority was tampered")
        certs.append(_select_exact_typed_certificate(
            relation, transition, transition.rule_id, theorem, cls, facts
        ))
    certs = tuple(certs)

    sources = [r.source for r in chain.relation_facts]
    fact_ids = [r.fact_id for r in chain.relation_facts]
    if len(sources) != len(set(sources)) or len(fact_ids) != len(set(fact_ids)):
        raise ValueError("mixed linear sequence relation authority is duplicated")
    records = {r.source: r for r in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    if len(states) != len(chain.states):
        raise ValueError("mixed linear sequence state authority is duplicated")
    try:
        before, after = states[segment.pre_state_id], states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError("mixed linear sequence state is not materialized") from exc

    rows = []
    produced_sources = set()
    produced_ids = set()
    rank_lists = []
    for transition, cert in zip(transitions, certs):
        try:
            if isinstance(cert, KRankLocalRelationCertificate):
                pre, post = records[cert.input_fact], records[cert.output_fact]
                row = ("local", transition, cert, pre, post)
                rank_lists += [pre.pm_tids, post.pm_tids]
                pre_records, post_records = (pre,), (post,)
            elif isinstance(cert, KRankAllToAllRelationCertificate):
                pre, post = records[cert.input_fact], records[cert.output_fact]
                row = ("a2a", transition, cert, pre, post)
                rank_lists += [pre.pm_tids, post.pm_tids]
                pre_records, post_records = (pre,), (post,)
            elif isinstance(cert, KRankReductionLinearProducerCertificate):
                activation = records[cert.activation_fact]
                weight = records[cert.weight_fact]
                post = records[cert.output_fact]
                row = ("reduction", transition, cert, activation, weight, post)
                rank_lists += [activation.pm_tids, weight.pm_tids, post.pm_tids]
                pre_records, post_records = (activation, weight), (post,)
            elif isinstance(cert, KRankAllGatherReconstructionCertificate):
                pre, post = records[cert.input_fact], records[cert.output_fact]
                row = ("gather", transition, cert, pre, post)
                rank_lists += [pre.pm_tids]
                pre_records, post_records = (pre,), (post,)
            else:
                activation = records[cert.activation_fact]
                weight = records[cert.weight_fact]
                post = records[cert.output_fact]
                row = ("output", transition, cert, activation, weight, post)
                rank_lists += [weight.pm_tids, post.pm_tids]
                pre_records, post_records = (activation, weight), (post,)
        except KeyError as exc:
            raise ValueError("mixed linear sequence fact is not materialized") from exc
        for record in pre_records:
            if record.fact_id not in before.fact_ids and record.source not in produced_sources:
                raise ValueError("mixed linear sequence input is neither live nor previously produced")
        rows.append(row)
        produced_sources.update(record.source for record in post_records)
        produced_ids.update(record.fact_id for record in post_records)

    k = len(rank_lists[0]) if rank_lists else 0
    if k <= 0 or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k:
        raise ValueError("mixed linear sequence dynamic graph rank authority is malformed")
    if any(len(items) != k for items in rank_lists) or any(int(c.rank_count) != k for c in certs):
        raise ValueError("mixed linear sequence certificates disagree with ordered rank authority")
    if not set(after.fact_ids) <= set(before.fact_ids) | produced_ids:
        raise ValueError("mixed linear sequence post-state introduces an unproved fact")

    sm_indices = tuple(range(*segment.sm_range))
    pm_indices = tuple(range(*segment.pm_range))
    sm_owned = tuple(i for t in transitions for i in t.sm_node_indices)
    pm_owned = tuple(i for t in transitions for i in t.pm_node_indices)
    if (len(sm_owned) != len(set(sm_owned)) or not set(sm_owned) <= set(sm_indices)
            or len(pm_owned) != len(set(pm_owned)) or not set(pm_owned) <= set(pm_indices)):
        raise ValueError("mixed linear sequence writers overlap or leave the complete frame")

    def step_index(step):
        parts = step.split(":")
        if len(parts) != 3 or parts[0] not in ("sm", "pm") or parts[2] != "0":
            raise ValueError("mixed linear sequence certificate step is malformed")
        return int(parts[1])

    authorities = tuple(chain.authority_facts)
    local_authorities = {}
    for row in rows:
        kind, transition, cert, *facts = row
        if kind == "local":
            pre, post = facts
            expected_sm = (step_index(cert.sm_step_id),)
            expected_pm = tuple(step_index(x) for x in cert.pm_step_ids)
        elif kind == "a2a":
            pre, post = facts
            expected_sm = ()
            expected_pm = tuple(step_index(x) for x in cert.pm_step_ids)
        elif kind == "reduction":
            activation, weight, post = facts
            expected_sm = (step_index(cert.sm_linear_step),)
            expected_pm = tuple(step_index(x) for x in cert.pm_linear_steps)
        elif kind == "gather":
            pre, post = facts
            expected_sm = ()
            expected_pm = (step_index(cert.pm_allgather_step),)
        else:
            activation, weight, post = facts
            expected_sm = (step_index(cert.sm_step_id),)
            expected_pm = tuple(step_index(x) for x in cert.pm_step_ids)
        if transition.sm_node_indices != expected_sm or transition.pm_node_indices != expected_pm:
            raise ValueError("mixed linear sequence certificate footprint was tampered")

        if kind == "local":
            if (cert.op != "FW_linear" or cert.gather_dim != 1
                    or pre.kind != "sharded" or post.kind != "sharded"
                    or pre.gather_dim != 1 or post.gather_dim != 1
                    or len(cert.external_tids) != 1 or len(cert.external_shapes) != 1):
                raise ValueError("mixed linear sequence local authority is malformed")
            weight_tid = cert.external_tids[0]
            eqs = [a for a in authorities if getattr(a, "kind", None) == "tensor_eq"
                   and a.left_side == "sm" and a.left_tid == weight_tid
                   and a.right_side == "pm" and a.right_tid == weight_tid]
            shapes = [a for a in authorities if getattr(a, "kind", None) == "tensor_shape"
                      and a.side == "pm" and a.tid == weight_tid
                      and tuple(a.shape) == tuple(cert.external_shapes[0])]
            if len(eqs) != 1 or len(shapes) != 1 or any(a.fact_id not in before.fact_ids for a in (*eqs, *shapes)):
                raise ValueError("mixed linear sequence local external authority is not exact and live")
            if (len(pre.shard_shape) != 3
                    or tuple(pre.full_shape) != (pre.shard_shape[0], pre.shard_shape[1] * k, pre.shard_shape[2])
                    or tuple(post.shard_shape) != (pre.shard_shape[0], pre.shard_shape[1], cert.external_shapes[0][0])
                    or tuple(post.full_shape) != (post.shard_shape[0], post.shard_shape[1] * k, post.shard_shape[2])
                    or tuple(cert.external_shapes[0]) != (post.shard_shape[2], pre.shard_shape[2])):
                raise ValueError("mixed linear sequence local shape authority is inconsistent")
            local_authorities[id(cert)] = (eqs[0], shapes[0])
            activation, weight, produced = pre, None, post
        elif kind == "a2a":
            idim, odim = cert.input_gather_dim, cert.output_gather_dim
            if (pre.kind != "sharded" or post.kind != "sharded"
                    or pre.gather_dim != idim or post.gather_dim != odim
                    or pre.sm_tid != post.sm_tid or pre.full_shape != post.full_shape):
                raise ValueError("mixed linear sequence AllToAll roles are malformed")
            for fact, dim in ((pre, idim), (post, odim)):
                shape = list(fact.shard_shape)
                if dim < 0 or dim >= len(shape):
                    raise ValueError("mixed linear sequence AllToAll dimension is invalid")
                shape[dim] *= k
                if tuple(shape) != tuple(fact.full_shape):
                    raise ValueError("mixed linear sequence AllToAll shape authority is malformed")
            activation, weight, produced = pre, None, post
        elif kind == "reduction":
            activation, weight, produced = facts
            if (activation.kind != "sharded" or activation.gather_dim != 2
                    or weight.kind != "sharded" or weight.gather_dim != 1
                    or produced.kind != "reduction"
                    or tuple(activation.full_shape) != cert.activation_full_shape
                    or tuple(activation.shard_shape) != cert.activation_shard_shape
                    or tuple(weight.full_shape) != cert.weight_full_shape
                    or tuple(weight.shard_shape) != cert.weight_shard_shape
                    or tuple(produced.full_shape) != cert.output_shape
                    or cert.activation_chunk_dim != 2 or cert.weight_gather_dim != 1
                    or cert.activation_full_shape[-1] != k * cert.activation_shard_shape[-1]
                    or cert.weight_full_shape[1] != k * cert.weight_shard_shape[1]
                    or cert.activation_shard_shape[-1] != cert.weight_shard_shape[1]):
                raise ValueError("mixed linear sequence reduction shape authority is malformed")
        elif kind == "gather":
            if (pre.kind != "sharded" or pre.gather_dim != cert.gather_dim
                    or post.kind != "joined" or post.joined_pm_tid is None
                    or tuple(pre.full_shape) != cert.full_shape
                    or tuple(pre.shard_shape) != cert.shard_shape
                    or tuple(post.full_shape) != cert.full_shape):
                raise ValueError("mixed linear sequence gather authority is malformed")
            activation, weight, produced = pre, None, post
        else:
            activation, weight, produced = facts
            if (activation.kind != "joined" or activation.joined_pm_tid is None
                    or weight.kind != "sharded" or weight.gather_dim != 0
                    or produced.kind != "sharded" or produced.gather_dim != 2
                    or tuple(activation.full_shape) != cert.activation_shape
                    or tuple(weight.full_shape) != cert.weight_full_shape
                    or tuple(weight.shard_shape) != cert.weight_shard_shape
                    or tuple(produced.full_shape) != cert.output_full_shape
                    or tuple(produced.shard_shape) != cert.output_shard_shape):
                raise ValueError("mixed linear sequence output authority is malformed")

        sm_nodes = [ir.sm_nodes[i] for i in transition.sm_node_indices]
        pm_nodes = [ir.pm_nodes[i] for i in transition.pm_node_indices]
        if kind == "a2a":
            if (transition.sm_node_indices or tuple(n.rank for n in pm_nodes) != tuple(range(k))
                    or any(n.op != "AllToAllPrim" or tuple(n.ins) != activation.pm_tids
                           or n.outs != [produced.pm_tids[r]]
                           or tuple(n.params or ()) != (cert.input_gather_dim, cert.output_gather_dim)
                           for r, n in enumerate(pm_nodes))):
                raise ValueError("mixed linear sequence AllToAll writer authority is malformed")
        elif kind == "gather":
            node = pm_nodes[0] if len(pm_nodes) == 1 else None
            if (node is None or node.rank != 0 or node.op != "AllGatherPrim"
                    or tuple(node.ins) != activation.pm_tids or node.outs != [produced.joined_pm_tid]
                    or tuple(node.params or ()) != (cert.gather_dim,)):
                raise ValueError("mixed linear sequence gather writer authority is malformed")
        else:
            if len(sm_nodes) != 1 or len(pm_nodes) != k or tuple(n.rank for n in pm_nodes) != tuple(range(k)):
                raise ValueError("mixed linear sequence linear writer cardinality/order is malformed")
            sm = sm_nodes[0]
            weight_tid = cert.external_tids[0] if kind == "local" else weight.sm_tid
            if (sm.rank != 0 or sm.op != "FW_linear" or sm.params
                    or sm.ins != [activation.sm_tid, weight_tid] or sm.outs != [produced.sm_tid]):
                raise ValueError("mixed linear sequence SM linear roles are malformed")
            for rank, node in enumerate(pm_nodes):
                activation_tid = activation.joined_pm_tid if kind == "output" else activation.pm_tids[rank]
                pm_weight_tid = cert.external_tids[0] if kind == "local" else weight.pm_tids[rank]
                if (node.op != "FW_linear" or node.params
                        or node.ins != [activation_tid, pm_weight_tid]
                        or node.outs != [produced.pm_tids[rank]]):
                    raise ValueError("mixed linear sequence PM linear roles are malformed")

    sm_nodes = ir.sm_nodes[slice(*segment.sm_range)]
    pm_nodes = ir.pm_nodes[slice(*segment.pm_range)]
    sm_pos = {i: i - segment.sm_range[0] for i in sm_indices}
    pm_pos = {i: i - segment.pm_range[0] for i in pm_indices}
    smg, pmg = ir.sm_graph_ref, ir.pm_graph_ref
    sm_name, pm_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    sm_final_name, pm_final_name = f"{segment_id}_smFinal", f"{segment_id}_pmFinal"
    publish_name = f"{segment_id}_publish_state"
    declarations = [
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 500000",
        f"private def {sm_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_nodes)}]",
        f"private def {pm_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_nodes)}]",
        f"@[irreducible] private def {sm_final_name} (smStore : Store) : Store :=",
        f"  {sm_name}.foldl (applyNodeDistributedFaithful {smg}) smStore",
        f"@[irreducible] private def {pm_final_name} (pmStore : Store) : Store :=",
        f"  {pm_name}.foldl (applyNodeDistributedFaithful {pmg}) pmStore", "",
    ]
    lines = []
    proof_by_source = {r.source: f"hframe {r.fact_id} (by native_decide)" for r in chain.relation_facts if r.fact_id in before.fact_ids}
    proof_by_id = {r.fact_id: proof_by_source[r.source] for r in chain.relation_facts if r.source in proof_by_source}

    def have_fact(name, record, proposition):
        try:
            proof = proof_by_source[record.source]
        except KeyError as exc:
            raise ValueError("mixed linear sequence emission dependency is not available") from exc
        lines.extend([f"    have {name} : {record.fact_id}.Holds smFinal pmFinal := {proof}", f"    change {proposition} at {name}"])

    writer_serial = 0
    writer_helpers = []
    def linear_writer(label, side, absolute_index, node):
        nonlocal writer_serial
        writer_serial += 1
        graph = smg if side == "sm" else pmg
        store = f"{side}Store"
        nodes = f"{side}Nodes"
        final = f"{side}Final"
        node_name = sm_name if side == "sm" else pm_name
        final_name = sm_final_name if side == "sm" else pm_final_name
        pos = (sm_pos if side == "sm" else pm_pos)[absolute_index]
        prefix = f"(({nodes}.take {pos}).foldl (applyNodeDistributedFaithful {graph}) {store})"
        helper = f"{segment_id}_{side}_linear_writer_{writer_serial}"
        p0 = f"hPrefix{writer_serial}_0"
        p1 = f"hPrefix{writer_serial}_1"
        writer_helpers.extend([
            f"private theorem {helper} ({store} : Store) :",
            f"    {final_name} {store} {node.outs[0]} = fw_linear ({final_name} {store} {node.ins[0]}) ({final_name} {store} {node.ins[1]}) := by",
            f"  unfold {final_name}",
            f"  let {nodes} : List NodeDecl := {node_name}",
            f"  let {final} := {nodes}.foldl (applyNodeDistributedFaithful {graph}) {store}",
            f"  change {final} {node.outs[0]} = fw_linear ({final} {node.ins[0]}) ({final} {node.ins[1]})",
            f"  have {p0} : {prefix} {node.ins[0]} = {final} {node.ins[0]} := by",
            f"    have h := foldl_applyNodeDistributedFaithful_at_not_written {graph} ({nodes}.drop {pos}) {prefix} {node.ins[0]} (by native_decide) (by native_decide)",
            f"    rw [← List.foldl_append, show {nodes}.take {pos} ++ {nodes}.drop {pos} = {nodes} by exact List.take_append_drop {pos} {nodes}] at h",
            "    exact h.symm",
            f"  have {p1} : {prefix} {node.ins[1]} = {final} {node.ins[1]} := by",
            f"    have h := foldl_applyNodeDistributedFaithful_at_not_written {graph} ({nodes}.drop {pos}) {prefix} {node.ins[1]} (by native_decide) (by native_decide)",
            f"    rw [← List.foldl_append, show {nodes}.take {pos} ++ {nodes}.drop {pos} = {nodes} by exact List.take_append_drop {pos} {nodes}] at h",
            "    exact h.symm",
            f"  change ({nodes}.foldl (applyNodeDistributedFaithful {graph}) {store}) {node.outs[0]} = _",
            f"  rw [show {nodes} = {nodes}.take {pos} ++ [{_node_text(node)}] ++ {nodes}.drop {pos + 1} by native_decide]",
            f"  rw [foldl_faithful_middle_writer {graph} {store} ({nodes}.take {pos}) ({nodes}.drop {pos + 1})",
            f"    {_node_text(node)} {node.outs[0]} (fun t => fw_linear (t {node.ins[0]}) (t {node.ins[1]})) (by",
            "      intro t", "      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective",
            "        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "      simp [applyNodeDistributed, applyNodeRingAttn]",
            f"      exact applyNode_fw_linear_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}",
            "    ) (by native_decide) (by native_decide)]",
            f"  rw [{p0}, {p1}]", "",
        ])
        lines.append(f"    have {label} : {final} {node.outs[0]} = fw_linear ({final} {node.ins[0]}) ({final} {node.ins[1]}) := {helper} {store}")

    def gather_writer(label, number, transition, cert, pre, post):
        index = transition.pm_node_indices[0]
        node = ir.pm_nodes[index]
        pos = pm_pos[index]
        helper = f"{segment_id}_pm_gather_writer_{number}"
        input_tids = "[" + ", ".join(str(t) for t in pre.pm_tids) + "]"
        inputs = "[" + ", ".join(f"{pm_final_name} pmStore {t}" for t in pre.pm_tids) + "]"
        prefix = f"((pmNodes.take {pos}).foldl (applyNodeDistributedFaithful {pmg}) pmStore)"
        prefix_names = [f"hGatherPrefix{number}_{rank}" for rank in range(k)]
        helper_lines = [
            f"private theorem {helper} (pmStore : Store) :",
            f"    {pm_final_name} pmStore {post.joined_pm_tid} = allGatherPrimDimN {cert.gather_dim} {k} 0 {inputs} := by",
            f"  unfold {pm_final_name}",
            f"  let pmNodes : List NodeDecl := {pm_name}",
            f"  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore",
            f"  change pmFinal {post.joined_pm_tid} = allGatherPrimDimN {cert.gather_dim} {k} 0 [{', '.join(f'pmFinal {x}' for x in pre.pm_tids)}]",
        ]
        for pname, tid in zip(prefix_names, pre.pm_tids):
            helper_lines += [
                f"  have {pname} : {prefix} {tid} = pmFinal {tid} := by",
                f"    have h := foldl_applyNodeDistributedFaithful_at_not_written {pmg} (pmNodes.drop {pos}) {prefix} {tid} (by native_decide) (by native_decide)",
                f"    rw [← List.foldl_append, show pmNodes.take {pos} ++ pmNodes.drop {pos} = pmNodes by exact List.take_append_drop {pos} pmNodes] at h",
                "    exact h.symm",
            ]
        helper_lines += [
            f"  change (pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore) {post.joined_pm_tid} = _",
            f"  rw [show pmNodes = pmNodes.take {pos} ++ [{_node_text(node)}] ++ pmNodes.drop {pos + 1} by native_decide]",
            f"  rw [foldl_faithful_middle_writer {pmg} pmStore (pmNodes.take {pos}) (pmNodes.drop {pos + 1})",
            f"    {_node_text(node)} {post.joined_pm_tid} (fun t => allGatherPrimDimN {cert.gather_dim} {k} 0 [{', '.join(f't {x}' for x in pre.pm_tids)}]) (by",
            "      intro t",
            "      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "      simp [applyNodeDistributed, applyNodeRingAttn]",
            f"      exact applyNode_allGatherPrimDimN_out {pmg} t 0 {input_tids} {post.joined_pm_tid} {cert.gather_dim}",
            "    ) (by native_decide) (by native_decide)]",
            f"  rw [{', '.join(prefix_names)}]", "",
        ]
        writer_helpers.extend(helper_lines)
        lines.append(
            f"    have {label} : pmFinal {post.joined_pm_tid} = allGatherPrimDimN {cert.gather_dim} {k} 0 [{', '.join(f'pmFinal {x}' for x in pre.pm_tids)}] := {helper} pmStore"
        )

    def register(record, proof):
        proof_by_source[record.source] = proof
        proof_by_id[record.fact_id] = proof

    local_no = a2a_no = reduction_no = gather_no = output_no = 0
    transition_helpers = []
    transition_calls = []
    helper_kinds = {"local": "ll", "a2a": "a2a", "reduction": "rlin", "gather": "ag", "output": "ol"}
    for transition_index, row in enumerate(rows):
        kind, transition, cert, *facts = row
        if kind in ("local", "a2a", "gather"):
            dependency_records, post_record = (facts[0],), facts[1]
        else:
            dependency_records, post_record = (facts[0], facts[1]), facts[2]
        dependency_records = tuple(record for record in dependency_records if record.fact_id not in before.fact_ids)
        dependency_bindings = tuple((record, proof_by_source[record.source]) for record in dependency_records)
        transition_helper = f"{segment_id}_transition_{transition_index}_{helper_kinds[kind]}"
        lines = [
            f"    let smFinal := {sm_final_name} smStore",
            f"    let pmFinal := {pm_final_name} pmStore",
        ]
        if kind == "local":
            number = local_no; local_no += 1
            pre, post = facts; eq, shape = local_authorities[id(cert)]
            pm_in = "[" + ", ".join(f"pmFinal {t}" for t in pre.pm_tids) + "]"
            pm_out = "[" + ", ".join(f"pmFinal {t}" for t in post.pm_tids) + "]"
            have_fact(f"hLocalIn{number}", pre, f"ShardedRel (smFinal {pre.sm_tid}) {pm_in} 1 {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))}")
            lines += [
                f"    have hLocalEq{number} : {eq.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
                f"    change smFinal {cert.external_tids[0]} = pmFinal {cert.external_tids[0]} at hLocalEq{number}",
                f"    have hLocalWeightShape{number} : {shape.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
                f"    change (pmFinal {cert.external_tids[0]}).shape = {_shape_text(list(cert.external_shapes[0]))} at hLocalWeightShape{number}",
            ]
            linear_writer(f"hLocalSm{number}", "sm", transition.sm_node_indices[0], ir.sm_nodes[transition.sm_node_indices[0]])
            for rank, index in enumerate(transition.pm_node_indices):
                linear_writer(f"hLocalPm{number}_{rank}", "pm", index, ir.pm_nodes[index])
            b, seq, inner = pre.shard_shape; width = post.shard_shape[2]
            theorem = contracts[transition.rule_id][0]
            lines += [
                f"    have hLocalComm{number} := ({theorem} (K := {pm_in}.length) (b := {b}) (s := {seq}) (i := {inner}) (o := {width}) (xs := {pm_in}) (w := pmFinal {cert.external_tids[0]}) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hLocalIn{number}.shard_shapes x hx) hLocalWeightShape{number})",
                f"    have hLocalValue{number} : smFinal {post.sm_tid} = allGatherPrimDimN 1 {pm_out}.length 0 {pm_out} := by",
                f"      rw [hLocalSm{number}, hLocalEq{number}, hLocalIn{number}.full_value, hLocalComm{number}]",
                "      simp only [List.map, List.length_cons, List.length_nil]",
                f"      rw [{', '.join('← hLocalPm'+str(number)+'_'+str(r) for r in range(k))}]",
            ]
            shapes = []
            for rank in range(k):
                name = f"hLocalShape{number}_{rank}"; shapes.append(name)
                lines += [f"    have {name} : (pmFinal {post.pm_tids[rank]}).shape = {_shape_text(list(post.shard_shape))} := by",
                          f"      rw [hLocalPm{number}_{rank}]",
                          f"      exact fw_linear_3d_shape {b} {seq} {inner} {width} _ _ (hLocalIn{number}.shard_shapes _ (by simp)) hLocalWeightShape{number}"]
            proof = f"hLocalOut{number}"
            lines += [f"    have {proof} : {post.fact_id}.Holds smFinal pmFinal := by",
                      f"      change ShardedRel (smFinal {post.sm_tid}) {pm_out} 1 {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
                      f"      refine {{ full_value := hLocalValue{number}, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }}",
                      f"      · rw [hLocalValue{number}, allGatherPrimDimN_shape 1 {pm_out}.length {pm_out} {_shape_text(list(post.shard_shape))}]",
                      "        · simp only [List.length_cons, List.length_nil]", "          native_decide",
                      f"        · simp only [List.head?, Option.map, Option.getD]; exact {shapes[0]}",
                      "      · intro shard hmem", "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
                      f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}"]
            lines += [f"        · exact {name}" for name in shapes]
            register(post, proof)

        elif kind == "a2a":
            number = a2a_no; a2a_no += 1
            pre, post = facts; idim, odim = cert.input_gather_dim, cert.output_gather_dim
            input_tids = "[" + ", ".join(str(t) for t in pre.pm_tids) + "]"
            output_tids = "[" + ", ".join(str(t) for t in post.pm_tids) + "]"
            inputs = "[" + ", ".join(f"pmFinal {t}" for t in pre.pm_tids) + "]"
            outputs = "[" + ", ".join(f"pmFinal {t}" for t in post.pm_tids) + "]"
            have_fact(f"hA2AIn{number}", pre, f"ShardedRel (smFinal {pre.sm_tid}) {inputs} {idim} {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))}")
            lines += [f"    let inputTids{number} : List Tid := {input_tids}",
                      f"    let outputTids{number} : List Tid := {output_tids}",
                      f"    let rankCount{number} := outputTids{number}.length",
                      f"    have hRankCount{number} : rankCount{number} = {pmg}.numRanks := by rfl",
                      f"    let xs{number} := inputTids{number}.map pmFinal",
                      f"    have hHead{number} : ((xs{number}.head?.map (fun t => t.shape)).getD []) = {_shape_text(list(pre.shard_shape))} := by",
                      f"      simp only [xs{number}, inputTids{number}, List.map, List.head?, Option.map, Option.getD]",
                      f"      exact hA2AIn{number}.shard_shapes _ (by simp)",
                      f"    have hRankXs{number} : rankCount{number} = xs{number}.length := by simp [rankCount{number}, outputTids{number}, xs{number}, inputTids{number}]"]
            writers, shape_names = [], []
            for rank, index in enumerate(transition.pm_node_indices):
                node = ir.pm_nodes[index]; pos = pm_pos[index]
                writer = f"hA2AWriter{number}_{rank}"; shape_name = f"hA2AShape{number}_{rank}"
                writers.append(writer); shape_names.append(shape_name)
                helper = f"{segment_id}_pm_a2a_writer_{number}_{rank}"
                hp = [f"hA2APrefix{number}_{rank}_{r}" for r in range(k)]
                helper_lines = [
                    f"private theorem {helper} (pmStore : Store) :",
                    f"    {pm_final_name} pmStore {node.outs[0]} = allToAllPrimWithDims {k} {rank} ({input_tids}.map ({pm_final_name} pmStore)) {idim} {odim} := by",
                    f"  unfold {pm_final_name}",
                    f"  let pmNodes : List NodeDecl := {pm_name}",
                    f"  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore",
                    f"  let inputTids : List Tid := {input_tids}",
                    f"  let outputTids : List Tid := {output_tids}",
                    f"  let rankCount := outputTids.length",
                    f"  let xs := inputTids.map pmFinal",
                    f"  change pmFinal {node.outs[0]} = allToAllPrimWithDims rankCount {rank} xs {idim} {odim}",
                ]
                prefix = f"((pmNodes.take {pos}).foldl (applyNodeDistributedFaithful {pmg}) pmStore)"
                for pname, tid in zip(hp, pre.pm_tids):
                    helper_lines += [
                        f"  have {pname} : {prefix} {tid} = pmFinal {tid} := by",
                        f"    have h := foldl_applyNodeDistributedFaithful_at_not_written {pmg} (pmNodes.drop {pos}) {prefix} {tid} (by native_decide) (by native_decide)",
                        f"    rw [← List.foldl_append, show pmNodes.take {pos} ++ pmNodes.drop {pos} = pmNodes by exact List.take_append_drop {pos} pmNodes] at h",
                        "    exact h.symm",
                    ]
                helper_lines += [
                    f"  have hInputs : inputTids.map {prefix} = xs := by",
                    "    simp only [inputTids, xs, List.map]",
                    f"    rw [{', '.join(hp)}]",
                    f"  change (pmNodes.foldl (applyNodeDistributedFaithful {pmg}) pmStore) {node.outs[0]} = _",
                    f"  rw [show pmNodes = pmNodes.take {pos} ++ [{_node_text(node)}] ++ pmNodes.drop {pos + 1} by native_decide]",
                    f"  rw [foldl_faithful_middle_writer {pmg} pmStore (pmNodes.take {pos}) (pmNodes.drop {pos + 1})",
                    f"    {_node_text(node)} {node.outs[0]} (fun t => allToAllPrimWithDims rankCount {rank} (inputTids.map t) {idim} {odim})]",
                    "  · rw [hInputs]", "  · intro t",
                    "    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                    "    simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]",
                    f"    have hRankCount : rankCount = {pmg}.numRanks := by rfl",
                    "    rw [hRankCount]",
                    f"    simpa [inputTids] using applyNode_allToAllPrimWithDims_out {pmg} t {rank} inputTids {node.outs[0]} {idim} {odim}",
                    "  · native_decide", "  · native_decide", "",
                ]
                writer_helpers.extend(helper_lines)
                lines += [
                    f"    have {writer} : pmFinal {node.outs[0]} = allToAllPrimWithDims rankCount{number} {rank} xs{number} {idim} {odim} := {helper} pmStore",
                    f"    have {shape_name} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by",
                    f"      rw [{writer}, allToAllPrimWithDims_shape rankCount{number} {rank} xs{number} {idim} {odim} {_shape_text(list(pre.shard_shape))} hHead{number} (by native_decide)]",
                    "      native_decide",
                ]
            theorem = contracts[transition.rule_id][0]
            proof = f"hA2AOut{number}"
            lines += [f"    have hOrdered{number} : outputTids{number}.map pmFinal = List.ofFn (fun r : Fin rankCount{number} => allToAllPrimWithDims rankCount{number} r.1 xs{number} {idim} {odim}) := by",
                      f"      simp only [outputTids{number}, rankCount{number}, List.map]", f"      rw [{', '.join(writers)}]", "      rfl",
                      f"    have hGatherShape{number} : (allGatherPrimDimN {idim} rankCount{number} 0 xs{number}).shape = {_shape_text(list(pre.full_shape))} := by",
                      f"      rw [hRankXs{number}]", f"      calc _ = (smFinal {pre.sm_tid}).shape := congrArg (fun t => t.shape) hA2AIn{number}.full_value.symm",
                      f"           _ = _ := hA2AIn{number}.full_shape",
                      f"    have hOdim{number} : {odim} < (allGatherPrimDimN {idim} rankCount{number} 0 xs{number}).shape.length := by rw [hGatherShape{number}]; native_decide",
                      f"    have hDiv{number} : (allGatherPrimDimN {idim} rankCount{number} 0 xs{number}).shape.getD {odim} 0 % rankCount{number} = 0 := by rw [hGatherShape{number}]; native_decide",
                      f"    have hOdimXs{number} := hOdim{number}", f"    have hDivXs{number} := hDiv{number}", f"    rw [hRankXs{number}] at hOdimXs{number} hDivXs{number}",
                      f"    have {proof} : {post.fact_id}.Holds smFinal pmFinal := by",
                      f"      change ShardedRel (smFinal {post.sm_tid}) {outputs} {odim} {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
                      f"      refine {{ full_value := ?_, full_shape := hA2AIn{number}.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }}",
                      f"      · rw [show {outputs} = outputTids{number}.map pmFinal by rfl, hOrdered{number}, List.length_ofFn]",
                      f"        rw [hRankXs{number}, {theorem} {idim} {odim} xs{number} (by simp [xs{number}, inputTids{number}]) hOdimXs{number} hDivXs{number}]",
                      f"        simp only [rankCount{number}, outputTids{number}, xs{number}, inputTids{number}, List.map, List.length_cons, List.length_nil]",
                      f"        exact hA2AIn{number}.full_value", "      · intro shard hmem",
                      "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
                      f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}"]
            lines += [f"        · exact {name}" for name in shape_names]
            register(post, proof)

        elif kind == "reduction":
            number = reduction_no; reduction_no += 1
            activation, weight, post = facts
            atids = "[" + ", ".join(str(t) for t in activation.pm_tids) + "]"
            wtids = "[" + ", ".join(str(t) for t in weight.pm_tids) + "]"
            otids = "[" + ", ".join(str(t) for t in post.pm_tids) + "]"
            have_fact(f"hActivation{number}", activation, f"ShardedRel (smFinal {activation.sm_tid}) ({atids}.map pmFinal) 2 {_shape_text(list(activation.full_shape))} {_shape_text(list(activation.shard_shape))}")
            have_fact(f"hReductionWeight{number}", weight, f"ShardedRel (smFinal {weight.sm_tid}) ({wtids}.map pmFinal) 1 {_shape_text(list(weight.full_shape))} {_shape_text(list(weight.shard_shape))}")
            lines += [f"    let pmActivationTids{number} : List Tid := {atids}", f"    let pmWeightTids{number} : List Tid := {wtids}",
                      f"    let pmOutputTids{number} : List Tid := {otids}", f"    let rankCountR{number} := pmWeightTids{number}.length"]
            linear_writer(f"hReductionSm{number}", "sm", transition.sm_node_indices[0], ir.sm_nodes[transition.sm_node_indices[0]])
            writers, chunks, shapes = [], [], []
            b, seq, _ = activation.full_shape; shard = activation.shard_shape[-1]; outdim = weight.full_shape[0]
            for rank, index in enumerate(transition.pm_node_indices):
                node = ir.pm_nodes[index]; writer = f"hReductionPm{number}_{rank}"; chunk = f"hReductionChunk{number}_{rank}"; shape = f"hReductionShape{number}_{rank}"
                linear_writer(writer, "pm", index, node); writers.append(writer); chunks.append(chunk); shapes.append(shape)
                lines += [f"    have {chunk} : chunkPrim {k} {rank} (smFinal {activation.sm_tid}) = pmFinal {node.ins[0]} := by",
                          f"      rw [hActivation{number}.full_value]",
                          f"      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d {k} {rank} {b} {seq} {shard} (pmActivationTids{number}.map pmFinal)",
                          f"        (by simp [rankCountR{number}, pmActivationTids{number}, pmWeightTids{number}]) hActivation{number}.shard_shapes",
                          "        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
                          f"      simpa [pmActivationTids{number}] using hcancel",
                          f"    have {shape} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(post.full_shape))} := by",
                          f"      rw [{writer}]", f"      have ha := hActivation{number}.shard_shapes (pmFinal {node.ins[0]}) (by simp [pmActivationTids{number}])",
                          f"      have hw := hReductionWeight{number}.shard_shapes (pmFinal {node.ins[1]}) (by simp [pmWeightTids{number}])",
                          "      simp [fw_linear, ha, hw]", "      rfl"]
            theorem = contracts[transition.rule_id][0]
            contributions = "[" + ", ".join(f"fw_linear (chunkPrim {k} {r} (smFinal {activation.sm_tid})) (pmFinal {weight.pm_tids[r]})" for r in range(k)) + "]"
            proof = f"hReductionOut{number}"
            lines += [f"    have hReductionWeightGather{number} : smFinal {weight.sm_tid} = allGatherPrim rankCountR{number} 0 (pmWeightTids{number}.map pmFinal) := by",
                      f"      change smFinal {weight.sm_tid} = allGatherPrim {k} 0 ({wtids}.map pmFinal)", f"      rw [hReductionWeight{number}.full_value]",
                      f"      have hhead : ((pmWeightTids{number}.map pmFinal).head?.map (fun t => t.shape)).getD [] = {_shape_text(list(weight.shard_shape))} := by",
                      f"        simpa [pmWeightTids{number}] using hReductionWeight{number}.shard_shapes _ (by simp [pmWeightTids{number}])",
                      f"      simpa [rankCountR{number}, pmWeightTids{number}] using (allGatherPrimDimN_1_eq_allGatherPrim_2d {k} ({wtids}.map pmFinal) {outdim} {shard} hhead (by native_decide) (by native_decide))",
                      f"    have hReductionFullShape{number} : (smFinal {post.sm_tid}).shape = {_shape_text(list(post.full_shape))} := by",
                      f"      rw [hReductionSm{number}]", f"      simp [fw_linear, hActivation{number}.full_shape, hReductionWeight{number}.full_shape]", "      rfl",
                      f"    have hReductionValue{number} : smFinal {post.sm_tid} = allReducePrim (pmOutputTids{number}.map pmFinal).length 0 (pmOutputTids{number}.map pmFinal) := by",
                      f"      rw [hReductionSm{number}, hReductionWeightGather{number}]",
                      f"      have hComm := {theorem} {k} {b} {seq} {activation.full_shape[-1]} {outdim} {shard} (smFinal {activation.sm_tid}) (pmWeightTids{number}.map pmFinal)",
                      f"        hActivation{number}.full_shape (by native_decide) (by simp [rankCountR{number}, pmWeightTids{number}]) hReductionWeight{number}.shard_shapes",
                      "        (by native_decide) (by native_decide) (by native_decide) (by native_decide)",
                      f"      have hContribs : List.ofFn (fun r : Fin {k} => fw_linear (chunkPrim {k} r.val (smFinal {activation.sm_tid})) ((pmWeightTids{number}.map pmFinal).get ⟨r.val, by simpa [pmWeightTids{number}] using r.isLt⟩)) = {contributions} := by rfl",
                      "      rw [hContribs] at hComm", f"      simp [rankCountR{number}, pmWeightTids{number}, pmOutputTids{number}] at hComm ⊢",
                      f"      rw [{', '.join(chunks)}] at hComm", "      rw [hComm]", f"      rw [{', '.join('← '+name for name in writers)}]",
                      f"    have {proof} : {post.fact_id}.Holds smFinal pmFinal := by",
                      f"      change ReductionRel (smFinal {post.sm_tid}) (pmOutputTids{number}.map pmFinal) {_shape_text(list(post.full_shape))}",
                      f"      refine {{ full_value := hReductionValue{number}, full_shape := hReductionFullShape{number}, contributions_nonempty := by simp [pmOutputTids{number}], contribution_shapes := ?_, reduced_shape := ?_ }}",
                      "      · intro contribution hmem", f"        simp only [pmOutputTids{number}, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
                      f"        rcases hmem with {' | '.join('rfl' for _ in range(k))}"]
            lines += [f"        · exact {name}" for name in shapes]
            lines += [f"      · rw [← hReductionValue{number}]", f"        exact hReductionFullShape{number}"]
            register(post, proof)

        elif kind == "gather":
            number = gather_no; gather_no += 1
            pre, post = facts
            inputs = "[" + ", ".join(f"pmFinal {t}" for t in pre.pm_tids) + "]"
            have_fact(f"hGatherIn{number}", pre, f"ShardedRel (smFinal {pre.sm_tid}) {inputs} {cert.gather_dim} {_shape_text(list(pre.full_shape))} {_shape_text(list(pre.shard_shape))}")
            gather_writer(f"hGatherWriter{number}", number, transition, cert, pre, post)
            lines += [f"    have hJoinedValue{number} : smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} := by",
                      f"      rw [{contracts[transition.rule_id][0]} hGatherIn{number}]", "      simp only [List.length_cons, List.length_nil]", f"      exact hGatherWriter{number}.symm"]
            proof = f"hJoinedOut{number}"
            lines += [f"    have {proof} : {post.fact_id}.Holds smFinal pmFinal := by",
                      f"      change smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} ∧ (smFinal {post.sm_tid}).shape = {_shape_text(list(post.full_shape))} ∧ (pmFinal {post.joined_pm_tid}).shape = {_shape_text(list(post.full_shape))}",
                      f"      refine ⟨hJoinedValue{number}, hGatherIn{number}.full_shape, ?_⟩", f"      rw [← hJoinedValue{number}]", f"      exact hGatherIn{number}.full_shape"]
            register(post, proof)

        else:
            number = output_no; output_no += 1
            activation, weight, post = facts
            ow_tids = "[" + ", ".join(str(t) for t in weight.pm_tids) + "]"
            out_tids = "[" + ", ".join(str(t) for t in post.pm_tids) + "]"
            have_fact(f"hJoined{number}", activation, f"smFinal {activation.sm_tid} = pmFinal {activation.joined_pm_tid} ∧ (smFinal {activation.sm_tid}).shape = {_shape_text(list(activation.full_shape))} ∧ (pmFinal {activation.joined_pm_tid}).shape = {_shape_text(list(activation.full_shape))}")
            have_fact(f"hOutputWeight{number}", weight, f"ShardedRel (smFinal {weight.sm_tid}) ({ow_tids}.map pmFinal) 0 {_shape_text(list(weight.full_shape))} {_shape_text(list(weight.shard_shape))}")
            linear_writer(f"hOutputSm{number}", "sm", transition.sm_node_indices[0], ir.sm_nodes[transition.sm_node_indices[0]])
            writers, shapes = [], []; b, seq, inner = activation.full_shape; local_out = weight.shard_shape[0]
            for rank, index in enumerate(transition.pm_node_indices):
                node = ir.pm_nodes[index]; writer = f"hOutputPm{number}_{rank}"; shape = f"hOutputShape{number}_{rank}"
                linear_writer(writer, "pm", index, node); writers.append(writer); shapes.append(shape)
                lines += [f"    have {shape} : (pmFinal {node.outs[0]}).shape = {_shape_text(list(post.shard_shape))} := by", f"      rw [{writer}]",
                          f"      exact fw_linear_3d_shape {b} {seq} {inner} {local_out} _ _ hJoined{number}.2.2 (hOutputWeight{number}.shard_shapes _ (by simp))"]
            theorem = contracts[transition.rule_id][0]; proof = f"hOutputOut{number}"
            lines += [f"    have hOutputComm{number} := ({theorem} (K := ({ow_tids}.map pmFinal).length) (b := {b}) (s := {seq}) (i := {inner}) (o := {local_out}) (x := pmFinal {activation.joined_pm_tid}) (ws := {ow_tids}.map pmFinal) (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by simp) hJoined{number}.2.2 (fun w hw => hOutputWeight{number}.shard_shapes w hw))",
                      f"    have hOutputValue{number} : smFinal {post.sm_tid} = allGatherPrimDimN 2 ({out_tids}.map pmFinal).length 0 ({out_tids}.map pmFinal) := by",
                      f"      rw [hOutputSm{number}, hJoined{number}.1, hOutputWeight{number}.full_value, hOutputComm{number}]",
                      "      simp only [List.map, List.length_cons, List.length_nil]", f"      rw [{', '.join('← '+name for name in writers)}]",
                      f"    have hOutputFullShape{number} : (smFinal {post.sm_tid}).shape = {_shape_text(list(post.full_shape))} := by",
                      f"      rw [hOutputValue{number}, allGatherPrimDimN_shape 2 ({out_tids}.map pmFinal).length ({out_tids}.map pmFinal) {_shape_text(list(post.shard_shape))}]",
                      "      · simp only [List.map, List.length_cons, List.length_nil]", "        native_decide",
                      f"      · simp only [List.map, List.head?, Option.map, Option.getD]; exact {shapes[0]}",
                      f"    have {proof} : {post.fact_id}.Holds smFinal pmFinal := by",
                      f"      change ShardedRel (smFinal {post.sm_tid}) ({out_tids}.map pmFinal) 2 {_shape_text(list(post.full_shape))} {_shape_text(list(post.shard_shape))}",
                      f"      refine {{ full_value := hOutputValue{number}, full_shape := hOutputFullShape{number}, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.map, List.length_cons, List.length_nil] <;> native_decide }}",
                      "      intro shard hmem", "      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",
                      f"      rcases hmem with {' | '.join('rfl' for _ in range(k))}"]
            lines += [f"      · exact {name}" for name in shapes]
            register(post, proof)

        lines.append(f"    exact {proof}")
        helper_declaration = [
            f"private theorem {transition_helper} (smStore pmStore : Store)",
            f"    (hframe : {before.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore))",
        ]
        for record, proof_name in dependency_bindings:
            helper_declaration.append(
                f"    ({proof_name} : {record.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore))"
            )
        helper_declaration += [
            f"    : {post_record.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
            *lines,
            "",
        ]
        transition_helpers.extend(helper_declaration)
        external_proof = f"hFact{transition_index}"
        call_arguments = " ".join(("smStore", "pmStore", "hframe", *(name for _, name in dependency_bindings)))
        transition_calls.append(
            f"    have {external_proof} : {post_record.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := {transition_helper} {call_arguments}"
        )
        proof_by_source[post_record.source] = external_proof
        proof_by_id[post_record.fact_id] = external_proof

    fresh_ids = [fact_id for fact_id in after.fact_ids if fact_id not in before.fact_ids]
    publish_lines = [
        f"private theorem {publish_name} (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    have hframe := {segment_id}_frame smStore pmStore hstate",
        *transition_calls,
        "    intro fact hfact",
        f"    have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
    ]
    if fresh_ids:
        publish_lines += [
            "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
            f"      rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}",
        ]
        publish_lines += [f"      · exact {proof_by_id[fact_id]}" for fact_id in fresh_ids]
    else:
        publish_lines += ["    · simp at fresh"]
    publish_lines += ["    · exact hframe fact old", ""]
    certificate_lines = [
        f"private def {segment_id} : ClosedDepSegmentCertificate {smg} {pmg} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_name}",
        f"  pmNodes := {pm_name}",
        "  sound := by",
        "    intro smStore pmStore hstate",
        f"    simpa [{sm_final_name}, {pm_final_name}] using",
        f"      ({publish_name} smStore pmStore hstate)", "",
    ]
    frame_helper = [
        f"private theorem {segment_id}_frame (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {before.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  unfold {sm_final_name} {pm_final_name}",
        f"  apply RelationState.Holds.fold_frame {sm_name} {pm_name} smStore pmStore hstate",
        "  · native_decide", "  · native_decide", "  · native_decide", "  · native_decide", "",
    ]
    return "\n".join(declarations + frame_helper + writer_helpers + transition_helpers + publish_lines + certificate_lines)
