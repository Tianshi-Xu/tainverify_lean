"""Single-fold renderer for shared BW_linear dX/dW projections and optional tails."""
from __future__ import annotations


def render_closed_k_rank_bw_linear_dual_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import (
            KRankBWLinearDxCertificate, KRankBWLinearDwShardedCertificate,
            KRankAllReduceReconstructionCertificate, JoinedBWViewCertificate,
        )
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import (
            KRankBWLinearDxCertificate, KRankBWLinearDwShardedCertificate,
            KRankAllReduceReconstructionCertificate, JoinedBWViewCertificate,
        )

    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) not in (1, 2, 3):
        raise ValueError("row BW_linear requires dW, optional dX, and at most one tail")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    try:
        segment_transitions = tuple(transition_map[item] for item in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("row BW_linear missing transition authority") from exc
    by_rule = {item.rule_id: item for item in segment_transitions}
    dw_rule = "bw-linear-dw-output-row-sharded-k-rank"
    legacy_rule = "bw-linear-dw-output-row-sharded-rank4"
    dx_rule = "bw-linear-dx-row-reduction-k-rank"
    known = {dx_rule, dw_rule, legacy_rule, "allreduce-reconstruction-k-rank", "bw-view-joined"}
    dx_transition = by_rule.get(dx_rule)
    dw_transition = by_rule.get(dw_rule) or by_rule.get(legacy_rule)
    allreduce_transition = by_rule.get("allreduce-reconstruction-k-rank")
    view_transition = by_rule.get("bw-view-joined")
    if (len(by_rule) != len(segment_transitions) or not set(by_rule) <= known
            or dw_transition is None or {dw_rule, legacy_rule} <= set(by_rule)
            or (allreduce_transition is not None and view_transition is not None)):
        raise ValueError("row BW_linear transition authority is malformed")
    general = dw_transition.rule_id == dw_rule
    if not general and dx_transition is None:
        raise ValueError("legacy row dW still requires its dX companion")
    try:
        from .bw_linear_dx_renderer import _render_row_dx_commutation
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from bw_linear_dx_renderer import _render_row_dx_commutation
        from relation_compiler import get_closed_rule_spec
    dw_theorem = ("TrainVerify.Denote.bw_linear_dw_row_allGather_rank3" if general
                  else dw_transition.lean_theorem)
    legacy_theorems = {
        "TrainVerify.Denote.bw_linear_dw_split_dim2_4_g119",
        "TrainVerify.Denote.bw_linear_dw_osplit_dim2_4_1_8_8_g179",
        "TrainVerify.Denote.bw_linear_dw_col_split_dim2_4_1_8_32_g141",
    }
    if not general and dw_theorem not in legacy_theorems:
        raise ValueError("legacy BW_linear dW theorem identity mismatch")
    dw_certificate = _select_exact_typed_certificate(
        relation, dw_transition, dw_transition.rule_id, dw_theorem,
        KRankBWLinearDwShardedCertificate,
        lambda cert: (tuple(sorted((cert.gradient_fact, cert.activation_fact,
                                    cert.weight_fact))), (cert.output_fact,)),
    )
    input_sources = (dw_certificate.gradient_fact, dw_certificate.activation_fact,
                     dw_certificate.weight_fact)
    certificate = None
    if dx_transition is not None:
        certificate = _select_exact_typed_certificate(
            relation, dx_transition, dx_rule, get_closed_rule_spec(dx_rule).lean_theorems[0],
            KRankBWLinearDxCertificate,
            lambda cert: (tuple(sorted(cert.input_facts)), (cert.output_fact,)),
        )
        if (certificate.family != "row-reduction" or certificate.input_facts != input_sources
                or certificate.output_layout != "reduction" or certificate.gather_dim is not None):
            raise ValueError("row BW_linear dX/dW input authority disagrees")
    # All projection writers are the same; dW remains the authority when dX is absent.
    transition = dx_transition or dw_transition
    allreduce_certificate = None
    if allreduce_transition is not None:
        allreduce_certificate = _select_exact_typed_certificate(
            relation, allreduce_transition, "allreduce-reconstruction-k-rank",
            "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",
            KRankAllReduceReconstructionCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
    view_certificate = None
    if view_transition is not None:
        view_certificate = _select_exact_typed_certificate(
            relation, view_transition, "bw-view-joined",
            "TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view", JoinedBWViewCertificate,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
    records = {item.source: item for item in chain.relation_facts}
    if len(records) != len(chain.relation_facts):
        raise ValueError("row BW_linear ambiguous source records")
    try:
        gradient, activation, weight = (records[source] for source in input_sources)
        output = records[certificate.output_fact] if certificate else None
        dw_output = records[dw_certificate.output_fact]
        reduce_input = records[allreduce_certificate.input_fact] if allreduce_certificate else None
        reduce_output = records[allreduce_certificate.output_fact] if allreduce_certificate else None
        view_input = records[view_certificate.input_fact] if view_certificate else None
        view_output = records[view_certificate.output_fact] if view_certificate else None
    except KeyError as exc:
        raise ValueError("row BW_linear relation fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required = {gradient.fact_id, activation.fact_id, weight.fact_id}
    fresh = {dw_output.fact_id} | ({output.fact_id} if output else set())
    if reduce_input is not None:
        required.add(reduce_input.fact_id); fresh.add(reduce_output.fact_id)
    if view_input is not None:
        required.add(view_input.fact_id); fresh.add(view_output.fact_id)
    if (not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids)
            or fresh & set(before.fact_ids)):
        raise ValueError("row BW_linear pre/post facts are not live")
    if not set(after.fact_ids) <= (fresh | set(before.fact_ids)):
        raise ValueError("row BW_linear post-state introduces an unproved fact")
    k = len(gradient.pm_tids)
    if (k <= 0 or dw_certificate.rank_count != k or (general and ir.pm_num_ranks != k)
            or gradient.kind != "sharded" or gradient.gather_dim != 2
            or activation.kind != "joined" or activation.pm_tids != ()
            or activation.joined_pm_tid is None
            or weight.kind != "sharded" or weight.gather_dim != 0
            or len(weight.pm_tids) != k
            or len(gradient.full_shape) != 3 or len(gradient.shard_shape) != 3
            or len(activation.full_shape) != 3 or len(weight.full_shape) != 2
            or len(weight.shard_shape) != 2):
        raise ValueError("row BW_linear rank/layout/shape arity is not exact")
    b, s, o = gradient.shard_shape
    i = activation.full_shape[2]
    if (min(b, s, o, i) <= 0 or gradient.full_shape != (b, s, o*k)
            or activation.full_shape != (b, s, i) or activation.shard_shape != (b, s, i)
            or weight.full_shape != (o*k, i) or weight.shard_shape != (o, i)
            or dw_output.kind != "sharded" or dw_output.gather_dim != 0
            or len(dw_output.pm_tids) != k or dw_output.full_shape != weight.full_shape
            or dw_output.shard_shape != weight.shard_shape):
        raise ValueError("row BW_linear dW exact shape contract mismatch")
    if output is not None and (certificate.rank_count != k or output.kind != "reduction"
            or output.gather_dim is not None or len(output.pm_tids) != k
            or output.full_shape != activation.full_shape or output.shard_shape != output.full_shape):
        raise ValueError("row BW_linear dX exact reduction contract mismatch")
    legacy_shapes = {
        (1, 8, 8, 32): "TrainVerify.Denote.bw_linear_dw_split_dim2_4_g119",
        (1, 8, 8, 128): "TrainVerify.Denote.bw_linear_dw_osplit_dim2_4_1_8_8_g179",
        (1, 8, 32, 32): "TrainVerify.Denote.bw_linear_dw_col_split_dim2_4_1_8_32_g141",
    }
    if not general and (k != 4 or legacy_shapes.get((b,s,o,i)) != dw_theorem):
        raise ValueError("legacy row dW theorem shape domain mismatch")
    sm_start, sm_end = segment.sm_range
    pm_start, pm_end = segment.pm_range
    if (not 0 <= sm_start <= sm_end <= len(ir.sm_nodes)
            or not 0 <= pm_start <= pm_end <= len(ir.pm_nodes)):
        raise ValueError("row BW_linear invalid complete frame range")
    sm_frame = list(ir.sm_nodes[sm_start:sm_end])
    pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    if (len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k
            or len(set(transition.pm_node_indices)) != k
            or tuple(sorted(transition.pm_node_indices)) != transition.pm_node_indices
            or not set(transition.sm_node_indices) <= set(range(sm_start,sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start,pm_end))):
        raise ValueError("row BW_linear footprint is not ordered exact 1+K")
    if (dw_transition.sm_node_indices != transition.sm_node_indices
            or dw_transition.pm_node_indices != transition.pm_node_indices
            or dw_certificate.sm_step_id != f"sm:{transition.sm_node_indices[0]}:1"
            or dw_certificate.pm_step_ids != tuple(f"pm:{n}:1" for n in transition.pm_node_indices)):
        raise ValueError("row BW_linear dW shared-writer footprint mismatch")
    if certificate is not None and (certificate.sm_step_id != f"sm:{transition.sm_node_indices[0]}:0"
            or certificate.pm_step_ids != tuple(f"pm:{n}:0" for n in transition.pm_node_indices)):
        raise ValueError("row BW_linear dX shared-writer footprint mismatch")
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    def check_writer(node, rank, ins, dw_tid, dx_tid):
        if (node.rank != rank or node.op != "BW_linear" or node.params not in (None, [])
                or tuple(node.ins) != ins or len(node.outs) != 2 or len(set(node.outs)) != 2
                or node.outs[1] != dw_tid or (dx_tid is not None and node.outs[0] != dx_tid)):
            raise ValueError("row BW_linear writer roles/ranks/projections are not exact")
    check_writer(sm_node,0,(gradient.sm_tid,activation.sm_tid,weight.sm_tid),dw_output.sm_tid,
                 output.sm_tid if output else None)
    for rank,node in enumerate(pm_nodes):
        check_writer(node,rank,(gradient.pm_tids[rank],activation.joined_pm_tid,weight.pm_tids[rank]),
                     dw_output.pm_tids[rank],output.pm_tids[rank] if output else None)
    view_sm_node = view_pm_node = None
    if view_transition is not None:
        if (len(view_transition.sm_node_indices) != 1 or len(view_transition.pm_node_indices) != 1
                or not set(view_transition.sm_node_indices) <= set(range(sm_start,sm_end))
                or not set(view_transition.pm_node_indices) <= set(range(pm_start,pm_end))
                or view_input.kind != "joined" or view_output.kind != "joined"
                or view_input.full_shape != tuple(view_certificate.input_shape)
                or view_output.full_shape != tuple(view_certificate.target_shape)
                or view_certificate.sm_step_id != f"sm:{view_transition.sm_node_indices[0]}:0"
                or view_certificate.pm_step_id != f"pm:{view_transition.pm_node_indices[0]}:0"):
            raise ValueError("row BW_linear/view exact authority mismatch")
        view_sm_node = ir.sm_nodes[view_transition.sm_node_indices[0]]
        view_pm_node = ir.pm_nodes[view_transition.pm_node_indices[0]]
        for node,src,dst in ((view_sm_node,view_input.sm_tid,view_output.sm_tid),
                            (view_pm_node,view_input.joined_pm_tid,view_output.joined_pm_tid)):
            if (node.op != "BW_view" or len(node.ins) != 2
                    or node.ins[0] != src or node.outs != [dst]
                    or not view_certificate.target_shape
                    or node.params != list(view_certificate.target_shape)):
                raise ValueError("row BW_linear/view writer mismatch")
    reduce_node = None
    if allreduce_transition is not None:
        if (allreduce_transition.sm_node_indices != () or len(allreduce_transition.pm_node_indices) != 1
                or reduce_input.kind != "reduction" or reduce_input.gather_dim is not None
                or reduce_output.kind != "joined"
                or reduce_output.sm_tid != reduce_input.sm_tid
                or reduce_output.full_shape != reduce_input.full_shape
                or reduce_input.shard_shape != reduce_input.full_shape
                or reduce_output.joined_pm_tid is None
                or allreduce_certificate.rank_count != len(reduce_input.pm_tids)
                or not reduce_input.pm_tids or allreduce_certificate.full_shape != reduce_input.full_shape):
            raise ValueError("row BW_linear AllReduce exact authority mismatch")
        reduce_index = allreduce_transition.pm_node_indices[0]
        if not pm_start <= reduce_index < pm_end:
            raise ValueError("row BW_linear AllReduce writer outside frame")
        reduce_node = ir.pm_nodes[reduce_index]
        if (reduce_node.rank != 0 or reduce_node.op != "AllReducePrim" or reduce_node.params not in (None, [])
                or tuple(reduce_node.ins) != reduce_input.pm_tids
                or reduce_node.outs != [reduce_output.joined_pm_tid]
                or allreduce_certificate.pm_allreduce_step != f"pm:{reduce_index}:0"):
            raise ValueError("row BW_linear AllReduce writer mismatch")

    if general:
        # Validate source identity independently of the materialized record.  Shapes
        # are checked above; a compatible shape never substitutes for the source TID.
        semantic_records = [gradient,activation,weight,dw_output]
        semantic_records += [r for r in (output,reduce_input,reduce_output,view_input,view_output) if r is not None]
        def resolve(ref, side, limit):
            fields = ref.split(":")
            nodes = ir.sm_nodes if side == "sm" else ir.pm_nodes
            def latest(tid):
                return next((index for index in range(limit-1,-1,-1) if tid in nodes[index].outs), None)
            if len(fields) == 2 and fields[0] == "init" and fields[1].isdigit():
                tid = int(fields[1])
                if latest(tid) is None:
                    return tid
                raise ValueError("row BW_linear initial source was overwritten")
            if len(fields) == 3 and fields[0] == side and all(v.isdigit() for v in fields[1:]):
                index, slot = map(int, fields[1:])
                if index < limit and slot < len(nodes[index].outs):
                    tid = nodes[index].outs[slot]
                    if latest(tid) == index:
                        return tid
            raise ValueError("row BW_linear unresolved source reference")
        for record in semantic_records:
            source = record.source
            sm_limit, pm_limit = ((sm_end,pm_end) if record.fact_id in fresh else (sm_start,pm_start))
            if (source.layout != record.kind or source.gather_dim != record.gather_dim
                    or source.source_step_triples or record.source_tid_triples
                    or record.metadata_tid is not None or record.metadata_region_id is not None
                    or record.row_shard_shape is not None):
                raise ValueError("row BW_linear source/record layout or axis mismatch")
            if record.kind == "joined":
                if (len(source.step_triple) != 1 or source.joined_pm_step is None
                        or record.pm_tids or record.joined_pm_tid is None
                        or record.gather_dim is not None or record.shard_shape != record.full_shape
                        or resolve(source.joined_pm_step,"pm",pm_limit) != record.joined_pm_tid):
                    raise ValueError("row BW_linear joined source/record mismatch")
            elif (source.joined_pm_step is not None or record.joined_pm_tid is not None
                    or len(source.step_triple) != 1+len(record.pm_tids)
                    or tuple(resolve(ref,"pm",pm_limit) for ref in source.step_triple[1:]) != record.pm_tids):
                raise ValueError("row BW_linear ordered source/record mismatch")
            if not source.step_triple or resolve(source.step_triple[0],"sm",sm_limit) != record.sm_tid:
                raise ValueError("row BW_linear SM source/record mismatch")

    # The public anchor is separate from authority_facts and must also survive.
    by_id = {r.fact_id:r for r in chain.relation_facts}
    authority = {a.fact_id:a for a in chain.authority_facts}
    if chain.anchor_fact is not None:
        authority[chain.anchor_fact.fact_id] = chain.anchor_fact
    if len(by_id) != len(chain.relation_facts) or set(by_id) & set(authority):
        raise ValueError("row BW_linear ambiguous live fact identity")
    protected = {"sm":set(), "pm":set()}
    authority_tids = {"sm":set(), "pm":set()}
    for fid in set(before.fact_ids) | set(after.fact_ids):
        if fid in by_id:
            r = by_id[fid]
            protected["sm"].add(r.sm_tid); protected["pm"].update(r.pm_tids)
            if r.joined_pm_tid is not None: protected["pm"].add(r.joined_pm_tid)
            if r.metadata_tid is not None:
                protected["sm"].add(r.metadata_tid); protected["pm"].add(r.metadata_tid)
            for sm,pm0,pm1 in r.source_tid_triples:
                protected["sm"].add(sm);protected["pm"].update((pm0,pm1))
        elif fid in authority:
            a = authority[fid]
            if a.kind in ("tensor_shape", "packed_cu", "label_bound"):
                authority_tids[a.side].add(a.tid)
            elif a.kind == "tensor_eq":
                authority_tids[a.left_side].add(a.left_tid)
                authority_tids[a.right_side].add(a.right_tid)
            elif a.kind == "gather":
                authority_tids["sm"].add(a.sm_tid)
                authority_tids["pm"].update((a.pm_rank0_tid,a.pm_rank1_tid))
            else: raise ValueError("row BW_linear unsupported frame authority")
        else: raise ValueError("row BW_linear unknown live fact")
    for side,frame,start in (("sm",sm_frame,sm_start),("pm",pm_frame,pm_start)):
        allowed = {}
        for t in segment_transitions:
            for post in t.post_facts:
                r = records[post]
                tids = (r.sm_tid,) if side == "sm" else ((r.joined_pm_tid,) if r.kind == "joined" else r.pm_tids)
                indices = t.sm_node_indices if side == "sm" else t.pm_node_indices
                for tid,index in zip(tids,indices): allowed.setdefault(index,set()).add(tid)
        pre_tids = set(authority_tids[side])
        for fid in before.fact_ids:
            if fid in by_id:
                r=by_id[fid]
                pre_tids.update((r.sm_tid,) if side == "sm" else (*r.pm_tids,*((r.joined_pm_tid,) if r.joined_pm_tid is not None else ())))
                if r.metadata_tid is not None:
                    pre_tids.add(r.metadata_tid)
                for sm,pm0,pm1 in r.source_tid_triples:
                    pre_tids.update((sm,) if side == "sm" else (pm0,pm1))
        for index,node in enumerate(frame,start):
            if set(node.outs) & (pre_tids | (protected[side] - allowed.get(index,set()))):
                raise ValueError("row BW_linear frame overwrites live relation/authority")
        for tids in allowed.values():
            for tid in tids:
                if sum(tid in node.outs for node in frame) != 1:
                    raise ValueError("row BW_linear output has multiple writers")

    sm_nodes_name = f"{segment_id}_sm_nodes"
    pm_nodes_name = f"{segment_id}_pm_nodes"
    sm_final_name = f"{segment_id}_sm_final"
    pm_final_name = f"{segment_id}_pm_final"
    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store",
        "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node, slot):
        theorem_name = f"{segment_id}_{name}"
        final = f"({final_name} {initial})"
        projection = ".1" if slot == 0 else ".2"
        apply_lemma = "applyNode_bw_linear_fst_out" if slot == 0 else "applyNode_bw_linear_snd_out"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[slot]} =",
            f"      (bw_linear ({final} {node.ins[0]}) ({final} {node.ins[1]}) ({final} {node.ins[2]})){projection} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}",
            "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[slot], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=(
                f"(bw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
                f"({{store}} {node.ins[2]})){projection}"
            ),
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact {apply_lemma} {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.ins[2]} "
                f"{node.outs[0]} {node.outs[1]} (by native_decide)",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
        return theorem_name

    sm_helper = None
    if output is not None:
        sm_helper = writer(
            "hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
            sm_nodes_name, sm_frame, transition.sm_node_indices[0] - sm_start, sm_node, 0,
        )
    sm_dw_helper = writer(
        "hSmDwWriter", ir.sm_graph_ref, "smStore", sm_final_name,
        sm_nodes_name, sm_frame, transition.sm_node_indices[0] - sm_start, sm_node, 1,
    )
    pm_helpers = []
    if output is not None:
        pm_helpers = [
            writer(
                f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
                pm_nodes_name, pm_frame, index - pm_start, node, 0,
            )
            for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
        ]
    pm_dw_helpers = [
        writer(
            f"hPmDwWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
            pm_nodes_name, pm_frame, index - pm_start, node, 1,
        )
        for rank, (index, node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
    ]
    reduce_helper = None
    if reduce_node is not None:
        final = f"({pm_final_name} pmStore)"
        reduce_inputs = "[" + ", ".join(str(tid) for tid in reduce_node.ins) + "]"
        expression = f"allReducePrim {len(reduce_node.ins)} 0 [" + ", ".join(
            f"{{store}} {tid}" for tid in reduce_node.ins
        ) + "]"
        reduce_helper = f"{segment_id}_hAllReduceWriter"
        lines.extend([
            f"private theorem {reduce_helper} (pmStore : Store) :",
            f"    {final} {reduce_node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {pm_nodes_name}.foldl",
            f"      (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by",
            f"    unfold {pm_final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=ir.pm_graph_ref, initial_store="pmStore", final_store=final,
            final_equality="hfinal", nodes_name=pm_nodes_name, nodes=pm_frame,
            position=allreduce_transition.pm_node_indices[0] - pm_start,
            output_tid=reduce_node.outs[0], input_tids=tuple(reduce_node.ins),
            written_tids={tid for item in pm_frame for tid in item.outs},
            expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "unfold applyNodeDistributed",
                "rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
                f"· exact applyNode_allReducePrim_out {ir.pm_graph_ref} t 0 {reduce_inputs} {reduce_node.outs[0]}",
                "· native_decide", "· native_decide",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""])
    view_sm_helper = view_pm_helper = None
    if view_transition is not None:
        def view_writer(name, graph, initial, final_name, nodes_name, frame, position, node):
            theorem_name=f"{segment_id}_{name}"; final=f"({final_name} {initial})"; shape=_shape_text(list(view_certificate.target_shape))
            lines.extend([f"private theorem {theorem_name} ({initial}:Store) : {final} {node.outs[0]} = fw_view {shape} ({final} {node.ins[0]}) := by",f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {final_name}; rfl"])
            helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=position,output_tid=node.outs[0],input_tids=(node.ins[0],),written_tids={tid for item in frame for tid in item.outs},expression=f"fw_view {shape} ({{store}} {node.ins[0]})",apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.ins[1]} {node.outs[0]}"])
            lines.extend(item[2:] if item.startswith("  ") else item for item in helper);lines.extend(["  exact hout",""]);return theorem_name
        view_sm_helper=view_writer("hViewSm",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,sm_frame,view_transition.sm_node_indices[0]-sm_start,view_sm_node)
        view_pm_helper=view_writer("hViewPm",ir.pm_graph_ref,"pmStore",pm_final_name,pm_nodes_name,pm_frame,view_transition.pm_node_indices[0]-pm_start,view_pm_node)

    glist = "[" + ", ".join(f"pmFinal {tid}" for tid in gradient.pm_tids) + "]"
    wlist = "[" + ", ".join(f"pmFinal {tid}" for tid in weight.pm_tids) + "]"
    olist = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]" if output else None
    dwlist = "[" + ", ".join(f"pmFinal {tid}" for tid in dw_output.pm_tids) + "]"
    gfull, gshard = (_shape_text(list(x)) for x in (gradient.full_shape, gradient.shard_shape))
    wfull, wshard = (_shape_text(list(x)) for x in (weight.full_shape, weight.shard_shape))
    oshape = _shape_text(list(output.full_shape)) if output else None
    lines.extend([
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smFinal := {sm_final_name} smStore",
        f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} 2 {gfull} {gshard} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change smFinal {activation.sm_tid} = pmFinal {activation.joined_pm_tid} ∧",
        f"      (smFinal {activation.sm_tid}).shape = {_shape_text(list(activation.full_shape))} ∧",
        f"      (pmFinal {activation.joined_pm_tid}).shape = {_shape_text(list(activation.full_shape))} at hx",
        f"    have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {weight.sm_tid}) {wlist} 0 {wfull} {wshard} at hw",
        f"    have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN 2 {k} 0 {glist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"    have hwValue : smFinal {weight.sm_tid} = allGatherPrimDimN 0 {k} 0 {wlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hw.full_value",
    ])
    if output is not None:
        lines.extend([
            f"    have hSmWriter : smFinal {sm_node.outs[0]} =",
            f"        (bw_linear (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) (smFinal {sm_node.ins[2]})).1 :=",
            f"      {sm_helper} smStore",
        ])
    lines.extend([
        f"    have hSmDwWriter : smFinal {sm_node.outs[1]} =",
        f"        (bw_linear (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) (smFinal {sm_node.ins[2]})).2 :=",
        f"      {sm_dw_helper} smStore",
    ])
    if view_transition is not None:
        target_shape=_shape_text(list(view_certificate.target_shape));input_shape=_shape_text(list(view_certificate.input_shape))
        lines.extend([f"    have hvi : {view_input.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"    have hvs := {view_sm_helper} smStore",f"    have hvp := {view_pm_helper} pmStore",f"    change smFinal {view_output.sm_tid} = fw_view {target_shape} (smFinal {view_input.sm_tid}) at hvs",f"    change pmFinal {view_output.joined_pm_tid} = fw_view {target_shape} (pmFinal {view_input.joined_pm_tid}) at hvp",f"    have houtView : {view_output.fact_id}.Holds smFinal pmFinal := by",f"      change smFinal {view_output.sm_tid} = pmFinal {view_output.joined_pm_tid} ∧ _ ∧ _","      rw [hvs, hvp]",f"      exact JoinedRel.fw_view {target_shape} {input_shape} hvi"])
    for rank, node in enumerate(pm_nodes):
        if output is not None:
            lines.extend([
                f"    have hPmWriter{rank} : pmFinal {node.outs[0]} =",
                f"        (bw_linear (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) (pmFinal {node.ins[2]})).1 :=",
                f"      {pm_helpers[rank]} pmStore",
            ])
        lines.extend([
            f"    have hPmDwWriter{rank} : pmFinal {node.outs[1]} =",
            f"        (bw_linear (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) (pmFinal {node.ins[2]})).2 :=",
            f"      {pm_dw_helpers[rank]} pmStore",
            f"    have hgShape{rank} := hg.shard_shapes (pmFinal {gradient.pm_tids[rank]}) (by simp)",
            f"    have hwShape{rank} := hw.shard_shapes (pmFinal {weight.pm_tids[rank]}) (by simp)",
        ])
        if output is not None:
            lines.extend([
                f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {oshape} := by",
                f"      rw [hPmWriter{rank}]",
                f"      exact bw_linear_3d_fst_shape {b} {s} {o} {i} _ _ _",
                f"        hgShape{rank} hx.2.2 hwShape{rank}",
            ])
        lines.extend([
            f"    have hDwOutShape{rank} : (pmFinal {dw_output.pm_tids[rank]}).shape = {wshard} := by",
            f"      rw [hPmDwWriter{rank}]",
            f"      exact bw_linear_3d_snd_shape {b} {s} {o} {i} _ _ _",
            f"        hgShape{rank} hx.2.2 hwShape{rank}",
        ])
    if output is not None:
        lines.extend(_render_row_dx_commutation(
            name="hcomm", theorem=transition.lean_theorem, k=k,
            gradient=gradient, weight=weight, activation=f"pmFinal {activation.joined_pm_tid}",
            gradient_shapes="hg.shard_shapes", weight_shapes="hw.shard_shapes", activation_shape="hx.2.2"))
        lines.extend([
            f"    have hOutValue : smFinal {output.sm_tid} = allReducePrim {k} 0 {olist} := by",
            "      rw [hSmWriter, hgValue, hx.1, hwValue, hcomm]",
            "      rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
            f"    have hOutValueList : smFinal {output.sm_tid} =",
            f"        allReducePrim {olist}.length 0 {olist} := by",
            "      simpa only [List.length_cons, List.length_nil] using hOutValue",
            f"    have hFullShape : (smFinal {output.sm_tid}).shape = {oshape} := by",
            "      rw [hSmWriter]",
            f"      exact bw_linear_3d_fst_shape {gradient.full_shape[0]} {gradient.full_shape[1]} {gradient.full_shape[2]} {activation.full_shape[2]} _ _ _",
            "        hg.full_shape hx.2.1 hw.full_shape",
            f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
            f"      change ReductionRel (smFinal {output.sm_tid}) {olist} {oshape}",
            "      refine {",
            "        full_value := hOutValueList", "        full_shape := hFullShape",
            "        contributions_nonempty := by simp",
            "        contribution_shapes := ?_", "        reduced_shape := ?_", "      }",
            "      · intro contribution hmem",
            "        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
            "        rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
        ])
        for rank in range(k):
            lines.extend(["        · subst contribution", f"          exact hOutShape{rank}"])
        lines.extend([
            "      · rw [← hOutValueList]", "        exact hFullShape",
        ])
    if general:
        local_dw = "[" + ", ".join(
            f"(bw_linear (pmFinal {gt}) (pmFinal {activation.joined_pm_tid}) (pmFinal {wt})).2"
            for gt,wt in zip(gradient.pm_tids,weight.pm_tids)) + "]"
        lines.extend([
            f"    have hDwCommRaw := {dw_theorem} {k} {b} {s} {o} {i}",
            f"      {glist} {wlist} (pmFinal {activation.joined_pm_tid})",
            "      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl",
            "      hg.shard_shapes hw.shard_shapes hx.2.2",
            f"    have hDwComm : (bw_linear (allGatherPrimDimN 2 {k} 0 {glist})",
            f"        (pmFinal {activation.joined_pm_tid}) (allGatherPrimDimN 0 {k} 0 {wlist})).2 =",
            f"        allGatherPrimDimN 0 {k} 0 {local_dw} := by",
            "      simpa only [List.zipWith] using hDwCommRaw",
            f"    have hDwValue : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 {k} 0 {dwlist} := by",
            "      rw [hSmDwWriter, hgValue, hx.1, hwValue, hDwComm]",
            "      rw [" + ", ".join(f"← hPmDwWriter{rank}" for rank in range(k)) + "]",
        ])
    elif dw_transition.lean_theorem.endswith("bw_linear_dw_split_dim2_4_g119"):
        for rank in range(k):
            lines.extend([
                f"    have hGradChunk{rank} : chunkPrimDimN 2 4 {rank} (smFinal {gradient.sm_tid}) = pmFinal {gradient.pm_tids[rank]} := by",
                "      rw [hgValue]",
                f"      rw [chunkPrimDimN_allGatherPrimDimN_dim2_4_1_8_8 _ {rank} (by native_decide) (by simp) hg.shard_shapes]",
                "      simp [List.getD]",
            ])
        lines.extend([
            f"    have hDwComm := {dw_transition.lean_theorem}",
            f"      (smFinal {gradient.sm_tid}) (smFinal {activation.sm_tid}) (smFinal {weight.sm_tid})",
            *(f"      (pmFinal {tid})" for tid in weight.pm_tids),
            "      hg.full_shape hx.2.1 hw.full_shape",
            *(f"      hwShape{rank}" for rank in range(k)),
            f"    have hDwValue : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 4 0 {dwlist} := by",
            "      rw [hSmDwWriter, hDwComm, hx.1]",
            "      rw [" + ", ".join(f"hGradChunk{rank}" for rank in range(k)) + "]",
            "      rw [" + ", ".join(f"← hPmDwWriter{rank}" for rank in range(k)) + "]",
        ])
    elif dw_transition.lean_theorem.endswith("bw_linear_dw_osplit_dim2_4_1_8_8_g179"):
        lines.extend([
            f"    have hDwComm := {dw_transition.lean_theorem}",
            f"      (pmFinal {activation.joined_pm_tid})",
            *(f"      (pmFinal {tid})" for tid in gradient.pm_tids),
            *(f"      (pmFinal {tid})" for tid in weight.pm_tids),
            "      hx.2.2",
            *(f"      hgShape{rank}" for rank in range(k)),
            *(f"      hwShape{rank}" for rank in range(k)),
            f"    have hDwValue : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 4 0 {dwlist} := by",
            "      rw [hSmDwWriter, hgValue, hx.1, hwValue, hDwComm]",
            "      rw [" + ", ".join(f"← hPmDwWriter{rank}" for rank in range(k)) + "]",
        ])
    else:
        lines.extend([
            f"    have hDwComm := {dw_transition.lean_theorem}",
            *(f"      (pmFinal {tid})" for tid in gradient.pm_tids),
            f"      (pmFinal {activation.joined_pm_tid})",
            *(f"      (pmFinal {tid})" for tid in weight.pm_tids),
            *(f"      hgShape{rank}" for rank in range(k)),
            "      hx.2.2",
            *(f"      hwShape{rank}" for rank in range(k)),
            f"    have hDwValue : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 4 0 {dwlist} := by",
            "      rw [hSmDwWriter, hgValue, hx.1, hwValue, hDwComm]",
            "      rw [" + ", ".join(f"← hPmDwWriter{rank}" for rank in range(k)) + "]",
        ])
    lines.extend([
        f"    have hDwValueList : smFinal {dw_output.sm_tid} = allGatherPrimDimN 0 {dwlist}.length 0 {dwlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hDwValue",
        f"    have hDwFullShape : (smFinal {dw_output.sm_tid}).shape = {wfull} := by",
        "      rw [hSmDwWriter]",
        f"      exact bw_linear_3d_snd_shape {gradient.full_shape[0]} {gradient.full_shape[1]} {gradient.full_shape[2]} {activation.full_shape[2]} _ _ _",
        "        hg.full_shape hx.2.1 hw.full_shape",
        f"    have houtDw : {dw_output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {dw_output.sm_tid}) {dwlist} 0 {wfull} {wshard}",
        "      refine {", "        full_value := hDwValueList", "        full_shape := hDwFullShape",
        "        shards_nonempty := by simp", "        gather_dim_lt := by native_decide",
        "        shard_shapes := ?_", "        shape_contract := by simp", "      }",
        "      intro shard hmem",
        "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend(["      · subst shard", f"        exact hDwOutShape{rank}"])
    if reduce_input is not None:
        reduce_list = "[" + ", ".join(f"pmFinal {tid}" for tid in reduce_input.pm_tids) + "]"
        reduce_shape = _shape_text(list(reduce_input.full_shape))
        lines.extend([
            f"    have hred : {reduce_input.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
            f"    change ReductionRel (smFinal {reduce_input.sm_tid}) {reduce_list} {reduce_shape} at hred",
            f"    have hReduceWriter := {reduce_helper} pmStore",
            f"    change pmFinal {reduce_output.joined_pm_tid} = allReducePrim {len(reduce_input.pm_tids)} 0 {reduce_list} at hReduceWriter",
            f"    have hReduceValue : smFinal {reduce_input.sm_tid} = allReducePrim {len(reduce_input.pm_tids)} 0 {reduce_list} := by",
            "      simpa only [List.length_cons, List.length_nil] using hred.full_value",
            f"    have hReduceJoined : smFinal {reduce_output.sm_tid} = pmFinal {reduce_output.joined_pm_tid} :=",
            "      hReduceValue.trans hReduceWriter.symm",
            f"    have houtReduce : {reduce_output.fact_id}.Holds smFinal pmFinal := by",
            f"      change smFinal {reduce_output.sm_tid} = pmFinal {reduce_output.joined_pm_tid} ∧ _ ∧ _",
            "      refine ⟨hReduceJoined, hred.full_shape, ?_⟩",
            "      rw [← hReduceJoined]", "      exact hred.full_shape",
        ])
    publication=([output.fact_id] if output else [])+[dw_output.fact_id]+([reduce_output.fact_id] if reduce_output else [])+([view_output.fact_id] if view_output else [])
    pub_list="["+", ".join(publication)+"]"
    proof_names=(["hout"] if output else [])+["houtDw"]+(["houtReduce"] if reduce_output else [])+(["houtView"] if view_output else [])
    fresh_lines=["      rcases fresh with " + " | ".join("rfl" for _ in proof_names)]
    fresh_lines.extend(f"      · exact {name}" for name in proof_names)
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ {pub_list} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {pub_list} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered",
        "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        *fresh_lines,
        "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    exact {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)
