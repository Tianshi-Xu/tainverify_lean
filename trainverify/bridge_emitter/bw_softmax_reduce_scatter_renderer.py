"""One-fold atomic BW_softmax(dim2) and independent prior ReduceScatter reconstruction."""
from __future__ import annotations


try:
    from .atomic_contracts import validate_atomic_transition_contracts
except ImportError:
    from atomic_contracts import validate_atomic_transition_contracts


def render_closed_bw_softmax_reduce_scatter_segment(ir, relation, segment_id: str) -> str:
    validate_atomic_transition_contracts(relation, segment_id)
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import (get_closed_rule_spec, KRankReduceScatterReconstructionCertificate, ClosedRelationFactRecord, ClosedTensorShapeFactRecord, ClosedTensorEqFactRecord, ClosedGatherFactRecord, ClosedPackedCuFactRecord, ClosedLabelBoundFactRecord)
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import (get_closed_rule_spec, KRankReduceScatterReconstructionCertificate, ClosedRelationFactRecord, ClosedTensorShapeFactRecord, ClosedTensorEqFactRecord, ClosedGatherFactRecord, ClosedPackedCuFactRecord, ClosedLabelBoundFactRecord)

    chain = relation.dependent_chain_plan
    segments = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segments) != 1:
        raise ValueError("BW_softmax/ReduceScatter requires one complete segment")
    segment = segments[0]
    by_transition = {t.transition_id: t for t in relation.transition_specs}
    if len(by_transition) != len(relation.transition_specs) or len(set(segment.transition_ids)) != 2:
        raise ValueError("BW_softmax/ReduceScatter requires two unique transitions")
    try:
        transitions = [by_transition[x] for x in segment.transition_ids]
        transition, = [t for t in transitions if t.rule_id == "bw-softmax-sharded-dim2-k-rank"]
        rt, = [t for t in transitions if t.rule_id == "reduce-scatter-reconstruction-k-rank"]
    except (KeyError, ValueError) as exc:
        raise ValueError("BW_softmax/ReduceScatter exact family mismatch") from exc
    rc = _select_exact_typed_certificate(relation, rt,
        "reduce-scatter-reconstruction-k-rank", "TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn",
        KRankReduceScatterReconstructionCertificate, lambda c: ((c.input_fact,), (c.output_fact,)))
    spec = get_closed_rule_spec(transition.rule_id)
    rule, theorem = spec.rule_id, spec.lean_theorems[0]
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, theorem, spec.certificate_type,
        lambda cert: (
            tuple(sorted((cert.gradient_fact, cert.activation_fact))),
            (cert.output_fact,),
        ),
    )
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient = records[certificate.gradient_fact]
        activation = records[certificate.activation_fact]
        output = records[certificate.output_fact]
        reduction = records[rc.input_fact]
        scattered = records[rc.output_fact]
    except KeyError as exc:
        raise ValueError("BW_softmax fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before,after = states[segment.pre_state_id],states[segment.post_state_id]
    if (not {gradient.fact_id,activation.fact_id} <= set(before.fact_ids)
            or not {output.fact_id,scattered.fact_id} <= set(after.fact_ids)
            or reduction.fact_id not in before.fact_ids):
        raise ValueError("BW_softmax pre/post facts are not live")
    if not set(after.fact_ids) <= ({output.fact_id,scattered.fact_id}|set(before.fact_ids)):
        raise ValueError("BW_softmax post-state introduces an unproved fact")
    k=len(output.pm_tids)
    if (k<=0 or certificate.rank_count!=k or certificate.gather_dim!=output.gather_dim
            or gradient.kind!="sharded" or activation.kind!="sharded" or output.kind!="sharded"
            or (gradient.full_shape,gradient.shard_shape,gradient.gather_dim)
               !=(activation.full_shape,activation.shard_shape,activation.gather_dim)
            or (output.full_shape,output.shard_shape,output.gather_dim)
               !=(activation.full_shape,activation.shard_shape,activation.gather_dim)
            or len(gradient.pm_tids)!=k or len(activation.pm_tids)!=k):
        raise ValueError("BW_softmax metadata is not exact")
    dim = 1 if rule == "bw-softmax-sharded-dim1-k-rank" else 2
    if any(r.source.layout!="sharded" or r.source.gather_dim!=dim for r in (gradient,activation,output)):
        raise ValueError("BW_softmax source/record axis mismatch")
    if (output.gather_dim != dim or len(output.shard_shape) != 4
            or min(output.shard_shape) <= 0
            or output.full_shape != tuple(v*k if i == dim else v for i,v in enumerate(output.shard_shape))):
        raise ValueError("BW_softmax positive rank-4 shape/axis contract mismatch")
    b,h,q,d = output.shard_shape
    if len(transition.sm_node_indices)!=1 or len(transition.pm_node_indices)!=k:
        raise ValueError("BW_softmax footprint is not exact 1+K")
    sm_start,sm_end=segment.sm_range;pm_start,pm_end=segment.pm_range
    if (not set(transition.sm_node_indices)<=set(range(sm_start,sm_end))
            or not set(transition.pm_node_indices)<=set(range(pm_start,pm_end))):
        raise ValueError("BW_softmax writers are outside complete frame")
    sm_frame=list(ir.sm_nodes[sm_start:sm_end]);pm_frame=list(ir.pm_nodes[pm_start:pm_end])
    sm_node=ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes=tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    if (certificate.sm_step_id!=f"sm:{transition.sm_node_indices[0]}:0"
            or certificate.pm_step_ids!=tuple(f"pm:{i}:0" for i in transition.pm_node_indices)):
        raise ValueError("BW_softmax certificate footprint was tampered")
    if (sm_node.rank!=0 or sm_node.op!="BW_softmax" or tuple(sm_node.params or [])!=certificate.parameters
            or sm_node.ins!=[gradient.sm_tid,activation.sm_tid]
            or sm_node.outs!=[output.sm_tid]):
        raise ValueError("BW_softmax SM writer roles are not exact")
    if tuple(node.rank for node in pm_nodes)!=tuple(range(k)):
        raise ValueError("BW_softmax PM ranks are not ordered")
    for rank,node in enumerate(pm_nodes):
        if (node.op!="BW_softmax" or tuple(node.params or [])!=certificate.parameters
                or node.ins!=[gradient.pm_tids[rank],activation.pm_tids[rank]]
                or node.outs!=[output.pm_tids[rank]]):
            raise ValueError("BW_softmax PM writer roles/order are not exact")

    def fact_tids(fact):
        if type(fact) is ClosedRelationFactRecord:
            if fact.kind in {"sharded", "chunked", "reduction", "replicated", "ordinary"}:
                return {fact.sm_tid}, set(fact.pm_tids)
            if fact.kind == "joined":
                if fact.joined_pm_tid is None:
                    raise ValueError("joined retained fact lacks PM TID")
                return {fact.sm_tid}, {fact.joined_pm_tid}
            if fact.kind == "zigzag":
                if fact.metadata_tid is None:
                    raise ValueError("zigzag retained fact lacks metadata TID")
                return {fact.sm_tid}, {*fact.pm_tids, fact.metadata_tid}
            if fact.kind == "joined_ordinary":
                if fact.joined_pm_tid is None:
                    raise ValueError("joined ordinary retained fact lacks PM TID")
                return {fact.sm_tid}, {*fact.pm_tids, fact.joined_pm_tid}
            if fact.kind == "joined_indexed_stack_dim1":
                if fact.joined_pm_tid is None or not fact.source_tid_triples:
                    raise ValueError("joined indexed-stack retained fact is incomplete")
                sm, pm = {fact.sm_tid}, {*fact.pm_tids, fact.joined_pm_tid}
                for source_sm, source_pm0, source_pm1 in fact.source_tid_triples:
                    sm.add(source_sm); pm.update((source_pm0, source_pm1))
                return sm, pm
            if fact.kind == "label_chunks":
                return set(), {fact.sm_tid, *fact.pm_tids}
            raise ValueError(f"unsupported retained relation fact kind: {fact.kind!r}")
        if type(fact) is ClosedTensorShapeFactRecord:
            if fact.side not in {"sm", "pm"}:
                raise ValueError("retained tensor-shape fact has invalid side")
            return ({fact.tid}, set()) if fact.side == "sm" else (set(), {fact.tid})
        if type(fact) is ClosedTensorEqFactRecord:
            if fact.left_side not in {"sm", "pm"} or fact.right_side not in {"sm", "pm"}:
                raise ValueError("retained tensor-equality fact has invalid side")
            sm, pm = set(), set()
            (sm if fact.left_side == "sm" else pm).add(fact.left_tid)
            (sm if fact.right_side == "sm" else pm).add(fact.right_tid)
            return sm, pm
        if type(fact) is ClosedGatherFactRecord:
            return {fact.sm_tid}, {fact.pm_rank0_tid, fact.pm_rank1_tid}
        if type(fact) in {ClosedPackedCuFactRecord, ClosedLabelBoundFactRecord}:
            if fact.side not in {"sm", "pm"}:
                raise ValueError("retained side-specific authority fact has invalid side")
            return ({fact.tid}, set()) if fact.side == "sm" else (set(), {fact.tid})
        raise ValueError(f"unsupported retained fact record: {type(fact).__name__}")

    def latest_ref(side, tid, end):
        nodes = ir.sm_nodes if side == "sm" else ir.pm_nodes
        latest = f"init:{tid}"
        for index, node in enumerate(nodes[:end]):
            for slot, out in enumerate(node.outs):
                if out == tid:
                    latest = f"{side}:{index}:{slot}"
        return latest

    def source_exact(fact, sm_end, pm_end):
        source = fact.source
        if source.layout != fact.kind or source.gather_dim != fact.gather_dim or source.source_step_triples:
            raise ValueError("BW_softmax/ReduceScatter source layout/axis mismatch")
        tids = (fact.sm_tid, *fact.pm_tids)
        expected = (latest_ref("sm", tids[0], sm_end),
                    *(latest_ref("pm", tid, pm_end) for tid in tids[1:]))
        if source.step_triple != expected:
            raise ValueError("BW_softmax/ReduceScatter source is not the latest ordered TID authority")
        joined = None if fact.joined_pm_tid is None else latest_ref("pm", fact.joined_pm_tid, pm_end)
        if source.joined_pm_step != joined:
            raise ValueError("BW_softmax/ReduceScatter joined source is not the latest writer")

    if (ir.sm_num_ranks != 1 or ir.pm_num_ranks != k or rc.rank_count != k
            or reduction.kind != "reduction" or reduction.gather_dim is not None
            or scattered.kind != "sharded" or scattered.sm_tid != reduction.sm_tid
            or len(reduction.pm_tids) != k or len(scattered.pm_tids) != k
            or reduction.full_shape != rc.full_shape or scattered.full_shape != rc.full_shape
            or scattered.shard_shape != rc.shard_shape or scattered.gather_dim != rc.scatter_dim
            or not 0 <= rc.scatter_dim < len(rc.shard_shape) or min(rc.shard_shape) <= 0
            or rc.full_shape != tuple(v*k if i == rc.scatter_dim else v for i,v in enumerate(rc.shard_shape))):
        raise ValueError("ReduceScatter rank/shape/axis authority mismatch")
    if (rt.sm_node_indices or len(rt.pm_node_indices) != k
            or rc.pm_step_ids != tuple(f"pm:{i}:0" for i in rt.pm_node_indices)
            or set(rt.pm_node_indices) & set(transition.pm_node_indices)
            or set(rt.pm_node_indices) | set(transition.pm_node_indices) != set(range(pm_start,pm_end))
            or set(transition.sm_node_indices) != set(range(sm_start,sm_end))):
        raise ValueError("atomic writer ownership is not a disjoint complete partition")
    scatter_nodes = tuple(ir.pm_nodes[i] for i in rt.pm_node_indices)
    for rank,node in enumerate(scatter_nodes):
        if (node.op != "ReduceScatterPrim" or node.rank != rank or tuple(node.params or []) != (rc.scatter_dim,)
                or tuple(node.ins) != reduction.pm_tids or node.outs != [scattered.pm_tids[rank]]):
            raise ValueError("ReduceScatter writer role/order mismatch")
    if not (0 <= sm_start <= sm_end <= len(ir.sm_nodes) and 0 <= pm_start <= pm_end <= len(ir.pm_nodes)):
        raise ValueError("invalid atomic range")
    if len(records) != len(chain.relation_facts) or len(states) != len(chain.states):
        raise ValueError("duplicate materialized identity")
    if any(len(s.fact_ids) != len(set(s.fact_ids)) for s in (before, after)):
        raise ValueError("duplicate state fact")
    if ({output.fact_id,scattered.fact_id} & set(before.fact_ids)
            or chain.anchor_fact.fact_id not in before.fact_ids
            or chain.anchor_fact.fact_id not in after.fact_ids):
        raise ValueError("fresh outputs or active anchor mismatch")
    for fact in (gradient, activation, reduction):
        source_exact(fact, sm_start, pm_start)
    for fact in (output, scattered):
        source_exact(fact, sm_end, pm_end)
    all_records = (*chain.relation_facts, *chain.authority_facts, chain.anchor_fact)
    by_id = {f.fact_id: f for f in all_records}
    if len(by_id) != len(all_records):
        raise ValueError("duplicate materialized fact ID")
    sm_writes = {tid for node in sm_frame for tid in node.outs}
    pm_writes = {tid for node in pm_frame for tid in node.outs}
    for fid in before.fact_ids:
        if fid not in by_id:
            raise ValueError("missing active authority")
        st, pt = fact_tids(by_id[fid])
        if st & sm_writes or pt & pm_writes:
            raise ValueError("atomic frame overwrites prior relation or active authority")
    for nodes,tids in ((sm_frame,(output.sm_tid,)), (pm_frame,(*output.pm_tids,*scattered.pm_tids))):
        for tid in tids:
            if sum(tid in n.outs for n in nodes) != 1:
                raise ValueError("same-store output overwrite")
    sm_nodes_name,pm_nodes_name=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes"
    sm_final_name,pm_final_name=f"{segment_id}_sm_final",f"{segment_id}_pm_final"
    lines=[
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store","",
    ]
    def writer(name,graph,initial,final_name,nodes_name,frame,position,node):
        theorem_name=f"{segment_id}_{name}";final=f"({final_name} {initial})"
        expression=f"bw_softmax ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})"
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}","    rfl",
        ])
        helper=_render_mixed_final_value(
            name="hout",graph=graph,initial_store=initial,final_store=final,
            final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=position,
            output_tid=node.outs[0],input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_softmax_out_g234 {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]} {_shape_text(node.params or [])}",
            ])
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout",""]);return theorem_name
    sm_helper=writer("hSmWriter",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,
                     sm_frame,transition.sm_node_indices[0]-sm_start,sm_node)
    pm_helpers=tuple(writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pm_final_name,
                            pm_nodes_name,pm_frame,index-pm_start,node)
                     for r,(index,node) in enumerate(zip(transition.pm_node_indices,pm_nodes)))
    scatter_helpers = []
    for rank,(index,node) in enumerate(zip(rt.pm_node_indices,scatter_nodes)):
        name=f"{segment_id}_scatter_writer{rank}";scatter_helpers.append(name)
        final=f"({pm_final_name} pmStore)"
        expression=f"reduceScatterPrimDimN {rc.scatter_dim} {ir.pm_graph_ref}.numRanks {rank} [" + ", ".join("{store} " + str(tid) for tid in reduction.pm_tids) + "]"
        lines.extend([f"private theorem {name} (pmStore : Store) : {final} {node.outs[0]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore := by unfold {pm_final_name}; rfl"])
        proof=_render_mixed_final_value(name="hout",graph=ir.pm_graph_ref,initial_store="pmStore",final_store=final,
            final_equality="hfinal",nodes_name=pm_nodes_name,nodes=pm_frame,position=index-pm_start,
            output_tid=node.outs[0],input_tids=tuple(node.ins),written_tids=pm_writes,expression=expression,
            apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "simp [applyNodeDistributed, applyNodeRingAttn]",
            f"exact applyNode_reduceScatterPrim_out {ir.pm_graph_ref} t {rank} {rc.scatter_dim} {_shape_text(node.ins)} {node.outs[0]}"])
        lines.extend(x[2:] if x.startswith("  ") else x for x in proof)
        lines.extend(["  exact hout", ""])
    glist="["+", ".join(f"pmFinal {t}" for t in gradient.pm_tids)+"]"
    xlist="["+", ".join(f"pmFinal {t}" for t in activation.pm_tids)+"]"
    olist="["+", ".join(f"pmFinal {t}" for t in output.pm_tids)+"]"
    full=_shape_text(list(output.full_shape));shard=_shape_text(list(output.shard_shape));dim=output.gather_dim
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smFinal := {sm_final_name} smStore",f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "      · native_decide","      · native_decide","      · native_decide","      · native_decide",
        f"    have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {gradient.sm_tid}) {glist} {dim} {full} {shard} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {activation.sm_tid}) {xlist} {dim} {full} {shard} at hx",
        f"    have hgValue : smFinal {gradient.sm_tid} = allGatherPrimDimN {dim} {k} 0 {glist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hg.full_value",
        f"    have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN {dim} {k} 0 {xlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"    have hSmWriter : smFinal {output.sm_tid} = bw_softmax (smFinal {gradient.sm_tid}) (smFinal {activation.sm_tid}) :=",
        f"      {sm_helper} smStore",
    ])
    for rank,(helper,node) in enumerate(zip(pm_helpers,pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {output.pm_tids[rank]} = bw_softmax (pmFinal {gradient.pm_tids[rank]}) (pmFinal {activation.pm_tids[rank]}) :=",
            f"      {helper} pmStore",
            f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {shard} := by",
            f"      rw [hPmWriter{rank}]",
            f"      exact bw_softmax_shape_g199 _ _ [{b}, {h}, {q}] {d} (hx.shard_shapes _ (by simp))",
        ])
    lines.extend([
        f"    have hcomm := {theorem} {glist} {xlist} {k} {b} {h} {q} {d}",
        "      (by omega) (by omega) (by omega) (by omega) (by omega)",
        "      (by simp) (by simp) hg.shard_shapes hx.shard_shapes",
        f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {k} 0 {olist} := by",
        "      rw [hSmWriter, hgValue, hxValue, hcomm]",
        "      simp only [List.zipWith]",
        "      rw ["+", ".join(f"← hPmWriter{r}" for r in range(k))+"]",
        f"    have hOutValueList : smFinal {output.sm_tid} = allGatherPrimDimN {dim} {olist}.length 0 {olist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hOutValue",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {full} := by",
        "      rw [hSmWriter]",
        f"      exact bw_softmax_shape_g199 _ _ {_shape_text(list(output.full_shape[:3]))} {d} hx.full_shape",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {output.sm_tid}) {olist} {dim} {full} {shard}",
        "      refine {","        full_value := hOutValueList","        full_shape := hFullShape",
        "        shards_nonempty := by simp","        gather_dim_lt := hx.gather_dim_lt",
        "        shard_shapes := ?_","        shape_contract := by",
        "          simp only [List.length_cons, List.length_nil]","          native_decide","      }",
        "      intro piece hmem","      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with "+" | ".join(f"h{r}" for r in range(k)),
    ])
    for rank in range(k):
        lines.extend(["      · subst piece",f"        exact hOutShape{rank}"])
    contrib="["+", ".join(f"pmFinal {x}" for x in reduction.pm_tids)+"]"
    outs="["+", ".join(f"pmFinal {x}" for x in scattered.pm_tids)+"]"
    rd=rc.scatter_dim;rf=_shape_text(list(rc.full_shape));rs=_shape_text(list(rc.shard_shape))
    lines.extend([f"    have hred : {reduction.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ReductionRel (smFinal {reduction.sm_tid}) {contrib} {rf} at hred"])
    for rank,helper in enumerate(scatter_helpers):
        lines.extend([f"    have hw{rank} := {helper} pmStore",
            f"    change pmFinal {scattered.pm_tids[rank]} = reduceScatterPrimDimN {rd} {k} {rank} {contrib} at hw{rank}",
            f"    have hr{rank} : smFinal {reduction.sm_tid} = allReducePrim {k} {rank} {contrib} := by simpa only [List.length_cons, List.length_nil, allReducePrim] using hred.full_value",
            f"    have hc{rank} : pmFinal {scattered.pm_tids[rank]} = chunkPrimDimN {rd} {k} {rank} (smFinal {reduction.sm_tid}) := by rw [hw{rank}]; unfold reduceScatterPrimDimN; rw [← hr{rank}]"])
    chunks="["+", ".join(f"chunkPrimDimN {rd} {k} {r} (smFinal {reduction.sm_tid})" for r in range(k))+"]"
    lines.extend([f"    have hordered : {outs} = List.ofFn (fun r : Fin {k} => chunkPrimDimN {rd} {k} r.1 (smFinal {reduction.sm_tid})) := by",
        f"      change {outs} = {chunks}",f"      rw [{', '.join('hc'+str(r) for r in range(k))}]",
        f"    have hvalue : smFinal {reduction.sm_tid} = allGatherPrimDimN {rd} {outs}.length 0 {outs} := by",
        "      rw [hordered]", "      simp only [List.length_ofFn]", "      symm",
        f"      exact allGatherPrimDimN_chunks_ofFn {rd} {k} (smFinal {reduction.sm_tid}) (by omega) (by rw [hred.full_shape]; native_decide) (by rw [hred.full_shape]; native_decide)"])
    for rank in range(k):
        lines.extend([f"    have hs{rank} : (pmFinal {scattered.pm_tids[rank]}).shape = {rs} := by",
            f"      rw [hc{rank}, chunkPrimDimN_shape {rd} {k} {rank} (smFinal {reduction.sm_tid}) {rf} hred.full_shape (by omega)]", "      native_decide"])
    lines.extend([f"    have houtScatter : {scattered.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {scattered.sm_tid}) {outs} {rd} {rf} {rs}",
        "      refine { full_value := hvalue, full_shape := hred.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp }",
        "      intro x hx", "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx",
        "      rcases hx with " + " | ".join("rfl" for _ in range(k))])
    for rank in range(k): lines.append(f"      · exact hs{rank}")
    lines.extend([
        "    intro fact hfact",f"    have covered : fact ∈ [{output.fact_id}, {scattered.fact_id}] ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ [{output.fact_id}, {scattered.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered","    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with rfl | rfl",
        "      · exact hout", "      · exact houtScatter","    · exact hframe fact old","","set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}",f"  pmNodes := {pm_nodes_name}","  sound := by",
        "    intro smStore pmStore hstate",f"    exact {segment_id}_sound smStore pmStore hstate","",
    ])
    return "\n".join(lines)
