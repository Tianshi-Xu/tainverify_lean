"""Closed renderer for plain hidden-axis sharded embeddings."""
from __future__ import annotations


def render_closed_k_rank_hidden_sharded_embedding_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import (_node_text, _shape_text, _render_mixed_final_value,
                               _select_exact_typed_certificate)
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (_node_text, _shape_text, _render_mixed_final_value,
                              _select_exact_typed_certificate)
        from relation_compiler import get_closed_rule_spec

    spec = get_closed_rule_spec("embedding-hidden-sharded-k-rank")
    rule = spec.rule_id
    chain = relation.dependent_chain_plan
    found = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(found) != 1:
        raise ValueError(f"{rule} requires one complete closed segment")
    segment = found[0]
    if len(segment.transition_ids) != 1:
        raise ValueError(f"{rule} requires one transition")
    matches = [t for t in relation.transition_specs if t.transition_id == segment.transition_ids[0]]
    if len(matches) != 1:
        raise ValueError(f"{rule} transition authority is missing or duplicated")
    transition = matches[0]
    if (transition.rule_id != spec.rule_id
            or transition.lean_theorem not in spec.lean_theorems):
        raise ValueError(f"{rule} theorem identity mismatch")
    certs = [c for c in relation.certificates
             if type(c) is spec.certificate_type
             and c.rule_id == transition.rule_id
             and c.lean_theorem == transition.lean_theorem
             and (c.weight_fact,) == transition.pre_facts
             and (c.output_fact,) == transition.post_facts]
    if len(certs) != 1:
        raise ValueError(f"{rule} lacks one exact typed certificate")
    cert = certs[0]
    records = {x.source: x for x in chain.relation_facts}
    states = {x.state_id: x for x in chain.states}
    try:
        weight = records[cert.weight_fact]; output = records[cert.output_fact]
        before = states[segment.pre_state_id]; after = states[segment.post_state_id]
    except KeyError as exc:
        raise ValueError(f"{rule} fact/state framing is unresolved") from exc
    k = cert.rank_count
    hidden_dim = len(cert.ids_shape)
    expected_theorem = ("TrainVerify.Denote.fw_embedding_hidden_shards_two"
                        if hidden_dim == 1 else
                        "TrainVerify.Denote.fw_embedding_hidden_shards_k_rank")
    if (k <= 0 or cert.lean_theorem != expected_theorem
            or hidden_dim not in (1, 2) or (hidden_dim == 1 and k != 2)
            or ir.sm_num_ranks != 1 or ir.pm_num_ranks != k
            or weight.kind != "sharded" or weight.gather_dim != 1
            or output.kind != "sharded" or output.gather_dim != hidden_dim
            or len(weight.pm_tids) != k or len(output.pm_tids) != k
            or tuple(weight.full_shape) != cert.full_weight_shape
            or tuple(weight.shard_shape) != cert.shard_weight_shape
            or tuple(output.full_shape) != cert.full_output_shape
            or tuple(output.shard_shape) != cert.shard_output_shape):
        raise ValueError(f"{rule} relation/rank/theorem authority disagrees")
    required = {weight.fact_id}
    if not required <= set(before.fact_ids) or not set(after.fact_ids) <= set(before.fact_ids) | {output.fact_id}:
        raise ValueError(f"{rule} liveness mismatch")

    sm_indices = tuple(range(*segment.sm_range)); pm_indices = tuple(range(*segment.pm_range))
    if (tuple(transition.sm_node_indices) != sm_indices or tuple(transition.pm_node_indices) != pm_indices
            or len(sm_indices) != 1 or len(pm_indices) != k
            or cert.sm_step_id != f"sm:{sm_indices[0]}:0"
            or cert.pm_step_ids != tuple(f"pm:{i}:0" for i in pm_indices)):
        raise ValueError(f"{rule} does not exactly own its physical frame")
    sm_node = ir.sm_nodes[sm_indices[0]]; pm_nodes = tuple(ir.pm_nodes[i] for i in pm_indices)
    def plain(node, rank, weight_tid, output_tid):
        return (node.op == "FW_embedding" and node.rank == rank and not node.params
                and tuple(node.ins) == (cert.ids_tid, weight_tid)
                and tuple(node.outs) == (output_tid,))
    if not plain(sm_node, 0, weight.sm_tid, output.sm_tid) or any(
        not plain(n, r, weight.pm_tids[r], output.pm_tids[r]) for r, n in enumerate(pm_nodes)
    ):
        raise ValueError(f"{rule} writer signatures disagree")

    def authority(kind, predicate):
        xs = [x for x in chain.authority_facts if x.kind == kind and predicate(x)]
        if len(xs) != 1 or xs[0].fact_id not in before.fact_ids:
            raise ValueError(f"{rule} lacks exact live {kind} authority")
        return xs[0]
    ids_eq = authority("tensor_eq", lambda x:
        (x.left_side, x.left_tid, x.right_side, x.right_tid) == ("sm", cert.ids_tid, "pm", cert.ids_tid))
    ids_shape = authority("tensor_shape", lambda x:
        x.side == "pm" and x.tid == cert.ids_tid and tuple(x.shape) == cert.ids_shape)

    sm_nodes = [sm_node]; pm_frame = list(pm_nodes)
    smn=f"{segment_id}_smNodes"; pmn=f"{segment_id}_pmNodes"
    smf=f"{segment_id}_sm_final"; pmf=f"{segment_id}_pm_final"
    lines=[
        f"private def {smn} : List NodeDecl := [{_node_text(sm_node)}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_nodes)}]",
        f"private def {smf} (s : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"private def {pmf} (s : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s", "",
    ]
    def writer(name, graph, store, final, nodes_name, frame, pos, node):
        theorem=f"{segment_id}_{name}"; fs=f"({final} {store})"
        expr=f"fw_embedding ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})"
        lines.extend([f"private theorem {theorem} ({store} : Store) :",f"    {fs} {node.outs[0]} = {expr.format(store=fs)} := by",f"  have hfinal : {fs} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {store} := by",f"    unfold {final}","    rfl"])
        proof=_render_mixed_final_value(name="hout",graph=graph,initial_store=store,final_store=fs,
            final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=pos,
            output_tid=node.outs[0],input_tids=tuple(node.ins),
            written_tids={t for n in frame for t in n.outs},expression=expr,apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_fw_embedding_out {graph} t {node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]}"])
        lines.extend(x[2:] if x.startswith("  ") else x for x in proof);lines.extend(["  exact hout",""])
        return theorem
    hs=writer("hSmWriter",ir.sm_graph_ref,"smStore",smf,smn,sm_nodes,0,sm_node)
    hp=[writer(f"hPmWriter{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pm_frame,r,n) for r,n in enumerate(pm_nodes)]
    weights="["+", ".join(f"pmFinal {t}" for t in weight.pm_tids)+"]"
    outputs="["+", ".join(f"pmFinal {t}" for t in output.pm_tids)+"]"
    full=_shape_text(list(output.full_shape)); shard=_shape_text(list(output.shard_shape)); ids=_shape_text(list(cert.ids_shape)); wf=_shape_text(list(weight.full_shape)); ws=_shape_text(list(weight.shard_shape))
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"  let smFinal := {smf} smStore",f"  let pmFinal := {pmf} pmStore",f"  have hframe : {before.state_id}.Holds smFinal pmFinal := by",f"    apply RelationState.Holds.fold_frame (smGraph := {ir.sm_graph_ref}) (pmGraph := {ir.pm_graph_ref}) {smn} {pmn} smStore pmStore hstate <;> native_decide",f"  have hidEq0 := hstate {ids_eq.fact_id} (by native_decide)",f"  change smStore {cert.ids_tid} = pmStore {cert.ids_tid} at hidEq0",f"  have hidShape0 := hstate {ids_shape.fact_id} (by native_decide)",f"  change (pmStore {cert.ids_tid}).shape = {ids} at hidShape0",f"  have hidSm : smFinal {cert.ids_tid} = smStore {cert.ids_tid} := by unfold smFinal {smf}; exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref} {smn} smStore {cert.ids_tid} (by native_decide) (by native_decide)",f"  have hidPm : pmFinal {cert.ids_tid} = pmStore {cert.ids_tid} := by unfold pmFinal {pmf}; exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} {pmn} pmStore {cert.ids_tid} (by native_decide) (by native_decide)",f"  have hidEq : smFinal {cert.ids_tid} = pmFinal {cert.ids_tid} := by rw [hidSm, hidPm]; exact hidEq0",f"  have hidShape : (pmFinal {cert.ids_tid}).shape = {ids} := by rw [hidPm]; exact hidShape0",f"  have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",f"  change ShardedRel (smFinal {weight.sm_tid}) {weights} 1 {wf} {ws} at hw",f"  have hsm := {hs} smStore",f"  change smFinal {output.sm_tid} = fw_embedding (smFinal {cert.ids_tid}) (smFinal {weight.sm_tid}) at hsm"])
    for r,h in enumerate(hp):lines.extend([f"  have hp{r} := {h} pmStore",f"  change pmFinal {output.pm_tids[r]} = fw_embedding (pmFinal {cert.ids_tid}) (pmFinal {weight.pm_tids[r]}) at hp{r}",f"  have hshape{r} : (pmFinal {output.pm_tids[r]}).shape = {shard} := by rw [hp{r}, fw_embedding_shape, hidShape, hw.shard_shapes (pmFinal {weight.pm_tids[r]}) (by simp)]; rfl"])
    if hidden_dim==1:
        tokens=cert.ids_shape[0]; vocab,hidden=cert.shard_weight_shape
        lines.extend([f"  have hwValue : smFinal {weight.sm_tid} = allGatherPrimDimN 1 2 0 {weights} := by simpa only [List.length_cons, List.length_nil] using hw.full_value",f"  have hcomm := {cert.lean_theorem} {tokens} {vocab} {hidden} (pmFinal {cert.ids_tid}) (pmFinal {weight.pm_tids[0]}) (pmFinal {weight.pm_tids[1]}) (by omega) (by omega) (by omega) hidShape (hw.shard_shapes (pmFinal {weight.pm_tids[0]}) (by simp)) (hw.shard_shapes (pmFinal {weight.pm_tids[1]}) (by simp))",f"  have hvalue : smFinal {output.sm_tid} = allGatherPrimDimN 1 2 0 {outputs} := by rw [hsm, hidEq, hwValue, hcomm, ←hp0, ←hp1]"])
    else:
        b,tokens=cert.ids_shape;vocab,hidden=cert.shard_weight_shape
        lines.extend([f"  have hcomm := {cert.lean_theorem} (K := {k}) (b := {b}) (tokens := {tokens}) (vocab := {vocab}) (hidden := {hidden}) (ids := pmFinal {cert.ids_tid}) (Ws := {weights}) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp) hidShape (by intro W hW; exact hw.shard_shapes W hW)",f"  have hvalue : smFinal {output.sm_tid} = allGatherPrimDimN 2 {k} 0 {outputs} := by rw [hsm, hidEq, hw.full_value, hcomm]; rw [{', '.join('←hp'+str(r) for r in range(k))}]"])
    lines.extend([f"  have hvalueL : smFinal {output.sm_tid} = allGatherPrimDimN {hidden_dim} {outputs}.length 0 {outputs} := by simpa only [List.length_cons, List.length_nil] using hvalue",f"  have hfull : (smFinal {output.sm_tid}).shape = {full} := by rw [hsm, fw_embedding_shape, hidEq, hidShape, hw.full_shape]; rfl",f"  have hout : {output.fact_id}.Holds smFinal pmFinal := by",f"    change ShardedRel (smFinal {output.sm_tid}) {outputs} {hidden_dim} {full} {shard}","    refine { full_value := hvalueL, full_shape := hfull, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp }","    intro x hx","    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx","    rcases hx with "+" | ".join("rfl" for _ in range(k))])
    for r in range(k):lines.append(f"    · exact hshape{r}")
    pub=[output.fact_id];lines.extend(["  intro fact hfact",f"  have hc : fact ∈ [{output.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact","  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc","  rcases hc with rfl | old","  · exact hout","  · exact hframe fact old","",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by",f"    intro smStore pmStore hstate",f"    change {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore)",f"    exact {segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)
