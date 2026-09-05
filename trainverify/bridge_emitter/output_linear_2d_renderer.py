"""Closed rank-2 output-sharded linear renderer."""
from __future__ import annotations


def render_closed_output_sharded_linear_2d_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate
        from .relation_compiler import KRankOutputShardedLinearCertificate
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate
        from relation_compiler import KRankOutputShardedLinearCertificate
    rule = "linear-output-sharded-two-rank-2d"
    theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_linear_output_dim1_two_2d"
    chain = relation.dependent_chain_plan
    seg = next((s for s in chain.segments if s.segment_id == segment_id), None)
    if seg is None or len(seg.transition_ids) != 1:
        raise ValueError("2D output-linear requires one transition")
    t = {x.transition_id: x for x in relation.transition_specs}[seg.transition_ids[0]]
    cert = _select_exact_typed_certificate(
        relation, t, rule, theorem, KRankOutputShardedLinearCertificate,
        lambda c: (tuple(sorted((c.activation_fact, c.weight_fact))), (c.output_fact,)),
    )
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    activation, weight, output = records[cert.activation_fact], records[cert.weight_fact], records[cert.output_fact]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if (cert.rank_count != 2 or cert.output_gather_dim != 1
            or activation.kind != "joined" or activation.joined_pm_tid is None
            or weight.kind not in {"sharded", "chunked"} or weight.gather_dim != 0 or len(weight.pm_tids) != 2
            or output.kind != "sharded" or output.gather_dim != 1 or len(output.pm_tids) != 2):
        raise ValueError(
            "2D output-linear relation metadata disagrees: "
            f"rank_count={cert.rank_count} output_gather_dim={cert.output_gather_dim} "
            f"activation={(activation.kind, activation.joined_pm_tid)} "
            f"weight={(weight.kind, weight.gather_dim, weight.pm_tids)} "
            f"output={(output.kind, output.gather_dim, output.pm_tids)}"
        )
    if (tuple(range(*seg.sm_range)) != t.sm_node_indices
            or tuple(range(*seg.pm_range)) != t.pm_node_indices
            or len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != 2):
        raise ValueError("2D output-linear footprint is not exact 1x2")
    sm = ir.sm_nodes[t.sm_node_indices[0]]
    p0, p1 = (ir.pm_nodes[i] for i in t.pm_node_indices)
    if ((sm.rank, p0.rank, p1.rank) != (0, 0, 1)
            or any(n.op != "FW_mix_precision_linear" or len(n.ins) != 2 or len(n.outs) != 1
                   or n.params not in (None, []) for n in (sm, p0, p1))
            or sm.ins != [activation.sm_tid, weight.sm_tid]
            or p0.ins != [activation.joined_pm_tid, weight.pm_tids[0]]
            or p1.ins != [activation.joined_pm_tid, weight.pm_tids[1]]
            or (sm.outs[0], p0.outs[0], p1.outs[0]) != (output.sm_tid, *output.pm_tids)):
        raise ValueError(
            "2D output-linear writer topology disagrees: "
            f"sm={sm} p0={p0} p1={p1} activation={(activation.sm_tid, activation.joined_pm_tid)} "
            f"weight={(weight.sm_tid, weight.pm_tids)} output={(output.sm_tid, output.pm_tids)}"
        )
    if (len(activation.full_shape) != 2 or activation.full_shape != activation.shard_shape
            or len(weight.shard_shape) != 2 or len(output.shard_shape) != 2):
        raise ValueError("2D output-linear shape ranks disagree")
    rows, input_dim = activation.full_shape
    local_output = weight.shard_shape[0]
    if (weight.shard_shape != (local_output, input_dim)
            or weight.full_shape != (local_output * 2, input_dim)
            or output.shard_shape != (rows, local_output)
            or output.full_shape != (rows, local_output * 2)
            or min(rows, input_dim, local_output) <= 0):
        raise ValueError("2D output-linear shape contract disagrees")
    if (not {activation.fact_id, weight.fact_id} <= set(before.fact_ids)
            or output.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= set(before.fact_ids) | {output.fact_id}):
        raise ValueError("2D output-linear liveness disagrees")
    smt, p0t, p1t = _node_text(sm), _node_text(p0), _node_text(p1)
    ashape = _shape_text(list(activation.full_shape)); wf = _shape_text(list(weight.full_shape))
    ws = _shape_text(list(weight.shard_shape)); of = _shape_text(list(output.full_shape)); os = _shape_text(list(output.shard_shape))
    sid = segment_id
    weight_relation = "ChunkedRel" if weight.kind == "chunked" else "ShardedRel"
    weight_argument = "hw.toShardedRel" if weight.kind == "chunked" else "hw"
    return f'''private def {sid} :
    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := [{smt}]
  pmNodes := [{p0t}, {p1t}]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{smt}]
    let pmNodes : List NodeDecl := [{p0t}, {p1t}]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore
    have hframe : {before.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide
    have hsm : smFinal {sm.outs[0]} = fw_linear (smStore {sm.ins[0]}) (smStore {sm.ins[1]}) := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_mix_precision_linear_out_1p {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {sm.ins[1]} {sm.outs[0]}
    have hp0 : pmFinal {p0.outs[0]} = fw_linear (pmStore {p0.ins[0]}) (pmStore {p0.ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_mix_precision_linear_out_1p {ir.pm_graph_ref} pmStore 0 {p0.ins[0]} {p0.ins[1]} {p0.outs[0]}
      · decide
    have hp1 : pmFinal {p1.outs[0]} = fw_linear (pmStore {p1.ins[0]}) (pmStore {p1.ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_fw_mix_precision_linear_out_1p]
      rw [applyNode_eq_of_not_mem_outs, applyNode_eq_of_not_mem_outs] <;> decide
    have ha : {activation.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hw : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hout : {output.fact_id}.Holds smFinal pmFinal := by
      change smStore {activation.sm_tid} = pmStore {activation.joined_pm_tid} ∧ (smStore {activation.sm_tid}).shape = {ashape} ∧ (pmStore {activation.joined_pm_tid}).shape = {ashape} at ha
      change {weight_relation} (smStore {weight.sm_tid}) [pmStore {weight.pm_tids[0]}, pmStore {weight.pm_tids[1]}] 0 {wf} {ws} at hw
      have core := ShardedRel.fw_linear_output_dim1_two_2d (rows := {rows}) (input := {input_dim}) (output := {local_output}) ha {weight_argument} (by native_decide) (by native_decide) (by native_decide)
      change ShardedRel (smFinal {output.sm_tid}) [pmFinal {output.pm_tids[0]}, pmFinal {output.pm_tids[1]}] 1 {of} {os}
      rw [hsm, hp0, hp1]
      exact core
    intro fact hfact
    have covered : fact ∈ [{output.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{output.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
'''
