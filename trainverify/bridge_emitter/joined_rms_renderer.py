"""Closed renderer for replicated RMSNorm over one joined PM tensor."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict


def _digest(c):
    return hashlib.sha256(json.dumps({"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def render_closed_joined_rms_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import FrontierRMSNormCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import FrontierRMSNormCertificate
    chain = relation.dependent_chain_plan
    segs = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segs) != 1:
        raise ValueError("joined RMS requires one complete segment")
    seg = segs[0]
    if len(seg.transition_ids) != 1:
        raise ValueError("joined RMS requires one transition")
    transitions = {t.transition_id: t for t in relation.transition_specs}
    t = transitions[seg.transition_ids[0]]
    if (t.rule_id != "rms-norm-joined-two-rank"
            or t.lean_theorem != "TrainVerify.Denote.RelationCompiler.JoinedRel.rms_norm"
            or len(t.pre_facts) != 2 or len(t.post_facts) != 1):
        raise ValueError("joined RMS theorem identity disagrees")
    def joined_refs(fact):
        return (*fact.step_triple, fact.joined_pm_step)
    candidates = [c for c in relation.certificates if type(c) is FrontierRMSNormCertificate
                  and c.rule_id == t.rule_id and c.lean_theorem == t.lean_theorem
                  and c.relation_kind == "joined" and _digest(c) == t.certificate_digest
                  and c.output_step_triple == joined_refs(t.post_facts[0])
                  and c.weight_fact in t.pre_facts
                  and any(joined_refs(f) == c.input_step_triple for f in t.pre_facts)]
    if len(candidates) != 1:
        raise ValueError("joined RMS lacks one exact certificate")
    c = candidates[0]
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    input_specs = [f for f in t.pre_facts if joined_refs(f) == c.input_step_triple]
    weight_specs = [f for f in t.pre_facts if f == c.weight_fact]
    if len(input_specs) != 1 or len(weight_specs) != 1:
        raise ValueError("joined RMS typed roles are ambiguous")
    inp, weight = records[input_specs[0]], records[weight_specs[0]]
    post = records[t.post_facts[0]]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if (inp.kind != "joined" or post.kind != "joined" or weight.kind != "joined"
            or inp.joined_pm_tid is None or post.joined_pm_tid is None or weight.joined_pm_tid is None
            or inp.full_shape != inp.shard_shape or post.full_shape != post.shard_shape
            or inp.full_shape != post.full_shape or len(inp.full_shape) != 2
            or weight.full_shape != (inp.full_shape[-1],)
            or weight.shard_shape != weight.full_shape):
        raise ValueError("joined RMS relation/shape payload disagrees")
    sm_indices, pm_indices = tuple(range(*seg.sm_range)), tuple(range(*seg.pm_range))
    if (len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != 1
            or not set(t.sm_node_indices) <= set(sm_indices)
            or not set(t.pm_node_indices) <= set(pm_indices)
            or len(sm_indices) != 1 or not pm_indices):
        raise ValueError("joined RMS writer is outside its complete frame")
    sm_frame = tuple(ir.sm_nodes[i] for i in sm_indices)
    pm_frame = tuple(ir.pm_nodes[i] for i in pm_indices)
    sm, pm = ir.sm_nodes[t.sm_node_indices[0]], ir.pm_nodes[t.pm_node_indices[0]]
    if t.pm_node_indices[0] != pm_indices[-1]:
        raise ValueError("joined RMS PM semantic writer is not the final same-TID writer")
    if ((sm.rank, pm.rank) != (0, ir.pm_num_ranks - 1)
            or sm.op != "FW_rms_norm" or len(sm.ins) != 2 or len(sm.outs) != 1
            or sm.params not in (None, []) or len(pm.ins) != 2 or len(pm.outs) != 1
            or tuple(n.rank for n in pm_frame) != tuple(range(ir.pm_num_ranks))
            or any(n.op != "FW_rms_norm" or tuple(n.ins) != tuple(pm.ins)
                   or tuple(n.outs) != tuple(pm.outs) or n.params not in (None, [])
                   for n in pm_frame)
            or (sm.ins[0], pm.ins[0]) != (inp.sm_tid, inp.joined_pm_tid)
            or sm.ins[1] != weight.sm_tid or pm.ins[1] != weight.joined_pm_tid
            or (sm.outs[0], pm.outs[0]) != (post.sm_tid, post.joined_pm_tid)):
        raise ValueError("joined RMS writer topology disagrees")
    fresh = {post.fact_id}
    if not {inp.fact_id, weight.fact_id} <= set(before.fact_ids) or not fresh <= set(after.fact_ids) or not set(after.fact_ids) <= set(before.fact_ids) | fresh:
        raise ValueError("joined RMS liveness disagrees")
    smt, pmts = _node_text(sm), tuple(_node_text(node) for node in pm_frame)
    shape, wshape = _shape_text(list(inp.full_shape)), _shape_text(list(weight.full_shape))
    rows, hidden = inp.full_shape
    sid = segment_id
    return f'''private def {sid} :
    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := [{smt}]
  pmNodes := [{', '.join(pmts)}]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{smt}]
    let pmNodes : List NodeDecl := [{', '.join(pmts)}]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore
    have hframe : {before.state_id}.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate <;> native_decide
    have hsm : smFinal {sm.outs[0]} = fw_rms_norm (smStore {sm.ins[0]}) (smStore {sm.ins[1]}) := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_rms_norm_out_1p {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {sm.ins[1]} {sm.outs[0]}
    have hpm : pmFinal {pm.outs[0]} = fw_rms_norm (pmStore {pm.ins[0]}) (pmStore {pm.ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_rms_norm_out_1p {ir.pm_graph_ref} pmStore {pm.rank} {pm.ins[0]} {pm.ins[1]} {pm.outs[0]}
    have hin : {inp.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hw : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hout : {post.fact_id}.Holds smFinal pmFinal := by
      change smStore {inp.sm_tid} = pmStore {inp.joined_pm_tid} ∧ (smStore {inp.sm_tid}).shape = {shape} ∧ (pmStore {inp.joined_pm_tid}).shape = {shape} at hin
      change smStore {weight.sm_tid} = pmStore {weight.joined_pm_tid} ∧ (smStore {weight.sm_tid}).shape = {wshape} ∧ (pmStore {weight.joined_pm_tid}).shape = {wshape} at hw
      have core := JoinedRel.rms_norm {rows} {hidden} hin hw.1
      change smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} ∧ (smFinal {post.sm_tid}).shape = {shape} ∧ (pmFinal {post.joined_pm_tid}).shape = {shape}
      rw [hsm, hpm]
      exact core
    intro fact hfact
    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
'''
