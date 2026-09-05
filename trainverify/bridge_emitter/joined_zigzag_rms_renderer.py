"""Draft generic closed renderer for replicated RMSNorm on joined-zigzag values."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict

RULE = "rms-norm-joined_zigzag-two-rank"
THEOREM = "TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.rms_norm"

def _digest(c):
    return hashlib.sha256(json.dumps(
        {"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":"),
    ).encode()).hexdigest()

def render_closed_joined_zigzag_rms_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import FrontierRMSNormCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import FrontierRMSNormCertificate
    chain = relation.dependent_chain_plan
    segs = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segs) != 1:
        raise ValueError("joined-zigzag RMS requires one complete segment")
    seg = segs[0]
    if len(seg.transition_ids) != 1:
        raise ValueError("joined-zigzag RMS requires one transition")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    t = by_id[seg.transition_ids[0]]
    if (t.rule_id != RULE or t.lean_theorem != THEOREM
            or len(t.pre_facts) != 2 or len(t.post_facts) != 1):
        raise ValueError("joined-zigzag RMS theorem identity disagrees")
    def refs(f): return (*f.step_triple, f.joined_pm_step)
    candidates = [c for c in relation.certificates
        if type(c) is FrontierRMSNormCertificate
        and c.rule_id == RULE and c.lean_theorem == THEOREM
        and c.relation_kind == "joined_zigzag" and _digest(c) == t.certificate_digest
        and c.output_step_triple == refs(t.post_facts[0])
        and c.weight_fact in t.pre_facts
        and any(refs(f) == c.input_step_triple for f in t.pre_facts)]
    if len(candidates) != 1:
        raise ValueError("joined-zigzag RMS lacks one exact typed certificate")
    c = candidates[0]
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    input_specs = [f for f in t.pre_facts if refs(f) == c.input_step_triple]
    weight_specs = [f for f in t.pre_facts if f == c.weight_fact]
    if len(input_specs) != 1 or len(weight_specs) != 1:
        raise ValueError("joined-zigzag RMS typed roles are ambiguous")
    inp, weight = records[input_specs[0]], records[weight_specs[0]]
    post = records[t.post_facts[0]]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if (inp.kind != "joined_zigzag" or post.kind != "joined_zigzag" or weight.kind != "joined"
            or inp.joined_pm_tid is None or post.joined_pm_tid is None or weight.joined_pm_tid is None
            or inp.metadata_tid is None or post.metadata_tid != inp.metadata_tid
            or inp.full_shape != post.full_shape or inp.shard_shape != post.shard_shape
            or inp.row_shard_shape != inp.shard_shape or post.row_shard_shape != post.shard_shape
            or len(inp.full_shape) != 2 or inp.full_shape[0] != 2 * inp.shard_shape[0]
            or inp.full_shape[1] != inp.shard_shape[1]
            or weight.full_shape != (inp.full_shape[-1],) or weight.shard_shape != weight.full_shape):
        raise ValueError("joined-zigzag RMS relation/shape payload disagrees")
    sm_indices, pm_indices = tuple(range(*seg.sm_range)), tuple(range(*seg.pm_range))
    if (tuple(t.sm_node_indices) != sm_indices or len(sm_indices) != 1
            or len(pm_indices) != ir.pm_num_ranks or len(t.pm_node_indices) != 1
            or t.pm_node_indices[0] != pm_indices[-1]):
        raise ValueError("joined-zigzag RMS frame/writer ownership disagrees")
    sm = ir.sm_nodes[sm_indices[0]]; pm_frame = tuple(ir.pm_nodes[i] for i in pm_indices); pm = pm_frame[-1]
    if (ir.pm_num_ranks != 2 or sm.rank != 0
            or tuple(n.rank for n in pm_frame) != (0, 1)
            or sm.op != "FW_rms_norm" or len(sm.ins) != 2 or len(sm.outs) != 1
            or sm.params not in (None, [])
            or any(n.op != "FW_rms_norm" or len(n.ins) != 2 or len(n.outs) != 1
                   or n.params not in (None, []) or tuple(n.ins) != tuple(pm.ins)
                   or tuple(n.outs) != tuple(pm.outs) for n in pm_frame)
            or (sm.ins[0], pm.ins[0]) != (inp.sm_tid, inp.joined_pm_tid)
            or (sm.ins[1], pm.ins[1]) != (weight.sm_tid, weight.joined_pm_tid)
            or (sm.outs[0], pm.outs[0]) != (post.sm_tid, post.joined_pm_tid)):
        raise ValueError("joined-zigzag RMS writer topology disagrees")
    fresh = {post.fact_id}
    if (not {inp.fact_id, weight.fact_id} <= set(before.fact_ids)
            or post.fact_id not in after.fact_ids
            or not set(after.fact_ids) <= set(before.fact_ids) | fresh):
        raise ValueError("joined-zigzag RMS liveness disagrees")
    smt = _node_text(sm); pmts = ", ".join(_node_text(n) for n in pm_frame)
    fs = _shape_text(list(inp.full_shape)); ss = _shape_text(list(inp.shard_shape)); ws = _shape_text(list(weight.full_shape))
    rows, hidden = inp.shard_shape
    return f'''private def {segment_id} :
    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
  smNodes := [{smt}]
  pmNodes := [{pmts}]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{smt}]
    let pmNodes : List NodeDecl := [{pmts}]
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
    have hmeta : pmFinal {inp.metadata_tid} = pmStore {inp.metadata_tid} := by
      exact foldl_applyNodeDistributedFaithful_at_not_written {ir.pm_graph_ref} pmNodes pmStore _ (by native_decide) (by native_decide)
    have hin : {inp.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hw : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hout : {post.fact_id}.Holds smFinal pmFinal := by
      change JoinedZigzagRel (smStore {inp.sm_tid}) (pmStore {inp.joined_pm_tid}) (pmStore {inp.metadata_tid}) {fs} {ss} at hin
      change smStore {weight.sm_tid} = pmStore {weight.joined_pm_tid} ∧ (smStore {weight.sm_tid}).shape = {ws} ∧ (pmStore {weight.joined_pm_tid}).shape = {ws} at hw
      have core := JoinedZigzagRel.rms_norm {rows} {hidden} hin hw.1 (by omega) (by omega)
      change JoinedZigzagRel (smFinal {post.sm_tid}) (pmFinal {post.joined_pm_tid}) (pmFinal {post.metadata_tid}) {fs} {ss}
      rw [hsm, hpm, hmeta]
      exact core
    intro fact hfact
    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
'''
