"""Atomic shared-writer renderer for ordinary and sharded CP2 addition."""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict


def _digest(c):
    return hashlib.sha256(json.dumps({"type": type(c).__name__, "fields": asdict(c)},
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def render_closed_mixed_add_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text
        from .relation_compiler import FrontierAddCertificate, KRankBinaryRelationCertificate
    except ImportError:
        from composer import _node_text, _shape_text
        from relation_compiler import FrontierAddCertificate, KRankBinaryRelationCertificate
    chain = relation.dependent_chain_plan
    segs = [] if chain is None else [s for s in chain.segments if s.segment_id == segment_id]
    if chain is None or not chain.complete or len(segs) != 1:
        raise ValueError("mixed add requires one complete segment")
    seg = segs[0]
    if len(seg.transition_ids) != 2:
        raise ValueError("mixed add requires two typed views")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    ot, st = (by_id[x] for x in seg.transition_ids)
    if (ot.rule_id, st.rule_id) != ("elementwise-add-ordinary-two-rank", "add-sharded-k-rank"):
        raise ValueError("mixed add transition order disagrees")
    ocs = [c for c in relation.certificates if type(c) is FrontierAddCertificate
           and c.rule_id == ot.rule_id and c.lean_theorem == ot.lean_theorem
           and _digest(c) == ot.certificate_digest
           and set(c.input_step_triples) == {f.step_triple for f in ot.pre_facts}
           and c.output_step_triple == ot.post_facts[0].step_triple]
    scs = [c for c in relation.certificates if type(c) is KRankBinaryRelationCertificate
           and c.rule_id == st.rule_id and c.lean_theorem == st.lean_theorem
           and _digest(c) == st.certificate_digest
           and set(c.input_facts) == set(st.pre_facts) and c.output_fact == st.post_facts[0]]
    if len(ocs) != 1 or len(scs) != 1:
        raise ValueError("mixed add lacks exact typed certificates")
    records = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    opre, spre = tuple(records[f] for f in ot.pre_facts), tuple(records[f] for f in st.pre_facts)
    opost, spost = records[ot.post_facts[0]], records[st.post_facts[0]]
    before, after = states[seg.pre_state_id], states[seg.post_state_id]
    if (ot.lean_theorem != "TrainVerify.Denote.GeneratedPatterns.elemwiseAdd_allGather0_commute_cp2"
            or st.lean_theorem != "TrainVerify.Denote.fw_add_allGather_dim_K"
            or len(opre) != 2 or len(spre) != 2
            or any(f.kind != "ordinary" for f in (*opre, opost))
            or any(f.kind != "sharded" for f in (*spre, spost))
            or scs[0].rank_count != 2 or scs[0].gather_dim != 0):
        raise ValueError("mixed add theorem/relation kinds disagree")
    if (ot.sm_node_indices != st.sm_node_indices or ot.pm_node_indices != st.pm_node_indices
            or tuple(range(*seg.sm_range)) != ot.sm_node_indices
            or tuple(range(*seg.pm_range)) != ot.pm_node_indices
            or len(ot.sm_node_indices) != 1 or len(ot.pm_node_indices) != 2):
        raise ValueError("mixed add does not share exact 1x2 writers")
    sm = ir.sm_nodes[ot.sm_node_indices[0]]
    p0, p1 = (ir.pm_nodes[i] for i in ot.pm_node_indices)
    if ((sm.rank, p0.rank, p1.rank) != (0, 0, 1)
            or any(n.op != "FW_add" or len(n.ins) != 2 or len(n.outs) != 1
                   or n.params not in (None, []) for n in (sm, p0, p1))):
        raise ValueError("mixed add writer signature disagrees")
    def roles(facts):
        by_tid = {f.sm_tid: f for f in facts}
        if len(by_tid) != 2 or any(tid not in by_tid for tid in sm.ins):
            raise ValueError("mixed add operand roles are ambiguous")
        return tuple(by_tid[tid] for tid in sm.ins)
    oa, ob = roles(opre); sa, sb = roles(spre)
    if (tuple(p0.ins) != (oa.pm_tids[0], ob.pm_tids[0])
            or tuple(p1.ins) != (oa.pm_tids[1], ob.pm_tids[1])
            or (sa.sm_tid, sb.sm_tid) != (oa.sm_tid, ob.sm_tid)
            or sa.pm_tids != oa.pm_tids or sb.pm_tids != ob.pm_tids
            or (sm.outs[0], p0.outs[0], p1.outs[0]) != (opost.sm_tid, *opost.pm_tids)
            or (spost.sm_tid, spost.pm_tids) != (opost.sm_tid, opost.pm_tids)):
        raise ValueError("mixed add TID roles disagree")
    shapes = {(f.full_shape, f.shard_shape) for f in (*opre, *spre, opost, spost)}
    if len(shapes) != 1:
        raise ValueError("mixed add shapes disagree")
    full_shape, shard_shape = next(iter(shapes))
    if (len(shard_shape) != 2 or full_shape != (shard_shape[0] * 2, shard_shape[1])
            or min(shard_shape) <= 0 or any(f.gather_dim != 0 for f in (*spre, spost))):
        raise ValueError("mixed add CP2 shape contract disagrees")
    fresh = {opost.fact_id, spost.fact_id}
    required = {f.fact_id for f in (*opre, *spre)}
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids) or not set(after.fact_ids) <= set(before.fact_ids) | fresh:
        raise ValueError("mixed add liveness disagrees")
    smt, p0t, p1t = _node_text(sm), _node_text(p0), _node_text(p1)
    full, shard = _shape_text(list(full_shape)), _shape_text(list(shard_shape))
    rows, hidden = shard_shape
    sid = segment_id
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
    have hsm : smFinal {sm.outs[0]} = elemwiseAdd (smStore {sm.ins[0]}) (smStore {sm.ins[1]}) := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_add2_out {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {sm.ins[1]} {sm.outs[0]}
    have hp0 : pmFinal {p0.outs[0]} = elemwiseAdd (pmStore {p0.ins[0]}) (pmStore {p0.ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_add2_out {ir.pm_graph_ref} pmStore 0 {p0.ins[0]} {p0.ins[1]} {p0.outs[0]}
      · decide
    have hp1 : pmFinal {p1.outs[0]} = elemwiseAdd (pmStore {p1.ins[0]}) (pmStore {p1.ins[1]}) := by
      simp [pmFinal, pmNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      rw [applyNode_fw_add2_out]
      rw [applyNode_eq_of_not_mem_outs, applyNode_eq_of_not_mem_outs] <;> decide
    have ha : {oa.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hb : {ob.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hOrdOut : {opost.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Ordinary2Rel (smStore {oa.sm_tid}) (pmStore {oa.pm_tids[0]}) (pmStore {oa.pm_tids[1]}) {full} {shard} at ha
      change GeneratedPatterns.Ordinary2Rel (smStore {ob.sm_tid}) (pmStore {ob.pm_tids[0]}) (pmStore {ob.pm_tids[1]}) {full} {shard} at hb
      have core := Ordinary2Rel.add {rows} {hidden} ha hb (by native_decide) (by native_decide)
      change GeneratedPatterns.Ordinary2Rel (smFinal {opost.sm_tid}) (pmFinal {opost.pm_tids[0]}) (pmFinal {opost.pm_tids[1]}) {full} {shard}
      rw [hsm, hp0, hp1]
      exact core
    have hShOut : {spost.fact_id}.Holds smFinal pmFinal := by
      change ShardedRel (smFinal {spost.sm_tid}) [pmFinal {spost.pm_tids[0]}, pmFinal {spost.pm_tids[1]}] 0 {full} {shard}
      exact ShardedRel.ofOrdinary2_dim0_rank2 (rows := {rows}) (width := {hidden}) hOrdOut
    intro fact hfact
    have covered : fact ∈ [{opost.fact_id}, {spost.fact_id}] ++ {before.state_id}.facts :=
      (show {after.state_id}.facts ⊆ [{opost.fact_id}, {spost.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with (rfl | rfl) | old
    · exact hOrdOut
    · exact hShOut
    · exact hframe fact old
'''
