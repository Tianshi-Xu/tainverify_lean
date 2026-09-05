"""Atomic shared-writer renderer for ordinary and sharded CP2 RMSNorm."""
from __future__ import annotations
import hashlib,json
from dataclasses import asdict

def _digest(c):
    return hashlib.sha256(json.dumps({"type":type(c).__name__,"fields":asdict(c)},sort_keys=True,separators=(",",":")).encode()).hexdigest()

def render_closed_mixed_rms_segment(ir,relation,segment_id):
    try:
        from .composer import _node_text,_shape_text
        from .relation_compiler import FrontierRMSNormCertificate,KRankLocalRelationCertificate
    except ImportError:
        from composer import _node_text,_shape_text
        from relation_compiler import FrontierRMSNormCertificate,KRankLocalRelationCertificate
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=2:raise ValueError("mixed RMS requires two transitions")
    by={t.transition_id:t for t in relation.transition_specs};transitions=tuple(by[x] for x in seg.transition_ids)
    ordinary=[t for t in transitions if t.rule_id=="rms-norm-ordinary-two-rank"]
    sharded=[t for t in transitions if t.rule_id=="rms-norm-sharded-two-rank-dim0"]
    if len(ordinary)!=1 or len(sharded)!=1:raise ValueError("mixed RMS transition roles disagree")
    ot,st=ordinary[0],sharded[0]
    weights=[f for f in ot.pre_facts if f.layout=="joined"];acts=[f for f in ot.pre_facts if f.layout=="ordinary"]
    if len(weights)!=1 or len(acts)!=1:raise ValueError("mixed RMS roles ambiguous")
    ws,os=weights[0],acts[0]
    ocs=[c for c in relation.certificates if type(c) is FrontierRMSNormCertificate and c.rule_id==ot.rule_id and c.lean_theorem==ot.lean_theorem and c.weight_fact==ws and c.input_step_triple==os.step_triple and c.output_step_triple==ot.post_facts[0].step_triple and _digest(c)==ot.certificate_digest]
    scs=[c for c in relation.certificates if type(c) is KRankLocalRelationCertificate and c.rule_id==st.rule_id and c.lean_theorem==st.lean_theorem and c.input_fact==st.pre_facts[0] and c.output_fact==st.post_facts[0] and _digest(c)==st.certificate_digest]
    if len(ocs)!=1 or len(scs)!=1:raise ValueError("mixed RMS exact certificate missing")
    records={f.source:f for f in chain.relation_facts};states={s.state_id:s for s in chain.states}
    weight,opre,opost,spre,spost=records[ws],records[os],records[ot.post_facts[0]],records[st.pre_facts[0]],records[st.post_facts[0]]
    before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if (ot.lean_theorem not in {"TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core","TrainVerify.Denote.RelationCompiler.Ordinary2Rel.rms_norm"}
            or st.lean_theorem!="TrainVerify.Denote.RelationCompiler.ShardedRel.fw_rms_norm_2d"
            or weight.kind!="joined" or opre.kind!="ordinary" or opost.kind!="ordinary" or spre.kind!="sharded" or spost.kind!="sharded"
            or scs[0].rank_count!=2 or scs[0].gather_dim!=0
            or (opre.sm_tid,opre.pm_tids)!=(spre.sm_tid,spre.pm_tids) or (opost.sm_tid,opost.pm_tids)!=(spost.sm_tid,spost.pm_tids)):
        raise ValueError("mixed RMS relation metadata disagrees")
    if (ot.sm_node_indices!=st.sm_node_indices or ot.pm_node_indices!=st.pm_node_indices or tuple(range(*seg.sm_range))!=ot.sm_node_indices or tuple(range(*seg.pm_range))!=ot.pm_node_indices or len(ot.sm_node_indices)!=1 or len(ot.pm_node_indices)!=2):raise ValueError("mixed RMS frame disagrees")
    sm=ir.sm_nodes[ot.sm_node_indices[0]];p0,p1=(ir.pm_nodes[i] for i in ot.pm_node_indices);wsm=weight.sm_tid;wpm=weight.joined_pm_tid
    if (wpm is None or (sm.rank,p0.rank,p1.rank)!=(0,0,1) or any(n.op!="FW_rms_norm" or len(n.ins)!=2 or len(n.outs)!=1 or n.params not in (None,[]) for n in (sm,p0,p1))
            or (sm.ins[0],p0.ins[0],p1.ins[0])!=(opre.sm_tid,*opre.pm_tids) or (sm.ins[1],p0.ins[1],p1.ins[1])!=(wsm,wpm,wpm)
            or (sm.outs[0],p0.outs[0],p1.outs[0])!=(opost.sm_tid,*opost.pm_tids)):
        raise ValueError(
            "mixed RMS writer topology disagrees: "
            f"nodes={(sm, p0, p1)} weight={(weight.sm_tid, weight.joined_pm_tid)} "
            f"input={(opre.sm_tid, opre.pm_tids)} output={(opost.sm_tid, opost.pm_tids)}"
        )
    if len(opre.shard_shape)!=2:raise ValueError("mixed RMS rank unsupported")
    rows,hidden=opre.shard_shape
    if (opre.full_shape!=(rows*2,hidden) or opost.full_shape!=opre.full_shape or opost.shard_shape!=opre.shard_shape or (spre.full_shape,spre.shard_shape)!=(opre.full_shape,opre.shard_shape) or (spost.full_shape,spost.shard_shape)!=(opost.full_shape,opost.shard_shape) or weight.full_shape!=(hidden,) or min(rows,hidden)<=0):raise ValueError("mixed RMS shape contract disagrees")
    fresh={opost.fact_id,spost.fact_id};required={weight.fact_id,opre.fact_id,spre.fact_id}
    if not required<=set(before.fact_ids) or not fresh<=set(after.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh:raise ValueError("mixed RMS liveness disagrees")
    smt,p0t,p1t=_node_text(sm),_node_text(p0),_node_text(p1);full=_shape_text(list(opre.full_shape));shard=_shape_text(list(opre.shard_shape));wshape=_shape_text(list(weight.full_shape));sid=segment_id
    return f'''private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
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
    have hsm : smFinal {sm.outs[0]} = fw_rms_norm (smStore {sm.ins[0]}) (smStore {wsm}) := by
      simp [smFinal,smNodes,applyNodeDistributedFaithful,applyNodeDistributed,applyNodeRingAttn]
      exact applyNode_fw_rms_norm_out_1p {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {wsm} {sm.outs[0]}
    have hp0 : pmFinal {p0.outs[0]} = fw_rms_norm (pmStore {p0.ins[0]}) (pmStore {wpm}) := by
      simp [pmFinal,pmNodes,applyNodeDistributedFaithful,applyNodeDistributed,applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_rms_norm_out_1p {ir.pm_graph_ref} pmStore 0 {p0.ins[0]} {wpm} {p0.outs[0]}
      · decide
    have hp1 : pmFinal {p1.outs[0]} = fw_rms_norm (pmStore {p1.ins[0]}) (pmStore {wpm}) := by
      simp [pmFinal,pmNodes,applyNodeDistributedFaithful,applyNodeDistributed,applyNodeRingAttn]
      rw [applyNode_fw_rms_norm_out_1p]
      rw [applyNode_eq_of_not_mem_outs,applyNode_eq_of_not_mem_outs] <;> decide
    have hw : {weight.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have ho : {opre.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hOrd : {opost.fact_id}.Holds smFinal pmFinal := by
      change smStore {wsm}=pmStore {wpm} ∧ (smStore {wsm}).shape={wshape} ∧ (pmStore {wpm}).shape={wshape} at hw
      change GeneratedPatterns.Ordinary2Rel (smStore {opre.sm_tid}) (pmStore {opre.pm_tids[0]}) (pmStore {opre.pm_tids[1]}) {full} {shard} at ho
      have core := GeneratedPatterns.Ordinary2Rel.rms_norm_2d (shard := {rows}) (hidden := {hidden}) ho hw.1 (by native_decide) (by native_decide)
      change GeneratedPatterns.Ordinary2Rel (smFinal {opost.sm_tid}) (pmFinal {opost.pm_tids[0]}) (pmFinal {opost.pm_tids[1]}) {full} {shard}
      rw [hsm,hp0,hp1]
      exact core
    have hSh : {spost.fact_id}.Holds smFinal pmFinal := by
      change ShardedRel (smFinal {spost.sm_tid}) [pmFinal {spost.pm_tids[0]},pmFinal {spost.pm_tids[1]}] 0 {full} {shard}
      exact ShardedRel.ofOrdinary2_dim0_rank2 (rows := {rows}) (width := {hidden}) hOrd
    intro fact hfact
    have covered : fact ∈ [{opost.fact_id},{spost.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{opost.fact_id},{spost.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with (rfl|rfl)|old
    · exact hOrd
    · exact hSh
    · exact hframe fact old
'''
