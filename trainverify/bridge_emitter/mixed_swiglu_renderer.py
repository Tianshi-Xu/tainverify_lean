"""Atomic shared-writer ordinary/sharded CP2 SwiGLU renderer."""
from __future__ import annotations
import hashlib,json
from dataclasses import asdict

def _digest(c):return hashlib.sha256(json.dumps({"type":type(c).__name__,"fields":asdict(c)},sort_keys=True,separators=(",",":")).encode()).hexdigest()

def render_closed_mixed_swiglu_segment(ir,relation,segment_id):
    try:
        from .composer import _node_text,_shape_text
        from .relation_compiler import FrontierPointwiseCertificate,KRankBinaryRelationCertificate
    except ImportError:
        from composer import _node_text,_shape_text
        from relation_compiler import FrontierPointwiseCertificate,KRankBinaryRelationCertificate
    chain=relation.dependent_chain_plan;seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=2:raise ValueError("mixed SwiGLU requires two transitions")
    by={t.transition_id:t for t in relation.transition_specs};ot,st=(by[x] for x in seg.transition_ids)
    if (ot.rule_id,st.rule_id)!=("swiglu-ordinary-two-rank","swiglu-sharded-two-rank-dim0"):raise ValueError("mixed SwiGLU order disagrees")
    ocs=[c for c in relation.certificates if type(c) is FrontierPointwiseCertificate and c.rule_id==ot.rule_id and c.lean_theorem==ot.lean_theorem and c.operator=="FW_swiglu" and c.relation_kind=="ordinary" and set(c.input_step_triples)=={f.step_triple for f in ot.pre_facts} and c.output_step_triple==ot.post_facts[0].step_triple and _digest(c)==ot.certificate_digest]
    scs=[c for c in relation.certificates if type(c) is KRankBinaryRelationCertificate and c.rule_id==st.rule_id and c.lean_theorem==st.lean_theorem and c.op=="FW_swiglu" and set(c.input_facts)==set(st.pre_facts) and c.output_fact==st.post_facts[0] and _digest(c)==st.certificate_digest]
    if len(ocs)!=1 or len(scs)!=1:raise ValueError("mixed SwiGLU exact certificate missing")
    records={f.source:f for f in chain.relation_facts};states={s.state_id:s for s in chain.states};opre=tuple(records[f] for f in ot.pre_facts);spre=tuple(records[f] for f in st.pre_facts);opost=records[ot.post_facts[0]];spost=records[st.post_facts[0]];before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if (ot.lean_theorem!="TrainVerify.Denote.RelationCompiler.Ordinary2Rel.swiglu" or st.lean_theorem!="TrainVerify.Denote.RelationCompiler.ShardedRel.fw_swiglu_dim0_two_2d" or len(opre)!=2 or len(spre)!=2 or any(f.kind!="ordinary" for f in (*opre,opost)) or any(f.kind!="sharded" for f in (*spre,spost)) or scs[0].rank_count!=2 or scs[0].gather_dim!=0):raise ValueError("mixed SwiGLU relation metadata disagrees")
    if ot.sm_node_indices!=st.sm_node_indices or ot.pm_node_indices!=st.pm_node_indices or tuple(range(*seg.sm_range))!=ot.sm_node_indices or tuple(range(*seg.pm_range))!=ot.pm_node_indices or len(ot.sm_node_indices)!=1 or len(ot.pm_node_indices)!=2:raise ValueError("mixed SwiGLU frame disagrees")
    sm=ir.sm_nodes[ot.sm_node_indices[0]];p0,p1=(ir.pm_nodes[i] for i in ot.pm_node_indices)
    def roles(fs):
        d={f.sm_tid:f for f in fs}
        if len(d)!=2 or any(t not in d for t in sm.ins):raise ValueError("mixed SwiGLU roles ambiguous")
        return tuple(d[t] for t in sm.ins)
    oa,ob=roles(opre);sa,sb=roles(spre)
    if ((sm.rank,p0.rank,p1.rank)!=(0,0,1) or any(n.op!="FW_swiglu" or len(n.ins)!=2 or len(n.outs)!=1 or n.params not in (None,[]) for n in (sm,p0,p1)) or tuple(p0.ins)!=(oa.pm_tids[0],ob.pm_tids[0]) or tuple(p1.ins)!=(oa.pm_tids[1],ob.pm_tids[1]) or (sa.sm_tid,sb.sm_tid)!=(oa.sm_tid,ob.sm_tid) or sa.pm_tids!=oa.pm_tids or sb.pm_tids!=ob.pm_tids or (sm.outs[0],p0.outs[0],p1.outs[0])!=(opost.sm_tid,*opost.pm_tids) or (spost.sm_tid,spost.pm_tids)!=(opost.sm_tid,opost.pm_tids)):raise ValueError("mixed SwiGLU writer/TID topology disagrees")
    shapes={(f.full_shape,f.shard_shape) for f in (*opre,*spre,opost,spost)}
    if len(shapes)!=1:raise ValueError("mixed SwiGLU shapes disagree")
    full_shape,shard_shape=next(iter(shapes));rows,hidden=shard_shape
    if full_shape!=(rows*2,hidden) or min(rows,hidden)<=0:raise ValueError("mixed SwiGLU CP2 shape disagrees")
    fresh={opost.fact_id,spost.fact_id};required={f.fact_id for f in (*opre,*spre)}
    if not required<=set(before.fact_ids) or not fresh<=set(after.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh:raise ValueError("mixed SwiGLU liveness disagrees")
    smt,p0t,p1t=_node_text(sm),_node_text(p0),_node_text(p1);full=_shape_text(list(full_shape));shard=_shape_text(list(shard_shape));sid=segment_id
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
    have hsm : smFinal {sm.outs[0]} = fw_swiglu (smStore {sm.ins[0]}) (smStore {sm.ins[1]}) := by
      simp [smFinal,smNodes,applyNodeDistributedFaithful,applyNodeDistributed,applyNodeRingAttn]
      exact applyNode_fw_swiglu_out_1p {ir.sm_graph_ref} smStore 0 {sm.ins[0]} {sm.ins[1]} {sm.outs[0]}
    have hp0 : pmFinal {p0.outs[0]} = fw_swiglu (pmStore {p0.ins[0]}) (pmStore {p0.ins[1]}) := by
      simp [pmFinal,pmNodes,applyNodeDistributedFaithful,applyNodeDistributed,applyNodeRingAttn]
      rw [applyNode_eq_of_not_mem_outs]
      · exact applyNode_fw_swiglu_out_1p {ir.pm_graph_ref} pmStore 0 {p0.ins[0]} {p0.ins[1]} {p0.outs[0]}
      · decide
    have hp1 : pmFinal {p1.outs[0]} = fw_swiglu (pmStore {p1.ins[0]}) (pmStore {p1.ins[1]}) := by
      simp [pmFinal,pmNodes,applyNodeDistributedFaithful,applyNodeDistributed,applyNodeRingAttn]
      rw [applyNode_fw_swiglu_out_1p]
      rw [applyNode_eq_of_not_mem_outs,applyNode_eq_of_not_mem_outs] <;> decide
    have ha : {oa.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hb : {ob.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    have hOrd : {opost.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Ordinary2Rel (smStore {oa.sm_tid}) (pmStore {oa.pm_tids[0]}) (pmStore {oa.pm_tids[1]}) {full} {shard} at ha
      change GeneratedPatterns.Ordinary2Rel (smStore {ob.sm_tid}) (pmStore {ob.pm_tids[0]}) (pmStore {ob.pm_tids[1]}) {full} {shard} at hb
      have core := Ordinary2Rel.swiglu {rows} {hidden} ha hb (by native_decide) (by native_decide)
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
