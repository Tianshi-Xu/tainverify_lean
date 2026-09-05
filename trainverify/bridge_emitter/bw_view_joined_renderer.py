"""Closed sparse/full-frame renderer for joined BW_view transitions."""
from __future__ import annotations


def render_closed_joined_bw_view_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import _node_text, _render_mixed_final_value, _select_exact_typed_certificate, _shape_text
        from relation_compiler import get_closed_rule_spec
    spec=get_closed_rule_spec("bw-view-joined");rule=spec.rule_id;theorem=spec.lean_theorems[0]
    chain=relation.dependent_chain_plan;segment=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if segment is None or len(segment.transition_ids)!=1: raise ValueError("joined BW_view requires one transition")
    transition={t.transition_id:t for t in relation.transition_specs}.get(segment.transition_ids[0])
    if transition is None: raise ValueError("joined BW_view transition is missing")
    cert=_select_exact_typed_certificate(relation,transition,rule,theorem,spec.certificate_type,
                                         lambda c:((c.input_fact,),(c.output_fact,)))
    records={r.source:r for r in chain.relation_facts}
    try: pre=records[cert.input_fact];post=records[cert.output_fact]
    except KeyError as exc: raise ValueError("joined BW_view fact is not materialized") from exc
    states={s.state_id:s for s in chain.states};before,after=states[segment.pre_state_id],states[segment.post_state_id]
    if pre.fact_id not in before.fact_ids or post.fact_id not in after.fact_ids: raise ValueError("joined BW_view facts are not live")
    if not set(after.fact_ids)<=({post.fact_id}|set(before.fact_ids)): raise ValueError("joined BW_view post-state introduces an unproved fact")
    if (pre.kind!="joined" or post.kind!="joined" or pre.pm_tids or post.pm_tids or pre.joined_pm_tid is None or post.joined_pm_tid is None
            or pre.full_shape!=cert.input_shape or post.full_shape!=cert.target_shape or pre.shard_shape!=pre.full_shape or post.shard_shape!=post.full_shape):
        raise ValueError("joined BW_view metadata is not exact")
    if len(transition.sm_node_indices)!=1 or len(transition.pm_node_indices)!=1: raise ValueError("joined BW_view footprint is not exact")
    ss,se=segment.sm_range;ps,pe=segment.pm_range;si=transition.sm_node_indices[0];pi=transition.pm_node_indices[0]
    if si not in range(ss,se) or pi not in range(ps,pe): raise ValueError("joined BW_view writers are outside complete frame")
    sf=list(ir.sm_nodes[ss:se]);pf=list(ir.pm_nodes[ps:pe]);sm=ir.sm_nodes[si];pm=ir.pm_nodes[pi];target=tuple(cert.target_shape)
    if (sm.rank!=0 or sm.op!="BW_view" or len(sm.ins)!=2 or sm.outs!=[post.sm_tid] or tuple(sm.params)!=target
            or sm.ins[0]!=pre.sm_tid or pm.op!="BW_view" or len(pm.ins)!=2 or pm.outs!=[post.joined_pm_tid]
            or tuple(pm.params)!=target or pm.ins[0]!=pre.joined_pm_tid): raise ValueError("joined BW_view writer roles are not exact")
    if cert.sm_step_id!=f"sm:{si}:0" or cert.pm_step_id!=f"pm:{pi}:0": raise ValueError("joined BW_view certificate footprint was tampered")
    smn,pmn=f"{segment_id}_sm_nodes",f"{segment_id}_pm_nodes";smf,pmf=f"{segment_id}_sm_final",f"{segment_id}_pm_final";shape=_shape_text(list(target))
    lines=[f"private def {smn} : List NodeDecl := [{', '.join(_node_text(n) for n in sf)}]",f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(n) for n in pf)}]",
           f"private def {smf} (s : Store) : Store := {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
           f"private def {pmf} (s : Store) : Store := {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
    def writer(name,graph,initial,fn,nn,frame,pos,node):
        tn=f"{segment_id}_{name}";final=f"({fn} {initial})";expr=f"fw_view {shape} ({{store}} {node.ins[0]})"
        lines.extend([f"private theorem {tn} ({initial} : Store) : {final} {node.outs[0]} = {expr.format(store=final)} := by",
                      f"  have hfinal : {final} = {nn}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by unfold {fn}; rfl"])
        h=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nn,nodes=frame,
          position=pos,output_tid=node.outs[0],input_tids=(node.ins[0],),written_tids={t for x in frame for t in x.outs},expression=expr,
          apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                       "simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.ins[1]} {node.outs[0]}"])
        lines.extend(x[2:] if x.startswith("  ") else x for x in h);lines.extend(["  exact hout",""]);return tn
    hs=writer("hSmWriter",ir.sm_graph_ref,"smStore",smf,smn,sf,si-ss,sm);hp=writer("hPmWriter",ir.pm_graph_ref,"pmStore",pmf,pmn,pf,pi-ps,pm)
    inp=_shape_text(list(pre.full_shape));out=_shape_text(list(post.full_shape))
    lines.extend(["set_option maxHeartbeats 500000 in",f"private theorem {segment_id}_sound (smStore pmStore : Store)",f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
      f"    {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    let smFinal := {smf} smStore",f"    let pmFinal := {pmf} pmStore",
      f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",f"      unfold smFinal pmFinal {smf} {pmf}",f"      apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate",
      "      · native_decide","      · native_decide","      · native_decide","      · native_decide",f"    have hin : {pre.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
      f"    change smFinal {pre.sm_tid} = pmFinal {pre.joined_pm_tid} ∧ (smFinal {pre.sm_tid}).shape = {inp} ∧ (pmFinal {pre.joined_pm_tid}).shape = {inp} at hin",
      f"    have hsm := {hs} smStore",f"    have hpm := {hp} pmStore",
      f"    change smFinal {post.sm_tid} = fw_view {out} (smFinal {pre.sm_tid}) at hsm",
      f"    change pmFinal {post.joined_pm_tid} = fw_view {out} (pmFinal {pre.joined_pm_tid}) at hpm",
      f"    have hout : {post.fact_id}.Holds smFinal pmFinal := by",
      f"      change smFinal {post.sm_tid} = pmFinal {post.joined_pm_tid} ∧ (smFinal {post.sm_tid}).shape = {out} ∧ (pmFinal {post.joined_pm_tid}).shape = {out}",
      "      rw [hsm, hpm]",f"      exact JoinedRel.fw_view {out} {inp} hin","    intro fact hfact",
      f"    have covered : fact ∈ [{post.fact_id}] ++ {before.state_id}.facts := by",f"      exact (show {after.state_id}.facts ⊆ [{post.fact_id}] ++ {before.state_id}.facts by native_decide) hfact",
      "    simp only [List.mem_append] at covered","    rcases covered with fresh | old","    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh","      rcases fresh with rfl","      exact hout","    · exact hframe fact old","",
      "set_option maxRecDepth 8192 in",f"private def {segment_id} :",f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by","    intro smStore pmStore hstate",f"    exact {segment_id}_sound smStore pmStore hstate",""])
    return "\n".join(lines)
