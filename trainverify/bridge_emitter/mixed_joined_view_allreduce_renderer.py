"""Atomic sparse/full-frame renderer for joined views plus AllReduce."""
from __future__ import annotations


def render_closed_joined_views_allreduce_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import JoinedUnaryViewCertificate, KRankAllReduceReconstructionCertificate
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import JoinedUnaryViewCertificate, KRankAllReduceReconstructionCertificate

    view_rule="joined-view-unary";view_theorem="TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view"
    reduce_rule="allreduce-reconstruction-k-rank"
    reduce_theorem="TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce"
    chain=relation.dependent_chain_plan
    segment=next(x for x in chain.segments if x.segment_id==segment_id)
    by_id={x.transition_id:x for x in relation.transition_specs}
    transitions=tuple(by_id[x] for x in segment.transition_ids)
    views=tuple(x for x in transitions if x.rule_id==view_rule)
    reductions=tuple(x for x in transitions if x.rule_id==reduce_rule)
    if len(views)<1 or len(reductions)!=1 or len(views)+1!=len(transitions):
        raise ValueError("joined-view/AllReduce requires positive views and one reduction")
    view_certs=tuple(_select_exact_typed_certificate(
        relation,t,view_rule,view_theorem,JoinedUnaryViewCertificate,
        lambda c:((c.input_fact,),(c.output_fact,))) for t in views)
    rt=reductions[0]
    rcert=_select_exact_typed_certificate(
        relation,rt,reduce_rule,reduce_theorem,KRankAllReduceReconstructionCertificate,
        lambda c:((c.input_fact,),(c.output_fact,)))
    records={x.source:x for x in chain.relation_facts};states={x.state_id:x for x in chain.states}
    view_pairs=tuple((records[c.input_fact],records[c.output_fact]) for c in view_certs)
    rpre,rpost=records[rcert.input_fact],records[rcert.output_fact]
    before,after=states[segment.pre_state_id],states[segment.post_state_id]
    fresh_ids=tuple([*(post.fact_id for _pre,post in view_pairs),rpost.fact_id])
    required={pre.fact_id for pre,_post in view_pairs}|{rpre.fact_id}
    if not required<=set(before.fact_ids) or not set(fresh_ids)<=set(after.fact_ids):
        raise ValueError("joined-view/AllReduce pre/post facts are not live")
    if not set(after.fact_ids)<=set(before.fact_ids)|set(fresh_ids):
        raise ValueError("joined-view/AllReduce post-state introduces an unproved fact")
    k=rcert.rank_count
    if k<=0 or len(rpre.pm_tids)!=k or rpre.kind!="reduction" or rpost.kind!="joined":
        raise ValueError("joined-view/AllReduce reduction metadata mismatch")
    sm_start,sm_end=segment.sm_range;pm_start,pm_end=segment.pm_range
    sm_owned=tuple(i for t in transitions for i in t.sm_node_indices)
    pm_owned=tuple(i for t in transitions for i in t.pm_node_indices)
    if (len(sm_owned)!=len(set(sm_owned)) or len(pm_owned)!=len(set(pm_owned))
            or not set(sm_owned)<=set(range(sm_start,sm_end))
            or not set(pm_owned)<=set(range(pm_start,pm_end))):
        raise ValueError("joined-view/AllReduce writers overlap or leave the complete frame")
    sm_frame=list(ir.sm_nodes[sm_start:sm_end]);pm_frame=list(ir.pm_nodes[pm_start:pm_end])
    validated_views=[]
    for number,(t,c,(pre,post)) in enumerate(zip(views,view_certs,view_pairs)):
        if (len(t.sm_node_indices)!=1 or len(t.pm_node_indices)!=1 or c.pm_rank<0
                or c.sm_step_id!=f"sm:{t.sm_node_indices[0]}:0"
                or c.pm_step_id!=f"pm:{t.pm_node_indices[0]}:0"
                or pre.kind!="joined" or post.kind!="joined"
                or pre.joined_pm_tid is None or post.joined_pm_tid is None):
            raise ValueError("joined-view typed authority mismatch")
        sm=ir.sm_nodes[t.sm_node_indices[0]];pm=ir.pm_nodes[t.pm_node_indices[0]]
        params=tuple(c.parameters)
        if (sm.op!="FW_view" or pm.op!="FW_view" or sm.rank!=0 or pm.rank!=c.pm_rank
                or tuple(sm.params or ())!=params or tuple(pm.params or ())!=params
                or sm.ins!=[pre.sm_tid] or pm.ins!=[pre.joined_pm_tid]
                or sm.outs!=[post.sm_tid] or pm.outs!=[post.joined_pm_tid]):
            raise ValueError("joined-view writer signatures mismatch")
        validated_views.append((number,t,c,pre,post,sm,pm))
    if rt.sm_node_indices or len(rt.pm_node_indices)!=1:
        raise ValueError("AllReduce footprint mismatch")
    reduce_index=rt.pm_node_indices[0];reduce_node=ir.pm_nodes[reduce_index]
    if (rcert.pm_allreduce_step!=f"pm:{reduce_index}:0" or reduce_node.op!="AllReducePrim"
            or reduce_node.rank!=0 or len(reduce_node.outs)!=1
            or tuple(reduce_node.ins)!=rpre.pm_tids or reduce_node.outs[0]!=rpost.joined_pm_tid):
        raise ValueError("AllReduce writer signature mismatch")

    shape=lambda x:_shape_text(list(x))
    sm_nodes_name=f"{segment_id}_smNodes";pm_nodes_name=f"{segment_id}_pmNodes"
    sm_final_name=f"{segment_id}_smFinal";pm_final_name=f"{segment_id}_pmFinal"
    lines=[
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"@[irreducible] private def {sm_final_name} (s : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pm_final_name} (s : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s","",
    ]
    def add_writer(name,graph,initial,final_name,nodes_name,frame,pos,node,expr,apply_lines):
        final=f"({final_name} {initial})";thm=f"{segment_id}_{name}"
        lines.extend([f"private theorem {thm} ({initial} : Store) :",
            f"    {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}","    rfl"])
        helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,
            final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=pos,
            output_tid=node.outs[0],input_tids=tuple(node.ins),written_tids={t for n in frame for t in n.outs},
            expression=expr,apply_lines=apply_lines)
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper);lines.extend(["  exact hout",""])
        return thm
    view_helpers=[]
    for number,t,c,pre,post,sm,pm in validated_views:
        target_shape=shape(post.full_shape)
        params_head=c.parameters[0]
        params_tail="["+", ".join(str(x) for x in c.parameters[1:])+"]"
        sm_expr=f"fw_view {target_shape} ({{store}} {sm.ins[0]})";pm_expr=f"fw_view {target_shape} ({{store}} {pm.ins[0]})"
        apply_sm=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                  "simp [applyNodeDistributed, applyNodeRingAttn]",
                  f"exact applyNode_fw_view_out {ir.sm_graph_ref} t {sm.rank} {params_head} {params_tail} {sm.ins[0]} {sm.outs[0]}"]
        apply_pm=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
                  "simp [applyNodeDistributed, applyNodeRingAttn]",
                  f"exact applyNode_fw_view_out {ir.pm_graph_ref} t {pm.rank} {params_head} {params_tail} {pm.ins[0]} {pm.outs[0]}"]
        hs=add_writer(f"viewSmWriter{number}",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,sm_frame,t.sm_node_indices[0]-sm_start,sm,sm_expr,apply_sm)
        hp=add_writer(f"viewPmWriter{number}",ir.pm_graph_ref,"pmStore",pm_final_name,pm_nodes_name,pm_frame,t.pm_node_indices[0]-pm_start,pm,pm_expr,apply_pm)
        view_helpers.append((hs,hp))
    input_text="["+", ".join(str(x) for x in rpre.pm_tids)+"]"
    reduce_expr=f"allReducePrim {k} 0 ["+", ".join(f"{{store}} {x}" for x in rpre.pm_tids)+"]"
    reduce_helper=add_writer("allReduceWriter",ir.pm_graph_ref,"pmStore",pm_final_name,pm_nodes_name,pm_frame,
        reduce_index-pm_start,reduce_node,reduce_expr,[
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]",
            "simp [applyNodeDistributed, applyNodeRingAttn]",
            f"exact applyNode_allReducePrim_out {ir.pm_graph_ref} t 0 {input_text} {reduce_node.outs[0]}"])

    for number,(row,helpers) in enumerate(zip(validated_views,view_helpers)):
        _n,_t,c,pre,post,_sm,_pm=row;hs,hp=helpers
        lines.extend([f"private theorem {segment_id}_viewOut{number} (smStore pmStore : Store)",
            f"    (hin : {pre.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore)) :",
            f"    {post.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
            f"  change ({sm_final_name} smStore) {pre.sm_tid} = ({pm_final_name} pmStore) {pre.joined_pm_tid} ∧",
            f"    (({sm_final_name} smStore) {pre.sm_tid}).shape = {shape(pre.full_shape)} ∧",
            f"    (({pm_final_name} pmStore) {pre.joined_pm_tid}).shape = {shape(pre.full_shape)} at hin",
            f"  change ({sm_final_name} smStore) {post.sm_tid} = ({pm_final_name} pmStore) {post.joined_pm_tid} ∧",
            f"    (({sm_final_name} smStore) {post.sm_tid}).shape = {shape(post.full_shape)} ∧",
            f"    (({pm_final_name} pmStore) {post.joined_pm_tid}).shape = {shape(post.full_shape)}",
            f"  rw [{hs} smStore, {hp} pmStore]",
            f"  exact JoinedRel.fw_view {shape(post.full_shape)} {shape(pre.full_shape)} hin",""])
    lines.extend([f"private theorem {segment_id}_allReduceOut (smStore pmStore : Store)",
        f"    (hin : {rpre.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore)) :",
        f"    {rpost.fact_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  change ReductionRel (({sm_final_name} smStore) {rpre.sm_tid}) [{', '.join(f'({pm_final_name} pmStore) {x}' for x in rpre.pm_tids)}] {shape(rpre.full_shape)} at hin",
        f"  have hWriter := {reduce_helper} pmStore",
        f"  have hJoined : ({sm_final_name} smStore) {rpre.sm_tid} = ({pm_final_name} pmStore) {rpost.joined_pm_tid} :=",
        "    (ReductionRel.to_joined_allReduce hin).trans hWriter.symm",
        f"  change ({sm_final_name} smStore) {rpost.sm_tid} = ({pm_final_name} pmStore) {rpost.joined_pm_tid} ∧",
        f"    (({sm_final_name} smStore) {rpost.sm_tid}).shape = {shape(rpost.full_shape)} ∧",
        f"    (({pm_final_name} pmStore) {rpost.joined_pm_tid}).shape = {shape(rpost.full_shape)}",
        "  refine ⟨hJoined, hin.full_shape, ?_⟩","  rw [← hJoined]","  exact hin.full_shape",""])
    lines.extend([f"private theorem {segment_id}_publish (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    unfold {sm_final_name} {pm_final_name}",f"    apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "    · native_decide","    · native_decide","    · native_decide","    · native_decide"])
    for n,(_pre,post) in enumerate(view_pairs):
        lines.extend([f"  have hView{n} := {segment_id}_viewOut{n} smStore pmStore (hframe _ (by native_decide))"])
    lines.extend([f"  have hReduce := {segment_id}_allReduceOut smStore pmStore (hframe _ (by native_decide))",
        "  intro fact hfact",f"  have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",
        f"    exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact",
        "  simp only [List.mem_append] at covered","  rcases covered with fresh | old",
        "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        f"    rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}"])
    for n in range(len(view_pairs)):lines.append(f"    · exact hView{n}")
    lines.extend(["    · exact hReduce","  · exact hframe fact old","",
        f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}",f"  pmNodes := {pm_nodes_name}","  sound := by","    intro smStore pmStore hstate",
        f"    simpa only [{sm_final_name}, {pm_final_name}] using {segment_id}_publish smStore pmStore hstate",""])
    return "\n".join(lines)
