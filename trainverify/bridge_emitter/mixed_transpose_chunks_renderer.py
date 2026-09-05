"""Atomic sparse/full-frame renderer for transpose tuples plus full-producer chunks."""
from __future__ import annotations


def render_closed_transpose_tuple_chunks_segment(ir, relation, segment_id: str) -> str:
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from .relation_compiler import KRankTransposeRelationCertificate, KRankFullProducerChunksCertificate
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value, _select_exact_typed_certificate
        from relation_compiler import KRankTransposeRelationCertificate, KRankFullProducerChunksCertificate
    trule="transpose-sharded-k-rank";crule="full-producer-chunks-k-rank"
    ctheorem="TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn"
    chain=relation.dependent_chain_plan;segment=next(x for x in chain.segments if x.segment_id==segment_id)
    by_id={x.transition_id:x for x in relation.transition_specs};transitions=tuple(by_id[x] for x in segment.transition_ids)
    trans=tuple(x for x in transitions if x.rule_id==trule);chunks=tuple(x for x in transitions if x.rule_id==crule)
    if not trans or len(chunks)!=1 or len(trans)+1!=len(transitions):raise ValueError("transpose/chunks family mismatch")
    tcerts=tuple(_select_exact_typed_certificate(relation,t,trule,t.lean_theorem,KRankTransposeRelationCertificate,
        lambda c:((c.input_fact,),(c.output_fact,))) for t in trans)
    ct=chunks[0];ccert=_select_exact_typed_certificate(relation,ct,crule,ctheorem,KRankFullProducerChunksCertificate,
        lambda c:((c.input_fact,),(c.output_fact,)))
    records={x.source:x for x in chain.relation_facts};states={x.state_id:x for x in chain.states}
    tpairs=tuple((records[c.input_fact],records[c.output_fact]) for c in tcerts)
    cpre,cpost=records[ccert.input_fact],records[ccert.output_fact]
    before,after=states[segment.pre_state_id],states[segment.post_state_id]
    fresh_ids=tuple([*(post.fact_id for _pre,post in tpairs),cpost.fact_id])
    required={pre.fact_id for pre,_post in tpairs}|{cpre.fact_id}
    if not required<=set(before.fact_ids) or not set(fresh_ids)<=set(after.fact_ids):raise ValueError("transpose/chunks facts not live")
    if not set(after.fact_ids)<=set(before.fact_ids)|set(fresh_ids):raise ValueError("transpose/chunks unproved post fact")
    k=ccert.rank_count
    if k<=0 or cpre.kind!="joined" or cpre.joined_pm_tid is None or cpost.kind!="sharded" or len(cpost.pm_tids)!=k:
        raise ValueError("chunks metadata mismatch")
    sm_start,sm_end=segment.sm_range;pm_start,pm_end=segment.pm_range
    sm_owned=tuple(i for t in transitions for i in t.sm_node_indices);pm_owned=tuple(i for t in transitions for i in t.pm_node_indices)
    if (len(sm_owned)!=len(set(sm_owned)) or len(pm_owned)!=len(set(pm_owned))
            or not set(sm_owned)<=set(range(sm_start,sm_end)) or not set(pm_owned)<=set(range(pm_start,pm_end))):
        raise ValueError("transpose/chunks writers overlap or leave frame")
    validated=[]
    for n,(t,c,(pre,post)) in enumerate(zip(trans,tcerts,tpairs)):
        if (len(t.sm_node_indices)!=1 or len(t.pm_node_indices)!=k or c.rank_count!=k
                or pre.kind!="sharded" or post.kind!="sharded" or len(pre.pm_tids)!=k or len(post.pm_tids)!=k):
            raise ValueError("transpose typed metadata mismatch")
        sm=ir.sm_nodes[t.sm_node_indices[0]];pms=tuple(ir.pm_nodes[i] for i in t.pm_node_indices)
        if (sm.op!="FW_transpose" or sm.rank!=0 or tuple(x.rank for x in pms)!=tuple(range(k))
                or any(x.op!="FW_transpose" for x in pms) or tuple(sm.params or ())!=tuple(c.parameters)
                or any(tuple(x.params or ())!=tuple(c.parameters) for x in pms)
                or sm.ins!=[pre.sm_tid] or sm.outs!=[post.sm_tid]
                or tuple(x.ins[0] for x in pms)!=pre.pm_tids or tuple(x.outs[0] for x in pms)!=post.pm_tids):
            raise ValueError("transpose writer signature mismatch")
        validated.append((n,t,c,pre,post,sm,pms))
    if ct.sm_node_indices or len(ct.pm_node_indices)!=k or ccert.chunk_dim!=cpost.gather_dim:
        raise ValueError("chunks footprint mismatch")
    chunk_nodes=tuple(ir.pm_nodes[i] for i in ct.pm_node_indices);dim=ccert.chunk_dim;producer=cpre.joined_pm_tid
    if (tuple(x.rank for x in chunk_nodes)!=tuple(range(k))
            or any(x.op!="ChunkPrim" or x.ins!=[producer] or x.params!=[dim] for x in chunk_nodes)
            or tuple(x.outs[0] for x in chunk_nodes)!=cpost.pm_tids):raise ValueError("chunk writer signature mismatch")
    sm_frame=list(ir.sm_nodes[sm_start:sm_end]);pm_frame=list(ir.pm_nodes[pm_start:pm_end])
    shape=lambda x:_shape_text(list(x));smn=f"{segment_id}_smNodes";pmn=f"{segment_id}_pmNodes"
    smf=f"{segment_id}_smFinal";pmf=f"{segment_id}_pmFinal"
    lines=[f"private def {smn} : List NodeDecl := [{', '.join(_node_text(x) for x in sm_frame)}]",
        f"private def {pmn} : List NodeDecl := [{', '.join(_node_text(x) for x in pm_frame)}]",
        f"@[irreducible] private def {smf} (s : Store) : Store :=",f"  {smn}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) s",
        f"@[irreducible] private def {pmf} (s : Store) : Store :=",f"  {pmn}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) s",""]
    def writer(name,graph,initial,final_name,nodes_name,frame,pos,node,expr,apply):
        final=f"({final_name} {initial})";thm=f"{segment_id}_{name}"
        lines.extend([f"private theorem {thm} ({initial} : Store) :",f"    {final} {node.outs[0]} = {expr.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",f"    unfold {final_name}","    rfl"])
        helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",
            nodes_name=nodes_name,nodes=frame,position=pos,output_tid=node.outs[0],input_tids=tuple(node.ins),
            written_tids={t for x in frame for t in x.outs},expression=expr,apply_lines=apply)
        lines.extend(x[2:] if x.startswith("  ") else x for x in helper);lines.extend(["  exact hout",""]);return thm
    thelpers=[]
    for n,t,c,pre,post,sm,pms in validated:
        p0,p1=c.parameters;expr=f"transposeAxes {p0} {p1} ({{store}} {{tid}})"
        hs=writer(f"transposeSmWriter{n}",ir.sm_graph_ref,"smStore",smf,smn,sm_frame,t.sm_node_indices[0]-sm_start,sm,
            expr.replace("{tid}",str(sm.ins[0])),["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_fw_transposeAxes_out {ir.sm_graph_ref} t {sm.rank} {sm.ins[0]} {sm.outs[0]} {p0} {p1}"])
        hp=[]
        for r,(idx,node) in enumerate(zip(t.pm_node_indices,pms)):
            hp.append(writer(f"transposePmWriter{n}_{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pm_frame,idx-pm_start,node,
                expr.replace("{tid}",str(node.ins[0])),["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"exact applyNode_fw_transposeAxes_out {ir.pm_graph_ref} t {node.rank} {node.ins[0]} {node.outs[0]} {p0} {p1}"]))
        thelpers.append((hs,hp))
    chelpers=[]
    for r,(idx,node) in enumerate(zip(ct.pm_node_indices,chunk_nodes)):
        expr=f"chunkPrimDimN {dim} {k} {r} ({{store}} {producer})"
        chelpers.append(writer(f"chunkWriter{r}",ir.pm_graph_ref,"pmStore",pmf,pmn,pm_frame,idx-pm_start,node,expr,[
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]","simp [applyNodeDistributed, applyNodeRingAttn]",f"rw [show {k} = {ir.pm_graph_ref}.numRanks by rfl]",f"simpa using applyNode_chunkPrimDimN_out {ir.pm_graph_ref} t {r} {producer} {node.outs[0]} {dim}"]))
    for n,(row,helpers) in enumerate(zip(validated,thelpers)):
        _n,t,c,pre,post,sm,pms=row;hs,hp=helpers
        ins="["+", ".join(f"({pmf} pmStore) {x}" for x in pre.pm_tids)+"]";outs="["+", ".join(f"({pmf} pmStore) {x}" for x in post.pm_tids)+"]"
        symbolic=[str(x) for x in pre.shard_shape]
        symbolic[pre.gather_dim]=f"{pre.shard_shape[pre.gather_dim]} * {ins}.length"
        symbolic_full="["+", ".join(symbolic)+"]"
        lines.extend([f"private theorem {segment_id}_transposeOut{n} (smStore pmStore : Store)",
            f"    (hin : {pre.fact_id}.Holds ({smf} smStore) ({pmf} pmStore)) : {post.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
            f"  change ShardedRel (({smf} smStore) {pre.sm_tid}) {ins} {pre.gather_dim} {symbolic_full} {shape(pre.shard_shape)} at hin",
            f"  have htransport := {c.lean_theorem} hin",f"  change ShardedRel (({smf} smStore) {post.sm_tid}) {outs} {post.gather_dim} {shape(post.full_shape)} {shape(post.shard_shape)}",
            f"  rw [{hs} smStore, {', '.join(h+' pmStore' for h in hp)}]","  simpa using htransport",""])
    cout="["+", ".join(f"({pmf} pmStore) {x}" for x in cpost.pm_tids)+"]"
    pm_tids="["+", ".join(str(x) for x in cpost.pm_tids)+"]"
    lines.extend([f"private theorem {segment_id}_chunksOut (smStore pmStore : Store)",
        f"    (hin : {cpre.fact_id}.Holds ({smf} smStore) ({pmf} pmStore)) : {cpost.fact_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  change ({smf} smStore) {cpre.sm_tid} = ({pmf} pmStore) {producer} ∧ (({smf} smStore) {cpre.sm_tid}).shape = {shape(cpre.full_shape)} ∧ (({pmf} pmStore) {producer}).shape = {shape(cpre.full_shape)} at hin",
        f"  let pmTids : List Tid := {pm_tids}",
        "  let rankCount := pmTids.length",
        f"  have hOrderedChunks : pmTids.map ({pmf} pmStore) = List.ofFn (fun r : Fin rankCount => chunkPrimDimN {dim} rankCount r.1 (({pmf} pmStore) {producer})) := by",
        "    simp only [pmTids, rankCount, List.map]",
        f"    rw [{', '.join(h+' pmStore' for h in chelpers)}]",
        "    rfl",
        f"  change ShardedRel (({smf} smStore) {cpost.sm_tid}) (pmTids.map ({pmf} pmStore)) {dim} {shape(cpost.full_shape)} {shape(cpost.shard_shape)}",
        "  refine {","    full_value := ?_","    full_shape := hin.2.1","    shards_nonempty := by simp [pmTids]","    gather_dim_lt := by native_decide","    shard_shapes := ?_","    shape_contract := by simp [pmTids]", "  }",
        "  · rw [hOrderedChunks, List.length_ofFn]",f"    rw [{ctheorem} {dim} rankCount (({pmf} pmStore) {producer}) (by native_decide) (by rw [hin.2.2]; native_decide) (by rw [hin.2.2]; native_decide)]","    exact hin.1",
        "  · intro shard hmem","    simp only [pmTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem",f"    rcases hmem with {' | '.join('rfl' for _ in range(k))}"])
    for r,h in enumerate(chelpers):lines.extend([f"    · rw [{h} pmStore]",f"      rw [chunkPrimDimN_shape {dim} {k} {r} (({pmf} pmStore) {producer}) {shape(cpre.full_shape)} hin.2.2 (by native_decide)]","      native_decide"])
    lines.append("")
    lines.extend([f"private theorem {segment_id}_publish (smStore pmStore : Store) (hstate : {before.state_id}.Holds smStore pmStore) : {after.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",
        f"  have hframe : {before.state_id}.Holds ({smf} smStore) ({pmf} pmStore) := by",f"    unfold {smf} {pmf}",f"    apply RelationState.Holds.fold_frame {smn} {pmn} smStore pmStore hstate","    · native_decide","    · native_decide","    · native_decide","    · native_decide"])
    for n in range(len(tpairs)):lines.append(f"  have hT{n} := {segment_id}_transposeOut{n} smStore pmStore (hframe _ (by native_decide))")
    lines.extend([f"  have hC := {segment_id}_chunksOut smStore pmStore (hframe _ (by native_decide))","  intro fact hfact",f"  have covered : fact ∈ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts := by",f"    exact (show {after.state_id}.facts ⊆ [{', '.join(fresh_ids)}] ++ {before.state_id}.facts by native_decide) hfact","  simp only [List.mem_append] at covered","  rcases covered with fresh | old","  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",f"    rcases fresh with {' | '.join('rfl' for _ in fresh_ids)}"])
    for n in range(len(tpairs)):lines.append(f"    · exact hT{n}")
    lines.extend(["    · exact hC","  · exact hframe fact old","",f"private def {segment_id} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",f"  smNodes := {smn}",f"  pmNodes := {pmn}","  sound := by","    intro smStore pmStore hstate",f"    simpa only [{smf}, {pmf}] using {segment_id}_publish smStore pmStore hstate",""])
    return "\n".join(lines)
