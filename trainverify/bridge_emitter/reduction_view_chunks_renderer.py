"""Atomic reduction→AllReduce→identity-view→chunks boundary renderer."""
from __future__ import annotations


def render_closed_reduction_view_chunks_segment(ir, relation, segment_id):
    try:
        from .composer import _node_text, _shape_text, _select_exact_typed_certificate
        from .relation_compiler import (ReductionChunkBoundaryCertificate,
            KRankAllReduceReconstructionCertificate, JoinedUnaryViewCertificate,
            KRankFullProducerChunksCertificate)
    except ImportError:
        from composer import _node_text, _shape_text, _select_exact_typed_certificate
        from relation_compiler import (ReductionChunkBoundaryCertificate,
            KRankAllReduceReconstructionCertificate, JoinedUnaryViewCertificate,
            KRankFullProducerChunksCertificate)
    family=("reduction-allreduce-chunks-ordinary-two-rank","allreduce-reconstruction-k-rank","joined-view-unary","full-producer-chunks-k-rank")
    chain=relation.dependent_chain_plan; seg=next((s for s in chain.segments if s.segment_id==segment_id),None)
    if seg is None or len(seg.transition_ids)!=4: raise ValueError("reduction/view/chunks requires four transitions")
    by={t.transition_id:t for t in relation.transition_specs}; ts=tuple(by[x] for x in seg.transition_ids)
    if tuple(t.rule_id for t in ts)!=family: raise ValueError("reduction/view/chunks family order disagrees")
    specs=((ReductionChunkBoundaryCertificate,lambda c:((c.input_fact,),(c.output_fact,))),
           (KRankAllReduceReconstructionCertificate,lambda c:((c.input_fact,),(c.output_fact,))),
           (JoinedUnaryViewCertificate,lambda c:((c.input_fact,),(c.output_fact,))),
           (KRankFullProducerChunksCertificate,lambda c:((c.input_fact,),(c.output_fact,))))
    cs=tuple(_select_exact_typed_certificate(relation,t,t.rule_id,t.lean_theorem,cls,proj) for t,(cls,proj) in zip(ts,specs))
    records={f.source:f for f in chain.relation_facts}; states={s.state_id:s for s in chain.states}
    red=records[ts[0].pre_facts[0]]; ordinary=records[ts[0].post_facts[0]]
    joined0=records[ts[1].post_facts[0]]; joined1=records[ts[2].post_facts[0]]; sharded=records[ts[3].post_facts[0]]
    before,after=states[seg.pre_state_id],states[seg.post_state_id]
    if (red.kind!="reduction" or ordinary.kind!="ordinary" or joined0.kind!="joined" or joined1.kind!="joined" or sharded.kind!="sharded"
            or len(ordinary.shard_shape) != 2 or len(red.full_shape) != 2):
        raise ValueError("reduction/view/chunks typed rank contract disagrees")
    rows, hidden = ordinary.shard_shape
    if (min(rows, hidden) <= 0 or red.full_shape != (rows * 2, hidden) or ordinary.full_shape!=red.full_shape
            or joined0.full_shape!=red.full_shape or joined1.full_shape!=red.full_shape
            or sharded.full_shape!=red.full_shape or sharded.shard_shape!=ordinary.shard_shape or sharded.gather_dim!=0
            or len(red.pm_tids)!=2 or len(ordinary.pm_tids)!=2 or len(sharded.pm_tids)!=2):
        raise ValueError("reduction/view/chunks typed shape contract disagrees")
    sm_frame=tuple(ir.sm_nodes[i] for i in range(*seg.sm_range)); pm_frame=tuple(ir.pm_nodes[i] for i in range(*seg.pm_range))
    if len(sm_frame)!=1 or len(pm_frame)!=5: raise ValueError("reduction/view/chunks frame cardinality disagrees")
    smv=sm_frame[0]; reduce,pv0,pv1,ch0,ch1=pm_frame
    sm0, pm0 = seg.sm_range[0], seg.pm_range[0]
    if (ts[0].sm_node_indices != (sm0,) or ts[0].pm_node_indices != (pm0, pm0+2, pm0+3, pm0+4)
            or ts[1].sm_node_indices or ts[1].pm_node_indices != (pm0,)
            or ts[2].sm_node_indices != (sm0,) or ts[2].pm_node_indices != (pm0+2,)
            or ts[3].sm_node_indices or ts[3].pm_node_indices != (pm0+3, pm0+4)):
        raise ValueError("reduction/view/chunks certificate footprints disagree")
    if (smv.op!="FW_view" or reduce.op!="AllReducePrim" or pv0.op!="FW_view" or pv1.op!="FW_view"
            or ch0.op!="ChunkPrim" or ch1.op!="ChunkPrim"
            or (smv.rank,reduce.rank,pv0.rank,pv1.rank,ch0.rank,ch1.rank)!=(0,0,0,1,0,1)
            or reduce.ins!=list(red.pm_tids) or reduce.outs!=[joined0.joined_pm_tid]
            or smv.ins!=[red.sm_tid] or smv.outs!=[joined1.sm_tid]
            or pv0.ins!=[joined0.joined_pm_tid] or pv1.ins!=[joined0.joined_pm_tid]
            or pv0.outs!=[joined1.joined_pm_tid] or pv1.outs!=[joined1.joined_pm_tid]
            or ch0.ins!=[joined1.joined_pm_tid] or ch1.ins!=[joined1.joined_pm_tid]
            or (ch0.outs[0],ch1.outs[0])!=ordinary.pm_tids or ordinary.pm_tids!=sharded.pm_tids):
        raise ValueError("reduction/view/chunks writer topology disagrees")
    required={red.fact_id}; fresh={ordinary.fact_id,joined0.fact_id,joined1.fact_id,sharded.fact_id}
    if not required<=set(before.fact_ids) or not set(after.fact_ids)<=set(before.fact_ids)|fresh:
        raise ValueError("reduction/view/chunks liveness disagrees")
    smt=_node_text(smv); pmts=tuple(_node_text(n) for n in pm_frame); shape=_shape_text(list(red.full_shape)); shardshape=_shape_text(list(ordinary.shard_shape)); sid=segment_id
    reduce_tail = "[" + ", ".join(_node_text(n) for n in pm_frame[1:]) + "]"
    view_prefix = "[" + ", ".join(_node_text(n) for n in pm_frame[:2]) + "]"
    view_suffix = "[" + ", ".join(_node_text(n) for n in pm_frame[3:]) + "]"
    view_read_tail = "[" + ", ".join(_node_text(n) for n in pm_frame[2:]) + "]"
    chunk0_prefix = "[" + ", ".join(_node_text(n) for n in pm_frame[:3]) + "]"
    chunk0_suffix = "[" + ", ".join(_node_text(n) for n in pm_frame[4:]) + "]"
    chunk0_read_tail = "[" + ", ".join(_node_text(n) for n in pm_frame[3:]) + "]"
    chunk1_prefix = "[" + ", ".join(_node_text(n) for n in pm_frame[:4]) + "]"
    chunk1_read_tail = "[" + _node_text(ch1) + "]"
    return f'''private def {sid} : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where
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
    have hRed : {red.fact_id}.Holds smStore pmStore := hstate _ (by native_decide)
    change ReductionRel (smStore {red.sm_tid}) [pmStore {red.pm_tids[0]}, pmStore {red.pm_tids[1]}] {shape} at hRed
    have hReduce : pmFinal {joined0.joined_pm_tid} = allReducePrim 2 0 [pmStore {red.pm_tids[0]}, pmStore {red.pm_tids[1]}] := by
      simpa [pmFinal, pmNodes] using
        (foldl_faithful_binary_middle_writer {ir.pm_graph_ref} pmStore [] {reduce_tail} {_node_text(reduce)}
          {reduce.ins[0]} {reduce.ins[1]} {reduce.outs[0]} (fun x y => allReducePrim 2 0 [x, y]) (by
            intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
            unfold applyNodeDistributed
            rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_allReducePrim_out {ir.pm_graph_ref} t 0 [{reduce.ins[0]}, {reduce.ins[1]}] {reduce.outs[0]}
            · native_decide
            · native_decide
          ) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    have hJoined0 : {joined0.fact_id}.Holds smFinal pmFinal := by
      change smFinal {joined0.sm_tid} = pmFinal {joined0.joined_pm_tid} ∧ (smFinal {joined0.sm_tid}).shape = {shape} ∧ (pmFinal {joined0.joined_pm_tid}).shape = {shape}
      have hsm : smFinal {joined0.sm_tid} = smStore {red.sm_tid} := by
        exact foldl_applyNodeDistributedFaithful_at_not_written {ir.sm_graph_ref} smNodes smStore {red.sm_tid} (by native_decide) (by native_decide)
      rw [hsm]
      have hv : smStore {red.sm_tid} = pmFinal {joined0.joined_pm_tid} := hRed.full_value.trans hReduce.symm
      exact ⟨hv, hRed.full_shape, by rw [← hv]; exact hRed.full_shape⟩
    have hSmView : smFinal {joined1.sm_tid} = fw_view {shape} (smStore {red.sm_tid}) := by
      simp [smFinal, smNodes, applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_view_out {ir.sm_graph_ref} smStore 0 {smv.params[0]} {_shape_text(smv.params[1:])} {smv.ins[0]} {smv.outs[0]}
    have hPmView : pmFinal {joined1.joined_pm_tid} = fw_view {shape} (pmFinal {joined0.joined_pm_tid}) := by
      have hWriter : pmFinal {joined1.joined_pm_tid} = fw_view {shape} (({view_prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined0.joined_pm_tid}) := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {view_prefix} {view_suffix} {_node_text(pv1)}
            {pv1.outs[0]} (fun t => fw_view {shape} (t {pv1.ins[0]})) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              unfold applyNodeDistributed
              rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
              · exact applyNode_fw_view_out {ir.pm_graph_ref} t {pv1.rank} {pv1.params[0]} {_shape_text(pv1.params[1:])} {pv1.ins[0]} {pv1.outs[0]}
              · native_decide
              · native_decide
            ) (by native_decide) (by native_decide))
      have hRead := foldl_faithful_prefix_read_eq_final {ir.pm_graph_ref} pmStore {view_prefix} {view_read_tail} {joined0.joined_pm_tid} (by native_decide) (by native_decide)
      change ({view_prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined0.joined_pm_tid} = pmFinal {joined0.joined_pm_tid} at hRead
      rw [hWriter, hRead]
    have hJoined1 : {joined1.fact_id}.Holds smFinal pmFinal := by
      change smFinal {joined1.sm_tid} = pmFinal {joined1.joined_pm_tid} ∧ (smFinal {joined1.sm_tid}).shape = {shape} ∧ (pmFinal {joined1.joined_pm_tid}).shape = {shape}
      rw [hSmView, hPmView]
      exact JoinedRel.fw_view {shape} {shape} hJoined0
    have hSmId : smFinal {joined1.sm_tid} = smStore {red.sm_tid} := by
      rw [hSmView, fw_view_id_of_shape _ _ hRed.full_shape]
    have hPmId : pmFinal {joined1.joined_pm_tid} = pmFinal {joined0.joined_pm_tid} := by
      rw [hPmView, fw_view_id_of_shape _ _ hJoined0.2.2]
    have hChunk0 : pmFinal {ordinary.pm_tids[0]} = chunkPrimDimN 0 2 0 (pmFinal {joined0.joined_pm_tid}) := by
      have hWriter : pmFinal {ordinary.pm_tids[0]} = chunkPrimDimN 0 2 0 (({chunk0_prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined1.joined_pm_tid}) := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {chunk0_prefix} {chunk0_suffix} {_node_text(ch0)}
            {ch0.outs[0]} (fun t => chunkPrimDimN 0 2 0 (t {ch0.ins[0]})) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              unfold applyNodeDistributed
              rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
              · simpa only [show {ir.pm_graph_ref}.numRanks = 2 by native_decide] using
                  (applyNode_chunkPrimDimN_out {ir.pm_graph_ref} t 0 {ch0.ins[0]} {ch0.outs[0]} 0)
              · native_decide
              · native_decide
            ) (by native_decide) (by native_decide))
      have hRead := foldl_faithful_prefix_read_eq_final {ir.pm_graph_ref} pmStore {chunk0_prefix} {chunk0_read_tail} {joined1.joined_pm_tid} (by native_decide) (by native_decide)
      change ({chunk0_prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined1.joined_pm_tid} = pmFinal {joined1.joined_pm_tid} at hRead
      rw [hWriter, hRead, hPmId]
    have hChunk1 : pmFinal {ordinary.pm_tids[1]} = chunkPrimDimN 0 2 1 (pmFinal {joined0.joined_pm_tid}) := by
      have hWriter : pmFinal {ordinary.pm_tids[1]} = chunkPrimDimN 0 2 1 (({chunk1_prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined1.joined_pm_tid}) := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer {ir.pm_graph_ref} pmStore {chunk1_prefix} [] {_node_text(ch1)}
            {ch1.outs[0]} (fun t => chunkPrimDimN 0 2 1 (t {ch1.ins[0]})) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              unfold applyNodeDistributed
              rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
              · simpa only [show {ir.pm_graph_ref}.numRanks = 2 by native_decide] using
                  (applyNode_chunkPrimDimN_out {ir.pm_graph_ref} t 1 {ch1.ins[0]} {ch1.outs[0]} 0)
              · native_decide
              · native_decide
            ) (by native_decide) (by native_decide))
      have hRead := foldl_faithful_prefix_read_eq_final {ir.pm_graph_ref} pmStore {chunk1_prefix} {chunk1_read_tail} {joined1.joined_pm_tid} (by native_decide) (by native_decide)
      change ({chunk1_prefix}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) pmStore) {joined1.joined_pm_tid} = pmFinal {joined1.joined_pm_tid} at hRead
      rw [hWriter, hRead, hPmId]
    have hOrd : {ordinary.fact_id}.Holds smFinal pmFinal := by
      change GeneratedPatterns.Ordinary2Rel (smFinal {ordinary.sm_tid}) (pmFinal {ordinary.pm_tids[0]}) (pmFinal {ordinary.pm_tids[1]}) {shape} {shardshape}
      rw [hSmId]
      exact ReductionRel.to_ordinary_chunks_2d {rows} {hidden} hRed hReduce hChunk0 hChunk1 (by native_decide) (by native_decide)
    have hSh : {sharded.fact_id}.Holds smFinal pmFinal := by
      change ShardedRel (smFinal {sharded.sm_tid}) [pmFinal {sharded.pm_tids[0]}, pmFinal {sharded.pm_tids[1]}] 0 {shape} {shardshape}
      exact ShardedRel.ofOrdinary2_dim0_rank2 (rows := {rows}) (width := {hidden}) hOrd
    intro fact hfact
    have covered : fact ∈ [{ordinary.fact_id}, {joined0.fact_id}, {joined1.fact_id}, {sharded.fact_id}] ++ {before.state_id}.facts := (show {after.state_id}.facts ⊆ [{ordinary.fact_id}, {joined0.fact_id}, {joined1.fact_id}, {sharded.fact_id}] ++ {before.state_id}.facts by native_decide) hfact
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with (rfl | rfl | rfl | rfl) | old
    · exact hOrd
    · exact hJoined0
    · exact hJoined1
    · exact hSh
    · exact hframe fact old
'''
