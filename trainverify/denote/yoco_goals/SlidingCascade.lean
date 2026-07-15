/- Worker #20 — Sliding-window attention cascade (L1–L11) over `denoteGraph_ringAttn`.

   Layer 1 (`FW_attn_sliding_window` output `4750`) is a *chunk-based* drop-in of
   Worker #10's layer-0 gear `recon_attn_sliding_window_2tp_layer`: the PM graph
   feeds each shard by `ChunkPrim` of the shared SM Q'/K'/V (pm nodes
   `7619/7620` = chunk(4746), `7621/7622` = chunk(4747), `7607/7608` = chunk(4744)),
   exactly the layer-0 pattern. The ONLY missing pieces are the three upstream
   input reconstructions `4746`/`4747`/`4744` (Q'/K'/V for layer 1), which descend
   from the layer-0 residual + MoE all2all cascade (blocked on the upstream
   `4714` MoE-all2all reconstruction, owned by a concurrent worker). We therefore
   expose the layer-1 sliding reconstruction **conditional** on those three input
   value-equalities + PM shapes: `recon_intermediateGoal_4750_of_inputs`. The
   moment the residual/MoE chain lands `recon_intermediateGoal_4746/4747/4744`,
   the three hypotheses discharge to the unconditional
   `recon_intermediateGoal_4750_ringAttn` (statement kept below, commented, ready).

   Everything here is fully proven (zero `sorry`, zero user axiom; kernel triple +
   `native_decide`). The cu-seqlens leaves `4748`/`4749` are recovered
   unconditionally via `recon_weight` (they are replicated init leaves, shape [2],
   members of `initGoals`), exactly as layer 0 recovered `4694`/`4695`.

   L2–L11 sliding outputs (`4804`…`5290`) use a DIFFERENT PM feed: the shards are
   recomputed per-rank by `FW_rotary_embedding` (Q'/K') and
   `FW_per_head_mix_precision_linear` (V), not `ChunkPrim`. Their reconstruction
   fires Worker #15's `recon_attn_rotary_2tp_layer` gears at the Q'/K' boundary
   and then the sliding gear; those are blocked on the same upstream MoE cascade
   AND on the per-layer rotary-input reconstruction (positions + Q/K linear). See
   the firing-plan note at the bottom of this file.
-/
import denote.yoco_goals.IntermediateReconstruction

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### Layer-1 sliding-window node literals (chunk-fed, 2-tp) -/

def nSM_L1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4746, 4747, 4744, 4748, 4749], outs := [4750], params := [16, 4, 64, 64, 1, 512] }
def nR0_L1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7619, 7621, 7607, 4748, 4749], outs := [7623], params := [16, 4, 64, 64, 1, 512] }
def nR1_L1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7620, 7622, 7608, 4748, 4749], outs := [7624], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L1 : ringAttnBuddies sm nSM_L1 = [nSM_L1] := by native_decide
theorem buddy_r0_L1 : ringAttnBuddies pm nR0_L1 = [nR0_L1, nR1_L1] := by native_decide
theorem buddy_r1_L1 : ringAttnBuddies pm nR1_L1 = [nR0_L1, nR1_L1] := by native_decide

/-- Ring-denotation chunk reduction: a `ChunkPrim` node (dim 0) reduces the ring
    denotation of its output to `chunkPrimDimN 0 numRanks rank` of the ring
    denotation of its input. Layer-1 chunk nodes live *after* the layer-0
    ring-attention node, so the plain `pm_chunk_reduce` (which silently assumes
    ring=plain) is unsound here; this stays entirely in `denoteGraph_ringAttn`. -/
private theorem pm_chunk_reduce_ring (initPM : Store) (k rank inTid outTid : Nat)
    (hk : k < pm.nodes.length)
    (hnode : pm.nodes[k]'hk = { rank := rank, op := "OpName.ChunkPrim", ins := [inTid], outs := [outTid], params := [0] })
    (hdrop_nil : ∀ n ∈ pm.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ pm.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ pm.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph_ringAttn pm initPM outTid
      = chunkPrimDimN 0 pm.numRanks rank (denoteGraph_ringAttn pm initPM inTid) :=
  ringAttn_reduce1 pm initPM k
    { rank := rank, op := "OpName.ChunkPrim", ins := [inTid], outs := [outTid], params := [0] }
    inTid outTid (chunkPrimDimN 0 pm.numRanks rank)
    hk hnode
    (show ("OpName.ChunkPrim" : String) ≠ "OpName.FW_attn_zigzag" from by decide)
    (show ("OpName.ChunkPrim" : String) ≠ "OpName.FW_attn_sliding_window" from by decide)
    (fun s => applyNode_chunkPrimDimN_out pm s rank inTid outTid 0)
    hdrop_nil hdrop hpre_nil hpre

/-! ### Layer-1 sliding reconstruction, conditional on the Q'/K'/V inputs

    Faithful chunk-based port of `recon_intermediateGoal_4696_ringAttn` (layer 0)
    to layer 1. SM sliding node index 48; PM r0 index 144, r1 index 145; PM chunk
    nodes at indices 138–143. -/
set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4750_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hveq4746 : denoteGraph_ringAttn sm initSM 4746 = denoteGraph_ringAttn pm initPM 4746)
    (hveq4747 : denoteGraph_ringAttn sm initSM 4747 = denoteGraph_ringAttn pm initPM 4747)
    (hveq4744 : denoteGraph_ringAttn sm initSM 4744 = denoteGraph_ringAttn pm initPM 4744)
    (hpm4746_shape : (denoteGraph_ringAttn pm initPM 4746).shape = [2 * 2048, 16, 64])
    (hpm4747_shape : (denoteGraph_ringAttn pm initPM 4747).shape = [2 * 2048, 4, 64])
    (hpm4744_shape : (denoteGraph_ringAttn pm initPM 4744).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_4750
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves, recovered unconditionally)
  have hcu4748 : denoteGraph sm initSM 4748 = denoteGraph pm initPM 4748 :=
    recon_weight initSM initPM hInit initGoal_4748 (by native_decide) 4748 rfl rfl rfl rfl
  have hcu4749 : denoteGraph sm initSM 4749 = denoteGraph pm initPM 4749 :=
    recon_weight initSM initPM hInit initGoal_4749 (by native_decide) 4749 rfl rfl rfl rfl
  -- chunk-node value reductions (ring pm)
  have hc7619 : denoteGraph_ringAttn pm initPM 7619 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4746) :=
    pm_chunk_reduce_ring initPM 140 0 4746 7619 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7620 : denoteGraph_ringAttn pm initPM 7620 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4746) :=
    pm_chunk_reduce_ring initPM 142 1 4746 7620 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7621 : denoteGraph_ringAttn pm initPM 7621 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4747) :=
    pm_chunk_reduce_ring initPM 141 0 4747 7621 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7622 : denoteGraph_ringAttn pm initPM 7622 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4747) :=
    pm_chunk_reduce_ring initPM 143 1 4747 7622 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7607 : denoteGraph_ringAttn pm initPM 7607 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4744) :=
    pm_chunk_reduce_ring initPM 138 0 4744 7607 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7608 : denoteGraph_ringAttn pm initPM 7608 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4744) :=
    pm_chunk_reduce_ring initPM 139 1 4744 7608 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- prefix bridges (SM inputs): take-48 ring fold = full ring denotation
  have bSsm4746 : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4746 = denoteGraph_ringAttn sm initSM 4746 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4746 48 (by native_decide) (by native_decide)).symm
  have bSsm4747 : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4747 = denoteGraph_ringAttn sm initSM 4747 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4747 48 (by native_decide) (by native_decide)).symm
  have bSsm4744 : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4744 = denoteGraph_ringAttn sm initSM 4744 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4744 48 (by native_decide) (by native_decide)).symm
  -- prefix bridges (PM chunks over take-144 fold): ring fold = ring chunk of ring input
  have bSpm7619 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7619
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4746) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7619 144 (by native_decide) (by native_decide)]
    exact hc7619
  have bSpm7620 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7620
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4746) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7620 144 (by native_decide) (by native_decide)]
    exact hc7620
  have bSpm7621 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7621
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4747) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7621 144 (by native_decide) (by native_decide)]
    exact hc7621
  have bSpm7622 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7622
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4747) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7622 144 (by native_decide) (by native_decide)]
    exact hc7622
  have bSpm7607 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7607
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4744) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7607 144 (by native_decide) (by native_decide)]
    exact hc7607
  have bSpm7608 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7608
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4744) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7608 144 (by native_decide) (by native_decide)]
    exact hc7608
  -- input pm-side shapes
  have hpm4746s : (denoteGraph_ringAttn pm initPM 4746).shape = [2 * 2048, 16, 64] := hpm4746_shape
  have hpm4747s : (denoteGraph_ringAttn pm initPM 4747).shape = [2 * 2048, 4, 64] := hpm4747_shape
  have hpm4744s : (denoteGraph_ringAttn pm initPM 4744).shape = [2 * 2048, 4, 64] := hpm4744_shape
  -- full q/k/v reconstructions (store-level, gear form)
  have hq_full : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4746
      = allGatherPrimDimN 0 2 0
          [(pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7619,
           (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7620] := by
    rw [bSsm4746, bSpm7619, bSpm7620, hveq4746, show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
            (denoteGraph_ringAttn pm initPM 4746) hpm4746s).symm
  have hk_full : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4747
      = allGatherPrimDimN 0 2 0
          [(pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7621,
           (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7622] := by
    rw [bSsm4747, bSpm7621, bSpm7622, hveq4747, show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega)
            (denoteGraph_ringAttn pm initPM 4747) hpm4747s).symm
  have hv_full : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4744
      = allGatherPrimDimN 0 2 0
          [(pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7607,
           (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7608] := by
    rw [bSsm4744, bSpm7607, bSpm7608, hveq4744, show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega)
            (denoteGraph_ringAttn pm initPM 4744) hpm4744s).symm
  -- SM input nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM (nSM_L1.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4746).shape.length
    rw [bSsm4746, hveq4746, hpm4746s]; decide
  have hk_sm : 0 < ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM (nSM_L1.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4747).shape.length
    rw [bSsm4747, hveq4747, hpm4747s]; decide
  have hv_sm : 0 < ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM (nSM_L1.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4744).shape.length
    rw [bSsm4744, hveq4744, hpm4744s]; decide
  -- cu_seqlens equalities
  have hSM4748 : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4748 = denoteGraph sm initSM 4748 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4748 48 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4748 (by native_decide)
  have hSM4749 : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4749 = denoteGraph sm initSM 4749 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4749 48 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4749 (by native_decide)
  have hPM4748 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 4748 = denoteGraph pm initPM 4748 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4748 144 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4748 (by native_decide)
  have hPM4749 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 4749 = denoteGraph pm initPM 4749 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4749 144 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4749 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM (nSM_L1.ins.getD 3 0)
      = (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 3 0) := by
    show (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4748
        = (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 4748
    rw [hSM4748, hPM4748, hcu4748]
  have hcuK_sm_pm : (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM (nSM_L1.ins.getD 4 0)
      = (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 4 0) := by
    show (sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM 4749
        = (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 4749
    rw [hSM4749, hPM4749, hcu4749]
  -- full attention output shape (take-144 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 0 0),
                                  (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 1 0),
                                  (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 2 0),
                                  (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 2 0)])
        ((pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 3 0))
        ((pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 4 0))
        (nR0_L1.params.getD 0 1) (nR0_L1.params.getD 1 1) (nR0_L1.params.getD 2 1) (nR0_L1.params.getD 3 1)
        (decide (nR0_L1.params.getD 4 0 ≠ 0)) (nR0_L1.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7619,
                                    (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7620]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm4746, hveq4746, hpm4746s]
    rfl
  -- store bridge take144 -> take145 for r1 inputs
  have e7619 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7619
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7619 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7619 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have e7620 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7620
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7620 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7620 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have e7621 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7621
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7621 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7621 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have e7622 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7622
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7622 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7622 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have e7607 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7607
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7607 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7607 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have e7608 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 7608
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7608 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7608 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have e4748 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 4748
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 4748 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4748 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have e4749 : (pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM 4749
      = (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 4749 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4749 144 145 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM) nR1_L1
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM) nR1_L1 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L1]; intro m hm; fin_cases hm
      · exact e7619
      · exact e7620
    · rw [buddy_r1_L1]; intro m hm; fin_cases hm
      · exact e7621
      · exact e7622
    · rw [buddy_r1_L1]; intro m hm; fin_cases hm
      · exact e7607
      · exact e7608
    · exact e4748
    · exact e4749
  -- node reductions
  have hSM4750 : denoteGraph_ringAttn sm initSM 4750
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM) nSM_L1 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 4750 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4750 49 (by native_decide) (by native_decide),
        show sm.nodes.take 49 = sm.nodes.take 48 ++ [nSM_L1] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4746 4747 4744 4748 4749 4750 [16, 4, 64, 64, 1, 512]
  have hPM7623 : denoteGraph_ringAttn pm initPM 7623
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM) nR0_L1 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7623 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7623 145 (by native_decide) (by native_decide),
        show pm.nodes.take 145 = pm.nodes.take 144 ++ [nR0_L1] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 7619 7621 7607 4748 4749 7623 [16, 4, 64, 64, 1, 512]
  have hPM7624 : denoteGraph_ringAttn pm initPM 7624
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM) nR1_L1 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7624 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7624 146 (by native_decide) (by native_decide),
        show pm.nodes.take 146 = pm.nodes.take 145 ++ [nR1_L1] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 7620 7622 7608 4748 4749 7624 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-145 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 0 0),
                                  (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 1 0),
                                  (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR0_L1.ins.getD 2 0),
                                  (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 2 0)])
        ((pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 3 0))
        ((pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM (nR1_L1.ins.getD 4 0))
        (nR1_L1.params.getD 0 1) (nR1_L1.params.getD 1 1) (nR1_L1.params.getD 2 1) (nR1_L1.params.getD 3 1)
        (decide (nR1_L1.params.getD 4 0 ≠ 0)) (nR1_L1.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7619,
                                    (pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM 7620]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e7619, ← e7620, ← hq_full, bSsm4746, hveq4746, hpm4746s]
    rfl
  -- Fire the Worker #10 sliding-window gear on the layer-1 witnesses.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_4750
    nSM_L1 nR0_L1 nR1_L1
    ((sm.nodes.take 48).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 144).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 145).foldl (applyNodeRingAttn pm) initPM)
    4750 7623 7624 2048 16 64 (by omega) (by omega) (by omega)
    hSM4750 hPM7623 hPM7624 bridge_r1
    buddy_sm_L1 buddy_r0_L1 buddy_r1_L1 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl

end TrainVerify.Denote.GeneratedPatterns
