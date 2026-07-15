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

/-! ### Layer-2 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4800, 4801, 4798, 4802, 4803], outs := [4804], params := [16, 4, 64, 64, 1, 512] }
def nR0_L2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7805, 7807, 7793, 4802, 4803], outs := [7809], params := [16, 4, 64, 64, 1, 512] }
def nR1_L2 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7806, 7808, 7794, 4802, 4803], outs := [7810], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L2 : ringAttnBuddies sm nSM_L2 = [nSM_L2] := by native_decide
theorem buddy_r0_L2 : ringAttnBuddies pm nR0_L2 = [nR0_L2, nR1_L2] := by native_decide
theorem buddy_r1_L2 : ringAttnBuddies pm nR1_L2 = [nR0_L2, nR1_L2] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4804_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 4800
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7805, denoteGraph_ringAttn pm initPM 7806])
    (hk_recon : denoteGraph_ringAttn sm initSM 4801
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7807, denoteGraph_ringAttn pm initPM 7808])
    (hv_recon : denoteGraph_ringAttn sm initSM 4798
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7793, denoteGraph_ringAttn pm initPM 7794])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 4800).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 4801).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 4798).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_4804
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu4802 : denoteGraph sm initSM 4802 = denoteGraph pm initPM 4802 :=
    recon_weight initSM initPM hInit initGoal_4802 (by native_decide) 4802 rfl rfl rfl rfl
  have hcu4803 : denoteGraph sm initSM 4803 = denoteGraph pm initPM 4803 :=
    recon_weight initSM initPM hInit initGoal_4803 (by native_decide) 4803 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm4800 : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4800 = denoteGraph_ringAttn sm initSM 4800 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4800 87 (by native_decide) (by native_decide)).symm
  have bSsm4801 : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4801 = denoteGraph_ringAttn sm initSM 4801 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4801 87 (by native_decide) (by native_decide)).symm
  have bSsm4798 : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4798 = denoteGraph_ringAttn sm initSM 4798 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4798 87 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP7805 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7805 = denoteGraph_ringAttn pm initPM 7805 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7805 235 (by native_decide) (by native_decide)).symm
  have bP7806 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7806 = denoteGraph_ringAttn pm initPM 7806 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7806 235 (by native_decide) (by native_decide)).symm
  have bP7807 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7807 = denoteGraph_ringAttn pm initPM 7807 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7807 235 (by native_decide) (by native_decide)).symm
  have bP7808 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7808 = denoteGraph_ringAttn pm initPM 7808 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7808 235 (by native_decide) (by native_decide)).symm
  have bP7793 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7793 = denoteGraph_ringAttn pm initPM 7793 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7793 235 (by native_decide) (by native_decide)).symm
  have bP7794 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7794 = denoteGraph_ringAttn pm initPM 7794 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7794 235 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4800
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7805, (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7806] := by
    rw [bSsm4800, bP7805, bP7806]; exact hq_recon
  have hk_full : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4801
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7807, (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7808] := by
    rw [bSsm4801, bP7807, bP7808]; exact hk_recon
  have hv_full : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4798
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7793, (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7794] := by
    rw [bSsm4798, bP7793, bP7794]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM (nSM_L2.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4800).shape.length
    rw [bSsm4800, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM (nSM_L2.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4801).shape.length
    rw [bSsm4801, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM (nSM_L2.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4798).shape.length
    rw [bSsm4798, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM4802 : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4802 = denoteGraph sm initSM 4802 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4802 87 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4802 (by native_decide)
  have hSM4803 : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4803 = denoteGraph sm initSM 4803 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4803 87 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4803 (by native_decide)
  have hPM4802 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 4802 = denoteGraph pm initPM 4802 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4802 235 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4802 (by native_decide)
  have hPM4803 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 4803 = denoteGraph pm initPM 4803 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4803 235 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4803 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM (nSM_L2.ins.getD 3 0)
      = (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 3 0) := by
    show (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4802 = (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 4802
    rw [hSM4802, hPM4802, hcu4802]
  have hcuK_sm_pm : (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM (nSM_L2.ins.getD 4 0)
      = (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 4 0) := by
    show (sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM 4803 = (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 4803
    rw [hSM4803, hPM4803, hcu4803]
  -- full attention output shape (take-235 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 0 0), (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 1 0), (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 2 0), (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 2 0)])
        ((pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 3 0))
        ((pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 4 0))
        (nR0_L2.params.getD 0 1) (nR0_L2.params.getD 1 1) (nR0_L2.params.getD 2 1) (nR0_L2.params.getD 3 1)
        (decide (nR0_L2.params.getD 4 0 ≠ 0)) (nR0_L2.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7805, (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7806]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm4800, hq_sm_shape]
    rfl
  -- take-235 -> take-236 bridges for r1 inputs
  have e7805 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7805 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7805 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7805 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have e7806 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7806 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7806 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7806 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have e7807 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7807 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7807 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7807 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have e7808 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7808 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7808 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7808 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have e7793 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7793 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7793 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7793 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have e7794 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 7794 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7794 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7794 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have e4802 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 4802 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 4802 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4802 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have e4803 : (pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM 4803 = (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 4803 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4803 235 236 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM) nR1_L2
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM) nR1_L2 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L2]; intro m hm; fin_cases hm
      · exact e7805
      · exact e7806
    · rw [buddy_r1_L2]; intro m hm; fin_cases hm
      · exact e7807
      · exact e7808
    · rw [buddy_r1_L2]; intro m hm; fin_cases hm
      · exact e7793
      · exact e7794
    · exact e4802
    · exact e4803
  -- node reductions
  have hSM4804 : denoteGraph_ringAttn sm initSM 4804
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM) nSM_L2 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 4804 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4804 88 (by native_decide) (by native_decide),
        show sm.nodes.take 88 = sm.nodes.take 87 ++ [nSM_L2] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4800 4801 4798 4802 4803 4804 [16, 4, 64, 64, 1, 512]
  have hPM7809 : denoteGraph_ringAttn pm initPM 7809
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM) nR0_L2 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7809 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7809 236 (by native_decide) (by native_decide),
        show pm.nodes.take 236 = pm.nodes.take 235 ++ [nR0_L2] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 7805 7807 7793 4802 4803 7809 [16, 4, 64, 64, 1, 512]
  have hPM7810 : denoteGraph_ringAttn pm initPM 7810
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM) nR1_L2 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7810 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7810 237 (by native_decide) (by native_decide),
        show pm.nodes.take 237 = pm.nodes.take 236 ++ [nR1_L2] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 7806 7808 7794 4802 4803 7810 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-236 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 0 0), (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 1 0), (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR0_L2.ins.getD 2 0), (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 2 0)])
        ((pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 3 0))
        ((pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM (nR1_L2.ins.getD 4 0))
        (nR1_L2.params.getD 0 1) (nR1_L2.params.getD 1 1) (nR1_L2.params.getD 2 1) (nR1_L2.params.getD 3 1)
        (decide (nR1_L2.params.getD 4 0 ≠ 0)) (nR1_L2.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7805, (pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM 7806]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e7805, ← e7806, ← hq_full, bSsm4800, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_4804
    nSM_L2 nR0_L2 nR1_L2
    ((sm.nodes.take 87).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 235).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 236).foldl (applyNodeRingAttn pm) initPM)
    4804 7809 7810 2048 16 64 (by omega) (by omega) (by omega)
    hSM4804 hPM7809 hPM7810 bridge_r1
    buddy_sm_L2 buddy_r0_L2 buddy_r1_L2 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl



/-! ### Layer-3 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L3 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4854, 4855, 4852, 4856, 4857], outs := [4858], params := [16, 4, 64, 64, 1, 512] }
def nR0_L3 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7991, 7993, 7979, 4856, 4857], outs := [7995], params := [16, 4, 64, 64, 1, 512] }
def nR1_L3 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7992, 7994, 7980, 4856, 4857], outs := [7996], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L3 : ringAttnBuddies sm nSM_L3 = [nSM_L3] := by native_decide
theorem buddy_r0_L3 : ringAttnBuddies pm nR0_L3 = [nR0_L3, nR1_L3] := by native_decide
theorem buddy_r1_L3 : ringAttnBuddies pm nR1_L3 = [nR0_L3, nR1_L3] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4858_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 4854
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7991, denoteGraph_ringAttn pm initPM 7992])
    (hk_recon : denoteGraph_ringAttn sm initSM 4855
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7993, denoteGraph_ringAttn pm initPM 7994])
    (hv_recon : denoteGraph_ringAttn sm initSM 4852
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7979, denoteGraph_ringAttn pm initPM 7980])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 4854).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 4855).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 4852).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_4858
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu4856 : denoteGraph sm initSM 4856 = denoteGraph pm initPM 4856 :=
    recon_weight initSM initPM hInit initGoal_4856 (by native_decide) 4856 rfl rfl rfl rfl
  have hcu4857 : denoteGraph sm initSM 4857 = denoteGraph pm initPM 4857 :=
    recon_weight initSM initPM hInit initGoal_4857 (by native_decide) 4857 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm4854 : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4854 = denoteGraph_ringAttn sm initSM 4854 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4854 126 (by native_decide) (by native_decide)).symm
  have bSsm4855 : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4855 = denoteGraph_ringAttn sm initSM 4855 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4855 126 (by native_decide) (by native_decide)).symm
  have bSsm4852 : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4852 = denoteGraph_ringAttn sm initSM 4852 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4852 126 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP7991 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7991 = denoteGraph_ringAttn pm initPM 7991 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7991 313 (by native_decide) (by native_decide)).symm
  have bP7992 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7992 = denoteGraph_ringAttn pm initPM 7992 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7992 313 (by native_decide) (by native_decide)).symm
  have bP7993 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7993 = denoteGraph_ringAttn pm initPM 7993 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7993 313 (by native_decide) (by native_decide)).symm
  have bP7994 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7994 = denoteGraph_ringAttn pm initPM 7994 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7994 313 (by native_decide) (by native_decide)).symm
  have bP7979 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7979 = denoteGraph_ringAttn pm initPM 7979 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7979 313 (by native_decide) (by native_decide)).symm
  have bP7980 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7980 = denoteGraph_ringAttn pm initPM 7980 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7980 313 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4854
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7991, (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7992] := by
    rw [bSsm4854, bP7991, bP7992]; exact hq_recon
  have hk_full : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4855
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7993, (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7994] := by
    rw [bSsm4855, bP7993, bP7994]; exact hk_recon
  have hv_full : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4852
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7979, (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7980] := by
    rw [bSsm4852, bP7979, bP7980]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM (nSM_L3.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4854).shape.length
    rw [bSsm4854, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM (nSM_L3.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4855).shape.length
    rw [bSsm4855, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM (nSM_L3.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4852).shape.length
    rw [bSsm4852, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM4856 : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4856 = denoteGraph sm initSM 4856 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4856 126 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4856 (by native_decide)
  have hSM4857 : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4857 = denoteGraph sm initSM 4857 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4857 126 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4857 (by native_decide)
  have hPM4856 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 4856 = denoteGraph pm initPM 4856 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4856 313 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4856 (by native_decide)
  have hPM4857 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 4857 = denoteGraph pm initPM 4857 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4857 313 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4857 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM (nSM_L3.ins.getD 3 0)
      = (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 3 0) := by
    show (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4856 = (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 4856
    rw [hSM4856, hPM4856, hcu4856]
  have hcuK_sm_pm : (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM (nSM_L3.ins.getD 4 0)
      = (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 4 0) := by
    show (sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM 4857 = (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 4857
    rw [hSM4857, hPM4857, hcu4857]
  -- full attention output shape (take-313 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 0 0), (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 1 0), (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 2 0), (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 2 0)])
        ((pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 3 0))
        ((pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 4 0))
        (nR0_L3.params.getD 0 1) (nR0_L3.params.getD 1 1) (nR0_L3.params.getD 2 1) (nR0_L3.params.getD 3 1)
        (decide (nR0_L3.params.getD 4 0 ≠ 0)) (nR0_L3.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7991, (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7992]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm4854, hq_sm_shape]
    rfl
  -- take-313 -> take-314 bridges for r1 inputs
  have e7991 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7991 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7991 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7991 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have e7992 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7992 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7992 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7992 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have e7993 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7993 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7993 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7993 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have e7994 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7994 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7994 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7994 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have e7979 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7979 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7979 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7979 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have e7980 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 7980 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7980 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7980 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have e4856 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 4856 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 4856 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4856 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have e4857 : (pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM 4857 = (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 4857 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4857 313 314 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM) nR1_L3
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM) nR1_L3 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L3]; intro m hm; fin_cases hm
      · exact e7991
      · exact e7992
    · rw [buddy_r1_L3]; intro m hm; fin_cases hm
      · exact e7993
      · exact e7994
    · rw [buddy_r1_L3]; intro m hm; fin_cases hm
      · exact e7979
      · exact e7980
    · exact e4856
    · exact e4857
  -- node reductions
  have hSM4858 : denoteGraph_ringAttn sm initSM 4858
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM) nSM_L3 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 4858 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4858 127 (by native_decide) (by native_decide),
        show sm.nodes.take 127 = sm.nodes.take 126 ++ [nSM_L3] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4854 4855 4852 4856 4857 4858 [16, 4, 64, 64, 1, 512]
  have hPM7995 : denoteGraph_ringAttn pm initPM 7995
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM) nR0_L3 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7995 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7995 314 (by native_decide) (by native_decide),
        show pm.nodes.take 314 = pm.nodes.take 313 ++ [nR0_L3] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 7991 7993 7979 4856 4857 7995 [16, 4, 64, 64, 1, 512]
  have hPM7996 : denoteGraph_ringAttn pm initPM 7996
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM) nR1_L3 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7996 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7996 315 (by native_decide) (by native_decide),
        show pm.nodes.take 315 = pm.nodes.take 314 ++ [nR1_L3] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 7992 7994 7980 4856 4857 7996 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-314 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 0 0), (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 1 0), (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR0_L3.ins.getD 2 0), (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 2 0)])
        ((pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 3 0))
        ((pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM (nR1_L3.ins.getD 4 0))
        (nR1_L3.params.getD 0 1) (nR1_L3.params.getD 1 1) (nR1_L3.params.getD 2 1) (nR1_L3.params.getD 3 1)
        (decide (nR1_L3.params.getD 4 0 ≠ 0)) (nR1_L3.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7991, (pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM 7992]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e7991, ← e7992, ← hq_full, bSsm4854, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_4858
    nSM_L3 nR0_L3 nR1_L3
    ((sm.nodes.take 126).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 313).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 314).foldl (applyNodeRingAttn pm) initPM)
    4858 7995 7996 2048 16 64 (by omega) (by omega) (by omega)
    hSM4858 hPM7995 hPM7996 bridge_r1
    buddy_sm_L3 buddy_r0_L3 buddy_r1_L3 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-4 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L4 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4908, 4909, 4906, 4910, 4911], outs := [4912], params := [16, 4, 64, 64, 1, 512] }
def nR0_L4 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8177, 8179, 8165, 4910, 4911], outs := [8181], params := [16, 4, 64, 64, 1, 512] }
def nR1_L4 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8178, 8180, 8166, 4910, 4911], outs := [8182], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L4 : ringAttnBuddies sm nSM_L4 = [nSM_L4] := by native_decide
theorem buddy_r0_L4 : ringAttnBuddies pm nR0_L4 = [nR0_L4, nR1_L4] := by native_decide
theorem buddy_r1_L4 : ringAttnBuddies pm nR1_L4 = [nR0_L4, nR1_L4] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4912_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 4908
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8177, denoteGraph_ringAttn pm initPM 8178])
    (hk_recon : denoteGraph_ringAttn sm initSM 4909
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8179, denoteGraph_ringAttn pm initPM 8180])
    (hv_recon : denoteGraph_ringAttn sm initSM 4906
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8165, denoteGraph_ringAttn pm initPM 8166])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 4908).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 4909).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 4906).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_4912
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu4910 : denoteGraph sm initSM 4910 = denoteGraph pm initPM 4910 :=
    recon_weight initSM initPM hInit initGoal_4910 (by native_decide) 4910 rfl rfl rfl rfl
  have hcu4911 : denoteGraph sm initSM 4911 = denoteGraph pm initPM 4911 :=
    recon_weight initSM initPM hInit initGoal_4911 (by native_decide) 4911 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm4908 : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4908 = denoteGraph_ringAttn sm initSM 4908 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4908 165 (by native_decide) (by native_decide)).symm
  have bSsm4909 : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4909 = denoteGraph_ringAttn sm initSM 4909 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4909 165 (by native_decide) (by native_decide)).symm
  have bSsm4906 : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4906 = denoteGraph_ringAttn sm initSM 4906 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4906 165 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP8177 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8177 = denoteGraph_ringAttn pm initPM 8177 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8177 391 (by native_decide) (by native_decide)).symm
  have bP8178 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8178 = denoteGraph_ringAttn pm initPM 8178 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8178 391 (by native_decide) (by native_decide)).symm
  have bP8179 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8179 = denoteGraph_ringAttn pm initPM 8179 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8179 391 (by native_decide) (by native_decide)).symm
  have bP8180 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8180 = denoteGraph_ringAttn pm initPM 8180 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8180 391 (by native_decide) (by native_decide)).symm
  have bP8165 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8165 = denoteGraph_ringAttn pm initPM 8165 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8165 391 (by native_decide) (by native_decide)).symm
  have bP8166 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8166 = denoteGraph_ringAttn pm initPM 8166 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8166 391 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4908
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8177, (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8178] := by
    rw [bSsm4908, bP8177, bP8178]; exact hq_recon
  have hk_full : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4909
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8179, (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8180] := by
    rw [bSsm4909, bP8179, bP8180]; exact hk_recon
  have hv_full : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4906
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8165, (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8166] := by
    rw [bSsm4906, bP8165, bP8166]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM (nSM_L4.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4908).shape.length
    rw [bSsm4908, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM (nSM_L4.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4909).shape.length
    rw [bSsm4909, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM (nSM_L4.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4906).shape.length
    rw [bSsm4906, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM4910 : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4910 = denoteGraph sm initSM 4910 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4910 165 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4910 (by native_decide)
  have hSM4911 : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4911 = denoteGraph sm initSM 4911 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4911 165 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4911 (by native_decide)
  have hPM4910 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 4910 = denoteGraph pm initPM 4910 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4910 391 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4910 (by native_decide)
  have hPM4911 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 4911 = denoteGraph pm initPM 4911 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4911 391 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4911 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM (nSM_L4.ins.getD 3 0)
      = (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 3 0) := by
    show (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4910 = (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 4910
    rw [hSM4910, hPM4910, hcu4910]
  have hcuK_sm_pm : (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM (nSM_L4.ins.getD 4 0)
      = (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 4 0) := by
    show (sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM 4911 = (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 4911
    rw [hSM4911, hPM4911, hcu4911]
  -- full attention output shape (take-391 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 0 0), (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 1 0), (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 2 0), (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 2 0)])
        ((pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 3 0))
        ((pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 4 0))
        (nR0_L4.params.getD 0 1) (nR0_L4.params.getD 1 1) (nR0_L4.params.getD 2 1) (nR0_L4.params.getD 3 1)
        (decide (nR0_L4.params.getD 4 0 ≠ 0)) (nR0_L4.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8177, (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8178]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm4908, hq_sm_shape]
    rfl
  -- take-391 -> take-392 bridges for r1 inputs
  have e8177 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8177 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8177 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8177 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have e8178 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8178 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8178 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8178 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have e8179 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8179 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8179 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8179 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have e8180 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8180 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8180 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8180 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have e8165 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8165 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8165 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8165 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have e8166 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 8166 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8166 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8166 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have e4910 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 4910 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 4910 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4910 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have e4911 : (pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM 4911 = (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 4911 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4911 391 392 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM) nR1_L4
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM) nR1_L4 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L4]; intro m hm; fin_cases hm
      · exact e8177
      · exact e8178
    · rw [buddy_r1_L4]; intro m hm; fin_cases hm
      · exact e8179
      · exact e8180
    · rw [buddy_r1_L4]; intro m hm; fin_cases hm
      · exact e8165
      · exact e8166
    · exact e4910
    · exact e4911
  -- node reductions
  have hSM4912 : denoteGraph_ringAttn sm initSM 4912
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM) nSM_L4 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 4912 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4912 166 (by native_decide) (by native_decide),
        show sm.nodes.take 166 = sm.nodes.take 165 ++ [nSM_L4] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4908 4909 4906 4910 4911 4912 [16, 4, 64, 64, 1, 512]
  have hPM8181 : denoteGraph_ringAttn pm initPM 8181
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM) nR0_L4 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8181 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8181 392 (by native_decide) (by native_decide),
        show pm.nodes.take 392 = pm.nodes.take 391 ++ [nR0_L4] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8177 8179 8165 4910 4911 8181 [16, 4, 64, 64, 1, 512]
  have hPM8182 : denoteGraph_ringAttn pm initPM 8182
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM) nR1_L4 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8182 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8182 393 (by native_decide) (by native_decide),
        show pm.nodes.take 393 = pm.nodes.take 392 ++ [nR1_L4] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8178 8180 8166 4910 4911 8182 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-392 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 0 0), (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 1 0), (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR0_L4.ins.getD 2 0), (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 2 0)])
        ((pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 3 0))
        ((pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM (nR1_L4.ins.getD 4 0))
        (nR1_L4.params.getD 0 1) (nR1_L4.params.getD 1 1) (nR1_L4.params.getD 2 1) (nR1_L4.params.getD 3 1)
        (decide (nR1_L4.params.getD 4 0 ≠ 0)) (nR1_L4.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8177, (pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM 8178]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e8177, ← e8178, ← hq_full, bSsm4908, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_4912
    nSM_L4 nR0_L4 nR1_L4
    ((sm.nodes.take 165).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 391).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 392).foldl (applyNodeRingAttn pm) initPM)
    4912 8181 8182 2048 16 64 (by omega) (by omega) (by omega)
    hSM4912 hPM8181 hPM8182 bridge_r1
    buddy_sm_L4 buddy_r0_L4 buddy_r1_L4 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-5 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4962, 4963, 4960, 4964, 4965], outs := [4966], params := [16, 4, 64, 64, 1, 512] }
def nR0_L5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8363, 8365, 8351, 4964, 4965], outs := [8367], params := [16, 4, 64, 64, 1, 512] }
def nR1_L5 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8364, 8366, 8352, 4964, 4965], outs := [8368], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L5 : ringAttnBuddies sm nSM_L5 = [nSM_L5] := by native_decide
theorem buddy_r0_L5 : ringAttnBuddies pm nR0_L5 = [nR0_L5, nR1_L5] := by native_decide
theorem buddy_r1_L5 : ringAttnBuddies pm nR1_L5 = [nR0_L5, nR1_L5] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4966_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 4962
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8363, denoteGraph_ringAttn pm initPM 8364])
    (hk_recon : denoteGraph_ringAttn sm initSM 4963
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8365, denoteGraph_ringAttn pm initPM 8366])
    (hv_recon : denoteGraph_ringAttn sm initSM 4960
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8351, denoteGraph_ringAttn pm initPM 8352])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 4962).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 4963).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 4960).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_4966
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu4964 : denoteGraph sm initSM 4964 = denoteGraph pm initPM 4964 :=
    recon_weight initSM initPM hInit initGoal_4964 (by native_decide) 4964 rfl rfl rfl rfl
  have hcu4965 : denoteGraph sm initSM 4965 = denoteGraph pm initPM 4965 :=
    recon_weight initSM initPM hInit initGoal_4965 (by native_decide) 4965 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm4962 : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4962 = denoteGraph_ringAttn sm initSM 4962 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4962 204 (by native_decide) (by native_decide)).symm
  have bSsm4963 : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4963 = denoteGraph_ringAttn sm initSM 4963 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4963 204 (by native_decide) (by native_decide)).symm
  have bSsm4960 : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4960 = denoteGraph_ringAttn sm initSM 4960 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4960 204 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP8363 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8363 = denoteGraph_ringAttn pm initPM 8363 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8363 469 (by native_decide) (by native_decide)).symm
  have bP8364 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8364 = denoteGraph_ringAttn pm initPM 8364 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8364 469 (by native_decide) (by native_decide)).symm
  have bP8365 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8365 = denoteGraph_ringAttn pm initPM 8365 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8365 469 (by native_decide) (by native_decide)).symm
  have bP8366 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8366 = denoteGraph_ringAttn pm initPM 8366 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8366 469 (by native_decide) (by native_decide)).symm
  have bP8351 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8351 = denoteGraph_ringAttn pm initPM 8351 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8351 469 (by native_decide) (by native_decide)).symm
  have bP8352 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8352 = denoteGraph_ringAttn pm initPM 8352 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8352 469 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4962
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8363, (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8364] := by
    rw [bSsm4962, bP8363, bP8364]; exact hq_recon
  have hk_full : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4963
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8365, (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8366] := by
    rw [bSsm4963, bP8365, bP8366]; exact hk_recon
  have hv_full : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4960
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8351, (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8352] := by
    rw [bSsm4960, bP8351, bP8352]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM (nSM_L5.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4962).shape.length
    rw [bSsm4962, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM (nSM_L5.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4963).shape.length
    rw [bSsm4963, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM (nSM_L5.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4960).shape.length
    rw [bSsm4960, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM4964 : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4964 = denoteGraph sm initSM 4964 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4964 204 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4964 (by native_decide)
  have hSM4965 : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4965 = denoteGraph sm initSM 4965 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4965 204 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4965 (by native_decide)
  have hPM4964 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 4964 = denoteGraph pm initPM 4964 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4964 469 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4964 (by native_decide)
  have hPM4965 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 4965 = denoteGraph pm initPM 4965 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4965 469 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4965 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM (nSM_L5.ins.getD 3 0)
      = (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 3 0) := by
    show (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4964 = (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 4964
    rw [hSM4964, hPM4964, hcu4964]
  have hcuK_sm_pm : (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM (nSM_L5.ins.getD 4 0)
      = (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 4 0) := by
    show (sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM 4965 = (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 4965
    rw [hSM4965, hPM4965, hcu4965]
  -- full attention output shape (take-469 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 0 0), (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 1 0), (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 2 0), (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 2 0)])
        ((pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 3 0))
        ((pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 4 0))
        (nR0_L5.params.getD 0 1) (nR0_L5.params.getD 1 1) (nR0_L5.params.getD 2 1) (nR0_L5.params.getD 3 1)
        (decide (nR0_L5.params.getD 4 0 ≠ 0)) (nR0_L5.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8363, (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8364]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm4962, hq_sm_shape]
    rfl
  -- take-469 -> take-470 bridges for r1 inputs
  have e8363 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8363 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8363 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8363 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have e8364 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8364 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8364 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8364 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have e8365 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8365 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8365 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8365 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have e8366 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8366 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8366 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8366 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have e8351 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8351 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8351 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8351 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have e8352 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 8352 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8352 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8352 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have e4964 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 4964 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 4964 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4964 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have e4965 : (pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM 4965 = (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 4965 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4965 469 470 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM) nR1_L5
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM) nR1_L5 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L5]; intro m hm; fin_cases hm
      · exact e8363
      · exact e8364
    · rw [buddy_r1_L5]; intro m hm; fin_cases hm
      · exact e8365
      · exact e8366
    · rw [buddy_r1_L5]; intro m hm; fin_cases hm
      · exact e8351
      · exact e8352
    · exact e4964
    · exact e4965
  -- node reductions
  have hSM4966 : denoteGraph_ringAttn sm initSM 4966
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM) nSM_L5 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 4966 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4966 205 (by native_decide) (by native_decide),
        show sm.nodes.take 205 = sm.nodes.take 204 ++ [nSM_L5] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4962 4963 4960 4964 4965 4966 [16, 4, 64, 64, 1, 512]
  have hPM8367 : denoteGraph_ringAttn pm initPM 8367
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM) nR0_L5 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8367 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8367 470 (by native_decide) (by native_decide),
        show pm.nodes.take 470 = pm.nodes.take 469 ++ [nR0_L5] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8363 8365 8351 4964 4965 8367 [16, 4, 64, 64, 1, 512]
  have hPM8368 : denoteGraph_ringAttn pm initPM 8368
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM) nR1_L5 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8368 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8368 471 (by native_decide) (by native_decide),
        show pm.nodes.take 471 = pm.nodes.take 470 ++ [nR1_L5] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8364 8366 8352 4964 4965 8368 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-470 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 0 0), (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 1 0), (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR0_L5.ins.getD 2 0), (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 2 0)])
        ((pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 3 0))
        ((pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM (nR1_L5.ins.getD 4 0))
        (nR1_L5.params.getD 0 1) (nR1_L5.params.getD 1 1) (nR1_L5.params.getD 2 1) (nR1_L5.params.getD 3 1)
        (decide (nR1_L5.params.getD 4 0 ≠ 0)) (nR1_L5.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8363, (pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM 8364]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e8363, ← e8364, ← hq_full, bSsm4962, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_4966
    nSM_L5 nR0_L5 nR1_L5
    ((sm.nodes.take 204).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 469).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 470).foldl (applyNodeRingAttn pm) initPM)
    4966 8367 8368 2048 16 64 (by omega) (by omega) (by omega)
    hSM4966 hPM8367 hPM8368 bridge_r1
    buddy_sm_L5 buddy_r0_L5 buddy_r1_L5 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-6 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L6 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5016, 5017, 5014, 5018, 5019], outs := [5020], params := [16, 4, 64, 64, 1, 512] }
def nR0_L6 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8549, 8551, 8537, 5018, 5019], outs := [8553], params := [16, 4, 64, 64, 1, 512] }
def nR1_L6 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8550, 8552, 8538, 5018, 5019], outs := [8554], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L6 : ringAttnBuddies sm nSM_L6 = [nSM_L6] := by native_decide
theorem buddy_r0_L6 : ringAttnBuddies pm nR0_L6 = [nR0_L6, nR1_L6] := by native_decide
theorem buddy_r1_L6 : ringAttnBuddies pm nR1_L6 = [nR0_L6, nR1_L6] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_5020_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 5016
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8549, denoteGraph_ringAttn pm initPM 8550])
    (hk_recon : denoteGraph_ringAttn sm initSM 5017
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8551, denoteGraph_ringAttn pm initPM 8552])
    (hv_recon : denoteGraph_ringAttn sm initSM 5014
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8537, denoteGraph_ringAttn pm initPM 8538])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 5016).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 5017).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 5014).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5020
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu5018 : denoteGraph sm initSM 5018 = denoteGraph pm initPM 5018 :=
    recon_weight initSM initPM hInit initGoal_5018 (by native_decide) 5018 rfl rfl rfl rfl
  have hcu5019 : denoteGraph sm initSM 5019 = denoteGraph pm initPM 5019 :=
    recon_weight initSM initPM hInit initGoal_5019 (by native_decide) 5019 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm5016 : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5016 = denoteGraph_ringAttn sm initSM 5016 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5016 243 (by native_decide) (by native_decide)).symm
  have bSsm5017 : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5017 = denoteGraph_ringAttn sm initSM 5017 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5017 243 (by native_decide) (by native_decide)).symm
  have bSsm5014 : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5014 = denoteGraph_ringAttn sm initSM 5014 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5014 243 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP8549 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8549 = denoteGraph_ringAttn pm initPM 8549 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8549 547 (by native_decide) (by native_decide)).symm
  have bP8550 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8550 = denoteGraph_ringAttn pm initPM 8550 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8550 547 (by native_decide) (by native_decide)).symm
  have bP8551 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8551 = denoteGraph_ringAttn pm initPM 8551 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8551 547 (by native_decide) (by native_decide)).symm
  have bP8552 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8552 = denoteGraph_ringAttn pm initPM 8552 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8552 547 (by native_decide) (by native_decide)).symm
  have bP8537 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8537 = denoteGraph_ringAttn pm initPM 8537 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8537 547 (by native_decide) (by native_decide)).symm
  have bP8538 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8538 = denoteGraph_ringAttn pm initPM 8538 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8538 547 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5016
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8549, (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8550] := by
    rw [bSsm5016, bP8549, bP8550]; exact hq_recon
  have hk_full : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5017
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8551, (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8552] := by
    rw [bSsm5017, bP8551, bP8552]; exact hk_recon
  have hv_full : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5014
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8537, (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8538] := by
    rw [bSsm5014, bP8537, bP8538]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM (nSM_L6.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5016).shape.length
    rw [bSsm5016, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM (nSM_L6.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5017).shape.length
    rw [bSsm5017, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM (nSM_L6.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5014).shape.length
    rw [bSsm5014, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM5018 : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5018 = denoteGraph sm initSM 5018 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5018 243 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5018 (by native_decide)
  have hSM5019 : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5019 = denoteGraph sm initSM 5019 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5019 243 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5019 (by native_decide)
  have hPM5018 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 5018 = denoteGraph pm initPM 5018 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5018 547 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5018 (by native_decide)
  have hPM5019 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 5019 = denoteGraph pm initPM 5019 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5019 547 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5019 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM (nSM_L6.ins.getD 3 0)
      = (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 3 0) := by
    show (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5018 = (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 5018
    rw [hSM5018, hPM5018, hcu5018]
  have hcuK_sm_pm : (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM (nSM_L6.ins.getD 4 0)
      = (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 4 0) := by
    show (sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM 5019 = (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 5019
    rw [hSM5019, hPM5019, hcu5019]
  -- full attention output shape (take-547 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 0 0), (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 1 0), (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 2 0), (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 2 0)])
        ((pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 3 0))
        ((pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 4 0))
        (nR0_L6.params.getD 0 1) (nR0_L6.params.getD 1 1) (nR0_L6.params.getD 2 1) (nR0_L6.params.getD 3 1)
        (decide (nR0_L6.params.getD 4 0 ≠ 0)) (nR0_L6.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8549, (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8550]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm5016, hq_sm_shape]
    rfl
  -- take-547 -> take-548 bridges for r1 inputs
  have e8549 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8549 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8549 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8549 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have e8550 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8550 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8550 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8550 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have e8551 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8551 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8551 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8551 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have e8552 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8552 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8552 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8552 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have e8537 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8537 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8537 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8537 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have e8538 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 8538 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8538 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8538 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have e5018 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 5018 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 5018 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5018 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have e5019 : (pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM 5019 = (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 5019 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5019 547 548 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM) nR1_L6
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM) nR1_L6 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L6]; intro m hm; fin_cases hm
      · exact e8549
      · exact e8550
    · rw [buddy_r1_L6]; intro m hm; fin_cases hm
      · exact e8551
      · exact e8552
    · rw [buddy_r1_L6]; intro m hm; fin_cases hm
      · exact e8537
      · exact e8538
    · exact e5018
    · exact e5019
  -- node reductions
  have hSM5020 : denoteGraph_ringAttn sm initSM 5020
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM) nSM_L6 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5020 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5020 244 (by native_decide) (by native_decide),
        show sm.nodes.take 244 = sm.nodes.take 243 ++ [nSM_L6] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5016 5017 5014 5018 5019 5020 [16, 4, 64, 64, 1, 512]
  have hPM8553 : denoteGraph_ringAttn pm initPM 8553
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM) nR0_L6 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8553 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8553 548 (by native_decide) (by native_decide),
        show pm.nodes.take 548 = pm.nodes.take 547 ++ [nR0_L6] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8549 8551 8537 5018 5019 8553 [16, 4, 64, 64, 1, 512]
  have hPM8554 : denoteGraph_ringAttn pm initPM 8554
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM) nR1_L6 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8554 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8554 549 (by native_decide) (by native_decide),
        show pm.nodes.take 549 = pm.nodes.take 548 ++ [nR1_L6] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8550 8552 8538 5018 5019 8554 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-548 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 0 0), (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 1 0), (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR0_L6.ins.getD 2 0), (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 2 0)])
        ((pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 3 0))
        ((pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM (nR1_L6.ins.getD 4 0))
        (nR1_L6.params.getD 0 1) (nR1_L6.params.getD 1 1) (nR1_L6.params.getD 2 1) (nR1_L6.params.getD 3 1)
        (decide (nR1_L6.params.getD 4 0 ≠ 0)) (nR1_L6.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8549, (pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM 8550]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e8549, ← e8550, ← hq_full, bSsm5016, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_5020
    nSM_L6 nR0_L6 nR1_L6
    ((sm.nodes.take 243).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 547).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 548).foldl (applyNodeRingAttn pm) initPM)
    5020 8553 8554 2048 16 64 (by omega) (by omega) (by omega)
    hSM5020 hPM8553 hPM8554 bridge_r1
    buddy_sm_L6 buddy_r0_L6 buddy_r1_L6 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-7 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L7 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5070, 5071, 5068, 5072, 5073], outs := [5074], params := [16, 4, 64, 64, 1, 512] }
def nR0_L7 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8735, 8737, 8723, 5072, 5073], outs := [8739], params := [16, 4, 64, 64, 1, 512] }
def nR1_L7 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8736, 8738, 8724, 5072, 5073], outs := [8740], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L7 : ringAttnBuddies sm nSM_L7 = [nSM_L7] := by native_decide
theorem buddy_r0_L7 : ringAttnBuddies pm nR0_L7 = [nR0_L7, nR1_L7] := by native_decide
theorem buddy_r1_L7 : ringAttnBuddies pm nR1_L7 = [nR0_L7, nR1_L7] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_5074_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 5070
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8735, denoteGraph_ringAttn pm initPM 8736])
    (hk_recon : denoteGraph_ringAttn sm initSM 5071
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8737, denoteGraph_ringAttn pm initPM 8738])
    (hv_recon : denoteGraph_ringAttn sm initSM 5068
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8723, denoteGraph_ringAttn pm initPM 8724])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 5070).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 5071).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 5068).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5074
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu5072 : denoteGraph sm initSM 5072 = denoteGraph pm initPM 5072 :=
    recon_weight initSM initPM hInit initGoal_5072 (by native_decide) 5072 rfl rfl rfl rfl
  have hcu5073 : denoteGraph sm initSM 5073 = denoteGraph pm initPM 5073 :=
    recon_weight initSM initPM hInit initGoal_5073 (by native_decide) 5073 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm5070 : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5070 = denoteGraph_ringAttn sm initSM 5070 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5070 282 (by native_decide) (by native_decide)).symm
  have bSsm5071 : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5071 = denoteGraph_ringAttn sm initSM 5071 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5071 282 (by native_decide) (by native_decide)).symm
  have bSsm5068 : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5068 = denoteGraph_ringAttn sm initSM 5068 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5068 282 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP8735 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8735 = denoteGraph_ringAttn pm initPM 8735 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8735 625 (by native_decide) (by native_decide)).symm
  have bP8736 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8736 = denoteGraph_ringAttn pm initPM 8736 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8736 625 (by native_decide) (by native_decide)).symm
  have bP8737 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8737 = denoteGraph_ringAttn pm initPM 8737 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8737 625 (by native_decide) (by native_decide)).symm
  have bP8738 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8738 = denoteGraph_ringAttn pm initPM 8738 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8738 625 (by native_decide) (by native_decide)).symm
  have bP8723 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8723 = denoteGraph_ringAttn pm initPM 8723 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8723 625 (by native_decide) (by native_decide)).symm
  have bP8724 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8724 = denoteGraph_ringAttn pm initPM 8724 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8724 625 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5070
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8735, (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8736] := by
    rw [bSsm5070, bP8735, bP8736]; exact hq_recon
  have hk_full : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5071
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8737, (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8738] := by
    rw [bSsm5071, bP8737, bP8738]; exact hk_recon
  have hv_full : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5068
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8723, (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8724] := by
    rw [bSsm5068, bP8723, bP8724]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM (nSM_L7.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5070).shape.length
    rw [bSsm5070, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM (nSM_L7.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5071).shape.length
    rw [bSsm5071, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM (nSM_L7.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5068).shape.length
    rw [bSsm5068, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM5072 : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5072 = denoteGraph sm initSM 5072 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5072 282 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5072 (by native_decide)
  have hSM5073 : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5073 = denoteGraph sm initSM 5073 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5073 282 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5073 (by native_decide)
  have hPM5072 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 5072 = denoteGraph pm initPM 5072 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5072 625 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5072 (by native_decide)
  have hPM5073 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 5073 = denoteGraph pm initPM 5073 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5073 625 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5073 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM (nSM_L7.ins.getD 3 0)
      = (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 3 0) := by
    show (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5072 = (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 5072
    rw [hSM5072, hPM5072, hcu5072]
  have hcuK_sm_pm : (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM (nSM_L7.ins.getD 4 0)
      = (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 4 0) := by
    show (sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM 5073 = (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 5073
    rw [hSM5073, hPM5073, hcu5073]
  -- full attention output shape (take-625 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 0 0), (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 1 0), (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 2 0), (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 2 0)])
        ((pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 3 0))
        ((pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 4 0))
        (nR0_L7.params.getD 0 1) (nR0_L7.params.getD 1 1) (nR0_L7.params.getD 2 1) (nR0_L7.params.getD 3 1)
        (decide (nR0_L7.params.getD 4 0 ≠ 0)) (nR0_L7.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8735, (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8736]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm5070, hq_sm_shape]
    rfl
  -- take-625 -> take-626 bridges for r1 inputs
  have e8735 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8735 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8735 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8735 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have e8736 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8736 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8736 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8736 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have e8737 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8737 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8737 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8737 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have e8738 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8738 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8738 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8738 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have e8723 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8723 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8723 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8723 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have e8724 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 8724 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8724 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8724 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have e5072 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 5072 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 5072 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5072 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have e5073 : (pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM 5073 = (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 5073 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5073 625 626 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM) nR1_L7
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM) nR1_L7 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L7]; intro m hm; fin_cases hm
      · exact e8735
      · exact e8736
    · rw [buddy_r1_L7]; intro m hm; fin_cases hm
      · exact e8737
      · exact e8738
    · rw [buddy_r1_L7]; intro m hm; fin_cases hm
      · exact e8723
      · exact e8724
    · exact e5072
    · exact e5073
  -- node reductions
  have hSM5074 : denoteGraph_ringAttn sm initSM 5074
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM) nSM_L7 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5074 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5074 283 (by native_decide) (by native_decide),
        show sm.nodes.take 283 = sm.nodes.take 282 ++ [nSM_L7] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5070 5071 5068 5072 5073 5074 [16, 4, 64, 64, 1, 512]
  have hPM8739 : denoteGraph_ringAttn pm initPM 8739
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM) nR0_L7 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8739 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8739 626 (by native_decide) (by native_decide),
        show pm.nodes.take 626 = pm.nodes.take 625 ++ [nR0_L7] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8735 8737 8723 5072 5073 8739 [16, 4, 64, 64, 1, 512]
  have hPM8740 : denoteGraph_ringAttn pm initPM 8740
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM) nR1_L7 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8740 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8740 627 (by native_decide) (by native_decide),
        show pm.nodes.take 627 = pm.nodes.take 626 ++ [nR1_L7] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8736 8738 8724 5072 5073 8740 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-626 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 0 0), (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 1 0), (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR0_L7.ins.getD 2 0), (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 2 0)])
        ((pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 3 0))
        ((pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM (nR1_L7.ins.getD 4 0))
        (nR1_L7.params.getD 0 1) (nR1_L7.params.getD 1 1) (nR1_L7.params.getD 2 1) (nR1_L7.params.getD 3 1)
        (decide (nR1_L7.params.getD 4 0 ≠ 0)) (nR1_L7.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8735, (pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM 8736]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e8735, ← e8736, ← hq_full, bSsm5070, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_5074
    nSM_L7 nR0_L7 nR1_L7
    ((sm.nodes.take 282).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 625).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 626).foldl (applyNodeRingAttn pm) initPM)
    5074 8739 8740 2048 16 64 (by omega) (by omega) (by omega)
    hSM5074 hPM8739 hPM8740 bridge_r1
    buddy_sm_L7 buddy_r0_L7 buddy_r1_L7 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-8 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L8 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5124, 5125, 5122, 5126, 5127], outs := [5128], params := [16, 4, 64, 64, 1, 512] }
def nR0_L8 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8921, 8923, 8909, 5126, 5127], outs := [8925], params := [16, 4, 64, 64, 1, 512] }
def nR1_L8 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8922, 8924, 8910, 5126, 5127], outs := [8926], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L8 : ringAttnBuddies sm nSM_L8 = [nSM_L8] := by native_decide
theorem buddy_r0_L8 : ringAttnBuddies pm nR0_L8 = [nR0_L8, nR1_L8] := by native_decide
theorem buddy_r1_L8 : ringAttnBuddies pm nR1_L8 = [nR0_L8, nR1_L8] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_5128_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 5124
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8921, denoteGraph_ringAttn pm initPM 8922])
    (hk_recon : denoteGraph_ringAttn sm initSM 5125
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8923, denoteGraph_ringAttn pm initPM 8924])
    (hv_recon : denoteGraph_ringAttn sm initSM 5122
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8909, denoteGraph_ringAttn pm initPM 8910])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 5124).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 5125).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 5122).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5128
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu5126 : denoteGraph sm initSM 5126 = denoteGraph pm initPM 5126 :=
    recon_weight initSM initPM hInit initGoal_5126 (by native_decide) 5126 rfl rfl rfl rfl
  have hcu5127 : denoteGraph sm initSM 5127 = denoteGraph pm initPM 5127 :=
    recon_weight initSM initPM hInit initGoal_5127 (by native_decide) 5127 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm5124 : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5124 = denoteGraph_ringAttn sm initSM 5124 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5124 321 (by native_decide) (by native_decide)).symm
  have bSsm5125 : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5125 = denoteGraph_ringAttn sm initSM 5125 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5125 321 (by native_decide) (by native_decide)).symm
  have bSsm5122 : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5122 = denoteGraph_ringAttn sm initSM 5122 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5122 321 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP8921 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8921 = denoteGraph_ringAttn pm initPM 8921 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8921 703 (by native_decide) (by native_decide)).symm
  have bP8922 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8922 = denoteGraph_ringAttn pm initPM 8922 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8922 703 (by native_decide) (by native_decide)).symm
  have bP8923 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8923 = denoteGraph_ringAttn pm initPM 8923 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8923 703 (by native_decide) (by native_decide)).symm
  have bP8924 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8924 = denoteGraph_ringAttn pm initPM 8924 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8924 703 (by native_decide) (by native_decide)).symm
  have bP8909 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8909 = denoteGraph_ringAttn pm initPM 8909 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8909 703 (by native_decide) (by native_decide)).symm
  have bP8910 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8910 = denoteGraph_ringAttn pm initPM 8910 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8910 703 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5124
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8921, (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8922] := by
    rw [bSsm5124, bP8921, bP8922]; exact hq_recon
  have hk_full : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5125
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8923, (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8924] := by
    rw [bSsm5125, bP8923, bP8924]; exact hk_recon
  have hv_full : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5122
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8909, (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8910] := by
    rw [bSsm5122, bP8909, bP8910]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM (nSM_L8.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5124).shape.length
    rw [bSsm5124, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM (nSM_L8.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5125).shape.length
    rw [bSsm5125, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM (nSM_L8.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5122).shape.length
    rw [bSsm5122, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM5126 : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5126 = denoteGraph sm initSM 5126 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5126 321 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5126 (by native_decide)
  have hSM5127 : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5127 = denoteGraph sm initSM 5127 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5127 321 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5127 (by native_decide)
  have hPM5126 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 5126 = denoteGraph pm initPM 5126 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5126 703 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5126 (by native_decide)
  have hPM5127 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 5127 = denoteGraph pm initPM 5127 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5127 703 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5127 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM (nSM_L8.ins.getD 3 0)
      = (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 3 0) := by
    show (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5126 = (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 5126
    rw [hSM5126, hPM5126, hcu5126]
  have hcuK_sm_pm : (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM (nSM_L8.ins.getD 4 0)
      = (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 4 0) := by
    show (sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM 5127 = (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 5127
    rw [hSM5127, hPM5127, hcu5127]
  -- full attention output shape (take-703 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 0 0), (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 1 0), (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 2 0), (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 2 0)])
        ((pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 3 0))
        ((pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 4 0))
        (nR0_L8.params.getD 0 1) (nR0_L8.params.getD 1 1) (nR0_L8.params.getD 2 1) (nR0_L8.params.getD 3 1)
        (decide (nR0_L8.params.getD 4 0 ≠ 0)) (nR0_L8.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8921, (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8922]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm5124, hq_sm_shape]
    rfl
  -- take-703 -> take-704 bridges for r1 inputs
  have e8921 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8921 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8921 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8921 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have e8922 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8922 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8922 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8922 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have e8923 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8923 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8923 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8923 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have e8924 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8924 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8924 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8924 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have e8909 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8909 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8909 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8909 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have e8910 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 8910 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8910 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 8910 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have e5126 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 5126 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 5126 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5126 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have e5127 : (pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM 5127 = (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 5127 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5127 703 704 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM) nR1_L8
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM) nR1_L8 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L8]; intro m hm; fin_cases hm
      · exact e8921
      · exact e8922
    · rw [buddy_r1_L8]; intro m hm; fin_cases hm
      · exact e8923
      · exact e8924
    · rw [buddy_r1_L8]; intro m hm; fin_cases hm
      · exact e8909
      · exact e8910
    · exact e5126
    · exact e5127
  -- node reductions
  have hSM5128 : denoteGraph_ringAttn sm initSM 5128
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM) nSM_L8 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5128 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5128 322 (by native_decide) (by native_decide),
        show sm.nodes.take 322 = sm.nodes.take 321 ++ [nSM_L8] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5124 5125 5122 5126 5127 5128 [16, 4, 64, 64, 1, 512]
  have hPM8925 : denoteGraph_ringAttn pm initPM 8925
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM) nR0_L8 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8925 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8925 704 (by native_decide) (by native_decide),
        show pm.nodes.take 704 = pm.nodes.take 703 ++ [nR0_L8] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8921 8923 8909 5126 5127 8925 [16, 4, 64, 64, 1, 512]
  have hPM8926 : denoteGraph_ringAttn pm initPM 8926
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM) nR1_L8 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 8926 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 8926 705 (by native_decide) (by native_decide),
        show pm.nodes.take 705 = pm.nodes.take 704 ++ [nR1_L8] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8922 8924 8910 5126 5127 8926 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-704 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 0 0), (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 1 0), (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR0_L8.ins.getD 2 0), (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 2 0)])
        ((pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 3 0))
        ((pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM (nR1_L8.ins.getD 4 0))
        (nR1_L8.params.getD 0 1) (nR1_L8.params.getD 1 1) (nR1_L8.params.getD 2 1) (nR1_L8.params.getD 3 1)
        (decide (nR1_L8.params.getD 4 0 ≠ 0)) (nR1_L8.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8921, (pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM 8922]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e8921, ← e8922, ← hq_full, bSsm5124, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_5128
    nSM_L8 nR0_L8 nR1_L8
    ((sm.nodes.take 321).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 703).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 704).foldl (applyNodeRingAttn pm) initPM)
    5128 8925 8926 2048 16 64 (by omega) (by omega) (by omega)
    hSM5128 hPM8925 hPM8926 bridge_r1
    buddy_sm_L8 buddy_r0_L8 buddy_r1_L8 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-9 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L9 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5178, 5179, 5176, 5180, 5181], outs := [5182], params := [16, 4, 64, 64, 1, 512] }
def nR0_L9 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9107, 9109, 9095, 5180, 5181], outs := [9111], params := [16, 4, 64, 64, 1, 512] }
def nR1_L9 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9108, 9110, 9096, 5180, 5181], outs := [9112], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L9 : ringAttnBuddies sm nSM_L9 = [nSM_L9] := by native_decide
theorem buddy_r0_L9 : ringAttnBuddies pm nR0_L9 = [nR0_L9, nR1_L9] := by native_decide
theorem buddy_r1_L9 : ringAttnBuddies pm nR1_L9 = [nR0_L9, nR1_L9] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_5182_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 5178
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9107, denoteGraph_ringAttn pm initPM 9108])
    (hk_recon : denoteGraph_ringAttn sm initSM 5179
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9109, denoteGraph_ringAttn pm initPM 9110])
    (hv_recon : denoteGraph_ringAttn sm initSM 5176
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9095, denoteGraph_ringAttn pm initPM 9096])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 5178).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 5179).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 5176).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5182
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu5180 : denoteGraph sm initSM 5180 = denoteGraph pm initPM 5180 :=
    recon_weight initSM initPM hInit initGoal_5180 (by native_decide) 5180 rfl rfl rfl rfl
  have hcu5181 : denoteGraph sm initSM 5181 = denoteGraph pm initPM 5181 :=
    recon_weight initSM initPM hInit initGoal_5181 (by native_decide) 5181 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm5178 : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5178 = denoteGraph_ringAttn sm initSM 5178 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5178 360 (by native_decide) (by native_decide)).symm
  have bSsm5179 : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5179 = denoteGraph_ringAttn sm initSM 5179 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5179 360 (by native_decide) (by native_decide)).symm
  have bSsm5176 : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5176 = denoteGraph_ringAttn sm initSM 5176 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5176 360 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP9107 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9107 = denoteGraph_ringAttn pm initPM 9107 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9107 781 (by native_decide) (by native_decide)).symm
  have bP9108 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9108 = denoteGraph_ringAttn pm initPM 9108 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9108 781 (by native_decide) (by native_decide)).symm
  have bP9109 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9109 = denoteGraph_ringAttn pm initPM 9109 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9109 781 (by native_decide) (by native_decide)).symm
  have bP9110 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9110 = denoteGraph_ringAttn pm initPM 9110 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9110 781 (by native_decide) (by native_decide)).symm
  have bP9095 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9095 = denoteGraph_ringAttn pm initPM 9095 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9095 781 (by native_decide) (by native_decide)).symm
  have bP9096 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9096 = denoteGraph_ringAttn pm initPM 9096 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9096 781 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5178
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9107, (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9108] := by
    rw [bSsm5178, bP9107, bP9108]; exact hq_recon
  have hk_full : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5179
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9109, (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9110] := by
    rw [bSsm5179, bP9109, bP9110]; exact hk_recon
  have hv_full : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5176
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9095, (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9096] := by
    rw [bSsm5176, bP9095, bP9096]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM (nSM_L9.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5178).shape.length
    rw [bSsm5178, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM (nSM_L9.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5179).shape.length
    rw [bSsm5179, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM (nSM_L9.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5176).shape.length
    rw [bSsm5176, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM5180 : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5180 = denoteGraph sm initSM 5180 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5180 360 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5180 (by native_decide)
  have hSM5181 : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5181 = denoteGraph sm initSM 5181 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5181 360 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5181 (by native_decide)
  have hPM5180 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 5180 = denoteGraph pm initPM 5180 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5180 781 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5180 (by native_decide)
  have hPM5181 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 5181 = denoteGraph pm initPM 5181 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5181 781 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5181 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM (nSM_L9.ins.getD 3 0)
      = (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 3 0) := by
    show (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5180 = (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 5180
    rw [hSM5180, hPM5180, hcu5180]
  have hcuK_sm_pm : (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM (nSM_L9.ins.getD 4 0)
      = (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 4 0) := by
    show (sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM 5181 = (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 5181
    rw [hSM5181, hPM5181, hcu5181]
  -- full attention output shape (take-781 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 0 0), (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 1 0), (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 2 0), (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 2 0)])
        ((pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 3 0))
        ((pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 4 0))
        (nR0_L9.params.getD 0 1) (nR0_L9.params.getD 1 1) (nR0_L9.params.getD 2 1) (nR0_L9.params.getD 3 1)
        (decide (nR0_L9.params.getD 4 0 ≠ 0)) (nR0_L9.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9107, (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9108]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm5178, hq_sm_shape]
    rfl
  -- take-781 -> take-782 bridges for r1 inputs
  have e9107 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9107 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9107 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9107 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have e9108 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9108 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9108 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9108 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have e9109 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9109 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9109 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9109 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have e9110 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9110 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9110 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9110 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have e9095 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9095 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9095 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9095 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have e9096 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 9096 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9096 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9096 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have e5180 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 5180 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 5180 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5180 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have e5181 : (pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM 5181 = (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 5181 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5181 781 782 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM) nR1_L9
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM) nR1_L9 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L9]; intro m hm; fin_cases hm
      · exact e9107
      · exact e9108
    · rw [buddy_r1_L9]; intro m hm; fin_cases hm
      · exact e9109
      · exact e9110
    · rw [buddy_r1_L9]; intro m hm; fin_cases hm
      · exact e9095
      · exact e9096
    · exact e5180
    · exact e5181
  -- node reductions
  have hSM5182 : denoteGraph_ringAttn sm initSM 5182
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM) nSM_L9 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5182 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5182 361 (by native_decide) (by native_decide),
        show sm.nodes.take 361 = sm.nodes.take 360 ++ [nSM_L9] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5178 5179 5176 5180 5181 5182 [16, 4, 64, 64, 1, 512]
  have hPM9111 : denoteGraph_ringAttn pm initPM 9111
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM) nR0_L9 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9111 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9111 782 (by native_decide) (by native_decide),
        show pm.nodes.take 782 = pm.nodes.take 781 ++ [nR0_L9] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 9107 9109 9095 5180 5181 9111 [16, 4, 64, 64, 1, 512]
  have hPM9112 : denoteGraph_ringAttn pm initPM 9112
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM) nR1_L9 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9112 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9112 783 (by native_decide) (by native_decide),
        show pm.nodes.take 783 = pm.nodes.take 782 ++ [nR1_L9] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 9108 9110 9096 5180 5181 9112 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-782 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 0 0), (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 1 0), (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR0_L9.ins.getD 2 0), (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 2 0)])
        ((pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 3 0))
        ((pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM (nR1_L9.ins.getD 4 0))
        (nR1_L9.params.getD 0 1) (nR1_L9.params.getD 1 1) (nR1_L9.params.getD 2 1) (nR1_L9.params.getD 3 1)
        (decide (nR1_L9.params.getD 4 0 ≠ 0)) (nR1_L9.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9107, (pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM 9108]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e9107, ← e9108, ← hq_full, bSsm5178, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_5182
    nSM_L9 nR0_L9 nR1_L9
    ((sm.nodes.take 360).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 781).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 782).foldl (applyNodeRingAttn pm) initPM)
    5182 9111 9112 2048 16 64 (by omega) (by omega) (by omega)
    hSM5182 hPM9111 hPM9112 bridge_r1
    buddy_sm_L9 buddy_r0_L9 buddy_r1_L9 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-10 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5232, 5233, 5230, 5234, 5235], outs := [5236], params := [16, 4, 64, 64, 1, 512] }
def nR0_L10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9293, 9295, 9281, 5234, 5235], outs := [9297], params := [16, 4, 64, 64, 1, 512] }
def nR1_L10 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9294, 9296, 9282, 5234, 5235], outs := [9298], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L10 : ringAttnBuddies sm nSM_L10 = [nSM_L10] := by native_decide
theorem buddy_r0_L10 : ringAttnBuddies pm nR0_L10 = [nR0_L10, nR1_L10] := by native_decide
theorem buddy_r1_L10 : ringAttnBuddies pm nR1_L10 = [nR0_L10, nR1_L10] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_5236_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 5232
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9293, denoteGraph_ringAttn pm initPM 9294])
    (hk_recon : denoteGraph_ringAttn sm initSM 5233
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9295, denoteGraph_ringAttn pm initPM 9296])
    (hv_recon : denoteGraph_ringAttn sm initSM 5230
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9281, denoteGraph_ringAttn pm initPM 9282])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 5232).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 5233).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 5230).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5236
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu5234 : denoteGraph sm initSM 5234 = denoteGraph pm initPM 5234 :=
    recon_weight initSM initPM hInit initGoal_5234 (by native_decide) 5234 rfl rfl rfl rfl
  have hcu5235 : denoteGraph sm initSM 5235 = denoteGraph pm initPM 5235 :=
    recon_weight initSM initPM hInit initGoal_5235 (by native_decide) 5235 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm5232 : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5232 = denoteGraph_ringAttn sm initSM 5232 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5232 399 (by native_decide) (by native_decide)).symm
  have bSsm5233 : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5233 = denoteGraph_ringAttn sm initSM 5233 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5233 399 (by native_decide) (by native_decide)).symm
  have bSsm5230 : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5230 = denoteGraph_ringAttn sm initSM 5230 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5230 399 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP9293 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9293 = denoteGraph_ringAttn pm initPM 9293 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9293 859 (by native_decide) (by native_decide)).symm
  have bP9294 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9294 = denoteGraph_ringAttn pm initPM 9294 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9294 859 (by native_decide) (by native_decide)).symm
  have bP9295 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9295 = denoteGraph_ringAttn pm initPM 9295 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9295 859 (by native_decide) (by native_decide)).symm
  have bP9296 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9296 = denoteGraph_ringAttn pm initPM 9296 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9296 859 (by native_decide) (by native_decide)).symm
  have bP9281 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9281 = denoteGraph_ringAttn pm initPM 9281 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9281 859 (by native_decide) (by native_decide)).symm
  have bP9282 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9282 = denoteGraph_ringAttn pm initPM 9282 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9282 859 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5232
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9293, (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9294] := by
    rw [bSsm5232, bP9293, bP9294]; exact hq_recon
  have hk_full : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5233
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9295, (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9296] := by
    rw [bSsm5233, bP9295, bP9296]; exact hk_recon
  have hv_full : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5230
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9281, (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9282] := by
    rw [bSsm5230, bP9281, bP9282]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM (nSM_L10.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5232).shape.length
    rw [bSsm5232, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM (nSM_L10.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5233).shape.length
    rw [bSsm5233, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM (nSM_L10.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5230).shape.length
    rw [bSsm5230, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM5234 : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5234 = denoteGraph sm initSM 5234 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5234 399 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5234 (by native_decide)
  have hSM5235 : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5235 = denoteGraph sm initSM 5235 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5235 399 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5235 (by native_decide)
  have hPM5234 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 5234 = denoteGraph pm initPM 5234 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5234 859 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5234 (by native_decide)
  have hPM5235 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 5235 = denoteGraph pm initPM 5235 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5235 859 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5235 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM (nSM_L10.ins.getD 3 0)
      = (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 3 0) := by
    show (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5234 = (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 5234
    rw [hSM5234, hPM5234, hcu5234]
  have hcuK_sm_pm : (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM (nSM_L10.ins.getD 4 0)
      = (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 4 0) := by
    show (sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM 5235 = (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 5235
    rw [hSM5235, hPM5235, hcu5235]
  -- full attention output shape (take-859 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 0 0), (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 1 0), (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 2 0), (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 2 0)])
        ((pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 3 0))
        ((pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 4 0))
        (nR0_L10.params.getD 0 1) (nR0_L10.params.getD 1 1) (nR0_L10.params.getD 2 1) (nR0_L10.params.getD 3 1)
        (decide (nR0_L10.params.getD 4 0 ≠ 0)) (nR0_L10.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9293, (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9294]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm5232, hq_sm_shape]
    rfl
  -- take-859 -> take-860 bridges for r1 inputs
  have e9293 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9293 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9293 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9293 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have e9294 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9294 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9294 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9294 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have e9295 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9295 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9295 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9295 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have e9296 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9296 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9296 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9296 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have e9281 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9281 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9281 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9281 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have e9282 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 9282 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9282 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9282 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have e5234 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 5234 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 5234 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5234 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have e5235 : (pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM 5235 = (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 5235 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5235 859 860 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM) nR1_L10
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM) nR1_L10 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L10]; intro m hm; fin_cases hm
      · exact e9293
      · exact e9294
    · rw [buddy_r1_L10]; intro m hm; fin_cases hm
      · exact e9295
      · exact e9296
    · rw [buddy_r1_L10]; intro m hm; fin_cases hm
      · exact e9281
      · exact e9282
    · exact e5234
    · exact e5235
  -- node reductions
  have hSM5236 : denoteGraph_ringAttn sm initSM 5236
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM) nSM_L10 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5236 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5236 400 (by native_decide) (by native_decide),
        show sm.nodes.take 400 = sm.nodes.take 399 ++ [nSM_L10] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5232 5233 5230 5234 5235 5236 [16, 4, 64, 64, 1, 512]
  have hPM9297 : denoteGraph_ringAttn pm initPM 9297
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM) nR0_L10 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9297 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9297 860 (by native_decide) (by native_decide),
        show pm.nodes.take 860 = pm.nodes.take 859 ++ [nR0_L10] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 9293 9295 9281 5234 5235 9297 [16, 4, 64, 64, 1, 512]
  have hPM9298 : denoteGraph_ringAttn pm initPM 9298
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM) nR1_L10 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9298 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9298 861 (by native_decide) (by native_decide),
        show pm.nodes.take 861 = pm.nodes.take 860 ++ [nR1_L10] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 9294 9296 9282 5234 5235 9298 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-860 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 0 0), (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 1 0), (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR0_L10.ins.getD 2 0), (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 2 0)])
        ((pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 3 0))
        ((pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM (nR1_L10.ins.getD 4 0))
        (nR1_L10.params.getD 0 1) (nR1_L10.params.getD 1 1) (nR1_L10.params.getD 2 1) (nR1_L10.params.getD 3 1)
        (decide (nR1_L10.params.getD 4 0 ≠ 0)) (nR1_L10.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9293, (pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM 9294]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e9293, ← e9294, ← hq_full, bSsm5232, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_5236
    nSM_L10 nR0_L10 nR1_L10
    ((sm.nodes.take 399).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 859).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 860).foldl (applyNodeRingAttn pm) initPM)
    5236 9297 9298 2048 16 64 (by omega) (by omega) (by omega)
    hSM5236 hPM9297 hPM9298 bridge_r1
    buddy_sm_L10 buddy_r0_L10 buddy_r1_L10 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl


/-! ### Layer-11 sliding reconstruction (rotary-fed shards, conditional) -/

def nSM_L11 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5286, 5287, 5284, 5288, 5289], outs := [5290], params := [16, 4, 64, 64, 1, 512] }
def nR0_L11 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9479, 9481, 9467, 5288, 5289], outs := [9483], params := [16, 4, 64, 64, 1, 512] }
def nR1_L11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9480, 9482, 9468, 5288, 5289], outs := [9484], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_L11 : ringAttnBuddies sm nSM_L11 = [nSM_L11] := by native_decide
theorem buddy_r0_L11 : ringAttnBuddies pm nR0_L11 = [nR0_L11, nR1_L11] := by native_decide
theorem buddy_r1_L11 : ringAttnBuddies pm nR1_L11 = [nR0_L11, nR1_L11] := by native_decide

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_5290_of_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_recon : denoteGraph_ringAttn sm initSM 5286
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9479, denoteGraph_ringAttn pm initPM 9480])
    (hk_recon : denoteGraph_ringAttn sm initSM 5287
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9481, denoteGraph_ringAttn pm initPM 9482])
    (hv_recon : denoteGraph_ringAttn sm initSM 5284
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9467, denoteGraph_ringAttn pm initPM 9468])
    (hq_sm_shape : (denoteGraph_ringAttn sm initSM 5286).shape = [2 * 2048, 16, 64])
    (hk_sm_shape : (denoteGraph_ringAttn sm initSM 5287).shape = [2 * 2048, 4, 64])
    (hv_sm_shape : (denoteGraph_ringAttn sm initSM 5284).shape = [2 * 2048, 4, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5290
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- cu-seqlens (replicated init leaves)
  have hcu5288 : denoteGraph sm initSM 5288 = denoteGraph pm initPM 5288 :=
    recon_weight initSM initPM hInit initGoal_5288 (by native_decide) 5288 rfl rfl rfl rfl
  have hcu5289 : denoteGraph sm initSM 5289 = denoteGraph pm initPM 5289 :=
    recon_weight initSM initPM hInit initGoal_5289 (by native_decide) 5289 rfl rfl rfl rfl
  -- SM prefix bridges
  have bSsm5286 : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5286 = denoteGraph_ringAttn sm initSM 5286 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5286 438 (by native_decide) (by native_decide)).symm
  have bSsm5287 : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5287 = denoteGraph_ringAttn sm initSM 5287 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5287 438 (by native_decide) (by native_decide)).symm
  have bSsm5284 : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5284 = denoteGraph_ringAttn sm initSM 5284 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5284 438 (by native_decide) (by native_decide)).symm
  -- PM prefix bridges (shards)
  have bP9479 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9479 = denoteGraph_ringAttn pm initPM 9479 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9479 937 (by native_decide) (by native_decide)).symm
  have bP9480 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9480 = denoteGraph_ringAttn pm initPM 9480 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9480 937 (by native_decide) (by native_decide)).symm
  have bP9481 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9481 = denoteGraph_ringAttn pm initPM 9481 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9481 937 (by native_decide) (by native_decide)).symm
  have bP9482 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9482 = denoteGraph_ringAttn pm initPM 9482 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9482 937 (by native_decide) (by native_decide)).symm
  have bP9467 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9467 = denoteGraph_ringAttn pm initPM 9467 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9467 937 (by native_decide) (by native_decide)).symm
  have bP9468 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9468 = denoteGraph_ringAttn pm initPM 9468 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9468 937 (by native_decide) (by native_decide)).symm
  -- full q/k/v reconstructions in fold form
  have hq_full : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5286
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9479, (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9480] := by
    rw [bSsm5286, bP9479, bP9480]; exact hq_recon
  have hk_full : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5287
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9481, (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9482] := by
    rw [bSsm5287, bP9481, bP9482]; exact hk_recon
  have hv_full : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5284
      = allGatherPrimDimN 0 2 0 [(pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9467, (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9468] := by
    rw [bSsm5284, bP9467, bP9468]; exact hv_recon
  -- SM nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM (nSM_L11.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5286).shape.length
    rw [bSsm5286, hq_sm_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM (nSM_L11.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5287).shape.length
    rw [bSsm5287, hk_sm_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM (nSM_L11.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5284).shape.length
    rw [bSsm5284, hv_sm_shape]; decide
  -- cu_seqlens equalities
  have hSM5288 : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5288 = denoteGraph sm initSM 5288 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5288 438 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5288 (by native_decide)
  have hSM5289 : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5289 = denoteGraph sm initSM 5289 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5289 438 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5289 (by native_decide)
  have hPM5288 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 5288 = denoteGraph pm initPM 5288 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5288 937 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5288 (by native_decide)
  have hPM5289 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 5289 = denoteGraph pm initPM 5289 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5289 937 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5289 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM (nSM_L11.ins.getD 3 0)
      = (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 3 0) := by
    show (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5288 = (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 5288
    rw [hSM5288, hPM5288, hcu5288]
  have hcuK_sm_pm : (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM (nSM_L11.ins.getD 4 0)
      = (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 4 0) := by
    show (sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM 5289 = (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 5289
    rw [hSM5289, hPM5289, hcu5289]
  -- full attention output shape (take-937 fold)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 0 0), (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 1 0), (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 2 0), (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 2 0)])
        ((pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 3 0))
        ((pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 4 0))
        (nR0_L11.params.getD 0 1) (nR0_L11.params.getD 1 1) (nR0_L11.params.getD 2 1) (nR0_L11.params.getD 3 1)
        (decide (nR0_L11.params.getD 4 0 ≠ 0)) (nR0_L11.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9479, (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9480]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm5286, hq_sm_shape]
    rfl
  -- take-937 -> take-938 bridges for r1 inputs
  have e9479 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9479 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9479 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9479 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have e9480 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9480 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9480 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9480 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have e9481 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9481 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9481 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9481 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have e9482 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9482 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9482 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9482 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have e9467 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9467 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9467 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9467 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have e9468 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 9468 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9468 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9468 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have e5288 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 5288 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 5288 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5288 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have e5289 : (pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM 5289 = (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 5289 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5289 937 938 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM) nR1_L11
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM) nR1_L11 := by
    apply attn_sw_store_congr
    · rw [buddy_r1_L11]; intro m hm; fin_cases hm
      · exact e9479
      · exact e9480
    · rw [buddy_r1_L11]; intro m hm; fin_cases hm
      · exact e9481
      · exact e9482
    · rw [buddy_r1_L11]; intro m hm; fin_cases hm
      · exact e9467
      · exact e9468
    · exact e5288
    · exact e5289
  -- node reductions
  have hSM5290 : denoteGraph_ringAttn sm initSM 5290
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM) nSM_L11 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5290 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5290 439 (by native_decide) (by native_decide),
        show sm.nodes.take 439 = sm.nodes.take 438 ++ [nSM_L11] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5286 5287 5284 5288 5289 5290 [16, 4, 64, 64, 1, 512]
  have hPM9483 : denoteGraph_ringAttn pm initPM 9483
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM) nR0_L11 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9483 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9483 938 (by native_decide) (by native_decide),
        show pm.nodes.take 938 = pm.nodes.take 937 ++ [nR0_L11] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 9479 9481 9467 5288 5289 9483 [16, 4, 64, 64, 1, 512]
  have hPM9484 : denoteGraph_ringAttn pm initPM 9484
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM) nR1_L11 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9484 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9484 939 (by native_decide) (by native_decide),
        show pm.nodes.take 939 = pm.nodes.take 938 ++ [nR1_L11] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 9480 9482 9468 5288 5289 9484 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-938 fold
  have hfull_shape145 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 0 0), (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 1 0), (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR0_L11.ins.getD 2 0), (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 2 0)])
        ((pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 3 0))
        ((pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM (nR1_L11.ins.getD 4 0))
        (nR1_L11.params.getD 0 1) (nR1_L11.params.getD 1 1) (nR1_L11.params.getD 2 1) (nR1_L11.params.getD 3 1)
        (decide (nR1_L11.params.getD 4 0 ≠ 0)) (nR1_L11.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9479, (pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM 9480]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e9479, ← e9480, ← hq_full, bSsm5286, hq_sm_shape]
    rfl
  -- Fire the sliding-window gear.
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_5290
    nSM_L11 nR0_L11 nR1_L11
    ((sm.nodes.take 438).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 937).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 938).foldl (applyNodeRingAttn pm) initPM)
    5290 9483 9484 2048 16 64 (by omega) (by omega) (by omega)
    hSM5290 hPM9483 hPM9484 bridge_r1
    buddy_sm_L11 buddy_r0_L11 buddy_r1_L11 (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape145
    rfl rfl rfl rfl rfl rfl

end TrainVerify.Denote.GeneratedPatterns
