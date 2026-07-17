/- Worker #25 — YOCO cross-decoder Layer-0 zigzag entry, made unconditional.

   `recon_intermediateGoal_5347_ringAttn` is the FW_attn_zigzag entry of the
   first cross-decoder layer.  Its `_of_qkv` predecessor (ZigzagReconstruction)
   assumes the Q/K/V lineage of the 2-tp/replicated boundary caches.  Here those
   assumptions are DISCHARGED faithfully from W24's already-proven L12-boundary
   goals:
   - `recon_intermediateGoal_5342_ringAttn` (2-tp Q gather over PM `9659`/`9660`,
     shard `[2048,16,64]`), from `L12MaybeShuffle`;
   - `recon_intermediateGoal_5343_ringAttn` / `_5344_` (replicated K/V casts,
     `[4096,4,64]`), from `L12BoundaryTail`.

   The gear consumes prefix folds; the proven goals speak of full folds.  We
   bridge them via `foldl_prefix_eq_full_ringAttn'` (every lineage tid is written
   strictly before SM node 505 / PM nodes 1072,1073) and the pure-init cu-seqlens
   leaf `5346` via `foldl_applyNodeRingAttn_at_not_written`.  Output shapes are
   discharged by `fw_attn_varlen_shape_p3` + `allGatherPrimDimN_shape`.

   The ONLY well-formedness input consumed is the genuine harness cu-seqlens
   bound `wf5347_hcuseq_bound` — a positive structural fact about the varlen
   attention mask, not a restatement of any goal conclusion. -/
import denote.yoco_goals.L12MaybeShuffle
import denote.yoco_goals.L12BoundaryTail

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- **Unconditional-given-well-formed-inputs `intermediateGoal_5347`** (Worker #25).

    The zigzag-CP L0 entry.  Unlike its `_of_qkv` predecessor, the Q/K/V lineage
    inputs are NOT assumed — they are extracted from W24's proven L12-boundary
    goals `5342` (2-tp Q gather over PM `9659`/`9660`), `5343`/`5344` (replicated
    K/V casts), bridged from full folds to the gear's prefix folds via
    `foldl_prefix_eq_full_ringAttn'`.  The attention output shapes are discharged
    by `fw_attn_varlen_shape_p3`.  The ONLY well-formedness input consumed is the
    genuine harness cu-seqlens bound `wf5347_hcuseq_bound`. -/
theorem recon_intermediateGoal_5347_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5347
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- Q lineage from proven 5342 (2-tp gather over pm 9659/9660).
  obtain ⟨hQval, hQs0, hQs1⟩ := twoTp_gather (denoteGraph_ringAttn sm initSM)
    (denoteGraph_ringAttn pm initPM) intermediateGoal_5342 5342 9659 9660 [2048, 16, 64]
    rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5342_ringAttn initSM initPM hSM hPM hInit hWF)
  have hQshapeSM : (denoteGraph_ringAttn sm initSM 5342).shape = [4096, 16, 64] := by
    have h := (recon_intermediateGoal_5342_ringAttn initSM initPM hSM hPM hInit hWF).1
    simpa [intermediateGoal_5342] using h
  -- K lineage from proven 5343 (replicated).
  have h5343 := recon_intermediateGoal_5343_ringAttn initSM initPM hSM hPM hInit hWF
  have hKval : denoteGraph_ringAttn sm initSM 5343 = denoteGraph_ringAttn pm initPM 5343 :=
    oneTp_valeq intermediateGoal_5343 _ _ 5343 rfl rfl rfl rfl h5343
  have hKshapeSM : (denoteGraph_ringAttn sm initSM 5343).shape = [4096, 4, 64] := by
    have h := h5343.1; simpa [intermediateGoal_5343] using h
  have hKshapePM : (denoteGraph_ringAttn pm initPM 5343).shape = [4096, 4, 64] := by
    rw [← hKval]; exact hKshapeSM
  -- V lineage from proven 5344 (replicated).
  have h5344 := recon_intermediateGoal_5344_ringAttn initSM initPM hSM hPM hInit hWF
  have hVval : denoteGraph_ringAttn sm initSM 5344 = denoteGraph_ringAttn pm initPM 5344 :=
    oneTp_valeq intermediateGoal_5344 _ _ 5344 rfl rfl rfl rfl h5344
  have hVshapeSM : (denoteGraph_ringAttn sm initSM 5344).shape = [4096, 4, 64] := by
    have h := h5344.1; simpa [intermediateGoal_5344] using h
  have hVshapePM : (denoteGraph_ringAttn pm initPM 5344).shape = [4096, 4, 64] := by
    rw [← hVval]; exact hVshapeSM
  -- Prefix ↔ full bridges (all tids written before SM node 505 / PM nodes 1072,1073).
  have bSM5342 : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5342
      = denoteGraph_ringAttn sm initSM 5342 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5342 505 (by native_decide) (by native_decide)).symm
  have bSM5343 : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5343
      = denoteGraph_ringAttn sm initSM 5343 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5343 505 (by native_decide) (by native_decide)).symm
  have bSM5344 : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5344
      = denoteGraph_ringAttn sm initSM 5344 :=
    (foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5344 505 (by native_decide) (by native_decide)).symm
  have bPM9659_72 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9659
      = denoteGraph_ringAttn pm initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9659 1072 (by native_decide) (by native_decide)).symm
  have bPM9660_72 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9660
      = denoteGraph_ringAttn pm initPM 9660 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9660 1072 (by native_decide) (by native_decide)).symm
  have bPM5343_72 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343
      = denoteGraph_ringAttn pm initPM 5343 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5343 1072 (by native_decide) (by native_decide)).symm
  have bPM5344_72 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344
      = denoteGraph_ringAttn pm initPM 5344 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5344 1072 (by native_decide) (by native_decide)).symm
  have bPM9659_73 : (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9659
      = denoteGraph_ringAttn pm initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9659 1073 (by native_decide) (by native_decide)).symm
  -- cu-seqlens leaf bridge (5346 is a pure init leaf, never written).
  have b5346_72 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346 = initPM 5346 :=
    foldl_applyNodeRingAttn_at_not_written pm (pm.nodes.take 1072) initPM 5346
      (by native_decide) (by native_decide)
  -- Assemble the `_of_qkv` hypotheses.
  have hq_full : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5342
      = allGatherPrimDimN 0 2 0
          [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9659,
           (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9660] := by
    rw [bSM5342, bPM9659_72, bPM9660_72]; exact hQval
  have hk_repl : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5343
      = (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343 := by
    rw [bSM5343, bPM5343_72]; exact hKval
  have hv_repl : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5344
      = (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344 := by
    rw [bSM5344, bPM5344_72]; exact hVval
  have hq_sm : 0 < ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5342).shape.length := by
    rw [bSM5342, hQshapeSM]; decide
  have hk_sm : 0 < ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5343).shape.length := by
    rw [bSM5343, hKshapeSM]; decide
  have hv_sm : 0 < ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5344).shape.length := by
    rw [bSM5344, hVshapeSM]; decide
  have hk_shape : ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343).shape
      = [4096, 4, 64] := by rw [bPM5343_72]; exact hKshapePM
  have hv_shape : ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344).shape
      = [4096, 4, 64] := by rw [bPM5344_72]; exact hVshapePM
  have h_bound : ∀ t, (decodeCuSeqlens
      ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346)).getD (t + 1) 0 ≤ 4096 := by
    rw [b5346_72]; exact hWF.wf5347_hcuseq_bound
  have hsh9659_72 : ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9659).shape
      = [2048, 16, 64] := by rw [bPM9659_72]; exact hQs0
  have hsh9659_73 : ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9659).shape
      = [2048, 16, 64] := by rw [bPM9659_73]; exact hQs0
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9659,
           (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9660])
        (allGatherPrimDimN 0 2 0
          [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343,
           (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343])
        (allGatherPrimDimN 0 2 0
          [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344,
           (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344])
        ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5345)
        ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346)
        16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsh9659_72])]
    decide
  have hfull_shape' :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9659,
           (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9660])
        (allGatherPrimDimN 0 2 0
          [(pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5343,
           (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5343])
        (allGatherPrimDimN 0 2 0
          [(pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5344,
           (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5344])
        ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5345)
        ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5346)
        16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsh9659_73])]
    decide
  exact recon_intermediateGoal_5347_ringAttn_of_qkv initSM initPM hInit
    hq_full hk_repl hv_repl hq_sm hk_sm hv_sm hk_shape hv_shape h_bound hfull_shape hfull_shape'

/-- **`intermediateGoal_5348` unconditional-given-WF** (Worker #25).
    Layer-0 cross-decoder post-attention reshape `[4096,16,64] → [4096,1024]`
    (SM node 506).  Reconstructs as the dim-0 gather of the two PM per-rank
    reshapes (nodes 1074/1075), chaining the proven `5347` zigzag output through
    the row-preserving-reshape commute lemma `fw_view_allGather0_reshape_16_64_2_g12`
    — the exact analogue of Worker #11's `4697` post-attention reshape. -/
theorem recon_intermediateGoal_5348_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5348
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h5347 := recon_intermediateGoal_5347_ringAttn initSM initPM hSM hPM hInit hWF
  -- extract the 5347 shard shapes [2048,16,64]
  have hshapes := h5347.2.1
  simp only [intermediateGoal_5347, List.map, List.cons.injEq, and_true] at hshapes
  obtain ⟨hs9687, hs9688⟩ := hshapes
  -- extract the 5347 value reconstruction
  have hval47 : denoteGraph_ringAttn sm initSM 5347
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9687, denoteGraph_ringAttn pm initPM 9688] := by
    have hv := h5347.2.2
    rw [reconstructForGoal_of_not_replicated intermediateGoal_5347 pm.numRanks _ rfl] at hv
    simp only [intermediateGoal_5347, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
          (by rw [hs9687]; decide)] at hv
    exact hv
  -- reshape node reductions over the ring denotation
  have rSM : denoteGraph_ringAttn sm initSM 5348
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5347) :=
    ringAttn_reshape_reduce_g12 sm initSM 506 0 5347 5348 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9689
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9687) :=
    ringAttn_reshape_reduce_g12 pm initPM 1074 0 9687 9689 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9690
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9688) :=
    ringAttn_reshape_reduce_g12 pm initPM 1075 1 9688 9690 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- the 5348 value reconstruction, via the commute lemma
  have hval48 : denoteGraph_ringAttn sm initSM 5348
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9689, denoteGraph_ringAttn pm initPM 9690] := by
    rw [rSM, hval47, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs9687 hs9688
  -- shapes
  have hs9689 : (denoteGraph_ringAttn pm initPM 9689).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9690 : (denoteGraph_ringAttn pm initPM 9690).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5348 : (denoteGraph_ringAttn sm initSM 5348).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5348 5348 9689 9690 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval48 hs5348 hs9689 hs9690

/-- **`intermediateGoal_5349` unconditional-given-WF** (Worker #25).
    Second post-attention reshape `[4096,1024] → [4096,1024]` (identity on the
    already-flat layout, SM node 507); reconstructs by chaining the proven `5348`
    through the row-preserving reshape commute `fw_view_allGather0_commute_2_of`.
    PM per-rank reshapes at nodes 1076/1077. -/
theorem recon_intermediateGoal_5349_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5349
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h5348 := recon_intermediateGoal_5348_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h5348.2.1
  simp only [intermediateGoal_5348, List.map, List.cons.injEq, and_true] at hshapes
  obtain ⟨hs9689, hs9690⟩ := hshapes
  have hval48 : denoteGraph_ringAttn sm initSM 5348
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9689, denoteGraph_ringAttn pm initPM 9690] := by
    have hv := h5348.2.2
    rw [reconstructForGoal_of_not_replicated intermediateGoal_5348 pm.numRanks _ rfl] at hv
    simp only [intermediateGoal_5348, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
          (by rw [hs9689]; decide)] at hv
    exact hv
  have rSM : denoteGraph_ringAttn sm initSM 5349
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5348) :=
    ringAttn_reshape_reduce_g12 sm initSM 507 0 5348 5349 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9695
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9689) :=
    ringAttn_reshape_reduce_g12 pm initPM 1076 0 9689 9695 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9696
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9690) :=
    ringAttn_reshape_reduce_g12 pm initPM 1077 1 9690 9696 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval49 : denoteGraph_ringAttn sm initSM 5349
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9695, denoteGraph_ringAttn pm initPM 9696] := by
    rw [rSM, hval48, rP0, rP1]
    exact fw_view_allGather0_commute_2_of _ _ 2048 1024 (by decide) hs9689 hs9690
  have hs9695 : (denoteGraph_ringAttn pm initPM 9695).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9696 : (denoteGraph_ringAttn pm initPM 9696).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5349 : (denoteGraph_ringAttn sm initSM 5349).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5349 5349 9695 9696 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval49 hs5349 hs9695 hs9696

/-- **`intermediateGoal_5351` unconditional-given-WF** (Worker #25).
    Post-attention output projection `FW_mix_precision_linear(5349, 5350)`
    (2-tp sharded activation, replicated weight `5350 : [1024,1024]`, SM node 508;
    PM nodes 1078/1079).  Reconstructs by reducing each linear node
    (`applyNode_fw_mix_precision_linear_out_1p` via `ringAttn_reduce2`), using the
    replicated-weight equality (`veq_weight_ring`), and pushing the dim-0 gather
    through `fw_mix_precision_linear_allGather0_commute_2`. -/
theorem recon_intermediateGoal_5351_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5351
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h5349 := recon_intermediateGoal_5349_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h5349.2.1
  simp only [intermediateGoal_5349, List.map, List.cons.injEq, and_true] at hshapes
  obtain ⟨hs9695, hs9696⟩ := hshapes
  have hs5349sm : (denoteGraph_ringAttn sm initSM 5349).shape = [4096, 1024] := by
    have := h5349.1; simpa [intermediateGoal_5349] using this
  have hval49 : denoteGraph_ringAttn sm initSM 5349
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9695, denoteGraph_ringAttn pm initPM 9696] := by
    have hv := h5349.2.2
    rw [reconstructForGoal_of_not_replicated intermediateGoal_5349 pm.numRanks _ rfl] at hv
    simp only [intermediateGoal_5349, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
          (by rw [hs9695]; decide)] at hv
    exact hv
  -- replicated weight 5350 : [1024,1024]
  have hw5350 : denoteGraph_ringAttn sm initSM 5350 = denoteGraph_ringAttn pm initPM 5350 :=
    veq_weight_ring initSM initPM hInit initGoal_5350 (by native_decide) 5350
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5350 : (denoteGraph_ringAttn sm initSM 5350).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5350 (by native_decide) 5350 [1024, 1024]
      rfl rfl (by native_decide)
  have hswPM5350 : (denoteGraph_ringAttn pm initPM 5350).shape = [1024, 1024] := by
    rw [← hw5350]; exact hsw5350
  -- linear node reductions
  have rSM : denoteGraph_ringAttn sm initSM 5351
      = fw_linear (denoteGraph_ringAttn sm initSM 5349) (denoteGraph_ringAttn sm initSM 5350) :=
    ringAttn_reduce2 sm initSM 508
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5349, 5350], outs := [5351] }
      5349 5350 5351 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5349 5350 5351)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9699
      = fw_linear (denoteGraph_ringAttn pm initPM 9695) (denoteGraph_ringAttn pm initPM 5350) :=
    ringAttn_reduce2 pm initPM 1078
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9695, 5350], outs := [9699] }
      9695 5350 9699 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9695 5350 9699)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9700
      = fw_linear (denoteGraph_ringAttn pm initPM 9696) (denoteGraph_ringAttn pm initPM 5350) :=
    ringAttn_reduce2 pm initPM 1079
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9696, 5350], outs := [9700] }
      9696 5350 9700 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9696 5350 9700)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval51 : denoteGraph_ringAttn sm initSM 5351
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9699, denoteGraph_ringAttn pm initPM 9700] := by
    rw [rSM, hval49, hw5350,
        fw_mix_precision_linear_allGather0_commute_2 (denoteGraph_ringAttn pm initPM 9695)
          (denoteGraph_ringAttn pm initPM 9696) (denoteGraph_ringAttn pm initPM 5350)
          2048 1024 1024 (by decide) (by decide) (by decide) hs9695 hs9696 hswPM5350,
        ← rP0, ← rP1]
  have hs9699 : (denoteGraph_ringAttn pm initPM 9699).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9695 hswPM5350
  have hs9700 : (denoteGraph_ringAttn pm initPM 9700).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9696 hswPM5350
  have hs5351 : (denoteGraph_ringAttn sm initSM 5351).shape = [4096, 1024] := by
    rw [rSM]; exact fw_linear_2d_shape 4096 1024 1024 _ _ hs5349sm hsw5350
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5351 5351 9699 9700 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval51 hs5351 hs9699 hs9700

/-- **`intermediateGoal_5352` unconditional-given-WF** (Worker #25).
    `FW_view(5351)` `[4096,1024]→[4096,1024]` (identity relabel, SM node 509;
    PM nodes 1080/1081), reconstructed via the row-preserving view commute. -/
theorem recon_intermediateGoal_5352_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5352
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hbr51, hs9699, hs9700⟩ := twoTp_gather _ _ intermediateGoal_5351 5351 9699 9700
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5351_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5352
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5351) :=
    ringAttn_reduce1_pm_opaque sm initSM 509
      { rank := 0, op := "OpName.FW_view", ins := [5351], outs := [5352], params := [4096, 1024] }
      5351 5352 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5351 5352)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9709
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9699) :=
    ringAttn_reduce1_pm_opaque pm initPM 1080
      { rank := 0, op := "OpName.FW_view", ins := [9699], outs := [9709], params := [2048, 1024] }
      9699 9709 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9699 9709)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9710
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9700) :=
    ringAttn_reduce1_pm_opaque pm initPM 1081
      { rank := 1, op := "OpName.FW_view", ins := [9700], outs := [9710], params := [2048, 1024] }
      9700 9710 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9700 9710)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5352
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9709, denoteGraph_ringAttn pm initPM 9710] := by
    rw [rSM, hbr51, rP0, rP1]
    exact fw_view_allGather0_commute_2_of _ _ 2048 1024 (by decide) hs9699 hs9700
  have hs9709 : (denoteGraph_ringAttn pm initPM 9709).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9710 : (denoteGraph_ringAttn pm initPM 9710).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5352 : (denoteGraph_ringAttn sm initSM 5352).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5352 5352 9709 9710 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5352 hs9709 hs9710

/-- **`intermediateGoal_5353` unconditional-given-WF** (Worker #25).
    `FW_float(5352)` (dtype cast, identity in the model, SM node 510;
    PM nodes 1082/1083). -/
theorem recon_intermediateGoal_5353_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5353
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr52, hs9709, hs9710⟩ := twoTp_gather _ _ intermediateGoal_5352 5352 9709 9710
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5352_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5353 = id (denoteGraph_ringAttn sm initSM 5352) :=
    ringAttn_reduce1_pm_opaque sm initSM 510
      { rank := 0, op := "OpName.FW_float", ins := [5352], outs := [5353] }
      5352 5353 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5352 5353 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9713 = id (denoteGraph_ringAttn pm initPM 9709) :=
    ringAttn_reduce1_pm_opaque pm initPM 1082
      { rank := 0, op := "OpName.FW_float", ins := [9709], outs := [9713] }
      9709 9713 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9709 9713 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9714 = id (denoteGraph_ringAttn pm initPM 9710) :=
    ringAttn_reduce1_pm_opaque pm initPM 1083
      { rank := 1, op := "OpName.FW_float", ins := [9710], outs := [9714] }
      9710 9714 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9710 9714 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5353
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9713, denoteGraph_ringAttn pm initPM 9714] := by
    rw [rSM, hbr52, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9713).shape = [2048, 1024] := by rw [rP0]; exact hs9709
  have hsp1 : (denoteGraph_ringAttn pm initPM 9714).shape = [2048, 1024] := by rw [rP1]; exact hs9710
  have hshape : (denoteGraph_ringAttn sm initSM 5353).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5353 5353 9713 9714 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
