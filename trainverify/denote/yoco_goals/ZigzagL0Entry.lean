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

end TrainVerify.Denote.GeneratedPatterns
