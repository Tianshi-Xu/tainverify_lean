/- Worker #24 — Layer-12 BOUNDARY tail (YOCO cross-decoder transition).

   L12 is the last MoE layer.  After its residual add (`5330`, a genuine 2-tp
   sharded goal proven in `L12Reconstruction`), the graph builds the global
   YOCO key/value cache once and broadcasts it to the cross-decoder half.

   This module closes the *replicated* (single-rank, `tid == ts`) boundary
   goals `5332, 5334, 5336, 5343, 5344`.  Each reconstruct is a 1-tp singleton
   (`reconstructForGoal` on a one-element `tps` returns that element), so the
   obligation is `sm_ring T = pm_ring T` + shape, closed by `wrap_1tp_gen`.

   Structure (verified from `GeneratedYOCOMoE.lean`):
   - SM computes on the FULL residual `5330`; PM gathers its two shards
     `9625 / 9626` with an `AllGatherPrim` (node 1004, `11917`), exactly the
     L2 node-228 gather-to-full bridge.  Both PM ranks then recompute the
     same replicated tensors.
   - Because `denoteGraph_ringAttn` is a left fold, a tid written by BOTH PM
     ranks resolves to the *last* writer (rank 1).  So each PM reconstruct is
     driven through the rank-1 node and its rank-1 intermediate multiref tids
     (`15749, 15753, 15815, 15921`).  Values are still rank-independent:
     rank-1 RMSNorm reads the same global gather `11917`, and the per-head /
     cast chains consume replicated weights, so `pm = sm`.
   - `twoTp_gather` on the proven periodic goal `5330` supplies
     `sm 5330 = allGather 0 2 0 [pm 9625, pm 9626] = pm 11917`.

   The remaining boundary goals `5338 / 5340 / 5342` route through
   `FW_maybe_shuffle` (a new op at this boundary) and stay 2-tp sharded; they
   require a fidelity-checked maybe_shuffle gear and are handled separately. -/
import denote.yoco_goals.L12Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 5332 — final-boundary RMSNorm on the gathered L12 residual.
    REPLICATED single-rank goal: `sm 5332 = pm 5332`.
    SM: `rms_norm(mref₀(5330), 5331)`.  PM (rank-1 last writer, node 1008):
    `rms_norm(11917, 5331)` with `11917 = AllGatherPrim[mref₀(9625), mref₀(9626)]`.
    Chains from the periodic 2-tp goal `5330`. -/
theorem recon_intermediateGoal_5332_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5332
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg30, hs9625, hs9626⟩ := twoTp_gather _ _ intermediateGoal_5330 5330 9625 9626
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5330_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8007 : denoteGraph_ringAttn sm initSM 8007 = id (denoteGraph_ringAttn sm initSM 5330) :=
    ringAttn_reduce1_pm_opaque sm initSM 470
      { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] }
      5330 8007 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5330 8007 8011)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14597 : denoteGraph_ringAttn pm initPM 14597 = id (denoteGraph_ringAttn pm initPM 9625) :=
    ringAttn_reduce1_pm_opaque pm initPM 1001
      { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] }
      9625 14597 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9625 14597 13257)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14599 : denoteGraph_ringAttn pm initPM 14599 = id (denoteGraph_ringAttn pm initPM 9626) :=
    ringAttn_reduce1_pm_opaque pm initPM 1002
      { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] }
      9626 14599 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9626 14599 13258)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8007 p14597 p14599
  have p11917 : denoteGraph_ringAttn pm initPM 11917
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 14597, denoteGraph_ringAttn pm initPM 14599] :=
    ringAttn_reduce2_pm_opaque pm initPM 1004
      { rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917], params := [0] }
      14597 14599 11917 (fun a b => allGatherPrimDimN 0 2 0 [a, b])
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_allGatherPrimDimN_out_thm pm s 0 [14597, 14599] 11917 0)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hw5331 : denoteGraph_ringAttn sm initSM 5331 = denoteGraph_ringAttn pm initPM 5331 :=
    veq_weight_ring initSM initPM hInit initGoal_5331 (by native_decide) 5331
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5332
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 8007) (denoteGraph_ringAttn sm initSM 5331) :=
    ringAttn_reduce2_pm_opaque sm initSM 471
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8007, 5331], outs := [5332] }
      8007 5331 5332 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 8007 5331 5332)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 5332
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 11917) (denoteGraph_ringAttn pm initPM 5331) :=
    ringAttn_reduce2_pm_opaque pm initPM 1008
      { rank := 1, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] }
      11917 5331 5332 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 11917 5331 5332)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5332 = denoteGraph_ringAttn pm initPM 5332 := by
    rw [rSM, rPM, s8007, hg30, hnr, p11917, p14597, p14599, hw5331]
  have hs8007 : (denoteGraph_ringAttn sm initSM 8007).shape = [4096, 1024] := by
    rw [s8007, hg30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9625])]
    simp [List.set, List.getD]
  have hshape : (denoteGraph_ringAttn sm initSM 5332).shape = [4096, 1024] := by
    rw [rSM]; exact fw_rms_norm_shape2 _ _ 4096 1024 hs8007
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5332 5332 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 5334 — global K per-head projection `per_head(mref₀(5332), 5333)`.
    REPLICATED single-rank; PM via rank-1 node 1017 reading `15749 = mref(5332)`. -/
theorem recon_intermediateGoal_5334_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5334
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h5332 := recon_intermediateGoal_5332_ringAttn initSM initPM hSM hPM hInit hWF
  have hv5332 : denoteGraph_ringAttn sm initSM 5332 = denoteGraph_ringAttn pm initPM 5332 :=
    oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl h5332
  have hs5332 : (denoteGraph_ringAttn sm initSM 5332).shape = [4096, 1024] := by
    have := h5332.1; simpa [intermediateGoal_5332] using this
  have s8015 : denoteGraph_ringAttn sm initSM 8015 = id (denoteGraph_ringAttn sm initSM 5332) :=
    ringAttn_reduce1_pm_opaque sm initSM 473
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] }
      5332 8015 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5332 8015 8019)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15749 : denoteGraph_ringAttn pm initPM 15749 = id (denoteGraph_ringAttn pm initPM 5332) :=
    ringAttn_reduce1_pm_opaque pm initPM 1012
      { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] }
      5332 15749 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 5332 15749 15753)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8015 p15749
  have hw5333 : denoteGraph_ringAttn sm initSM 5333 = denoteGraph_ringAttn pm initPM 5333 :=
    veq_weight_ring initSM initPM hInit initGoal_5333 (by native_decide) 5333
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5333 : (denoteGraph_ringAttn sm initSM 5333).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5333 (by native_decide) 5333 [4, 64, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5334
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 8015) (denoteGraph_ringAttn sm initSM 5333) :=
    ringAttn_reduce2_pm_opaque sm initSM 475
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8015, 5333], outs := [5334] }
      8015 5333 5334 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 8015 5333 5334 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 5334
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15749) (denoteGraph_ringAttn pm initPM 5333) :=
    ringAttn_reduce2_pm_opaque pm initPM 1017
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15749, 5333], outs := [5334] }
      15749 5333 5334 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15749 5333 5334 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 := by
    rw [rSM, rPM, s8015, p15749, hv5332, hw5333]
  have hshape : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    rw [rSM, s8015]
    exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 hs5332 hsw5333
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5334 5334 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-- 5336 — global V per-head projection `per_head(mref₁(5332), 5335)`.
    REPLICATED single-rank; PM via rank-1 node 1018 reading `15753 = mref₁(5332)`. -/
theorem recon_intermediateGoal_5336_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5336
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h5332 := recon_intermediateGoal_5332_ringAttn initSM initPM hSM hPM hInit hWF
  have hv5332 : denoteGraph_ringAttn sm initSM 5332 = denoteGraph_ringAttn pm initPM 5332 :=
    oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl h5332
  have hs5332 : (denoteGraph_ringAttn sm initSM 5332).shape = [4096, 1024] := by
    have := h5332.1; simpa [intermediateGoal_5332] using this
  have s8019 : denoteGraph_ringAttn sm initSM 8019 = denoteGraph_ringAttn sm initSM 5332 :=
    ringAttn_reduce1_pm_opaque sm initSM 473
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] }
      5332 8019 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5332 8015 8019 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15753 : denoteGraph_ringAttn pm initPM 15753 = denoteGraph_ringAttn pm initPM 5332 :=
    ringAttn_reduce1_pm_opaque pm initPM 1012
      { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] }
      5332 15753 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 5332 15749 15753 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hw5335 : denoteGraph_ringAttn sm initSM 5335 = denoteGraph_ringAttn pm initPM 5335 :=
    veq_weight_ring initSM initPM hInit initGoal_5335 (by native_decide) 5335
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5335 : (denoteGraph_ringAttn sm initSM 5335).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5335 (by native_decide) 5335 [4, 64, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5336
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 8019) (denoteGraph_ringAttn sm initSM 5335) :=
    ringAttn_reduce2_pm_opaque sm initSM 476
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8019, 5335], outs := [5336] }
      8019 5335 5336 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 8019 5335 5336 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 5336
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15753) (denoteGraph_ringAttn pm initPM 5335) :=
    ringAttn_reduce2_pm_opaque pm initPM 1018
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15753, 5335], outs := [5336] }
      15753 5335 5336 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15753 5335 5336 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 := by
    rw [rSM, rPM, s8019, p15753, hv5332, hw5335]
  have hshape : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    rw [rSM, s8019]
    exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 hs5332 hsw5335
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5336 5336 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-- 5343 — first per-layer cast `FW_to(mref-first₁₂(5334))` of the global K
    cache into the cross-decoder.  REPLICATED; PM via rank-1 node 1036
    reading `15815 = mref-first₁₂(5334)`. -/
theorem recon_intermediateGoal_5343_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5343
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h5334 := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hv5334 : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl h5334
  have hs5334 : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have := h5334.1; simpa [intermediateGoal_5334] using this
  have s8033 : denoteGraph_ringAttn sm initSM 8033 = denoteGraph_ringAttn sm initSM 5334 :=
    ringAttn_reduce1_pm_opaque sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334],
        outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8033 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 11 5334 8033
        [8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15815 : denoteGraph_ringAttn pm initPM 15815 = denoteGraph_ringAttn pm initPM 5334 :=
    ringAttn_reduce1_pm_opaque pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334],
        outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15815 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 11 5334 15815
        [15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5343 = denoteGraph_ringAttn sm initSM 8033 :=
    ringAttn_reduce1_pm_opaque sm initSM 481
      { rank := 0, op := "OpName.FW_to", ins := [8033], outs := [5343] }
      8033 5343 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_to_out sm s 0 8033 5343 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 5343 = denoteGraph_ringAttn pm initPM 15815 :=
    ringAttn_reduce1_pm_opaque pm initPM 1036
      { rank := 1, op := "OpName.FW_to", ins := [15815], outs := [5343] }
      15815 5343 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_to_out pm s 1 15815 5343 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5343 = denoteGraph_ringAttn pm initPM 5343 := by
    rw [rSM, rPM, s8033, p15815, hv5334]
  have hshape : (denoteGraph_ringAttn sm initSM 5343).shape = [4096, 4, 64] := by
    rw [rSM, s8033]; exact hs5334
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5343 5343 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-- 5344 — first per-layer cast `FW_to(mref-first₁₂(5336))` of the global V
    cache into the cross-decoder.  REPLICATED; PM via rank-1 node 1060
    reading `15921 = mref-first₁₂(5336)`. -/
theorem recon_intermediateGoal_5344_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5344
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h5336 := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hv5336 : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl h5336
  have hs5336 : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have := h5336.1; simpa [intermediateGoal_5336] using this
  have s8091 : denoteGraph_ringAttn sm initSM 8091 = denoteGraph_ringAttn sm initSM 5336 :=
    ringAttn_reduce1_pm_opaque sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336],
        outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8091 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 11 5336 8091
        [8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15921 : denoteGraph_ringAttn pm initPM 15921 = denoteGraph_ringAttn pm initPM 5336 :=
    ringAttn_reduce1_pm_opaque pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336],
        outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15921 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 11 5336 15921
        [15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5344 = denoteGraph_ringAttn sm initSM 8091 :=
    ringAttn_reduce1_pm_opaque sm initSM 493
      { rank := 0, op := "OpName.FW_to", ins := [8091], outs := [5344] }
      8091 5344 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_to_out sm s 0 8091 5344 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 5344 = denoteGraph_ringAttn pm initPM 15921 :=
    ringAttn_reduce1_pm_opaque pm initPM 1060
      { rank := 1, op := "OpName.FW_to", ins := [15921], outs := [5344] }
      15921 5344 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_to_out pm s 1 15921 5344 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5344 = denoteGraph_ringAttn pm initPM 5344 := by
    rw [rSM, rPM, s8091, p15921, hv5336]
  have hshape : (denoteGraph_ringAttn sm initSM 5344).shape = [4096, 4, 64] := by
    rw [rSM, s8091]; exact hs5336
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5344 5344 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
