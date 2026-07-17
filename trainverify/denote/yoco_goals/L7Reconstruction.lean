/- Worker #23 — Layer-7 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_5020_ringAttn` (the layer-7
   sliding-window attention output, unconditional-given-WF) through the layer-7
   forward block.

   Unlike L2, the L7 block has NO gather-to-full node (L2's PM node 228
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L7
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_5024` targets `[8565, 8566]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L6Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 5021 — 2-tp reshape of the L7 attention output `5020 : [4096,16,64]` to
    `[4096,1024]` (SM node 205, PM nodes 471/472). -/
theorem recon_intermediateGoal_5021_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5021
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs8553, hs8554⟩ := twoTp_gather _ _ intermediateGoal_5020 5020 8553 8554
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5020_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5021
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5020) :=
    ringAttn_reshape_reduce_pm sm initSM 244 0 5020 5021 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8555
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8553) :=
    ringAttn_reshape_reduce_pm pm initPM 549 0 8553 8555 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8556
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8554) :=
    ringAttn_reshape_reduce_pm pm initPM 550 1 8554 8556 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5021
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8555, denoteGraph_ringAttn pm initPM 8556] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs8553 hs8554
  have hs8555 : (denoteGraph_ringAttn pm initPM 8555).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8556 : (denoteGraph_ringAttn pm initPM 8556).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5021 : (denoteGraph_ringAttn sm initSM 5021).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5021 5021 8555 8556 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5021 hs8555 hs8556

/-- 5022 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 206, PM
    nodes 473/474). -/
theorem recon_intermediateGoal_5022_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5022
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs8555, hs8556⟩ := twoTp_gather _ _ intermediateGoal_5021 5021 8555 8556
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5021_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5021 : (denoteGraph_ringAttn sm initSM 5021).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8555])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5022
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5021) :=
    ringAttn_reshape_reduce_pm sm initSM 245 0 5021 5022 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8561
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8555) :=
    ringAttn_reshape_reduce_pm pm initPM 551 0 8555 8561 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8562
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8556) :=
    ringAttn_reshape_reduce_pm pm initPM 552 1 8556 8562 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8561 = denoteGraph_ringAttn pm initPM 8555 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8555]
  have h18 : denoteGraph_ringAttn pm initPM 8562 = denoteGraph_ringAttn pm initPM 8556 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8556]
  have hval : denoteGraph_ringAttn sm initSM 5022
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8561, denoteGraph_ringAttn pm initPM 8562] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5021, hval05, hnr, ← h17, ← h18]
  have hs8561 : (denoteGraph_ringAttn pm initPM 8561).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8562 : (denoteGraph_ringAttn pm initPM 8562).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5022 : (denoteGraph_ringAttn sm initSM 5022).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5022 5022 8561 8562 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5022 hs8561 hs8562

/-- 5024 — 2-tp down-projection `fw_linear(5022, 5023)` (weight `5023 : [1024,1024]`,
    SM node 207, PM nodes 475/476). -/
theorem recon_intermediateGoal_5024_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5024
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs8561, hs8562⟩ := twoTp_gather _ _ intermediateGoal_5022 5022 8561 8562
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5022_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5023 : denoteGraph_ringAttn sm initSM 5023 = denoteGraph_ringAttn pm initPM 5023 :=
    veq_weight_ring initSM initPM hInit initGoal_5023 (by native_decide) 5023
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5023 : (denoteGraph_ringAttn sm initSM 5023).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5023 (by native_decide) 5023 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw5023 : (denoteGraph_ringAttn pm initPM 5023).shape = [1024, 1024] := by
    rw [← hw5023]; exact hsw5023
  have rSM : denoteGraph_ringAttn sm initSM 5024
      = fw_linear (denoteGraph_ringAttn sm initSM 5022) (denoteGraph_ringAttn sm initSM 5023) :=
    ringAttn_reduce2_pm_opaque sm initSM 246
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5022, 5023], outs := [5024] }
      5022 5023 5024 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5022 5023 5024)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8565
      = fw_linear (denoteGraph_ringAttn pm initPM 8561) (denoteGraph_ringAttn pm initPM 5023) :=
    ringAttn_reduce2_pm_opaque pm initPM 553
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8561, 5023], outs := [8565] }
      8561 5023 8565 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8561 5023 8565)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8566
      = fw_linear (denoteGraph_ringAttn pm initPM 8562) (denoteGraph_ringAttn pm initPM 5023) :=
    ringAttn_reduce2_pm_opaque pm initPM 554
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8562, 5023], outs := [8566] }
      8562 5023 8566 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8562 5023 8566)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5024
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8565, denoteGraph_ringAttn pm initPM 8566] := by
    rw [rSM, hval06, hw5023, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs8561 hs8562 hpw5023,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8565).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8561 hpw5023
  have hsp1 : (denoteGraph_ringAttn pm initPM 8566).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8562 hpw5023
  have hshape : (denoteGraph_ringAttn sm initSM 5024).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5024 5024 8565 8566 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5025 — 2-tp identity view of `5024` (SM node 208, PM nodes 477/478). -/
theorem recon_intermediateGoal_5025_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5025
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs8565, hs8566⟩ := twoTp_gather _ _ intermediateGoal_5024 5024 8565 8566
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5024_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5024 : (denoteGraph_ringAttn sm initSM 5024).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8565])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5025
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5024) :=
    ringAttn_reduce1_pm_opaque sm initSM 247
      { rank := 0, op := "OpName.FW_view", ins := [5024], outs := [5025], params := [4096, 1024] }
      5024 5025 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5024 5025)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8575
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8565) :=
    ringAttn_reduce1_pm_opaque pm initPM 555
      { rank := 0, op := "OpName.FW_view", ins := [8565], outs := [8575], params := [2048, 1024] }
      8565 8575 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8565 8575)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8576
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8566) :=
    ringAttn_reduce1_pm_opaque pm initPM 556
      { rank := 1, op := "OpName.FW_view", ins := [8566], outs := [8576], params := [2048, 1024] }
      8566 8576 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8566 8576)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 8575 = denoteGraph_ringAttn pm initPM 8565 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8565]
  have h32 : denoteGraph_ringAttn pm initPM 8576 = denoteGraph_ringAttn pm initPM 8566 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8566]
  have hval : denoteGraph_ringAttn sm initSM 5025
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8575, denoteGraph_ringAttn pm initPM 8576] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5024, hval08, hnr, ← h31, ← h32]
  have hs8575 : (denoteGraph_ringAttn pm initPM 8575).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8576 : (denoteGraph_ringAttn pm initPM 8576).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5025 : (denoteGraph_ringAttn sm initSM 5025).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5025 5025 8575 8576 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5025 hs8575 hs8576

/-- 5026 — 2-tp `FW_float(5025)` (identity, SM node 209, PM nodes 479/480). -/
theorem recon_intermediateGoal_5026_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5026
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs8575, hs8576⟩ := twoTp_gather _ _ intermediateGoal_5025 5025 8575 8576
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5025_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5026 = id (denoteGraph_ringAttn sm initSM 5025) :=
    ringAttn_reduce1_pm_opaque sm initSM 248
      { rank := 0, op := "OpName.FW_float", ins := [5025], outs := [5026] }
      5025 5026 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5025 5026 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8579 = id (denoteGraph_ringAttn pm initPM 8575) :=
    ringAttn_reduce1_pm_opaque pm initPM 557
      { rank := 0, op := "OpName.FW_float", ins := [8575], outs := [8579] }
      8575 8579 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8575 8579 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8580 = id (denoteGraph_ringAttn pm initPM 8576) :=
    ringAttn_reduce1_pm_opaque pm initPM 558
      { rank := 1, op := "OpName.FW_float", ins := [8576], outs := [8580] }
      8576 8580 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8576 8580 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5026
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8579, denoteGraph_ringAttn pm initPM 8580] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8579).shape = [2048, 1024] := by rw [rP0]; exact hs8575
  have hsp1 : (denoteGraph_ringAttn pm initPM 8580).shape = [2048, 1024] := by rw [rP1]; exact hs8576
  have hshape : (denoteGraph_ringAttn sm initSM 5026).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5026 5026 8579 8580 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7699 — 2-tp `mref2`-second copy of the L2 residual `5006` (SM node 197,
    PM nodes 455/456), carried into the L7 residual add. -/
theorem recon_intermediateGoal_7699_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7699
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs8509, hs8510⟩ := twoTp_gather _ _ intermediateGoal_5006 5006 8509 8510
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5006_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7699 : denoteGraph_ringAttn sm initSM 7699 = id (denoteGraph_ringAttn sm initSM 5006) :=
    ringAttn_reduce1_pm_opaque sm initSM 236
      { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699], params := [2] }
      5006 7699 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5006 7695 7699 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15121 : denoteGraph_ringAttn pm initPM 15121 = id (denoteGraph_ringAttn pm initPM 8509) :=
    ringAttn_reduce1_pm_opaque pm initPM 533
      { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121], params := [2] }
      8509 15121 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8509 15117 15121 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15129 : denoteGraph_ringAttn pm initPM 15129 = id (denoteGraph_ringAttn pm initPM 8510) :=
    ringAttn_reduce1_pm_opaque pm initPM 534
      { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129], params := [2] }
      8510 15129 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8510 15125 15129 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7699 p15121 p15129
  have hsp0 : (denoteGraph_ringAttn pm initPM 15121).shape = [2048, 1024] := by
    rw [p15121]; exact hs8509
  have hsp1 : (denoteGraph_ringAttn pm initPM 15129).shape = [2048, 1024] := by
    rw [p15129]; exact hs8510
  have hval : denoteGraph_ringAttn sm initSM 7699
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15121, denoteGraph_ringAttn pm initPM 15129] := by
    rw [s7699, hbr90, ← p15121, ← p15129]
  have hshape : (denoteGraph_ringAttn sm initSM 7699).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7699 7699 15121 15129 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5027 — 2-tp L7 residual add `7699 + 5026` (SM node 210, PM nodes 481/482). -/
theorem recon_intermediateGoal_5027_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5027
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs15121, hs15129⟩ := twoTp_gather _ _ intermediateGoal_7699 7699 15121 15129
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7699_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs8579, hs8580⟩ := twoTp_gather _ _ intermediateGoal_5026 5026 8579 8580
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5026_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5027
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7699) (denoteGraph_ringAttn sm initSM 5026) :=
    ringAttn_reduce2_pm_opaque sm initSM 249
      { rank := 0, op := "OpName.FW_add", ins := [7699, 5026], outs := [5027] }
      7699 5026 5027 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7699 5026 5027)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8583
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15121) (denoteGraph_ringAttn pm initPM 8579) :=
    ringAttn_reduce2_pm_opaque pm initPM 559
      { rank := 0, op := "OpName.FW_add", ins := [15121, 8579], outs := [8583] }
      15121 8579 8583 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15121 8579 8583)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8584
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15129) (denoteGraph_ringAttn pm initPM 8580) :=
    ringAttn_reduce2_pm_opaque pm initPM 560
      { rank := 1, op := "OpName.FW_add", ins := [15129, 8580], outs := [8584] }
      15129 8580 8584 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15129 8580 8584)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5027
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8583, denoteGraph_ringAttn pm initPM 8584] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15121 hs15129 hs8579 hs8580,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8583).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15121 hs8579
  have hsp1 : (denoteGraph_ringAttn pm initPM 8584).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15129 hs8580
  have hshape : (denoteGraph_ringAttn sm initSM 5027).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5027 5027 8583 8584 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5029 — 2-tp RMSNorm of `mref2-first(5027)` with replicated weight
    `5028 : [1024]` (SM node 212, PM nodes 485/486). -/
theorem recon_intermediateGoal_5029_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5029
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8583, hs8584⟩ := twoTp_gather _ _ intermediateGoal_5027 5027 8583 8584
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5027_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7716 : denoteGraph_ringAttn sm initSM 7716 = id (denoteGraph_ringAttn sm initSM 5027) :=
    ringAttn_reduce1_pm_opaque sm initSM 250
      { rank := 0, op := "OpName.FW_multiref", ins := [5027], outs := [7716, 7720], params := [2] }
      5027 7716 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5027 7716 7720)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15159 : denoteGraph_ringAttn pm initPM 15159 = id (denoteGraph_ringAttn pm initPM 8583) :=
    ringAttn_reduce1_pm_opaque pm initPM 561
      { rank := 0, op := "OpName.FW_multiref", ins := [8583], outs := [15159, 15163], params := [2] }
      8583 15159 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8583 15159 15163)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15167 : denoteGraph_ringAttn pm initPM 15167 = id (denoteGraph_ringAttn pm initPM 8584) :=
    ringAttn_reduce1_pm_opaque pm initPM 562
      { rank := 1, op := "OpName.FW_multiref", ins := [8584], outs := [15167, 15171], params := [2] }
      8584 15167 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8584 15167 15171)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7716 p15159 p15167
  have hs15159 : (denoteGraph_ringAttn pm initPM 15159).shape = [2048, 1024] := by
    rw [p15159]; exact hs8583
  have hs15167 : (denoteGraph_ringAttn pm initPM 15167).shape = [2048, 1024] := by
    rw [p15167]; exact hs8584
  have hbr08 : denoteGraph_ringAttn sm initSM 7716
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15159, denoteGraph_ringAttn pm initPM 15167] := by
    rw [s7716, hbr11, ← p15159, ← p15167]
  have hw5028 : denoteGraph_ringAttn sm initSM 5028 = denoteGraph_ringAttn pm initPM 5028 :=
    veq_weight_ring initSM initPM hInit initGoal_5028 (by native_decide) 5028
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5029
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7716) (denoteGraph_ringAttn sm initSM 5028) :=
    ringAttn_reduce2_pm_opaque sm initSM 251
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7716, 5028], outs := [5029] }
      7716 5028 5029 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7716 5028 5029)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8587
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15159) (denoteGraph_ringAttn pm initPM 5028) :=
    ringAttn_reduce2_pm_opaque pm initPM 563
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15159, 5028], outs := [8587] }
      15159 5028 8587 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15159 5028 8587)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8588
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15167) (denoteGraph_ringAttn pm initPM 5028) :=
    ringAttn_reduce2_pm_opaque pm initPM 564
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15167, 5028], outs := [8588] }
      15167 5028 8588 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15167 5028 8588)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5029
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8587, denoteGraph_ringAttn pm initPM 8588] := by
    rw [rSM, hbr08, hw5028, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15159 hs15167,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8587).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15159
  have hsp1 : (denoteGraph_ringAttn pm initPM 8588).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15167
  have hshape : (denoteGraph_ringAttn sm initSM 5029).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5029 5029 8587 8588 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5030 — 2-tp `FW_float(mref5-first(5029))` (identity, SM node 214,
    PM nodes 489/493; mref5-first via SM node 213, PM 487/488). -/
theorem recon_intermediateGoal_5030_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5030
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8587, hs8588⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7727 : denoteGraph_ringAttn sm initSM 7727 = id (denoteGraph_ringAttn sm initSM 5029) :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029],
        outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7727 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 5029 7727 [7731, 7735, 7739, 7743])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15178 : denoteGraph_ringAttn pm initPM 15178 = id (denoteGraph_ringAttn pm initPM 8587) :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587],
        outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15178 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 8587 15178 [15182, 15186, 15190, 15194])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15201 : denoteGraph_ringAttn pm initPM 15201 = id (denoteGraph_ringAttn pm initPM 8588) :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588],
        outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15201 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 8588 15201 [15205, 15209, 15213, 15217])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7727 p15178 p15201
  have hbrm : denoteGraph_ringAttn sm initSM 7727
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15178, denoteGraph_ringAttn pm initPM 15201] := by
    rw [s7727, hbr13, ← p15178, ← p15201]
  have rSM : denoteGraph_ringAttn sm initSM 5030 = id (denoteGraph_ringAttn sm initSM 7727) :=
    ringAttn_reduce1_pm_opaque sm initSM 253
      { rank := 0, op := "OpName.FW_float", ins := [7727], outs := [5030] }
      7727 5030 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7727 5030 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8589 = id (denoteGraph_ringAttn pm initPM 15178) :=
    ringAttn_reduce1_pm_opaque pm initPM 567
      { rank := 0, op := "OpName.FW_float", ins := [15178], outs := [8589] }
      15178 8589 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 15178 8589 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8590 = id (denoteGraph_ringAttn pm initPM 15201) :=
    ringAttn_reduce1_pm_opaque pm initPM 571
      { rank := 1, op := "OpName.FW_float", ins := [15201], outs := [8590] }
      15201 8590 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 15201 8590 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs15178 : (denoteGraph_ringAttn pm initPM 15178).shape = [2048, 1024] := by
    rw [p15178]; exact hs8587
  have hs15201 : (denoteGraph_ringAttn pm initPM 15201).shape = [2048, 1024] := by
    rw [p15201]; exact hs8588
  have hval : denoteGraph_ringAttn sm initSM 5030
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8589, denoteGraph_ringAttn pm initPM 8590] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8589).shape = [2048, 1024] := by
    rw [rP0]; exact hs15178
  have hsp1 : (denoteGraph_ringAttn pm initPM 8590).shape = [2048, 1024] := by
    rw [rP1]; exact hs15201
  have hshape : (denoteGraph_ringAttn sm initSM 5030).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5030 5030 8589 8590 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5032 — 2-tp router logits `fw_norm_linear(5030, 5031)` with weight
    `5031 : [64, 1024]` → `[4096, 64]` (SM node 218, PM nodes 497/501). -/
theorem recon_intermediateGoal_5032_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5032
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs8589, hs8590⟩ := twoTp_gather _ _ intermediateGoal_5030 5030 8589 8590
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5030_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5031 : denoteGraph_ringAttn sm initSM 5031 = denoteGraph_ringAttn pm initPM 5031 :=
    veq_weight_ring initSM initPM hInit initGoal_5031 (by native_decide) 5031
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5031 : (denoteGraph_ringAttn sm initSM 5031).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5031 (by native_decide) 5031 [64, 1024]
      rfl rfl (by native_decide)
  have hpw5031 : (denoteGraph_ringAttn pm initPM 5031).shape = [64, 1024] := by
    rw [← hw5031]; exact hsw5031
  have rSM : denoteGraph_ringAttn sm initSM 5032
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 5030) (denoteGraph_ringAttn sm initSM 5031) :=
    ringAttn_reduce2_pm_opaque sm initSM 257
      { rank := 0, op := "OpName.FW_norm_linear", ins := [5030, 5031], outs := [5032] }
      5030 5031 5032 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 5030 5031 5032)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8595
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8589) (denoteGraph_ringAttn pm initPM 5031) :=
    ringAttn_reduce2_pm_opaque pm initPM 575
      { rank := 0, op := "OpName.FW_norm_linear", ins := [8589, 5031], outs := [8595] }
      8589 5031 8595 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 8589 5031 8595)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8596
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8590) (denoteGraph_ringAttn pm initPM 5031) :=
    ringAttn_reduce2_pm_opaque pm initPM 579
      { rank := 1, op := "OpName.FW_norm_linear", ins := [8590, 5031], outs := [8596] }
      8590 5031 8596 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 8590 5031 8596)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5032
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8595, denoteGraph_ringAttn pm initPM 8596] := by
    rw [rSM, hval14, hw5031, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs8589 hs8590 hpw5031,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8595).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8589 hpw5031
  have hsp1 : (denoteGraph_ringAttn pm initPM 8596).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8590 hpw5031
  have hshape : (denoteGraph_ringAttn sm initSM 5032).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5032 5032 8595 8596 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L7 top-k routing (`5033`/`5034`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`8595`/`8596`) directly. -/

/-- Shared L7 top-k core: `5032` (full logits) is the dim-0 gather of the two
    per-rank shards `8595`/`8596`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L7 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 5032
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 8595, denoteGraph_ringAttn pm initPM 8596]
      ∧ (denoteGraph_ringAttn sm initSM 5032).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8595).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8596).shape = [2048, 64]
      ∧ ((sm.nodes.take 261).foldl (applyNodeRingAttn sm) initSM 5032).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 583).foldl (applyNodeRingAttn pm) initPM 8595).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 587).foldl (applyNodeRingAttn pm) initPM 8596).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs8595, hs8596⟩ := twoTp_gather _ _ intermediateGoal_5032 5032 8595 8596
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5032_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs5032sm : (denoteGraph_ringAttn sm initSM 5032).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs8595])]
    simp [List.set, List.getD]
  have hpre5032sm : denoteGraph_ringAttn sm initSM 5032
      = (sm.nodes.take 261).foldl (applyNodeRingAttn sm) initSM 5032 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5032 261 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 261).foldl (applyNodeRingAttn sm) initSM 5032).shape.reverse.head? = some 64 := by
    rw [← hpre5032sm, hs5032sm]; rfl
  have hpre8595 : denoteGraph_ringAttn pm initPM 8595
      = (pm.nodes.take 583).foldl (applyNodeRingAttn pm) initPM 8595 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8595 583 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 583).foldl (applyNodeRingAttn pm) initPM 8595).shape.reverse.head? = some 64 := by
    rw [← hpre8595, hs8595]; rfl
  have hpre8596 : denoteGraph_ringAttn pm initPM 8596
      = (pm.nodes.take 587).foldl (applyNodeRingAttn pm) initPM 8596 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8596 587 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 587).foldl (applyNodeRingAttn pm) initPM 8596).shape.reverse.head? = some 64 := by
    rw [← hpre8596, hs8596]; rfl
  exact ⟨hbr16, hs5032sm, hs8595, hs8596, hlastSM, hlast271, hlast275⟩

/-- 5033 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5033_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5033
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5032sm, hs8595, hs8596, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L7 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5033
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5032) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 261
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5032], outs := [5033, 5034, 5035], params := [8, 1] }
      5032 5033 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 261).foldl (applyNodeRingAttn sm) initSM) 0 5032 5033 5034 5035 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8597
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8595) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 583
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8595], outs := [8597, 8599, 8601], params := [8, 1] }
      8595 8597 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 583).foldl (applyNodeRingAttn pm) initPM) 0 8595 8597 8599 8601 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8598
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8596) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 587
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8596], outs := [8598, 8600, 8602], params := [8, 1] }
      8596 8598 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 587).foldl (applyNodeRingAttn pm) initPM) 1 8596 8598 8600 8602 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5033
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8597, denoteGraph_ringAttn pm initPM 8598] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8595 hs8596,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5033).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs5032sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8597).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8595]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8598).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8596]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5033 5033 8597 8598 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5034 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5034_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5034
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5032sm, hs8595, hs8596, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L7 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5034
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5032) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 261
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5032], outs := [5033, 5034, 5035], params := [8, 1] }
      5032 5034 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 261).foldl (applyNodeRingAttn sm) initSM) 0 5032 5033 5034 5035 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8599
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8595) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 583
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8595], outs := [8597, 8599, 8601], params := [8, 1] }
      8595 8599 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 583).foldl (applyNodeRingAttn pm) initPM) 0 8595 8597 8599 8601 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8600
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8596) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 587
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8596], outs := [8598, 8600, 8602], params := [8, 1] }
      8596 8600 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 587).foldl (applyNodeRingAttn pm) initPM) 1 8596 8598 8600 8602 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5034
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8599, denoteGraph_ringAttn pm initPM 8600] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8595 hs8596,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5034).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs5032sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8599).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8595]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8600).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8596]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5034 5034 8599 8600 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L7 router expert branches — reshape (`5039`/`5044`/`5048`) of the
    `mref5` copies (positions 2/3/4) of `5029`, all identity 2-tp views. -/

/-- 5039 — 2-tp identity reshape of `mref5-pos2(5029)` (SM node 215, PM 490/494). -/
theorem recon_intermediateGoal_5039_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5039
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8587, hs8588⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5029sm : (denoteGraph_ringAttn sm initSM 5029).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8587])]
    simp [List.set, List.getD]
  have s7735 : denoteGraph_ringAttn sm initSM 7735 = id (denoteGraph_ringAttn sm initSM 5029) :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029],
        outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7735 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15186 : denoteGraph_ringAttn pm initPM 15186 = id (denoteGraph_ringAttn pm initPM 8587) :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587],
        outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15186 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15209 : denoteGraph_ringAttn pm initPM 15209 = id (denoteGraph_ringAttn pm initPM 8588) :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588],
        outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15209 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7735 p15186 p15209
  have hs7735 : (denoteGraph_ringAttn sm initSM 7735).shape = [4096, 1024] := by rw [s7735]; exact hs5029sm
  have hs15186 : (denoteGraph_ringAttn pm initPM 15186).shape = [2048, 1024] := by rw [p15186]; exact hs8587
  have hs15209 : (denoteGraph_ringAttn pm initPM 15209).shape = [2048, 1024] := by rw [p15209]; exact hs8588
  have hbrm : denoteGraph_ringAttn sm initSM 7735
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15186, denoteGraph_ringAttn pm initPM 15209] := by
    rw [s7735, hbr13, ← p15186, ← p15209]
  have rSM : denoteGraph_ringAttn sm initSM 5039
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7735) :=
    ringAttn_reduce1_pm_opaque sm initSM 254
      { rank := 0, op := "OpName.FW_reshape", ins := [7735], outs := [5039], params := [4096, 1024] }
      7735 5039 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7735 5039)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8609
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15186) :=
    ringAttn_reduce1_pm_opaque pm initPM 568
      { rank := 0, op := "OpName.FW_reshape", ins := [15186], outs := [8609], params := [2048, 1024] }
      15186 8609 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15186 8609)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8610
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15209) :=
    ringAttn_reduce1_pm_opaque pm initPM 572
      { rank := 1, op := "OpName.FW_reshape", ins := [15209], outs := [8610], params := [2048, 1024] }
      15209 8610 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15209 8610)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 8609 = denoteGraph_ringAttn pm initPM 15186 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15186]
  have h66 : denoteGraph_ringAttn pm initPM 8610 = denoteGraph_ringAttn pm initPM 15209 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15209]
  have hval : denoteGraph_ringAttn sm initSM 5039
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8609, denoteGraph_ringAttn pm initPM 8610] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7735, hbrm, hnr, ← h65, ← h66]
  have hs8609 : (denoteGraph_ringAttn pm initPM 8609).shape = [2048, 1024] := by rw [h65]; exact hs15186
  have hs8610 : (denoteGraph_ringAttn pm initPM 8610).shape = [2048, 1024] := by rw [h66]; exact hs15209
  have hs5039 : (denoteGraph_ringAttn sm initSM 5039).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7735]; exact hs7735
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5039 5039 8609 8610 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5039 hs8609 hs8610

/-- 5044 — 2-tp identity reshape of `mref5-pos3(5029)` (SM node 216, PM 491/495). -/
theorem recon_intermediateGoal_5044_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5044
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8587, hs8588⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5029sm : (denoteGraph_ringAttn sm initSM 5029).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8587])]
    simp [List.set, List.getD]
  have s7739 : denoteGraph_ringAttn sm initSM 7739 = id (denoteGraph_ringAttn sm initSM 5029) :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029],
        outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7739 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15190 : denoteGraph_ringAttn pm initPM 15190 = id (denoteGraph_ringAttn pm initPM 8587) :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587],
        outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15190 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15213 : denoteGraph_ringAttn pm initPM 15213 = id (denoteGraph_ringAttn pm initPM 8588) :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588],
        outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15213 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7739 p15190 p15213
  have hs7739 : (denoteGraph_ringAttn sm initSM 7739).shape = [4096, 1024] := by rw [s7739]; exact hs5029sm
  have hs15190 : (denoteGraph_ringAttn pm initPM 15190).shape = [2048, 1024] := by rw [p15190]; exact hs8587
  have hs15213 : (denoteGraph_ringAttn pm initPM 15213).shape = [2048, 1024] := by rw [p15213]; exact hs8588
  have hbrm : denoteGraph_ringAttn sm initSM 7739
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15190, denoteGraph_ringAttn pm initPM 15213] := by
    rw [s7739, hbr13, ← p15190, ← p15213]
  have rSM : denoteGraph_ringAttn sm initSM 5044
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7739) :=
    ringAttn_reduce1_pm_opaque sm initSM 255
      { rank := 0, op := "OpName.FW_reshape", ins := [7739], outs := [5044], params := [4096, 1024] }
      7739 5044 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7739 5044)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8623
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15190) :=
    ringAttn_reduce1_pm_opaque pm initPM 569
      { rank := 0, op := "OpName.FW_reshape", ins := [15190], outs := [8623], params := [2048, 1024] }
      15190 8623 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15190 8623)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8624
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15213) :=
    ringAttn_reduce1_pm_opaque pm initPM 573
      { rank := 1, op := "OpName.FW_reshape", ins := [15213], outs := [8624], params := [2048, 1024] }
      15213 8624 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15213 8624)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 8623 = denoteGraph_ringAttn pm initPM 15190 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15190]
  have h80 : denoteGraph_ringAttn pm initPM 8624 = denoteGraph_ringAttn pm initPM 15213 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15213]
  have hval : denoteGraph_ringAttn sm initSM 5044
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8623, denoteGraph_ringAttn pm initPM 8624] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7739, hbrm, hnr, ← h79, ← h80]
  have hs8623 : (denoteGraph_ringAttn pm initPM 8623).shape = [2048, 1024] := by rw [h79]; exact hs15190
  have hs8624 : (denoteGraph_ringAttn pm initPM 8624).shape = [2048, 1024] := by rw [h80]; exact hs15213
  have hs5044 : (denoteGraph_ringAttn sm initSM 5044).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7739]; exact hs7739
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5044 5044 8623 8624 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5044 hs8623 hs8624

/-- 5048 — 2-tp identity reshape of `mref5-pos4(5029)` (SM node 217, PM 492/496). -/
theorem recon_intermediateGoal_5048_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5048
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8587, hs8588⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5029sm : (denoteGraph_ringAttn sm initSM 5029).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8587])]
    simp [List.set, List.getD]
  have s7743 : denoteGraph_ringAttn sm initSM 7743 = id (denoteGraph_ringAttn sm initSM 5029) :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029],
        outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7743 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15194 : denoteGraph_ringAttn pm initPM 15194 = id (denoteGraph_ringAttn pm initPM 8587) :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587],
        outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15194 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15217 : denoteGraph_ringAttn pm initPM 15217 = id (denoteGraph_ringAttn pm initPM 8588) :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588],
        outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15217 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7743 p15194 p15217
  have hs7743 : (denoteGraph_ringAttn sm initSM 7743).shape = [4096, 1024] := by rw [s7743]; exact hs5029sm
  have hs15194 : (denoteGraph_ringAttn pm initPM 15194).shape = [2048, 1024] := by rw [p15194]; exact hs8587
  have hs15217 : (denoteGraph_ringAttn pm initPM 15217).shape = [2048, 1024] := by rw [p15217]; exact hs8588
  have hbrm : denoteGraph_ringAttn sm initSM 7743
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15194, denoteGraph_ringAttn pm initPM 15217] := by
    rw [s7743, hbr13, ← p15194, ← p15217]
  have rSM : denoteGraph_ringAttn sm initSM 5048
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7743) :=
    ringAttn_reduce1_pm_opaque sm initSM 256
      { rank := 0, op := "OpName.FW_reshape", ins := [7743], outs := [5048], params := [4096, 1024] }
      7743 5048 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7743 5048)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8641
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15194) :=
    ringAttn_reduce1_pm_opaque pm initPM 570
      { rank := 0, op := "OpName.FW_reshape", ins := [15194], outs := [8641], params := [2048, 1024] }
      15194 8641 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15194 8641)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8642
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15217) :=
    ringAttn_reduce1_pm_opaque pm initPM 574
      { rank := 1, op := "OpName.FW_reshape", ins := [15217], outs := [8642], params := [2048, 1024] }
      15217 8642 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15217 8642)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 8641 = denoteGraph_ringAttn pm initPM 15194 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15194]
  have h98 : denoteGraph_ringAttn pm initPM 8642 = denoteGraph_ringAttn pm initPM 15217 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15217]
  have hval : denoteGraph_ringAttn sm initSM 5048
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8641, denoteGraph_ringAttn pm initPM 8642] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7743, hbrm, hnr, ← h97, ← h98]
  have hs8641 : (denoteGraph_ringAttn pm initPM 8641).shape = [2048, 1024] := by rw [h97]; exact hs15194
  have hs8642 : (denoteGraph_ringAttn pm initPM 8642).shape = [2048, 1024] := by rw [h98]; exact hs15217
  have hs5048 : (denoteGraph_ringAttn sm initSM 5048).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7743]; exact hs7743
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5048 5048 8641 8642 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5048 hs8641 hs8642

/-! ### L7 router expert mixlins (`5041`/`5046`/`5050`), 2-tp. -/

/-- 5041 — 2-tp `fw_linear(5039, 5040)`, weight `5040 : [1, 1024]` → `[4096, 1]`
    (SM node 219, PM nodes 498/502). -/
theorem recon_intermediateGoal_5041_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5041
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs8609, hs8610⟩ := twoTp_gather _ _ intermediateGoal_5039 5039 8609 8610
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5039_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5040 : denoteGraph_ringAttn sm initSM 5040 = denoteGraph_ringAttn pm initPM 5040 :=
    veq_weight_ring initSM initPM hInit initGoal_5040 (by native_decide) 5040
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5040 : (denoteGraph_ringAttn pm initPM 5040).shape = [1, 1024] := by
    rw [← hw5040]
    exact shape_weight_ring initSM initPM hInit initGoal_5040 (by native_decide) 5040 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5041
      = fw_linear (denoteGraph_ringAttn sm initSM 5039) (denoteGraph_ringAttn sm initSM 5040) :=
    ringAttn_reduce2_pm_opaque sm initSM 258
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5039, 5040], outs := [5041] }
      5039 5040 5041 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5039 5040 5041)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8613
      = fw_linear (denoteGraph_ringAttn pm initPM 8609) (denoteGraph_ringAttn pm initPM 5040) :=
    ringAttn_reduce2_pm_opaque pm initPM 576
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8609, 5040], outs := [8613] }
      8609 5040 8613 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8609 5040 8613)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8614
      = fw_linear (denoteGraph_ringAttn pm initPM 8610) (denoteGraph_ringAttn pm initPM 5040) :=
    ringAttn_reduce2_pm_opaque pm initPM 580
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8610, 5040], outs := [8614] }
      8610 5040 8614 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8610 5040 8614)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5041
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8613, denoteGraph_ringAttn pm initPM 8614] := by
    rw [rSM, hval23, hw5040, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs8609 hs8610 hpw5040,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8613).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8609 hpw5040
  have hsp1 : (denoteGraph_ringAttn pm initPM 8614).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8610 hpw5040
  have hshape : (denoteGraph_ringAttn sm initSM 5041).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5041 5041 8613 8614 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5046 — 2-tp `fw_linear(5044, 5045)`, weight `5045 : [512, 1024]` → `[4096, 512]`
    (SM node 220, PM nodes 499/503). -/
theorem recon_intermediateGoal_5046_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5046
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs8623, hs8624⟩ := twoTp_gather _ _ intermediateGoal_5044 5044 8623 8624
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5044_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5045 : denoteGraph_ringAttn sm initSM 5045 = denoteGraph_ringAttn pm initPM 5045 :=
    veq_weight_ring initSM initPM hInit initGoal_5045 (by native_decide) 5045
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5045 : (denoteGraph_ringAttn pm initPM 5045).shape = [512, 1024] := by
    rw [← hw5045]
    exact shape_weight_ring initSM initPM hInit initGoal_5045 (by native_decide) 5045 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5046
      = fw_linear (denoteGraph_ringAttn sm initSM 5044) (denoteGraph_ringAttn sm initSM 5045) :=
    ringAttn_reduce2_pm_opaque sm initSM 259
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5044, 5045], outs := [5046] }
      5044 5045 5046 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5044 5045 5046)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8627
      = fw_linear (denoteGraph_ringAttn pm initPM 8623) (denoteGraph_ringAttn pm initPM 5045) :=
    ringAttn_reduce2_pm_opaque pm initPM 577
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8623, 5045], outs := [8627] }
      8623 5045 8627 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8623 5045 8627)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8628
      = fw_linear (denoteGraph_ringAttn pm initPM 8624) (denoteGraph_ringAttn pm initPM 5045) :=
    ringAttn_reduce2_pm_opaque pm initPM 581
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8624, 5045], outs := [8628] }
      8624 5045 8628 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8624 5045 8628)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5046
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8627, denoteGraph_ringAttn pm initPM 8628] := by
    rw [rSM, hval28, hw5045, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8623 hs8624 hpw5045,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8627).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8623 hpw5045
  have hsp1 : (denoteGraph_ringAttn pm initPM 8628).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8624 hpw5045
  have hshape : (denoteGraph_ringAttn sm initSM 5046).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5046 5046 8627 8628 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5050 — 2-tp `fw_linear(5048, 5049)`, weight `5049 : [512, 1024]` → `[4096, 512]`
    (SM node 221, PM nodes 500/504). -/
theorem recon_intermediateGoal_5050_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5050
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs8641, hs8642⟩ := twoTp_gather _ _ intermediateGoal_5048 5048 8641 8642
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5048_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5049 : denoteGraph_ringAttn sm initSM 5049 = denoteGraph_ringAttn pm initPM 5049 :=
    veq_weight_ring initSM initPM hInit initGoal_5049 (by native_decide) 5049
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5049 : (denoteGraph_ringAttn pm initPM 5049).shape = [512, 1024] := by
    rw [← hw5049]
    exact shape_weight_ring initSM initPM hInit initGoal_5049 (by native_decide) 5049 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5050
      = fw_linear (denoteGraph_ringAttn sm initSM 5048) (denoteGraph_ringAttn sm initSM 5049) :=
    ringAttn_reduce2_pm_opaque sm initSM 260
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5048, 5049], outs := [5050] }
      5048 5049 5050 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5048 5049 5050)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8645
      = fw_linear (denoteGraph_ringAttn pm initPM 8641) (denoteGraph_ringAttn pm initPM 5049) :=
    ringAttn_reduce2_pm_opaque pm initPM 578
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8641, 5049], outs := [8645] }
      8641 5049 8645 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8641 5049 8645)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8646
      = fw_linear (denoteGraph_ringAttn pm initPM 8642) (denoteGraph_ringAttn pm initPM 5049) :=
    ringAttn_reduce2_pm_opaque pm initPM 582
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8642, 5049], outs := [8646] }
      8642 5049 8646 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8642 5049 8646)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5050
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8645, denoteGraph_ringAttn pm initPM 8646] := by
    rw [rSM, hval32, hw5049, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8641 hs8642 hpw5049,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8645).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8641 hpw5049
  have hsp1 : (denoteGraph_ringAttn pm initPM 8646).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8642 hpw5049
  have hshape : (denoteGraph_ringAttn sm initSM 5050).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5050 5050 8645 8646 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L7 router expert views (`5042`/`5047`/`5051`), identity 2-tp views. -/

/-- 5042 — 2-tp identity view of `5041` → `[4096, 1]` (SM node 223, PM 506/510). -/
theorem recon_intermediateGoal_5042_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5042
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs8613, hs8614⟩ := twoTp_gather _ _ intermediateGoal_5041 5041 8613 8614
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5041_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5041 : (denoteGraph_ringAttn sm initSM 5041).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8613])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5042
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 5041) :=
    ringAttn_reduce1_pm_opaque sm initSM 262
      { rank := 0, op := "OpName.FW_view", ins := [5041], outs := [5042], params := [4096, 1] }
      5041 5042 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 5041 5042)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8619
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8613) :=
    ringAttn_reduce1_pm_opaque pm initPM 584
      { rank := 0, op := "OpName.FW_view", ins := [8613], outs := [8619], params := [2048, 1] }
      8613 8619 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 8613 8619)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8620
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8614) :=
    ringAttn_reduce1_pm_opaque pm initPM 588
      { rank := 1, op := "OpName.FW_view", ins := [8614], outs := [8620], params := [2048, 1] }
      8614 8620 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 8614 8620)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 8619 = denoteGraph_ringAttn pm initPM 8613 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs8613]
  have h76 : denoteGraph_ringAttn pm initPM 8620 = denoteGraph_ringAttn pm initPM 8614 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs8614]
  have hval : denoteGraph_ringAttn sm initSM 5042
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8619, denoteGraph_ringAttn pm initPM 8620] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5041, hval25, hnr, ← h75, ← h76]
  have hs8619 : (denoteGraph_ringAttn pm initPM 8619).shape = [2048, 1] := by rw [h75]; exact hs8613
  have hs8620 : (denoteGraph_ringAttn pm initPM 8620).shape = [2048, 1] := by rw [h76]; exact hs8614
  have hs5042 : (denoteGraph_ringAttn sm initSM 5042).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5041]; exact hs5041
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5042 5042 8619 8620 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5042 hs8619 hs8620

/-- 5047 — 2-tp identity view of `5046` → `[4096, 512]` (SM node 224, PM 507/511). -/
theorem recon_intermediateGoal_5047_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5047
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs8627, hs8628⟩ := twoTp_gather _ _ intermediateGoal_5046 5046 8627 8628
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5046_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5046 : (denoteGraph_ringAttn sm initSM 5046).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8627])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5047
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5046) :=
    ringAttn_reduce1_pm_opaque sm initSM 263
      { rank := 0, op := "OpName.FW_view", ins := [5046], outs := [5047], params := [4096, 512] }
      5046 5047 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5046 5047)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8637
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8627) :=
    ringAttn_reduce1_pm_opaque pm initPM 585
      { rank := 0, op := "OpName.FW_view", ins := [8627], outs := [8637], params := [2048, 512] }
      8627 8637 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8627 8637)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8638
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8628) :=
    ringAttn_reduce1_pm_opaque pm initPM 589
      { rank := 1, op := "OpName.FW_view", ins := [8628], outs := [8638], params := [2048, 512] }
      8628 8638 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8628 8638)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 8637 = denoteGraph_ringAttn pm initPM 8627 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8627]
  have h94 : denoteGraph_ringAttn pm initPM 8638 = denoteGraph_ringAttn pm initPM 8628 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8628]
  have hval : denoteGraph_ringAttn sm initSM 5047
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8637, denoteGraph_ringAttn pm initPM 8638] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5046, hval30, hnr, ← h93, ← h94]
  have hs8637 : (denoteGraph_ringAttn pm initPM 8637).shape = [2048, 512] := by rw [h93]; exact hs8627
  have hs8638 : (denoteGraph_ringAttn pm initPM 8638).shape = [2048, 512] := by rw [h94]; exact hs8628
  have hs5047 : (denoteGraph_ringAttn sm initSM 5047).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5046]; exact hs5046
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5047 5047 8637 8638 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5047 hs8637 hs8638

/-- 5051 — 2-tp identity view of `5050` → `[4096, 512]` (SM node 225, PM 508/512). -/
theorem recon_intermediateGoal_5051_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5051
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs8645, hs8646⟩ := twoTp_gather _ _ intermediateGoal_5050 5050 8645 8646
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5050_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5050 : (denoteGraph_ringAttn sm initSM 5050).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8645])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5051
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5050) :=
    ringAttn_reduce1_pm_opaque sm initSM 264
      { rank := 0, op := "OpName.FW_view", ins := [5050], outs := [5051], params := [4096, 512] }
      5050 5051 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5050 5051)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8655
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8645) :=
    ringAttn_reduce1_pm_opaque pm initPM 586
      { rank := 0, op := "OpName.FW_view", ins := [8645], outs := [8655], params := [2048, 512] }
      8645 8655 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8645 8655)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8656
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8646) :=
    ringAttn_reduce1_pm_opaque pm initPM 590
      { rank := 1, op := "OpName.FW_view", ins := [8646], outs := [8656], params := [2048, 512] }
      8646 8656 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8646 8656)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 8655 = denoteGraph_ringAttn pm initPM 8645 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8645]
  have h12 : denoteGraph_ringAttn pm initPM 8656 = denoteGraph_ringAttn pm initPM 8646 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8646]
  have hval : denoteGraph_ringAttn sm initSM 5051
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8655, denoteGraph_ringAttn pm initPM 8656] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5050, hval34, hnr, ← h11, ← h12]
  have hs8655 : (denoteGraph_ringAttn pm initPM 8655).shape = [2048, 512] := by rw [h11]; exact hs8645
  have hs8656 : (denoteGraph_ringAttn pm initPM 8656).shape = [2048, 512] := by rw [h12]; exact hs8646
  have hs5051 : (denoteGraph_ringAttn sm initSM 5051).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5050]; exact hs5050
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5051 5051 8655 8656 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5051 hs8655 hs8656

/-! ### L7 MoE gate/expert branch (`5043` sigmoid, `5052` swiglu, `5053` reshape,
    `5055` mixlin, `5056` view, `5057` broadcast-mul), all 2-tp shard-direct. -/

/-- 5043 — 2-tp `fw_sigmoid(5042)` → `[4096, 1]` (SM node 227, PM 514/517). -/
theorem recon_intermediateGoal_5043_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5043
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs8619, hs8620⟩ := twoTp_gather _ _ intermediateGoal_5042 5042 8619 8620
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5042_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5043 = fw_sigmoid (denoteGraph_ringAttn sm initSM 5042) :=
    ringAttn_reduce1_pm_opaque sm initSM 266
      { rank := 0, op := "OpName.FW_sigmoid", ins := [5042], outs := [5043] }
      5042 5043 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 5042 5043 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8621 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8619) :=
    ringAttn_reduce1_pm_opaque pm initPM 592
      { rank := 0, op := "OpName.FW_sigmoid", ins := [8619], outs := [8621] }
      8619 8621 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 8619 8621 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8622 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8620) :=
    ringAttn_reduce1_pm_opaque pm initPM 595
      { rank := 1, op := "OpName.FW_sigmoid", ins := [8620], outs := [8622] }
      8620 8622 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 8620 8622 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5043
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8621, denoteGraph_ringAttn pm initPM 8622] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs8619 hs8620, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5043).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8619])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8621).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs8619
  have hsp1 : (denoteGraph_ringAttn pm initPM 8622).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs8620
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5043 5043 8621 8622 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5052 — 2-tp `fw_swiglu(5047, 5051)` → `[4096, 512]` (SM node 228, PM 515/518). -/
theorem recon_intermediateGoal_5052_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5052
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs8637, hs8638⟩ := twoTp_gather _ _ intermediateGoal_5047 5047 8637 8638
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5047_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs8655, hs8656⟩ := twoTp_gather _ _ intermediateGoal_5051 5051 8655 8656
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5051_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5052
      = fw_swiglu (denoteGraph_ringAttn sm initSM 5047) (denoteGraph_ringAttn sm initSM 5051) :=
    ringAttn_reduce2_pm_opaque sm initSM 267
      { rank := 0, op := "OpName.FW_swiglu", ins := [5047, 5051], outs := [5052] }
      5047 5051 5052 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 5047 5051 5052 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8659
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8637) (denoteGraph_ringAttn pm initPM 8655) :=
    ringAttn_reduce2_pm_opaque pm initPM 593
      { rank := 0, op := "OpName.FW_swiglu", ins := [8637, 8655], outs := [8659] }
      8637 8655 8659 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 8637 8655 8659 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8660
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8638) (denoteGraph_ringAttn pm initPM 8656) :=
    ringAttn_reduce2_pm_opaque pm initPM 596
      { rank := 1, op := "OpName.FW_swiglu", ins := [8638, 8656], outs := [8660] }
      8638 8656 8660 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 8638 8656 8660 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5052
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8659, denoteGraph_ringAttn pm initPM 8660] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs8637 hs8638 hs8655 hs8656,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5052).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8655])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8659).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8655
  have hsp1 : (denoteGraph_ringAttn pm initPM 8660).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8656
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5052 5052 8659 8660 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5053 — 2-tp identity reshape of `5052` → `[4096, 512]` (SM node 229, PM 519/520). -/
theorem recon_intermediateGoal_5053_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5053
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs8659, hs8660⟩ := twoTp_gather _ _ intermediateGoal_5052 5052 8659 8660
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5052_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5052 : (denoteGraph_ringAttn sm initSM 5052).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8659])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5053
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5052) :=
    ringAttn_reduce1_pm_opaque sm initSM 268
      { rank := 0, op := "OpName.FW_reshape", ins := [5052], outs := [5053], params := [4096, 512] }
      5052 5053 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5052 5053)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8661
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8659) :=
    ringAttn_reduce1_pm_opaque pm initPM 597
      { rank := 0, op := "OpName.FW_reshape", ins := [8659], outs := [8661], params := [2048, 512] }
      8659 8661 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8659 8661)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8662
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8660) :=
    ringAttn_reduce1_pm_opaque pm initPM 598
      { rank := 1, op := "OpName.FW_reshape", ins := [8660], outs := [8662], params := [2048, 512] }
      8660 8662 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8660 8662)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8661 = denoteGraph_ringAttn pm initPM 8659 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8659]
  have h18 : denoteGraph_ringAttn pm initPM 8662 = denoteGraph_ringAttn pm initPM 8660 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8660]
  have hval : denoteGraph_ringAttn sm initSM 5053
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8661, denoteGraph_ringAttn pm initPM 8662] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5052, hval36, hnr, ← h17, ← h18]
  have hs8661 : (denoteGraph_ringAttn pm initPM 8661).shape = [2048, 512] := by rw [h17]; exact hs8659
  have hs8662 : (denoteGraph_ringAttn pm initPM 8662).shape = [2048, 512] := by rw [h18]; exact hs8660
  have hs5053 : (denoteGraph_ringAttn sm initSM 5053).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5052]; exact hs5052
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5053 5053 8661 8662 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5053 hs8661 hs8662

/-- 5055 — 2-tp `fw_linear(5053, 5054)`, weight `5054 : [1024, 512]` → `[4096, 1024]`
    (SM node 230, PM 521/522). -/
theorem recon_intermediateGoal_5055_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5055
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs8661, hs8662⟩ := twoTp_gather _ _ intermediateGoal_5053 5053 8661 8662
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5053_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5054 : denoteGraph_ringAttn sm initSM 5054 = denoteGraph_ringAttn pm initPM 5054 :=
    veq_weight_ring initSM initPM hInit initGoal_5054 (by native_decide) 5054
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5054 : (denoteGraph_ringAttn pm initPM 5054).shape = [1024, 512] := by
    rw [← hw5054]
    exact shape_weight_ring initSM initPM hInit initGoal_5054 (by native_decide) 5054 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5055
      = fw_linear (denoteGraph_ringAttn sm initSM 5053) (denoteGraph_ringAttn sm initSM 5054) :=
    ringAttn_reduce2_pm_opaque sm initSM 269
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5053, 5054], outs := [5055] }
      5053 5054 5055 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5053 5054 5055)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8667
      = fw_linear (denoteGraph_ringAttn pm initPM 8661) (denoteGraph_ringAttn pm initPM 5054) :=
    ringAttn_reduce2_pm_opaque pm initPM 599
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8661, 5054], outs := [8667] }
      8661 5054 8667 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8661 5054 8667)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8668
      = fw_linear (denoteGraph_ringAttn pm initPM 8662) (denoteGraph_ringAttn pm initPM 5054) :=
    ringAttn_reduce2_pm_opaque pm initPM 600
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8662, 5054], outs := [8668] }
      8662 5054 8668 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8662 5054 8668)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5055
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8667, denoteGraph_ringAttn pm initPM 8668] := by
    rw [rSM, hval37, hw5054, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs8661 hs8662 hpw5054,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8667).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8661 hpw5054
  have hsp1 : (denoteGraph_ringAttn pm initPM 8668).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8662 hpw5054
  have hshape : (denoteGraph_ringAttn sm initSM 5055).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5055 5055 8667 8668 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5056 — 2-tp identity view of `5055` → `[4096, 1024]` (SM node 231, PM 523/524). -/
theorem recon_intermediateGoal_5056_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5056
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs8667, hs8668⟩ := twoTp_gather _ _ intermediateGoal_5055 5055 8667 8668
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5055_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5055 : (denoteGraph_ringAttn sm initSM 5055).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8667])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5056
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5055) :=
    ringAttn_reduce1_pm_opaque sm initSM 270
      { rank := 0, op := "OpName.FW_view", ins := [5055], outs := [5056], params := [4096, 1024] }
      5055 5056 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5055 5056)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8677
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8667) :=
    ringAttn_reduce1_pm_opaque pm initPM 601
      { rank := 0, op := "OpName.FW_view", ins := [8667], outs := [8677], params := [2048, 1024] }
      8667 8677 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8667 8677)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8678
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8668) :=
    ringAttn_reduce1_pm_opaque pm initPM 602
      { rank := 1, op := "OpName.FW_view", ins := [8668], outs := [8678], params := [2048, 1024] }
      8668 8678 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8668 8678)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 8677 = denoteGraph_ringAttn pm initPM 8667 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8667]
  have h34 : denoteGraph_ringAttn pm initPM 8678 = denoteGraph_ringAttn pm initPM 8668 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8668]
  have hval : denoteGraph_ringAttn sm initSM 5056
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8677, denoteGraph_ringAttn pm initPM 8678] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5055, hval39, hnr, ← h33, ← h34]
  have hs8677 : (denoteGraph_ringAttn pm initPM 8677).shape = [2048, 1024] := by rw [h33]; exact hs8667
  have hs8678 : (denoteGraph_ringAttn pm initPM 8678).shape = [2048, 1024] := by rw [h34]; exact hs8668
  have hs5056 : (denoteGraph_ringAttn sm initSM 5056).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5055]; exact hs5055
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5056 5056 8677 8678 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5056 hs8677 hs8678

/-- 5057 — 2-tp broadcast `mul(5043, 5056)` → `[4096, 1024]` (SM node 232, PM 525/526). -/
theorem recon_intermediateGoal_5057_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5057
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_5043 5043 8621 8622
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5043_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_5056 5056 8677 8678
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5056_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5057
      = elemwiseMul (denoteGraph_ringAttn sm initSM 5043) (denoteGraph_ringAttn sm initSM 5056) :=
    ringAttn_reduce2_pm_opaque sm initSM 271
      { rank := 0, op := "OpName.FW_mul", ins := [5043, 5056], outs := [5057] }
      5043 5056 5057 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 5043 5056 5057)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8681
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8621) (denoteGraph_ringAttn pm initPM 8677) :=
    ringAttn_reduce2_pm_opaque pm initPM 603
      { rank := 0, op := "OpName.FW_mul", ins := [8621, 8677], outs := [8681] }
      8621 8677 8681 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 8621 8677 8681)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8682
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8622) (denoteGraph_ringAttn pm initPM 8678) :=
    ringAttn_reduce2_pm_opaque pm initPM 604
      { rank := 1, op := "OpName.FW_mul", ins := [8622, 8678], outs := [8682] }
      8622 8678 8682 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 8622 8678 8682)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5057
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8681, denoteGraph_ringAttn pm initPM 8682] := by
    rw [rSM, hvalS, hvalV, hnr,
        fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide) hsS0 hsS1 hsV0 hsV1,
        rP0, rP1]
  have mulBShape : ∀ (x y : Tensor) (a : Nat),
      x.shape = [a, 1] → y.shape = [a, 1024] → (elemwiseMul x y).shape = [a, 1024] := by
    intro x y a hx hy
    show outShape2 x y = [a, 1024]
    unfold outShape2
    rw [hx, hy]
    show (max a a) :: (1024 : Nat) :: [] = [a, 1024]
    rw [Nat.max_self]
  have hshape : (denoteGraph_ringAttn sm initSM 5057).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 5043).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 5056).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 8681).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 8682).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5057 5057 8681 8682 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 5038 — layer-7 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 5038 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`8607`), rank 1 →
    `[32, 64)` (`8608`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `8599`/`8600` are expert-local (the
    `wf5038_hdisjA/B` fields).  Token input `7731 = mref5-pos1(5029)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 226, PM nodes 513/516). -/
theorem recon_intermediateGoal_5038_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5038
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 7731 = mref5-pos1(5029).
  obtain ⟨hbr13, hs8587, hs8588⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7731 : denoteGraph_ringAttn sm initSM 7731 = id (denoteGraph_ringAttn sm initSM 5029) :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029],
        outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7731 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15182 : denoteGraph_ringAttn pm initPM 15182 = id (denoteGraph_ringAttn pm initPM 8587) :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587],
        outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15182 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15205 : denoteGraph_ringAttn pm initPM 15205 = id (denoteGraph_ringAttn pm initPM 8588) :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588],
        outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15205 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7731 p15182 p15205
  have hsInA : (denoteGraph_ringAttn pm initPM 15182).shape = [2048, 1024] := by
    rw [p15182]; exact hs8587
  have hsInB : (denoteGraph_ringAttn pm initPM 15205).shape = [2048, 1024] := by
    rw [p15205]; exact hs8588
  have hbrIn : denoteGraph_ringAttn sm initSM 7731
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 15182, denoteGraph_ringAttn pm initPM 15205] := by
    rw [s7731, hbr13, hnr, ← p15182, ← p15205]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_5033 5033 8597 8598
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5033_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_5034 5034 8599 8600
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5034_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 5033
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8597, denoteGraph_ringAttn pm initPM 8598] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 5034
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8599, denoteGraph_ringAttn pm initPM 8600] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_5036
    (by native_decide) 5036 8603 8604 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_5037
    (by native_decide) 5037 8605 8606 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 8603).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5036 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5036, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8603 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 8604).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5036 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5036, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8604 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 8605).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5037 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5037, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8605 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 8606).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5037 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5037, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8606 (by native_decide)]; exact hs.2
  -- SM 5038 = full-range all2all (SM node 226).
  have hSMout : denoteGraph_ringAttn sm initSM 5038
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7731)
          (denoteGraph_ringAttn sm initSM 5033) (denoteGraph_ringAttn sm initSM 5034)
          (denoteGraph_ringAttn sm initSM 5036) (denoteGraph_ringAttn sm initSM 5037)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 265
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7731, 5033, 5034, 5036, 5037],
        outs := [5038], params := [64, 0, 64, 8] }
      7731 5033 5034 5036 5037 5038
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7731 5033 5034 5036 5037 5038 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8607 = rank-0 sharded-range all2all (PM node 513).
  have hP0 : denoteGraph_ringAttn pm initPM 8607
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15182)
          (denoteGraph_ringAttn pm initPM 8597) (denoteGraph_ringAttn pm initPM 8599)
          (denoteGraph_ringAttn pm initPM 8603) (denoteGraph_ringAttn pm initPM 8605)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 591
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15182, 8597, 8599, 8603, 8605],
        outs := [8607], params := [64, 0, 32, 8] }
      15182 8597 8599 8603 8605 8607
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 15182 8597 8599 8603 8605 8607 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8608 = rank-1 sharded-range all2all (PM node 516).
  have hP1 : denoteGraph_ringAttn pm initPM 8608
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15205)
          (denoteGraph_ringAttn pm initPM 8598) (denoteGraph_ringAttn pm initPM 8600)
          (denoteGraph_ringAttn pm initPM 8604) (denoteGraph_ringAttn pm initPM 8606)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 594
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15205, 8598, 8600, 8604, 8606],
        outs := [8608], params := [64, 32, 64, 8] }
      15205 8598 8600 8604 8606 8608
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 15205 8598 8600 8604 8606 8608 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 15182) (denoteGraph_ringAttn pm initPM 15205)
      (denoteGraph_ringAttn pm initPM 8597) (denoteGraph_ringAttn pm initPM 8598)
      (denoteGraph_ringAttn pm initPM 8599) (denoteGraph_ringAttn pm initPM 8600)
      (denoteGraph_ringAttn pm initPM 8603) (denoteGraph_ringAttn pm initPM 8604)
      (denoteGraph_ringAttn pm initPM 8605) (denoteGraph_ringAttn pm initPM 8606)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf5038_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf5038_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 5038
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8607, denoteGraph_ringAttn pm initPM 8608] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8607).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8608).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 5038).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5038 5038 8607 8608 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L7 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7720 — second position of the L7 pre-MoE residual `mref2(5027)` (2-tp, PM
    shards `15163`/`15171`).  Unlike L2's `7668` there is no gather-to-full/chunk
    because `5027` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 211, PM nodes 477/478). -/
theorem recon_intermediateGoal_7720_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7720
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8583, hs8584⟩ := twoTp_gather _ _ intermediateGoal_5027 5027 8583 8584
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5027_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7720 : denoteGraph_ringAttn sm initSM 7720 = id (denoteGraph_ringAttn sm initSM 5027) :=
    ringAttn_reduce1_pm_opaque sm initSM 250
      { rank := 0, op := "OpName.FW_multiref", ins := [5027], outs := [7716, 7720], params := [2] }
      5027 7720 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5027 7716 7720 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15163 : denoteGraph_ringAttn pm initPM 15163 = id (denoteGraph_ringAttn pm initPM 8583) :=
    ringAttn_reduce1_pm_opaque pm initPM 561
      { rank := 0, op := "OpName.FW_multiref", ins := [8583], outs := [15159, 15163], params := [2] }
      8583 15163 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8583 15159 15163 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15171 : denoteGraph_ringAttn pm initPM 15171 = id (denoteGraph_ringAttn pm initPM 8584) :=
    ringAttn_reduce1_pm_opaque pm initPM 562
      { rank := 1, op := "OpName.FW_multiref", ins := [8584], outs := [15167, 15171], params := [2] }
      8584 15171 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8584 15167 15171 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7720 p15163 p15171
  have hsp0 : (denoteGraph_ringAttn pm initPM 15163).shape = [2048, 1024] := by
    rw [p15163]; exact hs8583
  have hsp1 : (denoteGraph_ringAttn pm initPM 15171).shape = [2048, 1024] := by
    rw [p15171]; exact hs8584
  have hval : denoteGraph_ringAttn sm initSM 7720
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15163, denoteGraph_ringAttn pm initPM 15171] := by
    rw [s7720, hbr11, ← p15163, ← p15171]
  have hshape : (denoteGraph_ringAttn sm initSM 7720).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7720 7720 15163 15171 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5058 — post-MoE residual add `5038 + 5057` (2-tp, PM `8685`/`8686`). -/
theorem recon_intermediateGoal_5058_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5058
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs8607, hs8608⟩ := twoTp_gather _ _ intermediateGoal_5038 5038 8607 8608
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5038_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs8681, hs8682⟩ := twoTp_gather _ _ intermediateGoal_5057 5057 8681 8682
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5057_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5058
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 5038) (denoteGraph_ringAttn sm initSM 5057) :=
    ringAttn_reduce2_pm_opaque sm initSM 272
      { rank := 0, op := "OpName.FW_add", ins := [5038, 5057], outs := [5058] }
      5038 5057 5058 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 5038 5057 5058)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8685
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8607) (denoteGraph_ringAttn pm initPM 8681) :=
    ringAttn_reduce2_pm_opaque pm initPM 605
      { rank := 0, op := "OpName.FW_add", ins := [8607, 8681], outs := [8685] }
      8607 8681 8685 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 8607 8681 8685)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8686
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8608) (denoteGraph_ringAttn pm initPM 8682) :=
    ringAttn_reduce2_pm_opaque pm initPM 606
      { rank := 1, op := "OpName.FW_add", ins := [8608, 8682], outs := [8686] }
      8608 8682 8686 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 8608 8682 8686)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5058
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8685, denoteGraph_ringAttn pm initPM 8686] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs8607 hs8608 hs8681 hs8682,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8685).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8607 hs8681
  have hsp1 : (denoteGraph_ringAttn pm initPM 8686).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8608 hs8682
  have hshape : (denoteGraph_ringAttn sm initSM 5058).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5058 5058 8685 8686 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5059 — `FW_float(5058)` (identity, 2-tp PM `8691`/`8692`). -/
theorem recon_intermediateGoal_5059_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5059
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs8685, hs8686⟩ := twoTp_gather _ _ intermediateGoal_5058 5058 8685 8686
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5058_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5059 = id (denoteGraph_ringAttn sm initSM 5058) :=
    ringAttn_reduce1_pm_opaque sm initSM 273
      { rank := 0, op := "OpName.FW_float", ins := [5058], outs := [5059] }
      5058 5059 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5058 5059 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8691 = id (denoteGraph_ringAttn pm initPM 8685) :=
    ringAttn_reduce1_pm_opaque pm initPM 607
      { rank := 0, op := "OpName.FW_float", ins := [8685], outs := [8691] }
      8685 8691 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8685 8691 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8692 = id (denoteGraph_ringAttn pm initPM 8686) :=
    ringAttn_reduce1_pm_opaque pm initPM 608
      { rank := 1, op := "OpName.FW_float", ins := [8686], outs := [8692] }
      8686 8692 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8686 8692 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5059
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8691, denoteGraph_ringAttn pm initPM 8692] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8691).shape = [2048, 1024] := by rw [rP0]; exact hs8685
  have hsp1 : (denoteGraph_ringAttn pm initPM 8692).shape = [2048, 1024] := by rw [rP1]; exact hs8686
  have hshape : (denoteGraph_ringAttn sm initSM 5059).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5059 5059 8691 8692 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5060 — cross-block residual add `7720 + 5059` (2-tp, PM `8695`/`8696`). -/
theorem recon_intermediateGoal_5060_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5060
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs15163, hs15171⟩ := twoTp_gather _ _ intermediateGoal_7720 7720 15163 15171
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7720_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs8691, hs8692⟩ := twoTp_gather _ _ intermediateGoal_5059 5059 8691 8692
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5059_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5060
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7720) (denoteGraph_ringAttn sm initSM 5059) :=
    ringAttn_reduce2_pm_opaque sm initSM 274
      { rank := 0, op := "OpName.FW_add", ins := [7720, 5059], outs := [5060] }
      7720 5059 5060 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7720 5059 5060)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8695
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15163) (denoteGraph_ringAttn pm initPM 8691) :=
    ringAttn_reduce2_pm_opaque pm initPM 609
      { rank := 0, op := "OpName.FW_add", ins := [15163, 8691], outs := [8695] }
      15163 8691 8695 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15163 8691 8695)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8696
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15171) (denoteGraph_ringAttn pm initPM 8692) :=
    ringAttn_reduce2_pm_opaque pm initPM 610
      { rank := 1, op := "OpName.FW_add", ins := [15171, 8692], outs := [8696] }
      15171 8692 8696 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15171 8692 8696)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5060
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8695, denoteGraph_ringAttn pm initPM 8696] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15163 hs15171 hs8691 hs8692,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8695).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15163 hs8691
  have hsp1 : (denoteGraph_ringAttn pm initPM 8696).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15171 hs8692
  have hshape : (denoteGraph_ringAttn sm initSM 5060).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5060 5060 8695 8696 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5062 — RMSNorm of `mref2-first(5060)` with replicated weight `5061`
    (2-tp, PM `8699`/`8700`). -/
theorem recon_intermediateGoal_5062_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5062
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs8695, hs8696⟩ := twoTp_gather _ _ intermediateGoal_5060 5060 8695 8696
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5060_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7747 : denoteGraph_ringAttn sm initSM 7747 = id (denoteGraph_ringAttn sm initSM 5060) :=
    ringAttn_reduce1_pm_opaque sm initSM 275
      { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751], params := [2] }
      5060 7747 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5060 7747 7751)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15221 : denoteGraph_ringAttn pm initPM 15221 = id (denoteGraph_ringAttn pm initPM 8695) :=
    ringAttn_reduce1_pm_opaque pm initPM 611
      { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225], params := [2] }
      8695 15221 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8695 15221 15225)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15229 : denoteGraph_ringAttn pm initPM 15229 = id (denoteGraph_ringAttn pm initPM 8696) :=
    ringAttn_reduce1_pm_opaque pm initPM 612
      { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233], params := [2] }
      8696 15229 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8696 15229 15233)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7747 p15221 p15229
  have hs15221 : (denoteGraph_ringAttn pm initPM 15221).shape = [2048, 1024] := by
    rw [p15221]; exact hs8695
  have hs15229 : (denoteGraph_ringAttn pm initPM 15229).shape = [2048, 1024] := by
    rw [p15229]; exact hs8696
  have hbr39 : denoteGraph_ringAttn sm initSM 7747
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15221, denoteGraph_ringAttn pm initPM 15229] := by
    rw [s7747, hbr44, ← p15221, ← p15229]
  have hw5061 : denoteGraph_ringAttn sm initSM 5061 = denoteGraph_ringAttn pm initPM 5061 :=
    veq_weight_ring initSM initPM hInit initGoal_5061 (by native_decide) 5061
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5062
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7747) (denoteGraph_ringAttn sm initSM 5061) :=
    ringAttn_reduce2_pm_opaque sm initSM 276
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7747, 5061], outs := [5062] }
      7747 5061 5062 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7747 5061 5062)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8699
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15221) (denoteGraph_ringAttn pm initPM 5061) :=
    ringAttn_reduce2_pm_opaque pm initPM 613
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15221, 5061], outs := [8699] }
      15221 5061 8699 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15221 5061 8699)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8700
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15229) (denoteGraph_ringAttn pm initPM 5061) :=
    ringAttn_reduce2_pm_opaque pm initPM 614
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15229, 5061], outs := [8700] }
      15229 5061 8700 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15229 5061 8700)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5062
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8699, denoteGraph_ringAttn pm initPM 8700] := by
    rw [rSM, hbr39, hw5061, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15221 hs15229,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8699).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15221
  have hsp1 : (denoteGraph_ringAttn pm initPM 8700).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15229
  have hshape : (denoteGraph_ringAttn sm initSM 5062).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5062 5062 8699 8700 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5064 — per-head Q projection `fw_per_head_linear(mref3₀(5062), 5063)`
    (2-tp, PM `8701`/`8702`, weight `5063 : [16,64,1024]`). -/
theorem recon_intermediateGoal_5064_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5064
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8699, hs8700⟩ := twoTp_gather _ _ intermediateGoal_5062 5062 8699 8700
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5062_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7756 : denoteGraph_ringAttn sm initSM 7756 = id (denoteGraph_ringAttn sm initSM 5062) :=
    ringAttn_reduce1_pm_opaque sm initSM 277
      { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
      5062 7756 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5062 7756 7760 7764)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15238 : denoteGraph_ringAttn pm initPM 15238 = id (denoteGraph_ringAttn pm initPM 8699) :=
    ringAttn_reduce1_pm_opaque pm initPM 615
      { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
      8699 15238 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8699 15238 15242 15246)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15251 : denoteGraph_ringAttn pm initPM 15251 = id (denoteGraph_ringAttn pm initPM 8700) :=
    ringAttn_reduce1_pm_opaque pm initPM 616
      { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
      8700 15251 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8700 15251 15255 15259)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7756 p15238 p15251
  have hs15238 : (denoteGraph_ringAttn pm initPM 15238).shape = [2048, 1024] := by
    rw [p15238]; exact hs8699
  have hs15251 : (denoteGraph_ringAttn pm initPM 15251).shape = [2048, 1024] := by
    rw [p15251]; exact hs8700
  have hbr48 : denoteGraph_ringAttn sm initSM 7756
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15238, denoteGraph_ringAttn pm initPM 15251] := by
    rw [s7756, hbr46, ← p15238, ← p15251]
  have hw5063 : denoteGraph_ringAttn sm initSM 5063 = denoteGraph_ringAttn pm initPM 5063 :=
    veq_weight_ring initSM initPM hInit initGoal_5063 (by native_decide) 5063
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5063 : (denoteGraph_ringAttn sm initSM 5063).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5063 (by native_decide) 5063 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5063 : (denoteGraph_ringAttn pm initPM 5063).shape = [16, 64, 1024] := by
    rw [← hw5063]; exact hsw5063
  have rSM : denoteGraph_ringAttn sm initSM 5064
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7756) (denoteGraph_ringAttn sm initSM 5063) :=
    ringAttn_reduce2_pm_opaque sm initSM 278
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7756, 5063], outs := [5064] }
      7756 5063 5064 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7756 5063 5064 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8701
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15238) (denoteGraph_ringAttn pm initPM 5063) :=
    ringAttn_reduce2_pm_opaque pm initPM 617
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15238, 5063], outs := [8701] }
      15238 5063 8701 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15238 5063 8701 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8702
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15251) (denoteGraph_ringAttn pm initPM 5063) :=
    ringAttn_reduce2_pm_opaque pm initPM 620
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15251, 5063], outs := [8702] }
      15251 5063 8702 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15251 5063 8702 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5064
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8701, denoteGraph_ringAttn pm initPM 8702] := by
    rw [rSM, hbr48, hw5063, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs15238 hs15251 hpw5063,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8701).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15238 hpw5063
  have hsp1 : (denoteGraph_ringAttn pm initPM 8702).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15251 hpw5063
  have hshape : (denoteGraph_ringAttn sm initSM 5064).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5064 5064 8701 8702 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5066 — per-head K projection `fw_per_head_linear(mref3₁(5062), 5065)`
    (2-tp, PM `8713`/`8714`, weight `5065 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5066_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5066
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8699, hs8700⟩ := twoTp_gather _ _ intermediateGoal_5062 5062 8699 8700
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5062_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7760 : denoteGraph_ringAttn sm initSM 7760 = id (denoteGraph_ringAttn sm initSM 5062) :=
    ringAttn_reduce1_pm_opaque sm initSM 277
      { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
      5062 7760 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5062 7756 7760 7764 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15242 : denoteGraph_ringAttn pm initPM 15242 = id (denoteGraph_ringAttn pm initPM 8699) :=
    ringAttn_reduce1_pm_opaque pm initPM 615
      { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
      8699 15242 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8699 15238 15242 15246 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15255 : denoteGraph_ringAttn pm initPM 15255 = id (denoteGraph_ringAttn pm initPM 8700) :=
    ringAttn_reduce1_pm_opaque pm initPM 616
      { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
      8700 15255 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8700 15251 15255 15259 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7760 p15242 p15255
  have hs15242 : (denoteGraph_ringAttn pm initPM 15242).shape = [2048, 1024] := by
    rw [p15242]; exact hs8699
  have hs15255 : (denoteGraph_ringAttn pm initPM 15255).shape = [2048, 1024] := by
    rw [p15255]; exact hs8700
  have hbr52 : denoteGraph_ringAttn sm initSM 7760
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15242, denoteGraph_ringAttn pm initPM 15255] := by
    rw [s7760, hbr46, ← p15242, ← p15255]
  have hw5065 : denoteGraph_ringAttn sm initSM 5065 = denoteGraph_ringAttn pm initPM 5065 :=
    veq_weight_ring initSM initPM hInit initGoal_5065 (by native_decide) 5065
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5065 : (denoteGraph_ringAttn sm initSM 5065).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5065 (by native_decide) 5065 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5065 : (denoteGraph_ringAttn pm initPM 5065).shape = [4, 64, 1024] := by
    rw [← hw5065]; exact hsw5065
  have rSM : denoteGraph_ringAttn sm initSM 5066
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7760) (denoteGraph_ringAttn sm initSM 5065) :=
    ringAttn_reduce2_pm_opaque sm initSM 279
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7760, 5065], outs := [5066] }
      7760 5065 5066 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7760 5065 5066 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8713
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15242) (denoteGraph_ringAttn pm initPM 5065) :=
    ringAttn_reduce2_pm_opaque pm initPM 618
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15242, 5065], outs := [8713] }
      15242 5065 8713 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15242 5065 8713 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8714
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15255) (denoteGraph_ringAttn pm initPM 5065) :=
    ringAttn_reduce2_pm_opaque pm initPM 621
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15255, 5065], outs := [8714] }
      15255 5065 8714 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15255 5065 8714 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5066
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8713, denoteGraph_ringAttn pm initPM 8714] := by
    rw [rSM, hbr52, hw5065, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15242 hs15255 hpw5065,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8713).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15242 hpw5065
  have hsp1 : (denoteGraph_ringAttn pm initPM 8714).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15255 hpw5065
  have hshape : (denoteGraph_ringAttn sm initSM 5066).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5066 5066 8713 8714 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5068 — per-head V projection `fw_per_head_linear(mref3₂(5062), 5067)`
    (2-tp, PM `8723`/`8724`, weight `5067 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5068_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5068
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8699, hs8700⟩ := twoTp_gather _ _ intermediateGoal_5062 5062 8699 8700
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5062_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7764 : denoteGraph_ringAttn sm initSM 7764 = id (denoteGraph_ringAttn sm initSM 5062) :=
    ringAttn_reduce1_pm_opaque sm initSM 277
      { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
      5062 7764 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5062 7756 7760 7764 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15246 : denoteGraph_ringAttn pm initPM 15246 = id (denoteGraph_ringAttn pm initPM 8699) :=
    ringAttn_reduce1_pm_opaque pm initPM 615
      { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
      8699 15246 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8699 15238 15242 15246 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15259 : denoteGraph_ringAttn pm initPM 15259 = id (denoteGraph_ringAttn pm initPM 8700) :=
    ringAttn_reduce1_pm_opaque pm initPM 616
      { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
      8700 15259 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8700 15251 15255 15259 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7764 p15246 p15259
  have hs15246 : (denoteGraph_ringAttn pm initPM 15246).shape = [2048, 1024] := by
    rw [p15246]; exact hs8699
  have hs15259 : (denoteGraph_ringAttn pm initPM 15259).shape = [2048, 1024] := by
    rw [p15259]; exact hs8700
  have hbr56 : denoteGraph_ringAttn sm initSM 7764
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15246, denoteGraph_ringAttn pm initPM 15259] := by
    rw [s7764, hbr46, ← p15246, ← p15259]
  have hw5067 : denoteGraph_ringAttn sm initSM 5067 = denoteGraph_ringAttn pm initPM 5067 :=
    veq_weight_ring initSM initPM hInit initGoal_5067 (by native_decide) 5067
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5067 : (denoteGraph_ringAttn sm initSM 5067).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5067 (by native_decide) 5067 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5067 : (denoteGraph_ringAttn pm initPM 5067).shape = [4, 64, 1024] := by
    rw [← hw5067]; exact hsw5067
  have rSM : denoteGraph_ringAttn sm initSM 5068
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7764) (denoteGraph_ringAttn sm initSM 5067) :=
    ringAttn_reduce2_pm_opaque sm initSM 280
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7764, 5067], outs := [5068] }
      7764 5067 5068 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7764 5067 5068 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8723
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15246) (denoteGraph_ringAttn pm initPM 5067) :=
    ringAttn_reduce2_pm_opaque pm initPM 619
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15246, 5067], outs := [8723] }
      15246 5067 8723 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15246 5067 8723 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8724
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15259) (denoteGraph_ringAttn pm initPM 5067) :=
    ringAttn_reduce2_pm_opaque pm initPM 622
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15259, 5067], outs := [8724] }
      15259 5067 8724 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15259 5067 8724 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5068
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8723, denoteGraph_ringAttn pm initPM 8724] := by
    rw [rSM, hbr56, hw5067, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15246 hs15259 hpw5067,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8723).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15246 hpw5067
  have hsp1 : (denoteGraph_ringAttn pm initPM 8724).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15259 hpw5067
  have hshape : (denoteGraph_ringAttn sm initSM 5068).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5068 5068 8723 8724 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L7 rotary cos/sin cache agreement: `sm 4691 = pm 11860` (`= 11853 + 3`). -/
theorem hcache_4691_11860 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11860 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11860 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11860 7 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 5070 — rotary-embedding Q output `rotary(4691, 5069, 5064, 5066).1`
    (2-tp, PM `8735`/`8736`; positions `5069 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_5070_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5070
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs8701, hs8702⟩ := twoTp_gather _ _ intermediateGoal_5064 5064 8701 8702
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5064_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_5066 5066 8713 8714
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5066_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11860 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5069 = denoteGraph_ringAttn pm initPM 5069 :=
    veq_weight_ring initSM initPM hInit initGoal_5069 (by native_decide) 5069
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5069 : (denoteGraph_ringAttn sm initSM 5069).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5069 (by native_decide) 5069 [4096]
      rfl rfl (by native_decide)
  have c8733 : denoteGraph_ringAttn pm initPM 8733
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5069) :=
    ringAttn_reduce1_pm_opaque pm initPM 7
      { rank := 0, op := "OpName.ChunkPrim", ins := [5069], outs := [8733], params := [0] }
      5069 8733 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5069 8733 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8734 : denoteGraph_ringAttn pm initPM 8734
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5069) :=
    ringAttn_reduce1_pm_opaque pm initPM 20
      { rank := 1, op := "OpName.ChunkPrim", ins := [5069], outs := [8734], params := [0] }
      5069 8734 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5069 8734 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5070
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5069)
          (denoteGraph_ringAttn sm initSM 5064) (denoteGraph_ringAttn sm initSM 5066) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 281
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5069, 5064, 5066], outs := [5070, 5071], params := [16, 4] }
          5070 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 281 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 281 5069 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 281 5064 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 281 5066 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8735
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11860) (denoteGraph_ringAttn pm initPM 8733)
          (denoteGraph_ringAttn pm initPM 8701) (denoteGraph_ringAttn pm initPM 8713) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 623
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11860, 8733, 8701, 8713], outs := [8735, 8737], params := [16, 4] }
          8735 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 623 11860 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 623 8733 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 623 8701 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 623 8713 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8736
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11860) (denoteGraph_ringAttn pm initPM 8734)
          (denoteGraph_ringAttn pm initPM 8702) (denoteGraph_ringAttn pm initPM 8714) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 624
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11860, 8734, 8702, 8714], outs := [8736, 8738], params := [16, 4] }
          8736 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 624 11860 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 624 8734 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 624 8702 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 624 8714 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5070
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8735, denoteGraph_ringAttn pm initPM 8736] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5069) (denoteGraph_ringAttn pm initPM 8701)
          (denoteGraph_ringAttn pm initPM 8702) 2048 16 64 (by omega) (by omega) (by omega)
          hsp5069 hs8701 hs8702,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8733
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5069) from c8733),
        ← (show denoteGraph_ringAttn pm initPM 8734
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5069) from c8734),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8735).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8701
  have hsp1 : (denoteGraph_ringAttn pm initPM 8736).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8702
  have hshape : (denoteGraph_ringAttn sm initSM 5070).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5070 5070 8735 8736 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 5071 — rotary-embedding K output `rotary(4691, 5069, 5064, 5066).2`
    (2-tp, PM `8737`/`8738`). -/
theorem recon_intermediateGoal_5071_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5071
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_5064 5064 8701 8702
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5064_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs8713, hs8714⟩ := twoTp_gather _ _ intermediateGoal_5066 5066 8713 8714
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5066_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11860 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5069 = denoteGraph_ringAttn pm initPM 5069 :=
    veq_weight_ring initSM initPM hInit initGoal_5069 (by native_decide) 5069
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5069 : (denoteGraph_ringAttn sm initSM 5069).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5069 (by native_decide) 5069 [4096]
      rfl rfl (by native_decide)
  have c8733 : denoteGraph_ringAttn pm initPM 8733
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5069) :=
    ringAttn_reduce1_pm_opaque pm initPM 7
      { rank := 0, op := "OpName.ChunkPrim", ins := [5069], outs := [8733], params := [0] }
      5069 8733 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5069 8733 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8734 : denoteGraph_ringAttn pm initPM 8734
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5069) :=
    ringAttn_reduce1_pm_opaque pm initPM 20
      { rank := 1, op := "OpName.ChunkPrim", ins := [5069], outs := [8734], params := [0] }
      5069 8734 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5069 8734 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5071
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5069)
          (denoteGraph_ringAttn sm initSM 5064) (denoteGraph_ringAttn sm initSM 5066) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 281
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5069, 5064, 5066], outs := [5070, 5071], params := [16, 4] }
          5071 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5069 5064 5066 5070 5071 (by decide),
        ringAttn_prefix_read_pm sm initSM 281 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 281 5069 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 281 5064 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 281 5066 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8737
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11860) (denoteGraph_ringAttn pm initPM 8733)
          (denoteGraph_ringAttn pm initPM 8701) (denoteGraph_ringAttn pm initPM 8713) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 623
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11860, 8733, 8701, 8713], outs := [8735, 8737], params := [16, 4] }
          8737 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11860 8733 8701 8713 8735 8737 (by decide),
        ringAttn_prefix_read_pm pm initPM 623 11860 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 623 8733 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 623 8701 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 623 8713 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8738
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11860) (denoteGraph_ringAttn pm initPM 8734)
          (denoteGraph_ringAttn pm initPM 8702) (denoteGraph_ringAttn pm initPM 8714) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 624
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11860, 8734, 8702, 8714], outs := [8736, 8738], params := [16, 4] }
          8738 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11860 8734 8702 8714 8736 8738 (by decide),
        ringAttn_prefix_read_pm pm initPM 624 11860 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 624 8734 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 624 8702 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 624 8714 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5071
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8737, denoteGraph_ringAttn pm initPM 8738] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5069) (denoteGraph_ringAttn pm initPM 8713)
          (denoteGraph_ringAttn pm initPM 8714) 2048 4 64 (by omega) (by omega) (by omega)
          hsp5069 hs8713 hs8714,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8733
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5069) from c8733),
        ← (show denoteGraph_ringAttn pm initPM 8734
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5069) from c8734),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8737).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8713
  have hsp1 : (denoteGraph_ringAttn pm initPM 8738).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8714
  have hshape : (denoteGraph_ringAttn sm initSM 5071).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5071 5071 8737 8738 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
