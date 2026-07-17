/- Worker #23 — Layer-11 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_5236_ringAttn` (the layer-11
   sliding-window attention output, unconditional-given-WF) through the layer-11
   forward block.

   Unlike L2, the L11 block has NO gather-to-full node (L2's PM node 228
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L11
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_5240` targets `[9309, 9310]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L10Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 5237 — 2-tp reshape of the L11 attention output `5236 : [4096,16,64]` to
    `[4096,1024]` (SM node 205, PM nodes 471/472). -/
theorem recon_intermediateGoal_5237_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5237
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs9297, hs9298⟩ := twoTp_gather _ _ intermediateGoal_5236 5236 9297 9298
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5236_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5237
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5236) :=
    ringAttn_reshape_reduce_pm sm initSM 400 0 5236 5237 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9299
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9297) :=
    ringAttn_reshape_reduce_pm pm initPM 861 0 9297 9299 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9300
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9298) :=
    ringAttn_reshape_reduce_pm pm initPM 862 1 9298 9300 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5237
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9299, denoteGraph_ringAttn pm initPM 9300] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs9297 hs9298
  have hs9299 : (denoteGraph_ringAttn pm initPM 9299).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9300 : (denoteGraph_ringAttn pm initPM 9300).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5237 : (denoteGraph_ringAttn sm initSM 5237).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5237 5237 9299 9300 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5237 hs9299 hs9300

/-- 5238 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 206, PM
    nodes 473/474). -/
theorem recon_intermediateGoal_5238_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5238
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs9299, hs9300⟩ := twoTp_gather _ _ intermediateGoal_5237 5237 9299 9300
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5237_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5237 : (denoteGraph_ringAttn sm initSM 5237).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9299])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5238
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5237) :=
    ringAttn_reshape_reduce_pm sm initSM 401 0 5237 5238 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9305
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9299) :=
    ringAttn_reshape_reduce_pm pm initPM 863 0 9299 9305 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9306
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9300) :=
    ringAttn_reshape_reduce_pm pm initPM 864 1 9300 9306 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 9305 = denoteGraph_ringAttn pm initPM 9299 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9299]
  have h18 : denoteGraph_ringAttn pm initPM 9306 = denoteGraph_ringAttn pm initPM 9300 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9300]
  have hval : denoteGraph_ringAttn sm initSM 5238
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9305, denoteGraph_ringAttn pm initPM 9306] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5237, hval05, hnr, ← h17, ← h18]
  have hs9305 : (denoteGraph_ringAttn pm initPM 9305).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9306 : (denoteGraph_ringAttn pm initPM 9306).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5238 : (denoteGraph_ringAttn sm initSM 5238).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5238 5238 9305 9306 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5238 hs9305 hs9306

/-- 5240 — 2-tp down-projection `fw_linear(5238, 5239)` (weight `5239 : [1024,1024]`,
    SM node 207, PM nodes 475/476). -/
theorem recon_intermediateGoal_5240_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5240
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs9305, hs9306⟩ := twoTp_gather _ _ intermediateGoal_5238 5238 9305 9306
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5238_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5239 : denoteGraph_ringAttn sm initSM 5239 = denoteGraph_ringAttn pm initPM 5239 :=
    veq_weight_ring initSM initPM hInit initGoal_5239 (by native_decide) 5239
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5239 : (denoteGraph_ringAttn sm initSM 5239).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5239 (by native_decide) 5239 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw5239 : (denoteGraph_ringAttn pm initPM 5239).shape = [1024, 1024] := by
    rw [← hw5239]; exact hsw5239
  have rSM : denoteGraph_ringAttn sm initSM 5240
      = fw_linear (denoteGraph_ringAttn sm initSM 5238) (denoteGraph_ringAttn sm initSM 5239) :=
    ringAttn_reduce2_pm_opaque sm initSM 402
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5238, 5239], outs := [5240] }
      5238 5239 5240 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5238 5239 5240)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9309
      = fw_linear (denoteGraph_ringAttn pm initPM 9305) (denoteGraph_ringAttn pm initPM 5239) :=
    ringAttn_reduce2_pm_opaque pm initPM 865
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9305, 5239], outs := [9309] }
      9305 5239 9309 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9305 5239 9309)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9310
      = fw_linear (denoteGraph_ringAttn pm initPM 9306) (denoteGraph_ringAttn pm initPM 5239) :=
    ringAttn_reduce2_pm_opaque pm initPM 866
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9306, 5239], outs := [9310] }
      9306 5239 9310 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9306 5239 9310)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5240
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9309, denoteGraph_ringAttn pm initPM 9310] := by
    rw [rSM, hval06, hw5239, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs9305 hs9306 hpw5239,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9309).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9305 hpw5239
  have hsp1 : (denoteGraph_ringAttn pm initPM 9310).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9306 hpw5239
  have hshape : (denoteGraph_ringAttn sm initSM 5240).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5240 5240 9309 9310 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5241 — 2-tp identity view of `5240` (SM node 208, PM nodes 477/478). -/
theorem recon_intermediateGoal_5241_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5241
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs9309, hs9310⟩ := twoTp_gather _ _ intermediateGoal_5240 5240 9309 9310
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5240_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5240 : (denoteGraph_ringAttn sm initSM 5240).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9309])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5241
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5240) :=
    ringAttn_reduce1_pm_opaque sm initSM 403
      { rank := 0, op := "OpName.FW_view", ins := [5240], outs := [5241], params := [4096, 1024] }
      5240 5241 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5240 5241)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9319
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9309) :=
    ringAttn_reduce1_pm_opaque pm initPM 867
      { rank := 0, op := "OpName.FW_view", ins := [9309], outs := [9319], params := [2048, 1024] }
      9309 9319 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9309 9319)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9320
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9310) :=
    ringAttn_reduce1_pm_opaque pm initPM 868
      { rank := 1, op := "OpName.FW_view", ins := [9310], outs := [9320], params := [2048, 1024] }
      9310 9320 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9310 9320)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 9319 = denoteGraph_ringAttn pm initPM 9309 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9309]
  have h32 : denoteGraph_ringAttn pm initPM 9320 = denoteGraph_ringAttn pm initPM 9310 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9310]
  have hval : denoteGraph_ringAttn sm initSM 5241
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9319, denoteGraph_ringAttn pm initPM 9320] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5240, hval08, hnr, ← h31, ← h32]
  have hs9319 : (denoteGraph_ringAttn pm initPM 9319).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9320 : (denoteGraph_ringAttn pm initPM 9320).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5241 : (denoteGraph_ringAttn sm initSM 5241).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5241 5241 9319 9320 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5241 hs9319 hs9320

/-- 5242 — 2-tp `FW_float(5241)` (identity, SM node 209, PM nodes 479/480). -/
theorem recon_intermediateGoal_5242_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5242
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs9319, hs9320⟩ := twoTp_gather _ _ intermediateGoal_5241 5241 9319 9320
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5241_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5242 = id (denoteGraph_ringAttn sm initSM 5241) :=
    ringAttn_reduce1_pm_opaque sm initSM 404
      { rank := 0, op := "OpName.FW_float", ins := [5241], outs := [5242] }
      5241 5242 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5241 5242 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9323 = id (denoteGraph_ringAttn pm initPM 9319) :=
    ringAttn_reduce1_pm_opaque pm initPM 869
      { rank := 0, op := "OpName.FW_float", ins := [9319], outs := [9323] }
      9319 9323 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9319 9323 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9324 = id (denoteGraph_ringAttn pm initPM 9320) :=
    ringAttn_reduce1_pm_opaque pm initPM 870
      { rank := 1, op := "OpName.FW_float", ins := [9320], outs := [9324] }
      9320 9324 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9320 9324 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5242
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9323, denoteGraph_ringAttn pm initPM 9324] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9323).shape = [2048, 1024] := by rw [rP0]; exact hs9319
  have hsp1 : (denoteGraph_ringAttn pm initPM 9324).shape = [2048, 1024] := by rw [rP1]; exact hs9320
  have hshape : (denoteGraph_ringAttn sm initSM 5242).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5242 5242 9323 9324 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7907 — 2-tp `mref2`-second copy of the L2 residual `5222` (SM node 197,
    PM nodes 455/456), carried into the L11 residual add. -/
theorem recon_intermediateGoal_7907_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7907
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs9253, hs9254⟩ := twoTp_gather _ _ intermediateGoal_5222 5222 9253 9254
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5222_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8309 : denoteGraph_ringAttn sm initSM 7907 = id (denoteGraph_ringAttn sm initSM 5222) :=
    ringAttn_reduce1_pm_opaque sm initSM 392
      { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907], params := [2] }
      5222 7907 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5222 7903 7907 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15537 : denoteGraph_ringAttn pm initPM 15537 = id (denoteGraph_ringAttn pm initPM 9253) :=
    ringAttn_reduce1_pm_opaque pm initPM 845
      { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537], params := [2] }
      9253 15537 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9253 15533 15537 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15545 : denoteGraph_ringAttn pm initPM 15545 = id (denoteGraph_ringAttn pm initPM 9254) :=
    ringAttn_reduce1_pm_opaque pm initPM 846
      { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545], params := [2] }
      9254 15545 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9254 15541 15545 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8309 p15537 p15545
  have hsp0 : (denoteGraph_ringAttn pm initPM 15537).shape = [2048, 1024] := by
    rw [p15537]; exact hs9253
  have hsp1 : (denoteGraph_ringAttn pm initPM 15545).shape = [2048, 1024] := by
    rw [p15545]; exact hs9254
  have hval : denoteGraph_ringAttn sm initSM 7907
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15537, denoteGraph_ringAttn pm initPM 15545] := by
    rw [s8309, hbr90, ← p15537, ← p15545]
  have hshape : (denoteGraph_ringAttn sm initSM 7907).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7907 7907 15537 15545 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5243 — 2-tp L11 residual add `7907 + 5242` (SM node 210, PM nodes 481/482). -/
theorem recon_intermediateGoal_5243_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5243
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs15537, hs15545⟩ := twoTp_gather _ _ intermediateGoal_7907 7907 15537 15545
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7907_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs9323, hs9324⟩ := twoTp_gather _ _ intermediateGoal_5242 5242 9323 9324
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5242_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5243
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7907) (denoteGraph_ringAttn sm initSM 5242) :=
    ringAttn_reduce2_pm_opaque sm initSM 405
      { rank := 0, op := "OpName.FW_add", ins := [7907, 5242], outs := [5243] }
      7907 5242 5243 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7907 5242 5243)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9327
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15537) (denoteGraph_ringAttn pm initPM 9323) :=
    ringAttn_reduce2_pm_opaque pm initPM 871
      { rank := 0, op := "OpName.FW_add", ins := [15537, 9323], outs := [9327] }
      15537 9323 9327 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15537 9323 9327)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9328
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15545) (denoteGraph_ringAttn pm initPM 9324) :=
    ringAttn_reduce2_pm_opaque pm initPM 872
      { rank := 1, op := "OpName.FW_add", ins := [15545, 9324], outs := [9328] }
      15545 9324 9328 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15545 9324 9328)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5243
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9327, denoteGraph_ringAttn pm initPM 9328] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15537 hs15545 hs9323 hs9324,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9327).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15537 hs9323
  have hsp1 : (denoteGraph_ringAttn pm initPM 9328).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15545 hs9324
  have hshape : (denoteGraph_ringAttn sm initSM 5243).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5243 5243 9327 9328 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5245 — 2-tp RMSNorm of `mref2-first(5243)` with replicated weight
    `5244 : [1024]` (SM node 212, PM nodes 485/486). -/
theorem recon_intermediateGoal_5245_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5245
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs9327, hs9328⟩ := twoTp_gather _ _ intermediateGoal_5243 5243 9327 9328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5243_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7924 : denoteGraph_ringAttn sm initSM 7924 = id (denoteGraph_ringAttn sm initSM 5243) :=
    ringAttn_reduce1_pm_opaque sm initSM 406
      { rank := 0, op := "OpName.FW_multiref", ins := [5243], outs := [7924, 7928], params := [2] }
      5243 7924 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5243 7924 7928)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15575 : denoteGraph_ringAttn pm initPM 15575 = id (denoteGraph_ringAttn pm initPM 9327) :=
    ringAttn_reduce1_pm_opaque pm initPM 873
      { rank := 0, op := "OpName.FW_multiref", ins := [9327], outs := [15575, 15579], params := [2] }
      9327 15575 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9327 15575 15579)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15583 : denoteGraph_ringAttn pm initPM 15583 = id (denoteGraph_ringAttn pm initPM 9328) :=
    ringAttn_reduce1_pm_opaque pm initPM 874
      { rank := 1, op := "OpName.FW_multiref", ins := [9328], outs := [15583, 15587], params := [2] }
      9328 15583 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9328 15583 15587)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7924 p15575 p15583
  have hs15575 : (denoteGraph_ringAttn pm initPM 15575).shape = [2048, 1024] := by
    rw [p15575]; exact hs9327
  have hs15583 : (denoteGraph_ringAttn pm initPM 15583).shape = [2048, 1024] := by
    rw [p15583]; exact hs9328
  have hbr08 : denoteGraph_ringAttn sm initSM 7924
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15575, denoteGraph_ringAttn pm initPM 15583] := by
    rw [s7924, hbr11, ← p15575, ← p15583]
  have hw5244 : denoteGraph_ringAttn sm initSM 5244 = denoteGraph_ringAttn pm initPM 5244 :=
    veq_weight_ring initSM initPM hInit initGoal_5244 (by native_decide) 5244
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5245
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7924) (denoteGraph_ringAttn sm initSM 5244) :=
    ringAttn_reduce2_pm_opaque sm initSM 407
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7924, 5244], outs := [5245] }
      7924 5244 5245 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7924 5244 5245)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9331
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15575) (denoteGraph_ringAttn pm initPM 5244) :=
    ringAttn_reduce2_pm_opaque pm initPM 875
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15575, 5244], outs := [9331] }
      15575 5244 9331 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15575 5244 9331)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9332
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15583) (denoteGraph_ringAttn pm initPM 5244) :=
    ringAttn_reduce2_pm_opaque pm initPM 876
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15583, 5244], outs := [9332] }
      15583 5244 9332 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15583 5244 9332)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5245
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9331, denoteGraph_ringAttn pm initPM 9332] := by
    rw [rSM, hbr08, hw5244, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15575 hs15583,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9331).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15575
  have hsp1 : (denoteGraph_ringAttn pm initPM 9332).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15583
  have hshape : (denoteGraph_ringAttn sm initSM 5245).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5245 5245 9331 9332 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5246 — 2-tp `FW_float(mref5-first(5245))` (identity, SM node 214,
    PM nodes 489/493; mref5-first via SM node 213, PM 487/488). -/
theorem recon_intermediateGoal_5246_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5246
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9331, hs9332⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7935 : denoteGraph_ringAttn sm initSM 7935 = id (denoteGraph_ringAttn sm initSM 5245) :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245],
        outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7935 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 5245 7935 [7939, 7943, 7947, 7951])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15594 : denoteGraph_ringAttn pm initPM 15594 = id (denoteGraph_ringAttn pm initPM 9331) :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331],
        outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15594 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 9331 15594 [15598, 15602, 15606, 15610])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15617 : denoteGraph_ringAttn pm initPM 15617 = id (denoteGraph_ringAttn pm initPM 9332) :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332],
        outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15617 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 9332 15617 [15621, 15625, 15629, 15633])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7935 p15594 p15617
  have hbrm : denoteGraph_ringAttn sm initSM 7935
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15594, denoteGraph_ringAttn pm initPM 15617] := by
    rw [s7935, hbr13, ← p15594, ← p15617]
  have rSM : denoteGraph_ringAttn sm initSM 5246 = id (denoteGraph_ringAttn sm initSM 7935) :=
    ringAttn_reduce1_pm_opaque sm initSM 409
      { rank := 0, op := "OpName.FW_float", ins := [7935], outs := [5246] }
      7935 5246 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7935 5246 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9333 = id (denoteGraph_ringAttn pm initPM 15594) :=
    ringAttn_reduce1_pm_opaque pm initPM 879
      { rank := 0, op := "OpName.FW_float", ins := [15594], outs := [9333] }
      15594 9333 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 15594 9333 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9334 = id (denoteGraph_ringAttn pm initPM 15617) :=
    ringAttn_reduce1_pm_opaque pm initPM 883
      { rank := 1, op := "OpName.FW_float", ins := [15617], outs := [9334] }
      15617 9334 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 15617 9334 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs15594 : (denoteGraph_ringAttn pm initPM 15594).shape = [2048, 1024] := by
    rw [p15594]; exact hs9331
  have hs15617 : (denoteGraph_ringAttn pm initPM 15617).shape = [2048, 1024] := by
    rw [p15617]; exact hs9332
  have hval : denoteGraph_ringAttn sm initSM 5246
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9333, denoteGraph_ringAttn pm initPM 9334] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9333).shape = [2048, 1024] := by
    rw [rP0]; exact hs15594
  have hsp1 : (denoteGraph_ringAttn pm initPM 9334).shape = [2048, 1024] := by
    rw [rP1]; exact hs15617
  have hshape : (denoteGraph_ringAttn sm initSM 5246).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5246 5246 9333 9334 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5248 — 2-tp router logits `fw_norm_linear(5246, 5247)` with weight
    `5247 : [64, 1024]` → `[4096, 64]` (SM node 218, PM nodes 497/501). -/
theorem recon_intermediateGoal_5248_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5248
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs9333, hs9334⟩ := twoTp_gather _ _ intermediateGoal_5246 5246 9333 9334
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5246_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5247 : denoteGraph_ringAttn sm initSM 5247 = denoteGraph_ringAttn pm initPM 5247 :=
    veq_weight_ring initSM initPM hInit initGoal_5247 (by native_decide) 5247
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5247 : (denoteGraph_ringAttn sm initSM 5247).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5247 (by native_decide) 5247 [64, 1024]
      rfl rfl (by native_decide)
  have hpw5247 : (denoteGraph_ringAttn pm initPM 5247).shape = [64, 1024] := by
    rw [← hw5247]; exact hsw5247
  have rSM : denoteGraph_ringAttn sm initSM 5248
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 5246) (denoteGraph_ringAttn sm initSM 5247) :=
    ringAttn_reduce2_pm_opaque sm initSM 413
      { rank := 0, op := "OpName.FW_norm_linear", ins := [5246, 5247], outs := [5248] }
      5246 5247 5248 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 5246 5247 5248)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9339
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9333) (denoteGraph_ringAttn pm initPM 5247) :=
    ringAttn_reduce2_pm_opaque pm initPM 887
      { rank := 0, op := "OpName.FW_norm_linear", ins := [9333, 5247], outs := [9339] }
      9333 5247 9339 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 9333 5247 9339)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9340
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9334) (denoteGraph_ringAttn pm initPM 5247) :=
    ringAttn_reduce2_pm_opaque pm initPM 891
      { rank := 1, op := "OpName.FW_norm_linear", ins := [9334, 5247], outs := [9340] }
      9334 5247 9340 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 9334 5247 9340)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5248
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9339, denoteGraph_ringAttn pm initPM 9340] := by
    rw [rSM, hval14, hw5247, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs9333 hs9334 hpw5247,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9339).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs9333 hpw5247
  have hsp1 : (denoteGraph_ringAttn pm initPM 9340).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs9334 hpw5247
  have hshape : (denoteGraph_ringAttn sm initSM 5248).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5248 5248 9339 9340 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L11 top-k routing (`5249`/`5250`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`9339`/`9340`) directly. -/

/-- Shared L11 top-k core: `5248` (full logits) is the dim-0 gather of the two
    per-rank shards `9339`/`9340`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L11 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 5248
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 9339, denoteGraph_ringAttn pm initPM 9340]
      ∧ (denoteGraph_ringAttn sm initSM 5248).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 9339).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 9340).shape = [2048, 64]
      ∧ ((sm.nodes.take 417).foldl (applyNodeRingAttn sm) initSM 5248).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 895).foldl (applyNodeRingAttn pm) initPM 9339).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 899).foldl (applyNodeRingAttn pm) initPM 9340).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs9339, hs9340⟩ := twoTp_gather _ _ intermediateGoal_5248 5248 9339 9340
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5248_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs5248sm : (denoteGraph_ringAttn sm initSM 5248).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs9339])]
    simp [List.set, List.getD]
  have hpre5248sm : denoteGraph_ringAttn sm initSM 5248
      = (sm.nodes.take 417).foldl (applyNodeRingAttn sm) initSM 5248 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5248 417 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 417).foldl (applyNodeRingAttn sm) initSM 5248).shape.reverse.head? = some 64 := by
    rw [← hpre5248sm, hs5248sm]; rfl
  have hpre9339 : denoteGraph_ringAttn pm initPM 9339
      = (pm.nodes.take 895).foldl (applyNodeRingAttn pm) initPM 9339 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9339 895 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 895).foldl (applyNodeRingAttn pm) initPM 9339).shape.reverse.head? = some 64 := by
    rw [← hpre9339, hs9339]; rfl
  have hpre9340 : denoteGraph_ringAttn pm initPM 9340
      = (pm.nodes.take 899).foldl (applyNodeRingAttn pm) initPM 9340 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9340 899 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 899).foldl (applyNodeRingAttn pm) initPM 9340).shape.reverse.head? = some 64 := by
    rw [← hpre9340, hs9340]; rfl
  exact ⟨hbr16, hs5248sm, hs9339, hs9340, hlastSM, hlast271, hlast275⟩

/-- 5249 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5249_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5249
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5248sm, hs9339, hs9340, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L11 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5249
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5248) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 417
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5248], outs := [5249, 5250, 5251], params := [8, 1] }
      5248 5249 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 417).foldl (applyNodeRingAttn sm) initSM) 0 5248 5249 5250 5251 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9341
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9339) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 895
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9339], outs := [9341, 9343, 9345], params := [8, 1] }
      9339 9341 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 895).foldl (applyNodeRingAttn pm) initPM) 0 9339 9341 9343 9345 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9342
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9340) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 899
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9340], outs := [9342, 9344, 9346], params := [8, 1] }
      9340 9342 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 899).foldl (applyNodeRingAttn pm) initPM) 1 9340 9342 9344 9346 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5249
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9341, denoteGraph_ringAttn pm initPM 9342] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9339 hs9340,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5249).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs5248sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9341).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9339]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9342).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9340]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5249 5249 9341 9342 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5250 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5250_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5250
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5248sm, hs9339, hs9340, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L11 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5250
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5248) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 417
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5248], outs := [5249, 5250, 5251], params := [8, 1] }
      5248 5250 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 417).foldl (applyNodeRingAttn sm) initSM) 0 5248 5249 5250 5251 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9343
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9339) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 895
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9339], outs := [9341, 9343, 9345], params := [8, 1] }
      9339 9343 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 895).foldl (applyNodeRingAttn pm) initPM) 0 9339 9341 9343 9345 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9344
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9340) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 899
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9340], outs := [9342, 9344, 9346], params := [8, 1] }
      9340 9344 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 899).foldl (applyNodeRingAttn pm) initPM) 1 9340 9342 9344 9346 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5250
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9343, denoteGraph_ringAttn pm initPM 9344] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9339 hs9340,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5250).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs5248sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9343).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9339]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9344).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9340]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5250 5250 9343 9344 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L11 router expert branches — reshape (`5255`/`5260`/`5264`) of the
    `mref5` copies (positions 2/3/4) of `5245`, all identity 2-tp views. -/

/-- 5255 — 2-tp identity reshape of `mref5-pos2(5245)` (SM node 215, PM 490/494). -/
theorem recon_intermediateGoal_5255_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5255
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9331, hs9332⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5245sm : (denoteGraph_ringAttn sm initSM 5245).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9331])]
    simp [List.set, List.getD]
  have s7943 : denoteGraph_ringAttn sm initSM 7943 = id (denoteGraph_ringAttn sm initSM 5245) :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245],
        outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7943 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15602 : denoteGraph_ringAttn pm initPM 15602 = id (denoteGraph_ringAttn pm initPM 9331) :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331],
        outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15602 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15625 : denoteGraph_ringAttn pm initPM 15625 = id (denoteGraph_ringAttn pm initPM 9332) :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332],
        outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15625 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7943 p15602 p15625
  have hs7943 : (denoteGraph_ringAttn sm initSM 7943).shape = [4096, 1024] := by rw [s7943]; exact hs5245sm
  have hs15602 : (denoteGraph_ringAttn pm initPM 15602).shape = [2048, 1024] := by rw [p15602]; exact hs9331
  have hs15625 : (denoteGraph_ringAttn pm initPM 15625).shape = [2048, 1024] := by rw [p15625]; exact hs9332
  have hbrm : denoteGraph_ringAttn sm initSM 7943
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15602, denoteGraph_ringAttn pm initPM 15625] := by
    rw [s7943, hbr13, ← p15602, ← p15625]
  have rSM : denoteGraph_ringAttn sm initSM 5255
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7943) :=
    ringAttn_reduce1_pm_opaque sm initSM 410
      { rank := 0, op := "OpName.FW_reshape", ins := [7943], outs := [5255], params := [4096, 1024] }
      7943 5255 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7943 5255)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9353
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15602) :=
    ringAttn_reduce1_pm_opaque pm initPM 880
      { rank := 0, op := "OpName.FW_reshape", ins := [15602], outs := [9353], params := [2048, 1024] }
      15602 9353 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15602 9353)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9354
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15625) :=
    ringAttn_reduce1_pm_opaque pm initPM 884
      { rank := 1, op := "OpName.FW_reshape", ins := [15625], outs := [9354], params := [2048, 1024] }
      15625 9354 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15625 9354)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 9353 = denoteGraph_ringAttn pm initPM 15602 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15602]
  have h66 : denoteGraph_ringAttn pm initPM 9354 = denoteGraph_ringAttn pm initPM 15625 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15625]
  have hval : denoteGraph_ringAttn sm initSM 5255
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9353, denoteGraph_ringAttn pm initPM 9354] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7943, hbrm, hnr, ← h65, ← h66]
  have hs9353 : (denoteGraph_ringAttn pm initPM 9353).shape = [2048, 1024] := by rw [h65]; exact hs15602
  have hs9354 : (denoteGraph_ringAttn pm initPM 9354).shape = [2048, 1024] := by rw [h66]; exact hs15625
  have hs5255 : (denoteGraph_ringAttn sm initSM 5255).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7943]; exact hs7943
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5255 5255 9353 9354 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5255 hs9353 hs9354

/-- 5260 — 2-tp identity reshape of `mref5-pos3(5245)` (SM node 216, PM 491/495). -/
theorem recon_intermediateGoal_5260_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5260
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9331, hs9332⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5245sm : (denoteGraph_ringAttn sm initSM 5245).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9331])]
    simp [List.set, List.getD]
  have s7947 : denoteGraph_ringAttn sm initSM 7947 = id (denoteGraph_ringAttn sm initSM 5245) :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245],
        outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7947 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15606 : denoteGraph_ringAttn pm initPM 15606 = id (denoteGraph_ringAttn pm initPM 9331) :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331],
        outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15606 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15629 : denoteGraph_ringAttn pm initPM 15629 = id (denoteGraph_ringAttn pm initPM 9332) :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332],
        outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15629 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7947 p15606 p15629
  have hs7947 : (denoteGraph_ringAttn sm initSM 7947).shape = [4096, 1024] := by rw [s7947]; exact hs5245sm
  have hs15606 : (denoteGraph_ringAttn pm initPM 15606).shape = [2048, 1024] := by rw [p15606]; exact hs9331
  have hs15629 : (denoteGraph_ringAttn pm initPM 15629).shape = [2048, 1024] := by rw [p15629]; exact hs9332
  have hbrm : denoteGraph_ringAttn sm initSM 7947
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15606, denoteGraph_ringAttn pm initPM 15629] := by
    rw [s7947, hbr13, ← p15606, ← p15629]
  have rSM : denoteGraph_ringAttn sm initSM 5260
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7947) :=
    ringAttn_reduce1_pm_opaque sm initSM 411
      { rank := 0, op := "OpName.FW_reshape", ins := [7947], outs := [5260], params := [4096, 1024] }
      7947 5260 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7947 5260)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9367
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15606) :=
    ringAttn_reduce1_pm_opaque pm initPM 881
      { rank := 0, op := "OpName.FW_reshape", ins := [15606], outs := [9367], params := [2048, 1024] }
      15606 9367 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15606 9367)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9368
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15629) :=
    ringAttn_reduce1_pm_opaque pm initPM 885
      { rank := 1, op := "OpName.FW_reshape", ins := [15629], outs := [9368], params := [2048, 1024] }
      15629 9368 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15629 9368)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 9367 = denoteGraph_ringAttn pm initPM 15606 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15606]
  have h80 : denoteGraph_ringAttn pm initPM 9368 = denoteGraph_ringAttn pm initPM 15629 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15629]
  have hval : denoteGraph_ringAttn sm initSM 5260
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9367, denoteGraph_ringAttn pm initPM 9368] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7947, hbrm, hnr, ← h79, ← h80]
  have hs9367 : (denoteGraph_ringAttn pm initPM 9367).shape = [2048, 1024] := by rw [h79]; exact hs15606
  have hs9368 : (denoteGraph_ringAttn pm initPM 9368).shape = [2048, 1024] := by rw [h80]; exact hs15629
  have hs5260 : (denoteGraph_ringAttn sm initSM 5260).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7947]; exact hs7947
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5260 5260 9367 9368 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5260 hs9367 hs9368

/-- 5264 — 2-tp identity reshape of `mref5-pos4(5245)` (SM node 217, PM 492/496). -/
theorem recon_intermediateGoal_5264_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5264
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9331, hs9332⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5245sm : (denoteGraph_ringAttn sm initSM 5245).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9331])]
    simp [List.set, List.getD]
  have s7951 : denoteGraph_ringAttn sm initSM 7951 = id (denoteGraph_ringAttn sm initSM 5245) :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245],
        outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7951 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15610 : denoteGraph_ringAttn pm initPM 15610 = id (denoteGraph_ringAttn pm initPM 9331) :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331],
        outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15610 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15633 : denoteGraph_ringAttn pm initPM 15633 = id (denoteGraph_ringAttn pm initPM 9332) :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332],
        outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15633 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7951 p15610 p15633
  have hs7951 : (denoteGraph_ringAttn sm initSM 7951).shape = [4096, 1024] := by rw [s7951]; exact hs5245sm
  have hs15610 : (denoteGraph_ringAttn pm initPM 15610).shape = [2048, 1024] := by rw [p15610]; exact hs9331
  have hs15633 : (denoteGraph_ringAttn pm initPM 15633).shape = [2048, 1024] := by rw [p15633]; exact hs9332
  have hbrm : denoteGraph_ringAttn sm initSM 7951
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15610, denoteGraph_ringAttn pm initPM 15633] := by
    rw [s7951, hbr13, ← p15610, ← p15633]
  have rSM : denoteGraph_ringAttn sm initSM 5264
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7951) :=
    ringAttn_reduce1_pm_opaque sm initSM 412
      { rank := 0, op := "OpName.FW_reshape", ins := [7951], outs := [5264], params := [4096, 1024] }
      7951 5264 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7951 5264)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9385
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15610) :=
    ringAttn_reduce1_pm_opaque pm initPM 882
      { rank := 0, op := "OpName.FW_reshape", ins := [15610], outs := [9385], params := [2048, 1024] }
      15610 9385 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15610 9385)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9386
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15633) :=
    ringAttn_reduce1_pm_opaque pm initPM 886
      { rank := 1, op := "OpName.FW_reshape", ins := [15633], outs := [9386], params := [2048, 1024] }
      15633 9386 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15633 9386)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 9385 = denoteGraph_ringAttn pm initPM 15610 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15610]
  have h98 : denoteGraph_ringAttn pm initPM 9386 = denoteGraph_ringAttn pm initPM 15633 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15633]
  have hval : denoteGraph_ringAttn sm initSM 5264
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9385, denoteGraph_ringAttn pm initPM 9386] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7951, hbrm, hnr, ← h97, ← h98]
  have hs9385 : (denoteGraph_ringAttn pm initPM 9385).shape = [2048, 1024] := by rw [h97]; exact hs15610
  have hs9386 : (denoteGraph_ringAttn pm initPM 9386).shape = [2048, 1024] := by rw [h98]; exact hs15633
  have hs5264 : (denoteGraph_ringAttn sm initSM 5264).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7951]; exact hs7951
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5264 5264 9385 9386 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5264 hs9385 hs9386

/-! ### L11 router expert mixlins (`5257`/`5262`/`5266`), 2-tp. -/

/-- 5257 — 2-tp `fw_linear(5255, 5256)`, weight `5256 : [1, 1024]` → `[4096, 1]`
    (SM node 219, PM nodes 498/502). -/
theorem recon_intermediateGoal_5257_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5257
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs9353, hs9354⟩ := twoTp_gather _ _ intermediateGoal_5255 5255 9353 9354
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5255_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5256 : denoteGraph_ringAttn sm initSM 5256 = denoteGraph_ringAttn pm initPM 5256 :=
    veq_weight_ring initSM initPM hInit initGoal_5256 (by native_decide) 5256
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5256 : (denoteGraph_ringAttn pm initPM 5256).shape = [1, 1024] := by
    rw [← hw5256]
    exact shape_weight_ring initSM initPM hInit initGoal_5256 (by native_decide) 5256 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5257
      = fw_linear (denoteGraph_ringAttn sm initSM 5255) (denoteGraph_ringAttn sm initSM 5256) :=
    ringAttn_reduce2_pm_opaque sm initSM 414
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5255, 5256], outs := [5257] }
      5255 5256 5257 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5255 5256 5257)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9357
      = fw_linear (denoteGraph_ringAttn pm initPM 9353) (denoteGraph_ringAttn pm initPM 5256) :=
    ringAttn_reduce2_pm_opaque pm initPM 888
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9353, 5256], outs := [9357] }
      9353 5256 9357 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9353 5256 9357)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9358
      = fw_linear (denoteGraph_ringAttn pm initPM 9354) (denoteGraph_ringAttn pm initPM 5256) :=
    ringAttn_reduce2_pm_opaque pm initPM 892
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9354, 5256], outs := [9358] }
      9354 5256 9358 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9354 5256 9358)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5257
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9357, denoteGraph_ringAttn pm initPM 9358] := by
    rw [rSM, hval23, hw5256, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs9353 hs9354 hpw5256,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9357).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9353 hpw5256
  have hsp1 : (denoteGraph_ringAttn pm initPM 9358).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9354 hpw5256
  have hshape : (denoteGraph_ringAttn sm initSM 5257).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5257 5257 9357 9358 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5262 — 2-tp `fw_linear(5260, 5261)`, weight `5261 : [512, 1024]` → `[4096, 512]`
    (SM node 220, PM nodes 499/503). -/
theorem recon_intermediateGoal_5262_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5262
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs9367, hs9368⟩ := twoTp_gather _ _ intermediateGoal_5260 5260 9367 9368
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5260_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5261 : denoteGraph_ringAttn sm initSM 5261 = denoteGraph_ringAttn pm initPM 5261 :=
    veq_weight_ring initSM initPM hInit initGoal_5261 (by native_decide) 5261
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5261 : (denoteGraph_ringAttn pm initPM 5261).shape = [512, 1024] := by
    rw [← hw5261]
    exact shape_weight_ring initSM initPM hInit initGoal_5261 (by native_decide) 5261 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5262
      = fw_linear (denoteGraph_ringAttn sm initSM 5260) (denoteGraph_ringAttn sm initSM 5261) :=
    ringAttn_reduce2_pm_opaque sm initSM 415
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5260, 5261], outs := [5262] }
      5260 5261 5262 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5260 5261 5262)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9371
      = fw_linear (denoteGraph_ringAttn pm initPM 9367) (denoteGraph_ringAttn pm initPM 5261) :=
    ringAttn_reduce2_pm_opaque pm initPM 889
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9367, 5261], outs := [9371] }
      9367 5261 9371 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9367 5261 9371)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9372
      = fw_linear (denoteGraph_ringAttn pm initPM 9368) (denoteGraph_ringAttn pm initPM 5261) :=
    ringAttn_reduce2_pm_opaque pm initPM 893
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9368, 5261], outs := [9372] }
      9368 5261 9372 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9368 5261 9372)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5262
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9371, denoteGraph_ringAttn pm initPM 9372] := by
    rw [rSM, hval28, hw5261, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs9367 hs9368 hpw5261,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9371).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9367 hpw5261
  have hsp1 : (denoteGraph_ringAttn pm initPM 9372).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9368 hpw5261
  have hshape : (denoteGraph_ringAttn sm initSM 5262).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5262 5262 9371 9372 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5266 — 2-tp `fw_linear(5264, 5265)`, weight `5265 : [512, 1024]` → `[4096, 512]`
    (SM node 221, PM nodes 500/504). -/
theorem recon_intermediateGoal_5266_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5266
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs9385, hs9386⟩ := twoTp_gather _ _ intermediateGoal_5264 5264 9385 9386
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5264_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5265 : denoteGraph_ringAttn sm initSM 5265 = denoteGraph_ringAttn pm initPM 5265 :=
    veq_weight_ring initSM initPM hInit initGoal_5265 (by native_decide) 5265
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5265 : (denoteGraph_ringAttn pm initPM 5265).shape = [512, 1024] := by
    rw [← hw5265]
    exact shape_weight_ring initSM initPM hInit initGoal_5265 (by native_decide) 5265 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5266
      = fw_linear (denoteGraph_ringAttn sm initSM 5264) (denoteGraph_ringAttn sm initSM 5265) :=
    ringAttn_reduce2_pm_opaque sm initSM 416
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5264, 5265], outs := [5266] }
      5264 5265 5266 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5264 5265 5266)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9389
      = fw_linear (denoteGraph_ringAttn pm initPM 9385) (denoteGraph_ringAttn pm initPM 5265) :=
    ringAttn_reduce2_pm_opaque pm initPM 890
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9385, 5265], outs := [9389] }
      9385 5265 9389 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9385 5265 9389)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9390
      = fw_linear (denoteGraph_ringAttn pm initPM 9386) (denoteGraph_ringAttn pm initPM 5265) :=
    ringAttn_reduce2_pm_opaque pm initPM 894
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9386, 5265], outs := [9390] }
      9386 5265 9390 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9386 5265 9390)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5266
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9389, denoteGraph_ringAttn pm initPM 9390] := by
    rw [rSM, hval32, hw5265, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs9385 hs9386 hpw5265,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9389).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9385 hpw5265
  have hsp1 : (denoteGraph_ringAttn pm initPM 9390).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9386 hpw5265
  have hshape : (denoteGraph_ringAttn sm initSM 5266).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5266 5266 9389 9390 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L11 router expert views (`5258`/`5263`/`5267`), identity 2-tp views. -/

/-- 5258 — 2-tp identity view of `5257` → `[4096, 1]` (SM node 223, PM 506/510). -/
theorem recon_intermediateGoal_5258_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5258
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs9357, hs9358⟩ := twoTp_gather _ _ intermediateGoal_5257 5257 9357 9358
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5257_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5257 : (denoteGraph_ringAttn sm initSM 5257).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs9357])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5258
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 5257) :=
    ringAttn_reduce1_pm_opaque sm initSM 418
      { rank := 0, op := "OpName.FW_view", ins := [5257], outs := [5258], params := [4096, 1] }
      5257 5258 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 5257 5258)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9363
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9357) :=
    ringAttn_reduce1_pm_opaque pm initPM 896
      { rank := 0, op := "OpName.FW_view", ins := [9357], outs := [9363], params := [2048, 1] }
      9357 9363 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 9357 9363)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9364
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9358) :=
    ringAttn_reduce1_pm_opaque pm initPM 900
      { rank := 1, op := "OpName.FW_view", ins := [9358], outs := [9364], params := [2048, 1] }
      9358 9364 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 9358 9364)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 9363 = denoteGraph_ringAttn pm initPM 9357 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs9357]
  have h76 : denoteGraph_ringAttn pm initPM 9364 = denoteGraph_ringAttn pm initPM 9358 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs9358]
  have hval : denoteGraph_ringAttn sm initSM 5258
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9363, denoteGraph_ringAttn pm initPM 9364] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5257, hval25, hnr, ← h75, ← h76]
  have hs9363 : (denoteGraph_ringAttn pm initPM 9363).shape = [2048, 1] := by rw [h75]; exact hs9357
  have hs9364 : (denoteGraph_ringAttn pm initPM 9364).shape = [2048, 1] := by rw [h76]; exact hs9358
  have hs5258 : (denoteGraph_ringAttn sm initSM 5258).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5257]; exact hs5257
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5258 5258 9363 9364 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5258 hs9363 hs9364

/-- 5263 — 2-tp identity view of `5262` → `[4096, 512]` (SM node 224, PM 507/511). -/
theorem recon_intermediateGoal_5263_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5263
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs9371, hs9372⟩ := twoTp_gather _ _ intermediateGoal_5262 5262 9371 9372
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5262_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5262 : (denoteGraph_ringAttn sm initSM 5262).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9371])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5263
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5262) :=
    ringAttn_reduce1_pm_opaque sm initSM 419
      { rank := 0, op := "OpName.FW_view", ins := [5262], outs := [5263], params := [4096, 512] }
      5262 5263 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5262 5263)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9381
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9371) :=
    ringAttn_reduce1_pm_opaque pm initPM 897
      { rank := 0, op := "OpName.FW_view", ins := [9371], outs := [9381], params := [2048, 512] }
      9371 9381 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9371 9381)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9382
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9372) :=
    ringAttn_reduce1_pm_opaque pm initPM 901
      { rank := 1, op := "OpName.FW_view", ins := [9372], outs := [9382], params := [2048, 512] }
      9372 9382 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9372 9382)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 9381 = denoteGraph_ringAttn pm initPM 9371 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9371]
  have h94 : denoteGraph_ringAttn pm initPM 9382 = denoteGraph_ringAttn pm initPM 9372 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9372]
  have hval : denoteGraph_ringAttn sm initSM 5263
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9381, denoteGraph_ringAttn pm initPM 9382] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5262, hval30, hnr, ← h93, ← h94]
  have hs9381 : (denoteGraph_ringAttn pm initPM 9381).shape = [2048, 512] := by rw [h93]; exact hs9371
  have hs9382 : (denoteGraph_ringAttn pm initPM 9382).shape = [2048, 512] := by rw [h94]; exact hs9372
  have hs5263 : (denoteGraph_ringAttn sm initSM 5263).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5262]; exact hs5262
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5263 5263 9381 9382 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5263 hs9381 hs9382

/-- 5267 — 2-tp identity view of `5266` → `[4096, 512]` (SM node 225, PM 508/512). -/
theorem recon_intermediateGoal_5267_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5267
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs9389, hs9390⟩ := twoTp_gather _ _ intermediateGoal_5266 5266 9389 9390
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5266_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5266 : (denoteGraph_ringAttn sm initSM 5266).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9389])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5267
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5266) :=
    ringAttn_reduce1_pm_opaque sm initSM 420
      { rank := 0, op := "OpName.FW_view", ins := [5266], outs := [5267], params := [4096, 512] }
      5266 5267 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5266 5267)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9399
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9389) :=
    ringAttn_reduce1_pm_opaque pm initPM 898
      { rank := 0, op := "OpName.FW_view", ins := [9389], outs := [9399], params := [2048, 512] }
      9389 9399 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9389 9399)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9400
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9390) :=
    ringAttn_reduce1_pm_opaque pm initPM 902
      { rank := 1, op := "OpName.FW_view", ins := [9390], outs := [9400], params := [2048, 512] }
      9390 9400 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9390 9400)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 9399 = denoteGraph_ringAttn pm initPM 9389 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9389]
  have h12 : denoteGraph_ringAttn pm initPM 9400 = denoteGraph_ringAttn pm initPM 9390 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9390]
  have hval : denoteGraph_ringAttn sm initSM 5267
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9399, denoteGraph_ringAttn pm initPM 9400] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5266, hval34, hnr, ← h11, ← h12]
  have hs9399 : (denoteGraph_ringAttn pm initPM 9399).shape = [2048, 512] := by rw [h11]; exact hs9389
  have hs9400 : (denoteGraph_ringAttn pm initPM 9400).shape = [2048, 512] := by rw [h12]; exact hs9390
  have hs5267 : (denoteGraph_ringAttn sm initSM 5267).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5266]; exact hs5266
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5267 5267 9399 9400 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5267 hs9399 hs9400

/-! ### L11 MoE gate/expert branch (`5259` sigmoid, `5268` swiglu, `5269` reshape,
    `5271` mixlin, `5272` view, `5273` broadcast-mul), all 2-tp shard-direct. -/

/-- 5259 — 2-tp `fw_sigmoid(5258)` → `[4096, 1]` (SM node 227, PM 514/517). -/
theorem recon_intermediateGoal_5259_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5259
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs9363, hs9364⟩ := twoTp_gather _ _ intermediateGoal_5258 5258 9363 9364
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5258_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5259 = fw_sigmoid (denoteGraph_ringAttn sm initSM 5258) :=
    ringAttn_reduce1_pm_opaque sm initSM 422
      { rank := 0, op := "OpName.FW_sigmoid", ins := [5258], outs := [5259] }
      5258 5259 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 5258 5259 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9365 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9363) :=
    ringAttn_reduce1_pm_opaque pm initPM 904
      { rank := 0, op := "OpName.FW_sigmoid", ins := [9363], outs := [9365] }
      9363 9365 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 9363 9365 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9366 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9364) :=
    ringAttn_reduce1_pm_opaque pm initPM 907
      { rank := 1, op := "OpName.FW_sigmoid", ins := [9364], outs := [9366] }
      9364 9366 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 9364 9366 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5259
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9365, denoteGraph_ringAttn pm initPM 9366] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs9363 hs9364, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5259).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs9363])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9365).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs9363
  have hsp1 : (denoteGraph_ringAttn pm initPM 9366).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs9364
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5259 5259 9365 9366 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5268 — 2-tp `fw_swiglu(5263, 5267)` → `[4096, 512]` (SM node 228, PM 515/518). -/
theorem recon_intermediateGoal_5268_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5268
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs9381, hs9382⟩ := twoTp_gather _ _ intermediateGoal_5263 5263 9381 9382
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5263_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs9399, hs9400⟩ := twoTp_gather _ _ intermediateGoal_5267 5267 9399 9400
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5267_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5268
      = fw_swiglu (denoteGraph_ringAttn sm initSM 5263) (denoteGraph_ringAttn sm initSM 5267) :=
    ringAttn_reduce2_pm_opaque sm initSM 423
      { rank := 0, op := "OpName.FW_swiglu", ins := [5263, 5267], outs := [5268] }
      5263 5267 5268 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 5263 5267 5268 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9403
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9381) (denoteGraph_ringAttn pm initPM 9399) :=
    ringAttn_reduce2_pm_opaque pm initPM 905
      { rank := 0, op := "OpName.FW_swiglu", ins := [9381, 9399], outs := [9403] }
      9381 9399 9403 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 9381 9399 9403 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9404
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9382) (denoteGraph_ringAttn pm initPM 9400) :=
    ringAttn_reduce2_pm_opaque pm initPM 908
      { rank := 1, op := "OpName.FW_swiglu", ins := [9382, 9400], outs := [9404] }
      9382 9400 9404 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 9382 9400 9404 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5268
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9403, denoteGraph_ringAttn pm initPM 9404] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs9381 hs9382 hs9399 hs9400,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5268).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9399])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9403).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9399
  have hsp1 : (denoteGraph_ringAttn pm initPM 9404).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9400
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5268 5268 9403 9404 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5269 — 2-tp identity reshape of `5268` → `[4096, 512]` (SM node 229, PM 519/520). -/
theorem recon_intermediateGoal_5269_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5269
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs9403, hs9404⟩ := twoTp_gather _ _ intermediateGoal_5268 5268 9403 9404
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5268_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5268 : (denoteGraph_ringAttn sm initSM 5268).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9403])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5269
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5268) :=
    ringAttn_reduce1_pm_opaque sm initSM 424
      { rank := 0, op := "OpName.FW_reshape", ins := [5268], outs := [5269], params := [4096, 512] }
      5268 5269 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5268 5269)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9405
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9403) :=
    ringAttn_reduce1_pm_opaque pm initPM 909
      { rank := 0, op := "OpName.FW_reshape", ins := [9403], outs := [9405], params := [2048, 512] }
      9403 9405 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9403 9405)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9406
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9404) :=
    ringAttn_reduce1_pm_opaque pm initPM 910
      { rank := 1, op := "OpName.FW_reshape", ins := [9404], outs := [9406], params := [2048, 512] }
      9404 9406 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9404 9406)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 9405 = denoteGraph_ringAttn pm initPM 9403 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9403]
  have h18 : denoteGraph_ringAttn pm initPM 9406 = denoteGraph_ringAttn pm initPM 9404 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9404]
  have hval : denoteGraph_ringAttn sm initSM 5269
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9405, denoteGraph_ringAttn pm initPM 9406] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5268, hval36, hnr, ← h17, ← h18]
  have hs9405 : (denoteGraph_ringAttn pm initPM 9405).shape = [2048, 512] := by rw [h17]; exact hs9403
  have hs9406 : (denoteGraph_ringAttn pm initPM 9406).shape = [2048, 512] := by rw [h18]; exact hs9404
  have hs5269 : (denoteGraph_ringAttn sm initSM 5269).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5268]; exact hs5268
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5269 5269 9405 9406 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5269 hs9405 hs9406

/-- 5271 — 2-tp `fw_linear(5269, 5270)`, weight `5270 : [1024, 512]` → `[4096, 1024]`
    (SM node 230, PM 521/522). -/
theorem recon_intermediateGoal_5271_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5271
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs9405, hs9406⟩ := twoTp_gather _ _ intermediateGoal_5269 5269 9405 9406
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5269_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5270 : denoteGraph_ringAttn sm initSM 5270 = denoteGraph_ringAttn pm initPM 5270 :=
    veq_weight_ring initSM initPM hInit initGoal_5270 (by native_decide) 5270
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5270 : (denoteGraph_ringAttn pm initPM 5270).shape = [1024, 512] := by
    rw [← hw5270]
    exact shape_weight_ring initSM initPM hInit initGoal_5270 (by native_decide) 5270 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5271
      = fw_linear (denoteGraph_ringAttn sm initSM 5269) (denoteGraph_ringAttn sm initSM 5270) :=
    ringAttn_reduce2_pm_opaque sm initSM 425
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5269, 5270], outs := [5271] }
      5269 5270 5271 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5269 5270 5271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9411
      = fw_linear (denoteGraph_ringAttn pm initPM 9405) (denoteGraph_ringAttn pm initPM 5270) :=
    ringAttn_reduce2_pm_opaque pm initPM 911
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9405, 5270], outs := [9411] }
      9405 5270 9411 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9405 5270 9411)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9412
      = fw_linear (denoteGraph_ringAttn pm initPM 9406) (denoteGraph_ringAttn pm initPM 5270) :=
    ringAttn_reduce2_pm_opaque pm initPM 912
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9406, 5270], outs := [9412] }
      9406 5270 9412 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9406 5270 9412)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5271
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9411, denoteGraph_ringAttn pm initPM 9412] := by
    rw [rSM, hval37, hw5270, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs9405 hs9406 hpw5270,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9411).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9405 hpw5270
  have hsp1 : (denoteGraph_ringAttn pm initPM 9412).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9406 hpw5270
  have hshape : (denoteGraph_ringAttn sm initSM 5271).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5271 5271 9411 9412 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5272 — 2-tp identity view of `5271` → `[4096, 1024]` (SM node 231, PM 523/524). -/
theorem recon_intermediateGoal_5272_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5272
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs9411, hs9412⟩ := twoTp_gather _ _ intermediateGoal_5271 5271 9411 9412
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5271_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5271 : (denoteGraph_ringAttn sm initSM 5271).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9411])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5272
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5271) :=
    ringAttn_reduce1_pm_opaque sm initSM 426
      { rank := 0, op := "OpName.FW_view", ins := [5271], outs := [5272], params := [4096, 1024] }
      5271 5272 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5271 5272)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9421
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9411) :=
    ringAttn_reduce1_pm_opaque pm initPM 913
      { rank := 0, op := "OpName.FW_view", ins := [9411], outs := [9421], params := [2048, 1024] }
      9411 9421 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9411 9421)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9422
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9412) :=
    ringAttn_reduce1_pm_opaque pm initPM 914
      { rank := 1, op := "OpName.FW_view", ins := [9412], outs := [9422], params := [2048, 1024] }
      9412 9422 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9412 9422)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 9421 = denoteGraph_ringAttn pm initPM 9411 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9411]
  have h34 : denoteGraph_ringAttn pm initPM 9422 = denoteGraph_ringAttn pm initPM 9412 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9412]
  have hval : denoteGraph_ringAttn sm initSM 5272
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9421, denoteGraph_ringAttn pm initPM 9422] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5271, hval39, hnr, ← h33, ← h34]
  have hs9421 : (denoteGraph_ringAttn pm initPM 9421).shape = [2048, 1024] := by rw [h33]; exact hs9411
  have hs9422 : (denoteGraph_ringAttn pm initPM 9422).shape = [2048, 1024] := by rw [h34]; exact hs9412
  have hs5272 : (denoteGraph_ringAttn sm initSM 5272).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5271]; exact hs5271
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5272 5272 9421 9422 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5272 hs9421 hs9422

/-- 5273 — 2-tp broadcast `mul(5259, 5272)` → `[4096, 1024]` (SM node 232, PM 525/526). -/
theorem recon_intermediateGoal_5273_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5273
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_5259 5259 9365 9366
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5259_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_5272 5272 9421 9422
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5272_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5273
      = elemwiseMul (denoteGraph_ringAttn sm initSM 5259) (denoteGraph_ringAttn sm initSM 5272) :=
    ringAttn_reduce2_pm_opaque sm initSM 427
      { rank := 0, op := "OpName.FW_mul", ins := [5259, 5272], outs := [5273] }
      5259 5272 5273 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 5259 5272 5273)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9425
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9365) (denoteGraph_ringAttn pm initPM 9421) :=
    ringAttn_reduce2_pm_opaque pm initPM 915
      { rank := 0, op := "OpName.FW_mul", ins := [9365, 9421], outs := [9425] }
      9365 9421 9425 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 9365 9421 9425)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9426
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9366) (denoteGraph_ringAttn pm initPM 9422) :=
    ringAttn_reduce2_pm_opaque pm initPM 916
      { rank := 1, op := "OpName.FW_mul", ins := [9366, 9422], outs := [9426] }
      9366 9422 9426 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 9366 9422 9426)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5273
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9425, denoteGraph_ringAttn pm initPM 9426] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 5273).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 5259).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 5272).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 9425).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 9426).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5273 5273 9425 9426 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 5254 — layer-11 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 5254 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`9351`), rank 1 →
    `[32, 64)` (`9352`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `9343`/`9344` are expert-local (the
    `wf5254_hdisjA/B` fields).  Token input `7939 = mref5-pos1(5245)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 226, PM nodes 513/516). -/
theorem recon_intermediateGoal_5254_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5254
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 8475 = mref5-pos1(5245).
  obtain ⟨hbr13, hs9331, hs9332⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8475 : denoteGraph_ringAttn sm initSM 7939 = id (denoteGraph_ringAttn sm initSM 5245) :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245],
        outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7939 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15598 : denoteGraph_ringAttn pm initPM 15598 = id (denoteGraph_ringAttn pm initPM 9331) :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331],
        outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15598 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15621 : denoteGraph_ringAttn pm initPM 15621 = id (denoteGraph_ringAttn pm initPM 9332) :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332],
        outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15621 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8475 p15598 p15621
  have hsInA : (denoteGraph_ringAttn pm initPM 15598).shape = [2048, 1024] := by
    rw [p15598]; exact hs9331
  have hsInB : (denoteGraph_ringAttn pm initPM 15621).shape = [2048, 1024] := by
    rw [p15621]; exact hs9332
  have hbrIn : denoteGraph_ringAttn sm initSM 7939
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 15598, denoteGraph_ringAttn pm initPM 15621] := by
    rw [s8475, hbr13, hnr, ← p15598, ← p15621]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_5249 5249 9341 9342
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5249_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_5250 5250 9343 9344
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5250_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 5249
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9341, denoteGraph_ringAttn pm initPM 9342] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 5250
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9343, denoteGraph_ringAttn pm initPM 9344] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_5252
    (by native_decide) 5252 9347 9348 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_5253
    (by native_decide) 5253 9349 9350 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 9347).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5252 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5252, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9347 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 9348).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5252 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5252, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9348 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 9349).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5253 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5253, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9349 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 9350).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5253 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5253, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9350 (by native_decide)]; exact hs.2
  -- SM 5254 = full-range all2all (SM node 226).
  have hSMout : denoteGraph_ringAttn sm initSM 5254
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7939)
          (denoteGraph_ringAttn sm initSM 5249) (denoteGraph_ringAttn sm initSM 5250)
          (denoteGraph_ringAttn sm initSM 5252) (denoteGraph_ringAttn sm initSM 5253)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 421
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7939, 5249, 5250, 5252, 5253],
        outs := [5254], params := [64, 0, 64, 8] }
      7939 5249 5250 5252 5253 5254
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7939 5249 5250 5252 5253 5254 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9351 = rank-0 sharded-range all2all (PM node 513).
  have hP0 : denoteGraph_ringAttn pm initPM 9351
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15598)
          (denoteGraph_ringAttn pm initPM 9341) (denoteGraph_ringAttn pm initPM 9343)
          (denoteGraph_ringAttn pm initPM 9347) (denoteGraph_ringAttn pm initPM 9349)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 903
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15598, 9341, 9343, 9347, 9349],
        outs := [9351], params := [64, 0, 32, 8] }
      15598 9341 9343 9347 9349 9351
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 15598 9341 9343 9347 9349 9351 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9352 = rank-1 sharded-range all2all (PM node 516).
  have hP1 : denoteGraph_ringAttn pm initPM 9352
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15621)
          (denoteGraph_ringAttn pm initPM 9342) (denoteGraph_ringAttn pm initPM 9344)
          (denoteGraph_ringAttn pm initPM 9348) (denoteGraph_ringAttn pm initPM 9350)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 906
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15621, 9342, 9344, 9348, 9350],
        outs := [9352], params := [64, 32, 64, 8] }
      15621 9342 9344 9348 9350 9352
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 15621 9342 9344 9348 9350 9352 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 15598) (denoteGraph_ringAttn pm initPM 15621)
      (denoteGraph_ringAttn pm initPM 9341) (denoteGraph_ringAttn pm initPM 9342)
      (denoteGraph_ringAttn pm initPM 9343) (denoteGraph_ringAttn pm initPM 9344)
      (denoteGraph_ringAttn pm initPM 9347) (denoteGraph_ringAttn pm initPM 9348)
      (denoteGraph_ringAttn pm initPM 9349) (denoteGraph_ringAttn pm initPM 9350)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf5254_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf5254_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 5254
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9351, denoteGraph_ringAttn pm initPM 9352] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9351).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9352).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 5254).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5254 5254 9351 9352 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L11 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7928 — second position of the L11 pre-MoE residual `mref2(5243)` (2-tp, PM
    shards `15579`/`15587`).  Unlike L2's `7876` there is no gather-to-full/chunk
    because `5243` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 211, PM nodes 477/478). -/
theorem recon_intermediateGoal_7928_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7928
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs9327, hs9328⟩ := twoTp_gather _ _ intermediateGoal_5243 5243 9327 9328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5243_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8330 : denoteGraph_ringAttn sm initSM 7928 = id (denoteGraph_ringAttn sm initSM 5243) :=
    ringAttn_reduce1_pm_opaque sm initSM 406
      { rank := 0, op := "OpName.FW_multiref", ins := [5243], outs := [7924, 7928], params := [2] }
      5243 7928 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5243 7924 7928 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15579 : denoteGraph_ringAttn pm initPM 15579 = id (denoteGraph_ringAttn pm initPM 9327) :=
    ringAttn_reduce1_pm_opaque pm initPM 873
      { rank := 0, op := "OpName.FW_multiref", ins := [9327], outs := [15575, 15579], params := [2] }
      9327 15579 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9327 15575 15579 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15587 : denoteGraph_ringAttn pm initPM 15587 = id (denoteGraph_ringAttn pm initPM 9328) :=
    ringAttn_reduce1_pm_opaque pm initPM 874
      { rank := 1, op := "OpName.FW_multiref", ins := [9328], outs := [15583, 15587], params := [2] }
      9328 15587 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9328 15583 15587 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8330 p15579 p15587
  have hsp0 : (denoteGraph_ringAttn pm initPM 15579).shape = [2048, 1024] := by
    rw [p15579]; exact hs9327
  have hsp1 : (denoteGraph_ringAttn pm initPM 15587).shape = [2048, 1024] := by
    rw [p15587]; exact hs9328
  have hval : denoteGraph_ringAttn sm initSM 7928
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15579, denoteGraph_ringAttn pm initPM 15587] := by
    rw [s8330, hbr11, ← p15579, ← p15587]
  have hshape : (denoteGraph_ringAttn sm initSM 7928).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7928 7928 15579 15587 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5274 — post-MoE residual add `5254 + 5273` (2-tp, PM `9429`/`9430`). -/
theorem recon_intermediateGoal_5274_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5274
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs9351, hs9352⟩ := twoTp_gather _ _ intermediateGoal_5254 5254 9351 9352
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5254_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs9425, hs9426⟩ := twoTp_gather _ _ intermediateGoal_5273 5273 9425 9426
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5273_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5274
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 5254) (denoteGraph_ringAttn sm initSM 5273) :=
    ringAttn_reduce2_pm_opaque sm initSM 428
      { rank := 0, op := "OpName.FW_add", ins := [5254, 5273], outs := [5274] }
      5254 5273 5274 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 5254 5273 5274)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9429
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9351) (denoteGraph_ringAttn pm initPM 9425) :=
    ringAttn_reduce2_pm_opaque pm initPM 917
      { rank := 0, op := "OpName.FW_add", ins := [9351, 9425], outs := [9429] }
      9351 9425 9429 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 9351 9425 9429)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9430
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9352) (denoteGraph_ringAttn pm initPM 9426) :=
    ringAttn_reduce2_pm_opaque pm initPM 918
      { rank := 1, op := "OpName.FW_add", ins := [9352, 9426], outs := [9430] }
      9352 9426 9430 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 9352 9426 9430)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5274
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9429, denoteGraph_ringAttn pm initPM 9430] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs9351 hs9352 hs9425 hs9426,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9429).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9351 hs9425
  have hsp1 : (denoteGraph_ringAttn pm initPM 9430).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9352 hs9426
  have hshape : (denoteGraph_ringAttn sm initSM 5274).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5274 5274 9429 9430 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5275 — `FW_float(5274)` (identity, 2-tp PM `9435`/`9436`). -/
theorem recon_intermediateGoal_5275_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5275
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs9429, hs9430⟩ := twoTp_gather _ _ intermediateGoal_5274 5274 9429 9430
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5274_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5275 = id (denoteGraph_ringAttn sm initSM 5274) :=
    ringAttn_reduce1_pm_opaque sm initSM 429
      { rank := 0, op := "OpName.FW_float", ins := [5274], outs := [5275] }
      5274 5275 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5274 5275 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9435 = id (denoteGraph_ringAttn pm initPM 9429) :=
    ringAttn_reduce1_pm_opaque pm initPM 919
      { rank := 0, op := "OpName.FW_float", ins := [9429], outs := [9435] }
      9429 9435 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9429 9435 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9436 = id (denoteGraph_ringAttn pm initPM 9430) :=
    ringAttn_reduce1_pm_opaque pm initPM 920
      { rank := 1, op := "OpName.FW_float", ins := [9430], outs := [9436] }
      9430 9436 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9430 9436 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5275
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9435, denoteGraph_ringAttn pm initPM 9436] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9435).shape = [2048, 1024] := by rw [rP0]; exact hs9429
  have hsp1 : (denoteGraph_ringAttn pm initPM 9436).shape = [2048, 1024] := by rw [rP1]; exact hs9430
  have hshape : (denoteGraph_ringAttn sm initSM 5275).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5275 5275 9435 9436 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5276 — cross-block residual add `7928 + 5275` (2-tp, PM `9439`/`9440`). -/
theorem recon_intermediateGoal_5276_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5276
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs15579, hs15587⟩ := twoTp_gather _ _ intermediateGoal_7928 7928 15579 15587
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7928_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs9435, hs9436⟩ := twoTp_gather _ _ intermediateGoal_5275 5275 9435 9436
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5275_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5276
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7928) (denoteGraph_ringAttn sm initSM 5275) :=
    ringAttn_reduce2_pm_opaque sm initSM 430
      { rank := 0, op := "OpName.FW_add", ins := [7928, 5275], outs := [5276] }
      7928 5275 5276 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7928 5275 5276)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9439
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15579) (denoteGraph_ringAttn pm initPM 9435) :=
    ringAttn_reduce2_pm_opaque pm initPM 921
      { rank := 0, op := "OpName.FW_add", ins := [15579, 9435], outs := [9439] }
      15579 9435 9439 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15579 9435 9439)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9440
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15587) (denoteGraph_ringAttn pm initPM 9436) :=
    ringAttn_reduce2_pm_opaque pm initPM 922
      { rank := 1, op := "OpName.FW_add", ins := [15587, 9436], outs := [9440] }
      15587 9436 9440 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15587 9436 9440)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5276
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9439, denoteGraph_ringAttn pm initPM 9440] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15579 hs15587 hs9435 hs9436,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9439).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15579 hs9435
  have hsp1 : (denoteGraph_ringAttn pm initPM 9440).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15587 hs9436
  have hshape : (denoteGraph_ringAttn sm initSM 5276).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5276 5276 9439 9440 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5278 — RMSNorm of `mref2-first(5276)` with replicated weight `5277`
    (2-tp, PM `9443`/`9444`). -/
theorem recon_intermediateGoal_5278_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5278
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs9439, hs9440⟩ := twoTp_gather _ _ intermediateGoal_5276 5276 9439 9440
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5276_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8491 : denoteGraph_ringAttn sm initSM 7955 = id (denoteGraph_ringAttn sm initSM 5276) :=
    ringAttn_reduce1_pm_opaque sm initSM 431
      { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959], params := [2] }
      5276 7955 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5276 7955 7959)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15637 : denoteGraph_ringAttn pm initPM 15637 = id (denoteGraph_ringAttn pm initPM 9439) :=
    ringAttn_reduce1_pm_opaque pm initPM 923
      { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641], params := [2] }
      9439 15637 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9439 15637 15641)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15645 : denoteGraph_ringAttn pm initPM 15645 = id (denoteGraph_ringAttn pm initPM 9440) :=
    ringAttn_reduce1_pm_opaque pm initPM 924
      { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649], params := [2] }
      9440 15645 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9440 15645 15649)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8491 p15637 p15645
  have hs15637 : (denoteGraph_ringAttn pm initPM 15637).shape = [2048, 1024] := by
    rw [p15637]; exact hs9439
  have hs15645 : (denoteGraph_ringAttn pm initPM 15645).shape = [2048, 1024] := by
    rw [p15645]; exact hs9440
  have hbr39 : denoteGraph_ringAttn sm initSM 7955
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15637, denoteGraph_ringAttn pm initPM 15645] := by
    rw [s8491, hbr44, ← p15637, ← p15645]
  have hw5277 : denoteGraph_ringAttn sm initSM 5277 = denoteGraph_ringAttn pm initPM 5277 :=
    veq_weight_ring initSM initPM hInit initGoal_5277 (by native_decide) 5277
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5278
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7955) (denoteGraph_ringAttn sm initSM 5277) :=
    ringAttn_reduce2_pm_opaque sm initSM 432
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7955, 5277], outs := [5278] }
      7955 5277 5278 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7955 5277 5278)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9443
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15637) (denoteGraph_ringAttn pm initPM 5277) :=
    ringAttn_reduce2_pm_opaque pm initPM 925
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15637, 5277], outs := [9443] }
      15637 5277 9443 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15637 5277 9443)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9444
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15645) (denoteGraph_ringAttn pm initPM 5277) :=
    ringAttn_reduce2_pm_opaque pm initPM 926
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15645, 5277], outs := [9444] }
      15645 5277 9444 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15645 5277 9444)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5278
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9443, denoteGraph_ringAttn pm initPM 9444] := by
    rw [rSM, hbr39, hw5277, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15637 hs15645,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9443).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15637
  have hsp1 : (denoteGraph_ringAttn pm initPM 9444).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15645
  have hshape : (denoteGraph_ringAttn sm initSM 5278).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5278 5278 9443 9444 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5280 — per-head Q projection `fw_per_head_linear(mref3₀(5278), 5279)`
    (2-tp, PM `9445`/`9446`, weight `5279 : [16,64,1024]`). -/
theorem recon_intermediateGoal_5280_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5280
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9443, hs9444⟩ := twoTp_gather _ _ intermediateGoal_5278 5278 9443 9444
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5278_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8500 : denoteGraph_ringAttn sm initSM 7964 = id (denoteGraph_ringAttn sm initSM 5278) :=
    ringAttn_reduce1_pm_opaque sm initSM 433
      { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
      5278 7964 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5278 7964 7968 7972)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15654 : denoteGraph_ringAttn pm initPM 15654 = id (denoteGraph_ringAttn pm initPM 9443) :=
    ringAttn_reduce1_pm_opaque pm initPM 927
      { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
      9443 15654 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 9443 15654 15658 15662)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15667 : denoteGraph_ringAttn pm initPM 15667 = id (denoteGraph_ringAttn pm initPM 9444) :=
    ringAttn_reduce1_pm_opaque pm initPM 928
      { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
      9444 15667 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 9444 15667 15671 15675)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8500 p15654 p15667
  have hs15654 : (denoteGraph_ringAttn pm initPM 15654).shape = [2048, 1024] := by
    rw [p15654]; exact hs9443
  have hs15667 : (denoteGraph_ringAttn pm initPM 15667).shape = [2048, 1024] := by
    rw [p15667]; exact hs9444
  have hbr48 : denoteGraph_ringAttn sm initSM 7964
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15654, denoteGraph_ringAttn pm initPM 15667] := by
    rw [s8500, hbr46, ← p15654, ← p15667]
  have hw5279 : denoteGraph_ringAttn sm initSM 5279 = denoteGraph_ringAttn pm initPM 5279 :=
    veq_weight_ring initSM initPM hInit initGoal_5279 (by native_decide) 5279
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5279 : (denoteGraph_ringAttn sm initSM 5279).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5279 (by native_decide) 5279 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5279 : (denoteGraph_ringAttn pm initPM 5279).shape = [16, 64, 1024] := by
    rw [← hw5279]; exact hsw5279
  have rSM : denoteGraph_ringAttn sm initSM 5280
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7964) (denoteGraph_ringAttn sm initSM 5279) :=
    ringAttn_reduce2_pm_opaque sm initSM 434
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7964, 5279], outs := [5280] }
      7964 5279 5280 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7964 5279 5280 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9445
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15654) (denoteGraph_ringAttn pm initPM 5279) :=
    ringAttn_reduce2_pm_opaque pm initPM 929
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15654, 5279], outs := [9445] }
      15654 5279 9445 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15654 5279 9445 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9446
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15667) (denoteGraph_ringAttn pm initPM 5279) :=
    ringAttn_reduce2_pm_opaque pm initPM 932
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15667, 5279], outs := [9446] }
      15667 5279 9446 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15667 5279 9446 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5280
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9445, denoteGraph_ringAttn pm initPM 9446] := by
    rw [rSM, hbr48, hw5279, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs15654 hs15667 hpw5279,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9445).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15654 hpw5279
  have hsp1 : (denoteGraph_ringAttn pm initPM 9446).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15667 hpw5279
  have hshape : (denoteGraph_ringAttn sm initSM 5280).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5280 5280 9445 9446 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5282 — per-head K projection `fw_per_head_linear(mref3₁(5278), 5281)`
    (2-tp, PM `9457`/`9458`, weight `5281 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5282_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5282
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9443, hs9444⟩ := twoTp_gather _ _ intermediateGoal_5278 5278 9443 9444
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5278_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8370 : denoteGraph_ringAttn sm initSM 7968 = id (denoteGraph_ringAttn sm initSM 5278) :=
    ringAttn_reduce1_pm_opaque sm initSM 433
      { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
      5278 7968 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5278 7964 7968 7972 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15658 : denoteGraph_ringAttn pm initPM 15658 = id (denoteGraph_ringAttn pm initPM 9443) :=
    ringAttn_reduce1_pm_opaque pm initPM 927
      { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
      9443 15658 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 9443 15654 15658 15662 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15671 : denoteGraph_ringAttn pm initPM 15671 = id (denoteGraph_ringAttn pm initPM 9444) :=
    ringAttn_reduce1_pm_opaque pm initPM 928
      { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
      9444 15671 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 9444 15667 15671 15675 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8370 p15658 p15671
  have hs15658 : (denoteGraph_ringAttn pm initPM 15658).shape = [2048, 1024] := by
    rw [p15658]; exact hs9443
  have hs15671 : (denoteGraph_ringAttn pm initPM 15671).shape = [2048, 1024] := by
    rw [p15671]; exact hs9444
  have hbr52 : denoteGraph_ringAttn sm initSM 7968
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15658, denoteGraph_ringAttn pm initPM 15671] := by
    rw [s8370, hbr46, ← p15658, ← p15671]
  have hw5281 : denoteGraph_ringAttn sm initSM 5281 = denoteGraph_ringAttn pm initPM 5281 :=
    veq_weight_ring initSM initPM hInit initGoal_5281 (by native_decide) 5281
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5281 : (denoteGraph_ringAttn sm initSM 5281).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5281 (by native_decide) 5281 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5281 : (denoteGraph_ringAttn pm initPM 5281).shape = [4, 64, 1024] := by
    rw [← hw5281]; exact hsw5281
  have rSM : denoteGraph_ringAttn sm initSM 5282
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7968) (denoteGraph_ringAttn sm initSM 5281) :=
    ringAttn_reduce2_pm_opaque sm initSM 435
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7968, 5281], outs := [5282] }
      7968 5281 5282 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7968 5281 5282 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9457
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15658) (denoteGraph_ringAttn pm initPM 5281) :=
    ringAttn_reduce2_pm_opaque pm initPM 930
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15658, 5281], outs := [9457] }
      15658 5281 9457 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15658 5281 9457 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9458
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15671) (denoteGraph_ringAttn pm initPM 5281) :=
    ringAttn_reduce2_pm_opaque pm initPM 933
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15671, 5281], outs := [9458] }
      15671 5281 9458 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15671 5281 9458 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5282
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9457, denoteGraph_ringAttn pm initPM 9458] := by
    rw [rSM, hbr52, hw5281, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15658 hs15671 hpw5281,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9457).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15658 hpw5281
  have hsp1 : (denoteGraph_ringAttn pm initPM 9458).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15671 hpw5281
  have hshape : (denoteGraph_ringAttn sm initSM 5282).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5282 5282 9457 9458 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5284 — per-head V projection `fw_per_head_linear(mref3₂(5278), 5283)`
    (2-tp, PM `9467`/`9468`, weight `5283 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5284_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5284
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9443, hs9444⟩ := twoTp_gather _ _ intermediateGoal_5278 5278 9443 9444
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5278_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7972 : denoteGraph_ringAttn sm initSM 7972 = id (denoteGraph_ringAttn sm initSM 5278) :=
    ringAttn_reduce1_pm_opaque sm initSM 433
      { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
      5278 7972 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5278 7964 7968 7972 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15662 : denoteGraph_ringAttn pm initPM 15662 = id (denoteGraph_ringAttn pm initPM 9443) :=
    ringAttn_reduce1_pm_opaque pm initPM 927
      { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
      9443 15662 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 9443 15654 15658 15662 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15675 : denoteGraph_ringAttn pm initPM 15675 = id (denoteGraph_ringAttn pm initPM 9444) :=
    ringAttn_reduce1_pm_opaque pm initPM 928
      { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
      9444 15675 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 9444 15667 15671 15675 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7972 p15662 p15675
  have hs15662 : (denoteGraph_ringAttn pm initPM 15662).shape = [2048, 1024] := by
    rw [p15662]; exact hs9443
  have hs15675 : (denoteGraph_ringAttn pm initPM 15675).shape = [2048, 1024] := by
    rw [p15675]; exact hs9444
  have hbr56 : denoteGraph_ringAttn sm initSM 7972
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15662, denoteGraph_ringAttn pm initPM 15675] := by
    rw [s7972, hbr46, ← p15662, ← p15675]
  have hw5283 : denoteGraph_ringAttn sm initSM 5283 = denoteGraph_ringAttn pm initPM 5283 :=
    veq_weight_ring initSM initPM hInit initGoal_5283 (by native_decide) 5283
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5283 : (denoteGraph_ringAttn sm initSM 5283).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5283 (by native_decide) 5283 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5283 : (denoteGraph_ringAttn pm initPM 5283).shape = [4, 64, 1024] := by
    rw [← hw5283]; exact hsw5283
  have rSM : denoteGraph_ringAttn sm initSM 5284
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7972) (denoteGraph_ringAttn sm initSM 5283) :=
    ringAttn_reduce2_pm_opaque sm initSM 436
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7972, 5283], outs := [5284] }
      7972 5283 5284 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7972 5283 5284 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9467
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15662) (denoteGraph_ringAttn pm initPM 5283) :=
    ringAttn_reduce2_pm_opaque pm initPM 931
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15662, 5283], outs := [9467] }
      15662 5283 9467 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15662 5283 9467 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9468
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15675) (denoteGraph_ringAttn pm initPM 5283) :=
    ringAttn_reduce2_pm_opaque pm initPM 934
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15675, 5283], outs := [9468] }
      15675 5283 9468 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15675 5283 9468 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5284
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9467, denoteGraph_ringAttn pm initPM 9468] := by
    rw [rSM, hbr56, hw5283, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15662 hs15675 hpw5283,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9467).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15662 hpw5283
  have hsp1 : (denoteGraph_ringAttn pm initPM 9468).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15675 hpw5283
  have hshape : (denoteGraph_ringAttn sm initSM 5284).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5284 5284 9467 9468 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L11 rotary cos/sin cache agreement: `sm 4691 = pm 11864` (`= 11853 + 3`). -/
theorem hcache_4691_11864 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11864 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11864 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11864 11 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 5286 — rotary-embedding Q output `rotary(4691, 5285, 5280, 5282).1`
    (2-tp, PM `9479`/`9480`; positions `5285 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_5286_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5286
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs9445, hs9446⟩ := twoTp_gather _ _ intermediateGoal_5280 5280 9445 9446
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5280_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_5282 5282 9457 9458
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5282_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11864 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5285 = denoteGraph_ringAttn pm initPM 5285 :=
    veq_weight_ring initSM initPM hInit initGoal_5285 (by native_decide) 5285
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5285 : (denoteGraph_ringAttn sm initSM 5285).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5285 (by native_decide) 5285 [4096]
      rfl rfl (by native_decide)
  have c9477 : denoteGraph_ringAttn pm initPM 9477
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5285) :=
    ringAttn_reduce1_pm_opaque pm initPM 11
      { rank := 0, op := "OpName.ChunkPrim", ins := [5285], outs := [9477], params := [0] }
      5285 9477 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5285 9477 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c9478 : denoteGraph_ringAttn pm initPM 9478
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5285) :=
    ringAttn_reduce1_pm_opaque pm initPM 24
      { rank := 1, op := "OpName.ChunkPrim", ins := [5285], outs := [9478], params := [0] }
      5285 9478 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5285 9478 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5286
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5285)
          (denoteGraph_ringAttn sm initSM 5280) (denoteGraph_ringAttn sm initSM 5282) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 437
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5285, 5280, 5282], outs := [5286, 5287], params := [16, 4] }
          5286 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 437 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 437 5285 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 437 5280 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 437 5282 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 9479
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11864) (denoteGraph_ringAttn pm initPM 9477)
          (denoteGraph_ringAttn pm initPM 9445) (denoteGraph_ringAttn pm initPM 9457) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 935
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11864, 9477, 9445, 9457], outs := [9479, 9481], params := [16, 4] }
          9479 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 935 11864 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 935 9477 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 935 9445 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 935 9457 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 9480
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11864) (denoteGraph_ringAttn pm initPM 9478)
          (denoteGraph_ringAttn pm initPM 9446) (denoteGraph_ringAttn pm initPM 9458) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 936
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11864, 9478, 9446, 9458], outs := [9480, 9482], params := [16, 4] }
          9480 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 936 11864 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 936 9478 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 936 9446 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 936 9458 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5286
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9479, denoteGraph_ringAttn pm initPM 9480] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5285) (denoteGraph_ringAttn pm initPM 9445)
          (denoteGraph_ringAttn pm initPM 9446) 2048 16 64 (by omega) (by omega) (by omega)
          hsp5285 hs9445 hs9446,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 9477
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5285) from c9477),
        ← (show denoteGraph_ringAttn pm initPM 9478
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5285) from c9478),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9479).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs9445
  have hsp1 : (denoteGraph_ringAttn pm initPM 9480).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs9446
  have hshape : (denoteGraph_ringAttn sm initSM 5286).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5286 5286 9479 9480 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 5287 — rotary-embedding K output `rotary(4691, 5285, 5280, 5282).2`
    (2-tp, PM `9481`/`9482`). -/
theorem recon_intermediateGoal_5287_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5287
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_5280 5280 9445 9446
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5280_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs9457, hs9458⟩ := twoTp_gather _ _ intermediateGoal_5282 5282 9457 9458
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5282_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11864 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5285 = denoteGraph_ringAttn pm initPM 5285 :=
    veq_weight_ring initSM initPM hInit initGoal_5285 (by native_decide) 5285
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5285 : (denoteGraph_ringAttn sm initSM 5285).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5285 (by native_decide) 5285 [4096]
      rfl rfl (by native_decide)
  have c9477 : denoteGraph_ringAttn pm initPM 9477
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5285) :=
    ringAttn_reduce1_pm_opaque pm initPM 11
      { rank := 0, op := "OpName.ChunkPrim", ins := [5285], outs := [9477], params := [0] }
      5285 9477 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5285 9477 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c9478 : denoteGraph_ringAttn pm initPM 9478
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5285) :=
    ringAttn_reduce1_pm_opaque pm initPM 24
      { rank := 1, op := "OpName.ChunkPrim", ins := [5285], outs := [9478], params := [0] }
      5285 9478 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5285 9478 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5287
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5285)
          (denoteGraph_ringAttn sm initSM 5280) (denoteGraph_ringAttn sm initSM 5282) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 437
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5285, 5280, 5282], outs := [5286, 5287], params := [16, 4] }
          5287 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5285 5280 5282 5286 5287 (by decide),
        ringAttn_prefix_read_pm sm initSM 437 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 437 5285 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 437 5280 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 437 5282 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 9481
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11864) (denoteGraph_ringAttn pm initPM 9477)
          (denoteGraph_ringAttn pm initPM 9445) (denoteGraph_ringAttn pm initPM 9457) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 935
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11864, 9477, 9445, 9457], outs := [9479, 9481], params := [16, 4] }
          9481 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11864 9477 9445 9457 9479 9481 (by decide),
        ringAttn_prefix_read_pm pm initPM 935 11864 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 935 9477 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 935 9445 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 935 9457 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 9482
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11864) (denoteGraph_ringAttn pm initPM 9478)
          (denoteGraph_ringAttn pm initPM 9446) (denoteGraph_ringAttn pm initPM 9458) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 936
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11864, 9478, 9446, 9458], outs := [9480, 9482], params := [16, 4] }
          9482 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11864 9478 9446 9458 9480 9482 (by decide),
        ringAttn_prefix_read_pm pm initPM 936 11864 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 936 9478 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 936 9446 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 936 9458 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5287
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9481, denoteGraph_ringAttn pm initPM 9482] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5285) (denoteGraph_ringAttn pm initPM 9457)
          (denoteGraph_ringAttn pm initPM 9458) 2048 4 64 (by omega) (by omega) (by omega)
          hsp5285 hs9457 hs9458,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 9477
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5285) from c9477),
        ← (show denoteGraph_ringAttn pm initPM 9478
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5285) from c9478),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9481).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs9457
  have hsp1 : (denoteGraph_ringAttn pm initPM 9482).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs9458
  have hshape : (denoteGraph_ringAttn sm initSM 5287).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5287 5287 9481 9482 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
