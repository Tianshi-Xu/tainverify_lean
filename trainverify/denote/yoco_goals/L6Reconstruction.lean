/- Worker #23 — Layer-6 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_4966_ringAttn` (the layer-6
   sliding-window attention output, unconditional-given-WF) through the layer-6
   forward block.

   Unlike L2, the L6 block has NO gather-to-full node (L2's PM node 228
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L6
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_4970` targets `[8379, 8380]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L5Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 4967 — 2-tp reshape of the L6 attention output `4966 : [4096,16,64]` to
    `[4096,1024]` (SM node 205, PM nodes 471/472). -/
theorem recon_intermediateGoal_4967_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4967
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs8367, hs8368⟩ := twoTp_gather _ _ intermediateGoal_4966 4966 8367 8368
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4966_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4967
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4966) :=
    ringAttn_reshape_reduce_pm sm initSM 205 0 4966 4967 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8369
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8367) :=
    ringAttn_reshape_reduce_pm pm initPM 471 0 8367 8369 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8370
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8368) :=
    ringAttn_reshape_reduce_pm pm initPM 472 1 8368 8370 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4967
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8369, denoteGraph_ringAttn pm initPM 8370] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs8367 hs8368
  have hs8369 : (denoteGraph_ringAttn pm initPM 8369).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8370 : (denoteGraph_ringAttn pm initPM 8370).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4967 : (denoteGraph_ringAttn sm initSM 4967).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4967 4967 8369 8370 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4967 hs8369 hs8370

/-- 4968 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 206, PM
    nodes 473/474). -/
theorem recon_intermediateGoal_4968_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4968
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs8369, hs8370⟩ := twoTp_gather _ _ intermediateGoal_4967 4967 8369 8370
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4967_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4967 : (denoteGraph_ringAttn sm initSM 4967).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8369])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4968
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4967) :=
    ringAttn_reshape_reduce_pm sm initSM 206 0 4967 4968 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8375
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8369) :=
    ringAttn_reshape_reduce_pm pm initPM 473 0 8369 8375 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8376
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8370) :=
    ringAttn_reshape_reduce_pm pm initPM 474 1 8370 8376 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8375 = denoteGraph_ringAttn pm initPM 8369 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8369]
  have h18 : denoteGraph_ringAttn pm initPM 8376 = denoteGraph_ringAttn pm initPM 8370 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8370]
  have hval : denoteGraph_ringAttn sm initSM 4968
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8375, denoteGraph_ringAttn pm initPM 8376] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4967, hval05, hnr, ← h17, ← h18]
  have hs8375 : (denoteGraph_ringAttn pm initPM 8375).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8376 : (denoteGraph_ringAttn pm initPM 8376).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4968 : (denoteGraph_ringAttn sm initSM 4968).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4968 4968 8375 8376 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4968 hs8375 hs8376

/-- 4970 — 2-tp down-projection `fw_linear(4968, 4969)` (weight `4969 : [1024,1024]`,
    SM node 207, PM nodes 475/476). -/
theorem recon_intermediateGoal_4970_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4970
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs8375, hs8376⟩ := twoTp_gather _ _ intermediateGoal_4968 4968 8375 8376
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4968_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4969 : denoteGraph_ringAttn sm initSM 4969 = denoteGraph_ringAttn pm initPM 4969 :=
    veq_weight_ring initSM initPM hInit initGoal_4969 (by native_decide) 4969
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4969 : (denoteGraph_ringAttn sm initSM 4969).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4969 (by native_decide) 4969 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw4969 : (denoteGraph_ringAttn pm initPM 4969).shape = [1024, 1024] := by
    rw [← hw4969]; exact hsw4969
  have rSM : denoteGraph_ringAttn sm initSM 4970
      = fw_linear (denoteGraph_ringAttn sm initSM 4968) (denoteGraph_ringAttn sm initSM 4969) :=
    ringAttn_reduce2_pm_opaque sm initSM 207
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4968, 4969], outs := [4970] }
      4968 4969 4970 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4968 4969 4970)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8379
      = fw_linear (denoteGraph_ringAttn pm initPM 8375) (denoteGraph_ringAttn pm initPM 4969) :=
    ringAttn_reduce2_pm_opaque pm initPM 475
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8375, 4969], outs := [8379] }
      8375 4969 8379 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8375 4969 8379)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8380
      = fw_linear (denoteGraph_ringAttn pm initPM 8376) (denoteGraph_ringAttn pm initPM 4969) :=
    ringAttn_reduce2_pm_opaque pm initPM 476
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8376, 4969], outs := [8380] }
      8376 4969 8380 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8376 4969 8380)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4970
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8379, denoteGraph_ringAttn pm initPM 8380] := by
    rw [rSM, hval06, hw4969, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs8375 hs8376 hpw4969,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8379).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8375 hpw4969
  have hsp1 : (denoteGraph_ringAttn pm initPM 8380).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8376 hpw4969
  have hshape : (denoteGraph_ringAttn sm initSM 4970).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4970 4970 8379 8380 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4971 — 2-tp identity view of `4970` (SM node 208, PM nodes 477/478). -/
theorem recon_intermediateGoal_4971_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4971
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs8379, hs8380⟩ := twoTp_gather _ _ intermediateGoal_4970 4970 8379 8380
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4970_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4970 : (denoteGraph_ringAttn sm initSM 4970).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8379])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4971
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4970) :=
    ringAttn_reduce1_pm_opaque sm initSM 208
      { rank := 0, op := "OpName.FW_view", ins := [4970], outs := [4971], params := [4096, 1024] }
      4970 4971 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4970 4971)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8389
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8379) :=
    ringAttn_reduce1_pm_opaque pm initPM 477
      { rank := 0, op := "OpName.FW_view", ins := [8379], outs := [8389], params := [2048, 1024] }
      8379 8389 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8379 8389)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8390
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8380) :=
    ringAttn_reduce1_pm_opaque pm initPM 478
      { rank := 1, op := "OpName.FW_view", ins := [8380], outs := [8390], params := [2048, 1024] }
      8380 8390 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8380 8390)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 8389 = denoteGraph_ringAttn pm initPM 8379 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8379]
  have h32 : denoteGraph_ringAttn pm initPM 8390 = denoteGraph_ringAttn pm initPM 8380 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8380]
  have hval : denoteGraph_ringAttn sm initSM 4971
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8389, denoteGraph_ringAttn pm initPM 8390] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4970, hval08, hnr, ← h31, ← h32]
  have hs8389 : (denoteGraph_ringAttn pm initPM 8389).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8390 : (denoteGraph_ringAttn pm initPM 8390).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4971 : (denoteGraph_ringAttn sm initSM 4971).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4971 4971 8389 8390 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4971 hs8389 hs8390

/-- 4972 — 2-tp `FW_float(4971)` (identity, SM node 209, PM nodes 479/480). -/
theorem recon_intermediateGoal_4972_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4972
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs8389, hs8390⟩ := twoTp_gather _ _ intermediateGoal_4971 4971 8389 8390
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4971_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4972 = id (denoteGraph_ringAttn sm initSM 4971) :=
    ringAttn_reduce1_pm_opaque sm initSM 209
      { rank := 0, op := "OpName.FW_float", ins := [4971], outs := [4972] }
      4971 4972 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4971 4972 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8393 = id (denoteGraph_ringAttn pm initPM 8389) :=
    ringAttn_reduce1_pm_opaque pm initPM 479
      { rank := 0, op := "OpName.FW_float", ins := [8389], outs := [8393] }
      8389 8393 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8389 8393 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8394 = id (denoteGraph_ringAttn pm initPM 8390) :=
    ringAttn_reduce1_pm_opaque pm initPM 480
      { rank := 1, op := "OpName.FW_float", ins := [8390], outs := [8394] }
      8390 8394 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8390 8394 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 4972
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8393, denoteGraph_ringAttn pm initPM 8394] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8393).shape = [2048, 1024] := by rw [rP0]; exact hs8389
  have hsp1 : (denoteGraph_ringAttn pm initPM 8394).shape = [2048, 1024] := by rw [rP1]; exact hs8390
  have hshape : (denoteGraph_ringAttn sm initSM 4972).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4972 4972 8393 8394 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7647 — 2-tp `mref2`-second copy of the L2 residual `4952` (SM node 197,
    PM nodes 455/456), carried into the L6 residual add. -/
theorem recon_intermediateGoal_7647_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7647
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs8323, hs8324⟩ := twoTp_gather _ _ intermediateGoal_4952 4952 8323 8324
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4952_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7647 : denoteGraph_ringAttn sm initSM 7647 = id (denoteGraph_ringAttn sm initSM 4952) :=
    ringAttn_reduce1_pm_opaque sm initSM 197
      { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647], params := [2] }
      4952 7647 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4952 7643 7647 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15017 : denoteGraph_ringAttn pm initPM 15017 = id (denoteGraph_ringAttn pm initPM 8323) :=
    ringAttn_reduce1_pm_opaque pm initPM 455
      { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017], params := [2] }
      8323 15017 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8323 15013 15017 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15025 : denoteGraph_ringAttn pm initPM 15025 = id (denoteGraph_ringAttn pm initPM 8324) :=
    ringAttn_reduce1_pm_opaque pm initPM 456
      { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025], params := [2] }
      8324 15025 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8324 15021 15025 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7647 p15017 p15025
  have hsp0 : (denoteGraph_ringAttn pm initPM 15017).shape = [2048, 1024] := by
    rw [p15017]; exact hs8323
  have hsp1 : (denoteGraph_ringAttn pm initPM 15025).shape = [2048, 1024] := by
    rw [p15025]; exact hs8324
  have hval : denoteGraph_ringAttn sm initSM 7647
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15017, denoteGraph_ringAttn pm initPM 15025] := by
    rw [s7647, hbr90, ← p15017, ← p15025]
  have hshape : (denoteGraph_ringAttn sm initSM 7647).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7647 7647 15017 15025 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4973 — 2-tp L6 residual add `7647 + 4972` (SM node 210, PM nodes 481/482). -/
theorem recon_intermediateGoal_4973_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4973
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs15017, hs15025⟩ := twoTp_gather _ _ intermediateGoal_7647 7647 15017 15025
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7647_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs8393, hs8394⟩ := twoTp_gather _ _ intermediateGoal_4972 4972 8393 8394
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4972_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4973
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7647) (denoteGraph_ringAttn sm initSM 4972) :=
    ringAttn_reduce2_pm_opaque sm initSM 210
      { rank := 0, op := "OpName.FW_add", ins := [7647, 4972], outs := [4973] }
      7647 4972 4973 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7647 4972 4973)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8397
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15017) (denoteGraph_ringAttn pm initPM 8393) :=
    ringAttn_reduce2_pm_opaque pm initPM 481
      { rank := 0, op := "OpName.FW_add", ins := [15017, 8393], outs := [8397] }
      15017 8393 8397 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15017 8393 8397)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8398
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15025) (denoteGraph_ringAttn pm initPM 8394) :=
    ringAttn_reduce2_pm_opaque pm initPM 482
      { rank := 1, op := "OpName.FW_add", ins := [15025, 8394], outs := [8398] }
      15025 8394 8398 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15025 8394 8398)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4973
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8397, denoteGraph_ringAttn pm initPM 8398] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15017 hs15025 hs8393 hs8394,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8397).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15017 hs8393
  have hsp1 : (denoteGraph_ringAttn pm initPM 8398).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15025 hs8394
  have hshape : (denoteGraph_ringAttn sm initSM 4973).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4973 4973 8397 8398 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4975 — 2-tp RMSNorm of `mref2-first(4973)` with replicated weight
    `4974 : [1024]` (SM node 212, PM nodes 485/486). -/
theorem recon_intermediateGoal_4975_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4975
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8397, hs8398⟩ := twoTp_gather _ _ intermediateGoal_4973 4973 8397 8398
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4973_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7664 : denoteGraph_ringAttn sm initSM 7664 = id (denoteGraph_ringAttn sm initSM 4973) :=
    ringAttn_reduce1_pm_opaque sm initSM 211
      { rank := 0, op := "OpName.FW_multiref", ins := [4973], outs := [7664, 7668], params := [2] }
      4973 7664 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4973 7664 7668)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15055 : denoteGraph_ringAttn pm initPM 15055 = id (denoteGraph_ringAttn pm initPM 8397) :=
    ringAttn_reduce1_pm_opaque pm initPM 483
      { rank := 0, op := "OpName.FW_multiref", ins := [8397], outs := [15055, 15059], params := [2] }
      8397 15055 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8397 15055 15059)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15063 : denoteGraph_ringAttn pm initPM 15063 = id (denoteGraph_ringAttn pm initPM 8398) :=
    ringAttn_reduce1_pm_opaque pm initPM 484
      { rank := 1, op := "OpName.FW_multiref", ins := [8398], outs := [15063, 15067], params := [2] }
      8398 15063 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8398 15063 15067)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7664 p15055 p15063
  have hs15055 : (denoteGraph_ringAttn pm initPM 15055).shape = [2048, 1024] := by
    rw [p15055]; exact hs8397
  have hs15063 : (denoteGraph_ringAttn pm initPM 15063).shape = [2048, 1024] := by
    rw [p15063]; exact hs8398
  have hbr08 : denoteGraph_ringAttn sm initSM 7664
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15055, denoteGraph_ringAttn pm initPM 15063] := by
    rw [s7664, hbr11, ← p15055, ← p15063]
  have hw4974 : denoteGraph_ringAttn sm initSM 4974 = denoteGraph_ringAttn pm initPM 4974 :=
    veq_weight_ring initSM initPM hInit initGoal_4974 (by native_decide) 4974
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4975
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7664) (denoteGraph_ringAttn sm initSM 4974) :=
    ringAttn_reduce2_pm_opaque sm initSM 212
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7664, 4974], outs := [4975] }
      7664 4974 4975 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7664 4974 4975)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8401
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15055) (denoteGraph_ringAttn pm initPM 4974) :=
    ringAttn_reduce2_pm_opaque pm initPM 485
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15055, 4974], outs := [8401] }
      15055 4974 8401 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15055 4974 8401)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8402
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15063) (denoteGraph_ringAttn pm initPM 4974) :=
    ringAttn_reduce2_pm_opaque pm initPM 486
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15063, 4974], outs := [8402] }
      15063 4974 8402 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15063 4974 8402)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4975
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8401, denoteGraph_ringAttn pm initPM 8402] := by
    rw [rSM, hbr08, hw4974, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15055 hs15063,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8401).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15055
  have hsp1 : (denoteGraph_ringAttn pm initPM 8402).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15063
  have hshape : (denoteGraph_ringAttn sm initSM 4975).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4975 4975 8401 8402 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4976 — 2-tp `FW_float(mref5-first(4975))` (identity, SM node 214,
    PM nodes 489/493; mref5-first via SM node 213, PM 487/488). -/
theorem recon_intermediateGoal_4976_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4976
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8401, hs8402⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7675 : denoteGraph_ringAttn sm initSM 7675 = id (denoteGraph_ringAttn sm initSM 4975) :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975],
        outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7675 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 4975 7675 [7679, 7683, 7687, 7691])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15074 : denoteGraph_ringAttn pm initPM 15074 = id (denoteGraph_ringAttn pm initPM 8401) :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401],
        outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15074 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 8401 15074 [15078, 15082, 15086, 15090])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15097 : denoteGraph_ringAttn pm initPM 15097 = id (denoteGraph_ringAttn pm initPM 8402) :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402],
        outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15097 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 8402 15097 [15101, 15105, 15109, 15113])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7675 p15074 p15097
  have hbrm : denoteGraph_ringAttn sm initSM 7675
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15074, denoteGraph_ringAttn pm initPM 15097] := by
    rw [s7675, hbr13, ← p15074, ← p15097]
  have rSM : denoteGraph_ringAttn sm initSM 4976 = id (denoteGraph_ringAttn sm initSM 7675) :=
    ringAttn_reduce1_pm_opaque sm initSM 214
      { rank := 0, op := "OpName.FW_float", ins := [7675], outs := [4976] }
      7675 4976 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7675 4976 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8403 = id (denoteGraph_ringAttn pm initPM 15074) :=
    ringAttn_reduce1_pm_opaque pm initPM 489
      { rank := 0, op := "OpName.FW_float", ins := [15074], outs := [8403] }
      15074 8403 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 15074 8403 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8404 = id (denoteGraph_ringAttn pm initPM 15097) :=
    ringAttn_reduce1_pm_opaque pm initPM 493
      { rank := 1, op := "OpName.FW_float", ins := [15097], outs := [8404] }
      15097 8404 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 15097 8404 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs15074 : (denoteGraph_ringAttn pm initPM 15074).shape = [2048, 1024] := by
    rw [p15074]; exact hs8401
  have hs15097 : (denoteGraph_ringAttn pm initPM 15097).shape = [2048, 1024] := by
    rw [p15097]; exact hs8402
  have hval : denoteGraph_ringAttn sm initSM 4976
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8403, denoteGraph_ringAttn pm initPM 8404] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8403).shape = [2048, 1024] := by
    rw [rP0]; exact hs15074
  have hsp1 : (denoteGraph_ringAttn pm initPM 8404).shape = [2048, 1024] := by
    rw [rP1]; exact hs15097
  have hshape : (denoteGraph_ringAttn sm initSM 4976).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4976 4976 8403 8404 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4978 — 2-tp router logits `fw_norm_linear(4976, 4977)` with weight
    `4977 : [64, 1024]` → `[4096, 64]` (SM node 218, PM nodes 497/501). -/
theorem recon_intermediateGoal_4978_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4978
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs8403, hs8404⟩ := twoTp_gather _ _ intermediateGoal_4976 4976 8403 8404
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4976_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4977 : denoteGraph_ringAttn sm initSM 4977 = denoteGraph_ringAttn pm initPM 4977 :=
    veq_weight_ring initSM initPM hInit initGoal_4977 (by native_decide) 4977
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4977 : (denoteGraph_ringAttn sm initSM 4977).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4977 (by native_decide) 4977 [64, 1024]
      rfl rfl (by native_decide)
  have hpw4977 : (denoteGraph_ringAttn pm initPM 4977).shape = [64, 1024] := by
    rw [← hw4977]; exact hsw4977
  have rSM : denoteGraph_ringAttn sm initSM 4978
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 4976) (denoteGraph_ringAttn sm initSM 4977) :=
    ringAttn_reduce2_pm_opaque sm initSM 218
      { rank := 0, op := "OpName.FW_norm_linear", ins := [4976, 4977], outs := [4978] }
      4976 4977 4978 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 4976 4977 4978)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8409
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8403) (denoteGraph_ringAttn pm initPM 4977) :=
    ringAttn_reduce2_pm_opaque pm initPM 497
      { rank := 0, op := "OpName.FW_norm_linear", ins := [8403, 4977], outs := [8409] }
      8403 4977 8409 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 8403 4977 8409)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8410
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8404) (denoteGraph_ringAttn pm initPM 4977) :=
    ringAttn_reduce2_pm_opaque pm initPM 501
      { rank := 1, op := "OpName.FW_norm_linear", ins := [8404, 4977], outs := [8410] }
      8404 4977 8410 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 8404 4977 8410)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4978
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8409, denoteGraph_ringAttn pm initPM 8410] := by
    rw [rSM, hval14, hw4977, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs8403 hs8404 hpw4977,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8409).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8403 hpw4977
  have hsp1 : (denoteGraph_ringAttn pm initPM 8410).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8404 hpw4977
  have hshape : (denoteGraph_ringAttn sm initSM 4978).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4978 4978 8409 8410 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L6 top-k routing (`4979`/`4980`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`8409`/`8410`) directly. -/

/-- Shared L6 top-k core: `4978` (full logits) is the dim-0 gather of the two
    per-rank shards `8409`/`8410`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L6 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 4978
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 8409, denoteGraph_ringAttn pm initPM 8410]
      ∧ (denoteGraph_ringAttn sm initSM 4978).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8409).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8410).shape = [2048, 64]
      ∧ ((sm.nodes.take 222).foldl (applyNodeRingAttn sm) initSM 4978).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 505).foldl (applyNodeRingAttn pm) initPM 8409).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 509).foldl (applyNodeRingAttn pm) initPM 8410).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs8409, hs8410⟩ := twoTp_gather _ _ intermediateGoal_4978 4978 8409 8410
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4978_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs4978sm : (denoteGraph_ringAttn sm initSM 4978).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs8409])]
    simp [List.set, List.getD]
  have hpre4978sm : denoteGraph_ringAttn sm initSM 4978
      = (sm.nodes.take 222).foldl (applyNodeRingAttn sm) initSM 4978 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 4978 222 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 222).foldl (applyNodeRingAttn sm) initSM 4978).shape.reverse.head? = some 64 := by
    rw [← hpre4978sm, hs4978sm]; rfl
  have hpre8409 : denoteGraph_ringAttn pm initPM 8409
      = (pm.nodes.take 505).foldl (applyNodeRingAttn pm) initPM 8409 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8409 505 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 505).foldl (applyNodeRingAttn pm) initPM 8409).shape.reverse.head? = some 64 := by
    rw [← hpre8409, hs8409]; rfl
  have hpre8410 : denoteGraph_ringAttn pm initPM 8410
      = (pm.nodes.take 509).foldl (applyNodeRingAttn pm) initPM 8410 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8410 509 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 509).foldl (applyNodeRingAttn pm) initPM 8410).shape.reverse.head? = some 64 := by
    rw [← hpre8410, hs8410]; rfl
  exact ⟨hbr16, hs4978sm, hs8409, hs8410, hlastSM, hlast271, hlast275⟩

/-- 4979 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4979_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4979
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4978sm, hs8409, hs8410, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L6 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4979
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4978) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 222
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4978], outs := [4979, 4980, 4981], params := [8, 1] }
      4978 4979 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 222).foldl (applyNodeRingAttn sm) initSM) 0 4978 4979 4980 4981 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8411
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8409) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 505
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8409], outs := [8411, 8413, 8415], params := [8, 1] }
      8409 8411 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 505).foldl (applyNodeRingAttn pm) initPM) 0 8409 8411 8413 8415 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8412
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8410) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 509
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8410], outs := [8412, 8414, 8416], params := [8, 1] }
      8410 8412 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 509).foldl (applyNodeRingAttn pm) initPM) 1 8410 8412 8414 8416 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4979
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8411, denoteGraph_ringAttn pm initPM 8412] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8409 hs8410,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4979).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs4978sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8411).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8409]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8412).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8410]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4979 4979 8411 8412 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4980 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4980_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4980
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4978sm, hs8409, hs8410, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L6 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4980
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4978) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 222
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4978], outs := [4979, 4980, 4981], params := [8, 1] }
      4978 4980 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 222).foldl (applyNodeRingAttn sm) initSM) 0 4978 4979 4980 4981 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8413
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8409) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 505
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8409], outs := [8411, 8413, 8415], params := [8, 1] }
      8409 8413 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 505).foldl (applyNodeRingAttn pm) initPM) 0 8409 8411 8413 8415 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8414
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8410) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 509
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8410], outs := [8412, 8414, 8416], params := [8, 1] }
      8410 8414 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 509).foldl (applyNodeRingAttn pm) initPM) 1 8410 8412 8414 8416 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4980
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8413, denoteGraph_ringAttn pm initPM 8414] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8409 hs8410,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4980).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs4978sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8413).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8409]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8414).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8410]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4980 4980 8413 8414 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L6 router expert branches — reshape (`4985`/`4990`/`4994`) of the
    `mref5` copies (positions 2/3/4) of `4975`, all identity 2-tp views. -/

/-- 4985 — 2-tp identity reshape of `mref5-pos2(4975)` (SM node 215, PM 490/494). -/
theorem recon_intermediateGoal_4985_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4985
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8401, hs8402⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4975sm : (denoteGraph_ringAttn sm initSM 4975).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8401])]
    simp [List.set, List.getD]
  have s7683 : denoteGraph_ringAttn sm initSM 7683 = id (denoteGraph_ringAttn sm initSM 4975) :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975],
        outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7683 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15082 : denoteGraph_ringAttn pm initPM 15082 = id (denoteGraph_ringAttn pm initPM 8401) :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401],
        outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15082 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15105 : denoteGraph_ringAttn pm initPM 15105 = id (denoteGraph_ringAttn pm initPM 8402) :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402],
        outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15105 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7683 p15082 p15105
  have hs7683 : (denoteGraph_ringAttn sm initSM 7683).shape = [4096, 1024] := by rw [s7683]; exact hs4975sm
  have hs15082 : (denoteGraph_ringAttn pm initPM 15082).shape = [2048, 1024] := by rw [p15082]; exact hs8401
  have hs15105 : (denoteGraph_ringAttn pm initPM 15105).shape = [2048, 1024] := by rw [p15105]; exact hs8402
  have hbrm : denoteGraph_ringAttn sm initSM 7683
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15082, denoteGraph_ringAttn pm initPM 15105] := by
    rw [s7683, hbr13, ← p15082, ← p15105]
  have rSM : denoteGraph_ringAttn sm initSM 4985
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7683) :=
    ringAttn_reduce1_pm_opaque sm initSM 215
      { rank := 0, op := "OpName.FW_reshape", ins := [7683], outs := [4985], params := [4096, 1024] }
      7683 4985 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7683 4985)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8423
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15082) :=
    ringAttn_reduce1_pm_opaque pm initPM 490
      { rank := 0, op := "OpName.FW_reshape", ins := [15082], outs := [8423], params := [2048, 1024] }
      15082 8423 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15082 8423)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8424
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15105) :=
    ringAttn_reduce1_pm_opaque pm initPM 494
      { rank := 1, op := "OpName.FW_reshape", ins := [15105], outs := [8424], params := [2048, 1024] }
      15105 8424 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15105 8424)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 8423 = denoteGraph_ringAttn pm initPM 15082 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15082]
  have h66 : denoteGraph_ringAttn pm initPM 8424 = denoteGraph_ringAttn pm initPM 15105 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15105]
  have hval : denoteGraph_ringAttn sm initSM 4985
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8423, denoteGraph_ringAttn pm initPM 8424] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7683, hbrm, hnr, ← h65, ← h66]
  have hs8423 : (denoteGraph_ringAttn pm initPM 8423).shape = [2048, 1024] := by rw [h65]; exact hs15082
  have hs8424 : (denoteGraph_ringAttn pm initPM 8424).shape = [2048, 1024] := by rw [h66]; exact hs15105
  have hs4985 : (denoteGraph_ringAttn sm initSM 4985).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7683]; exact hs7683
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4985 4985 8423 8424 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4985 hs8423 hs8424

/-- 4990 — 2-tp identity reshape of `mref5-pos3(4975)` (SM node 216, PM 491/495). -/
theorem recon_intermediateGoal_4990_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4990
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8401, hs8402⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4975sm : (denoteGraph_ringAttn sm initSM 4975).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8401])]
    simp [List.set, List.getD]
  have s7687 : denoteGraph_ringAttn sm initSM 7687 = id (denoteGraph_ringAttn sm initSM 4975) :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975],
        outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7687 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15086 : denoteGraph_ringAttn pm initPM 15086 = id (denoteGraph_ringAttn pm initPM 8401) :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401],
        outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15086 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15109 : denoteGraph_ringAttn pm initPM 15109 = id (denoteGraph_ringAttn pm initPM 8402) :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402],
        outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15109 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7687 p15086 p15109
  have hs7687 : (denoteGraph_ringAttn sm initSM 7687).shape = [4096, 1024] := by rw [s7687]; exact hs4975sm
  have hs15086 : (denoteGraph_ringAttn pm initPM 15086).shape = [2048, 1024] := by rw [p15086]; exact hs8401
  have hs15109 : (denoteGraph_ringAttn pm initPM 15109).shape = [2048, 1024] := by rw [p15109]; exact hs8402
  have hbrm : denoteGraph_ringAttn sm initSM 7687
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15086, denoteGraph_ringAttn pm initPM 15109] := by
    rw [s7687, hbr13, ← p15086, ← p15109]
  have rSM : denoteGraph_ringAttn sm initSM 4990
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7687) :=
    ringAttn_reduce1_pm_opaque sm initSM 216
      { rank := 0, op := "OpName.FW_reshape", ins := [7687], outs := [4990], params := [4096, 1024] }
      7687 4990 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7687 4990)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8437
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15086) :=
    ringAttn_reduce1_pm_opaque pm initPM 491
      { rank := 0, op := "OpName.FW_reshape", ins := [15086], outs := [8437], params := [2048, 1024] }
      15086 8437 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15086 8437)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8438
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15109) :=
    ringAttn_reduce1_pm_opaque pm initPM 495
      { rank := 1, op := "OpName.FW_reshape", ins := [15109], outs := [8438], params := [2048, 1024] }
      15109 8438 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15109 8438)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 8437 = denoteGraph_ringAttn pm initPM 15086 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15086]
  have h80 : denoteGraph_ringAttn pm initPM 8438 = denoteGraph_ringAttn pm initPM 15109 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15109]
  have hval : denoteGraph_ringAttn sm initSM 4990
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8437, denoteGraph_ringAttn pm initPM 8438] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7687, hbrm, hnr, ← h79, ← h80]
  have hs8437 : (denoteGraph_ringAttn pm initPM 8437).shape = [2048, 1024] := by rw [h79]; exact hs15086
  have hs8438 : (denoteGraph_ringAttn pm initPM 8438).shape = [2048, 1024] := by rw [h80]; exact hs15109
  have hs4990 : (denoteGraph_ringAttn sm initSM 4990).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7687]; exact hs7687
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4990 4990 8437 8438 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4990 hs8437 hs8438

/-- 4994 — 2-tp identity reshape of `mref5-pos4(4975)` (SM node 217, PM 492/496). -/
theorem recon_intermediateGoal_4994_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4994
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8401, hs8402⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4975sm : (denoteGraph_ringAttn sm initSM 4975).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8401])]
    simp [List.set, List.getD]
  have s7691 : denoteGraph_ringAttn sm initSM 7691 = id (denoteGraph_ringAttn sm initSM 4975) :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975],
        outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7691 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15090 : denoteGraph_ringAttn pm initPM 15090 = id (denoteGraph_ringAttn pm initPM 8401) :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401],
        outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15090 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15113 : denoteGraph_ringAttn pm initPM 15113 = id (denoteGraph_ringAttn pm initPM 8402) :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402],
        outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15113 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7691 p15090 p15113
  have hs7691 : (denoteGraph_ringAttn sm initSM 7691).shape = [4096, 1024] := by rw [s7691]; exact hs4975sm
  have hs15090 : (denoteGraph_ringAttn pm initPM 15090).shape = [2048, 1024] := by rw [p15090]; exact hs8401
  have hs15113 : (denoteGraph_ringAttn pm initPM 15113).shape = [2048, 1024] := by rw [p15113]; exact hs8402
  have hbrm : denoteGraph_ringAttn sm initSM 7691
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15090, denoteGraph_ringAttn pm initPM 15113] := by
    rw [s7691, hbr13, ← p15090, ← p15113]
  have rSM : denoteGraph_ringAttn sm initSM 4994
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7691) :=
    ringAttn_reduce1_pm_opaque sm initSM 217
      { rank := 0, op := "OpName.FW_reshape", ins := [7691], outs := [4994], params := [4096, 1024] }
      7691 4994 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7691 4994)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8455
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15090) :=
    ringAttn_reduce1_pm_opaque pm initPM 492
      { rank := 0, op := "OpName.FW_reshape", ins := [15090], outs := [8455], params := [2048, 1024] }
      15090 8455 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15090 8455)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8456
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15113) :=
    ringAttn_reduce1_pm_opaque pm initPM 496
      { rank := 1, op := "OpName.FW_reshape", ins := [15113], outs := [8456], params := [2048, 1024] }
      15113 8456 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15113 8456)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 8455 = denoteGraph_ringAttn pm initPM 15090 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15090]
  have h98 : denoteGraph_ringAttn pm initPM 8456 = denoteGraph_ringAttn pm initPM 15113 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15113]
  have hval : denoteGraph_ringAttn sm initSM 4994
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8455, denoteGraph_ringAttn pm initPM 8456] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7691, hbrm, hnr, ← h97, ← h98]
  have hs8455 : (denoteGraph_ringAttn pm initPM 8455).shape = [2048, 1024] := by rw [h97]; exact hs15090
  have hs8456 : (denoteGraph_ringAttn pm initPM 8456).shape = [2048, 1024] := by rw [h98]; exact hs15113
  have hs4994 : (denoteGraph_ringAttn sm initSM 4994).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7691]; exact hs7691
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4994 4994 8455 8456 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4994 hs8455 hs8456

/-! ### L6 router expert mixlins (`4987`/`4992`/`4996`), 2-tp. -/

/-- 4987 — 2-tp `fw_linear(4985, 4986)`, weight `4986 : [1, 1024]` → `[4096, 1]`
    (SM node 219, PM nodes 498/502). -/
theorem recon_intermediateGoal_4987_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4987
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs8423, hs8424⟩ := twoTp_gather _ _ intermediateGoal_4985 4985 8423 8424
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4985_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4986 : denoteGraph_ringAttn sm initSM 4986 = denoteGraph_ringAttn pm initPM 4986 :=
    veq_weight_ring initSM initPM hInit initGoal_4986 (by native_decide) 4986
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4986 : (denoteGraph_ringAttn pm initPM 4986).shape = [1, 1024] := by
    rw [← hw4986]
    exact shape_weight_ring initSM initPM hInit initGoal_4986 (by native_decide) 4986 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4987
      = fw_linear (denoteGraph_ringAttn sm initSM 4985) (denoteGraph_ringAttn sm initSM 4986) :=
    ringAttn_reduce2_pm_opaque sm initSM 219
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4985, 4986], outs := [4987] }
      4985 4986 4987 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4985 4986 4987)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8427
      = fw_linear (denoteGraph_ringAttn pm initPM 8423) (denoteGraph_ringAttn pm initPM 4986) :=
    ringAttn_reduce2_pm_opaque pm initPM 498
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8423, 4986], outs := [8427] }
      8423 4986 8427 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8423 4986 8427)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8428
      = fw_linear (denoteGraph_ringAttn pm initPM 8424) (denoteGraph_ringAttn pm initPM 4986) :=
    ringAttn_reduce2_pm_opaque pm initPM 502
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8424, 4986], outs := [8428] }
      8424 4986 8428 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8424 4986 8428)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4987
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8427, denoteGraph_ringAttn pm initPM 8428] := by
    rw [rSM, hval23, hw4986, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs8423 hs8424 hpw4986,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8427).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8423 hpw4986
  have hsp1 : (denoteGraph_ringAttn pm initPM 8428).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8424 hpw4986
  have hshape : (denoteGraph_ringAttn sm initSM 4987).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4987 4987 8427 8428 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4992 — 2-tp `fw_linear(4990, 4991)`, weight `4991 : [512, 1024]` → `[4096, 512]`
    (SM node 220, PM nodes 499/503). -/
theorem recon_intermediateGoal_4992_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4992
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs8437, hs8438⟩ := twoTp_gather _ _ intermediateGoal_4990 4990 8437 8438
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4990_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4991 : denoteGraph_ringAttn sm initSM 4991 = denoteGraph_ringAttn pm initPM 4991 :=
    veq_weight_ring initSM initPM hInit initGoal_4991 (by native_decide) 4991
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4991 : (denoteGraph_ringAttn pm initPM 4991).shape = [512, 1024] := by
    rw [← hw4991]
    exact shape_weight_ring initSM initPM hInit initGoal_4991 (by native_decide) 4991 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4992
      = fw_linear (denoteGraph_ringAttn sm initSM 4990) (denoteGraph_ringAttn sm initSM 4991) :=
    ringAttn_reduce2_pm_opaque sm initSM 220
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4990, 4991], outs := [4992] }
      4990 4991 4992 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4990 4991 4992)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8441
      = fw_linear (denoteGraph_ringAttn pm initPM 8437) (denoteGraph_ringAttn pm initPM 4991) :=
    ringAttn_reduce2_pm_opaque pm initPM 499
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8437, 4991], outs := [8441] }
      8437 4991 8441 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8437 4991 8441)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8442
      = fw_linear (denoteGraph_ringAttn pm initPM 8438) (denoteGraph_ringAttn pm initPM 4991) :=
    ringAttn_reduce2_pm_opaque pm initPM 503
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8438, 4991], outs := [8442] }
      8438 4991 8442 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8438 4991 8442)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4992
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8441, denoteGraph_ringAttn pm initPM 8442] := by
    rw [rSM, hval28, hw4991, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8437 hs8438 hpw4991,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8441).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8437 hpw4991
  have hsp1 : (denoteGraph_ringAttn pm initPM 8442).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8438 hpw4991
  have hshape : (denoteGraph_ringAttn sm initSM 4992).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4992 4992 8441 8442 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4996 — 2-tp `fw_linear(4994, 4995)`, weight `4995 : [512, 1024]` → `[4096, 512]`
    (SM node 221, PM nodes 500/504). -/
theorem recon_intermediateGoal_4996_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4996
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs8455, hs8456⟩ := twoTp_gather _ _ intermediateGoal_4994 4994 8455 8456
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4994_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4995 : denoteGraph_ringAttn sm initSM 4995 = denoteGraph_ringAttn pm initPM 4995 :=
    veq_weight_ring initSM initPM hInit initGoal_4995 (by native_decide) 4995
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4995 : (denoteGraph_ringAttn pm initPM 4995).shape = [512, 1024] := by
    rw [← hw4995]
    exact shape_weight_ring initSM initPM hInit initGoal_4995 (by native_decide) 4995 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4996
      = fw_linear (denoteGraph_ringAttn sm initSM 4994) (denoteGraph_ringAttn sm initSM 4995) :=
    ringAttn_reduce2_pm_opaque sm initSM 221
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4994, 4995], outs := [4996] }
      4994 4995 4996 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4994 4995 4996)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8459
      = fw_linear (denoteGraph_ringAttn pm initPM 8455) (denoteGraph_ringAttn pm initPM 4995) :=
    ringAttn_reduce2_pm_opaque pm initPM 500
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8455, 4995], outs := [8459] }
      8455 4995 8459 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8455 4995 8459)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8460
      = fw_linear (denoteGraph_ringAttn pm initPM 8456) (denoteGraph_ringAttn pm initPM 4995) :=
    ringAttn_reduce2_pm_opaque pm initPM 504
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8456, 4995], outs := [8460] }
      8456 4995 8460 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8456 4995 8460)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4996
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8459, denoteGraph_ringAttn pm initPM 8460] := by
    rw [rSM, hval32, hw4995, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8455 hs8456 hpw4995,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8459).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8455 hpw4995
  have hsp1 : (denoteGraph_ringAttn pm initPM 8460).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8456 hpw4995
  have hshape : (denoteGraph_ringAttn sm initSM 4996).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4996 4996 8459 8460 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L6 router expert views (`4988`/`4993`/`4997`), identity 2-tp views. -/

/-- 4988 — 2-tp identity view of `4987` → `[4096, 1]` (SM node 223, PM 506/510). -/
theorem recon_intermediateGoal_4988_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4988
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs8427, hs8428⟩ := twoTp_gather _ _ intermediateGoal_4987 4987 8427 8428
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4987_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4987 : (denoteGraph_ringAttn sm initSM 4987).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8427])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4988
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 4987) :=
    ringAttn_reduce1_pm_opaque sm initSM 223
      { rank := 0, op := "OpName.FW_view", ins := [4987], outs := [4988], params := [4096, 1] }
      4987 4988 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 4987 4988)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8433
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8427) :=
    ringAttn_reduce1_pm_opaque pm initPM 506
      { rank := 0, op := "OpName.FW_view", ins := [8427], outs := [8433], params := [2048, 1] }
      8427 8433 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 8427 8433)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8434
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8428) :=
    ringAttn_reduce1_pm_opaque pm initPM 510
      { rank := 1, op := "OpName.FW_view", ins := [8428], outs := [8434], params := [2048, 1] }
      8428 8434 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 8428 8434)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 8433 = denoteGraph_ringAttn pm initPM 8427 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs8427]
  have h76 : denoteGraph_ringAttn pm initPM 8434 = denoteGraph_ringAttn pm initPM 8428 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs8428]
  have hval : denoteGraph_ringAttn sm initSM 4988
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8433, denoteGraph_ringAttn pm initPM 8434] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4987, hval25, hnr, ← h75, ← h76]
  have hs8433 : (denoteGraph_ringAttn pm initPM 8433).shape = [2048, 1] := by rw [h75]; exact hs8427
  have hs8434 : (denoteGraph_ringAttn pm initPM 8434).shape = [2048, 1] := by rw [h76]; exact hs8428
  have hs4988 : (denoteGraph_ringAttn sm initSM 4988).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4987]; exact hs4987
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4988 4988 8433 8434 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4988 hs8433 hs8434

/-- 4993 — 2-tp identity view of `4992` → `[4096, 512]` (SM node 224, PM 507/511). -/
theorem recon_intermediateGoal_4993_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4993
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs8441, hs8442⟩ := twoTp_gather _ _ intermediateGoal_4992 4992 8441 8442
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4992_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4992 : (denoteGraph_ringAttn sm initSM 4992).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8441])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4993
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4992) :=
    ringAttn_reduce1_pm_opaque sm initSM 224
      { rank := 0, op := "OpName.FW_view", ins := [4992], outs := [4993], params := [4096, 512] }
      4992 4993 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4992 4993)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8451
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8441) :=
    ringAttn_reduce1_pm_opaque pm initPM 507
      { rank := 0, op := "OpName.FW_view", ins := [8441], outs := [8451], params := [2048, 512] }
      8441 8451 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8441 8451)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8452
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8442) :=
    ringAttn_reduce1_pm_opaque pm initPM 511
      { rank := 1, op := "OpName.FW_view", ins := [8442], outs := [8452], params := [2048, 512] }
      8442 8452 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8442 8452)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 8451 = denoteGraph_ringAttn pm initPM 8441 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8441]
  have h94 : denoteGraph_ringAttn pm initPM 8452 = denoteGraph_ringAttn pm initPM 8442 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8442]
  have hval : denoteGraph_ringAttn sm initSM 4993
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8451, denoteGraph_ringAttn pm initPM 8452] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4992, hval30, hnr, ← h93, ← h94]
  have hs8451 : (denoteGraph_ringAttn pm initPM 8451).shape = [2048, 512] := by rw [h93]; exact hs8441
  have hs8452 : (denoteGraph_ringAttn pm initPM 8452).shape = [2048, 512] := by rw [h94]; exact hs8442
  have hs4993 : (denoteGraph_ringAttn sm initSM 4993).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4992]; exact hs4992
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4993 4993 8451 8452 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4993 hs8451 hs8452

/-- 4997 — 2-tp identity view of `4996` → `[4096, 512]` (SM node 225, PM 508/512). -/
theorem recon_intermediateGoal_4997_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4997
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs8459, hs8460⟩ := twoTp_gather _ _ intermediateGoal_4996 4996 8459 8460
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4996_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4996 : (denoteGraph_ringAttn sm initSM 4996).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8459])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4997
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4996) :=
    ringAttn_reduce1_pm_opaque sm initSM 225
      { rank := 0, op := "OpName.FW_view", ins := [4996], outs := [4997], params := [4096, 512] }
      4996 4997 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4996 4997)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8469
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8459) :=
    ringAttn_reduce1_pm_opaque pm initPM 508
      { rank := 0, op := "OpName.FW_view", ins := [8459], outs := [8469], params := [2048, 512] }
      8459 8469 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8459 8469)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8470
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8460) :=
    ringAttn_reduce1_pm_opaque pm initPM 512
      { rank := 1, op := "OpName.FW_view", ins := [8460], outs := [8470], params := [2048, 512] }
      8460 8470 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8460 8470)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 8469 = denoteGraph_ringAttn pm initPM 8459 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8459]
  have h12 : denoteGraph_ringAttn pm initPM 8470 = denoteGraph_ringAttn pm initPM 8460 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8460]
  have hval : denoteGraph_ringAttn sm initSM 4997
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8469, denoteGraph_ringAttn pm initPM 8470] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4996, hval34, hnr, ← h11, ← h12]
  have hs8469 : (denoteGraph_ringAttn pm initPM 8469).shape = [2048, 512] := by rw [h11]; exact hs8459
  have hs8470 : (denoteGraph_ringAttn pm initPM 8470).shape = [2048, 512] := by rw [h12]; exact hs8460
  have hs4997 : (denoteGraph_ringAttn sm initSM 4997).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4996]; exact hs4996
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4997 4997 8469 8470 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4997 hs8469 hs8470

/-! ### L6 MoE gate/expert branch (`4989` sigmoid, `4998` swiglu, `4999` reshape,
    `5001` mixlin, `5002` view, `5003` broadcast-mul), all 2-tp shard-direct. -/

/-- 4989 — 2-tp `fw_sigmoid(4988)` → `[4096, 1]` (SM node 227, PM 514/517). -/
theorem recon_intermediateGoal_4989_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4989
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs8433, hs8434⟩ := twoTp_gather _ _ intermediateGoal_4988 4988 8433 8434
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4988_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4989 = fw_sigmoid (denoteGraph_ringAttn sm initSM 4988) :=
    ringAttn_reduce1_pm_opaque sm initSM 227
      { rank := 0, op := "OpName.FW_sigmoid", ins := [4988], outs := [4989] }
      4988 4989 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 4988 4989 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8435 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8433) :=
    ringAttn_reduce1_pm_opaque pm initPM 514
      { rank := 0, op := "OpName.FW_sigmoid", ins := [8433], outs := [8435] }
      8433 8435 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 8433 8435 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8436 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8434) :=
    ringAttn_reduce1_pm_opaque pm initPM 517
      { rank := 1, op := "OpName.FW_sigmoid", ins := [8434], outs := [8436] }
      8434 8436 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 8434 8436 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4989
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8435, denoteGraph_ringAttn pm initPM 8436] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs8433 hs8434, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4989).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8433])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8435).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs8433
  have hsp1 : (denoteGraph_ringAttn pm initPM 8436).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs8434
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4989 4989 8435 8436 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4998 — 2-tp `fw_swiglu(4993, 4997)` → `[4096, 512]` (SM node 228, PM 515/518). -/
theorem recon_intermediateGoal_4998_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4998
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs8451, hs8452⟩ := twoTp_gather _ _ intermediateGoal_4993 4993 8451 8452
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4993_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs8469, hs8470⟩ := twoTp_gather _ _ intermediateGoal_4997 4997 8469 8470
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4997_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4998
      = fw_swiglu (denoteGraph_ringAttn sm initSM 4993) (denoteGraph_ringAttn sm initSM 4997) :=
    ringAttn_reduce2_pm_opaque sm initSM 228
      { rank := 0, op := "OpName.FW_swiglu", ins := [4993, 4997], outs := [4998] }
      4993 4997 4998 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 4993 4997 4998 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8473
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8451) (denoteGraph_ringAttn pm initPM 8469) :=
    ringAttn_reduce2_pm_opaque pm initPM 515
      { rank := 0, op := "OpName.FW_swiglu", ins := [8451, 8469], outs := [8473] }
      8451 8469 8473 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 8451 8469 8473 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8474
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8452) (denoteGraph_ringAttn pm initPM 8470) :=
    ringAttn_reduce2_pm_opaque pm initPM 518
      { rank := 1, op := "OpName.FW_swiglu", ins := [8452, 8470], outs := [8474] }
      8452 8470 8474 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 8452 8470 8474 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4998
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8473, denoteGraph_ringAttn pm initPM 8474] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs8451 hs8452 hs8469 hs8470,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4998).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8469])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8473).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8469
  have hsp1 : (denoteGraph_ringAttn pm initPM 8474).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8470
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4998 4998 8473 8474 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4999 — 2-tp identity reshape of `4998` → `[4096, 512]` (SM node 229, PM 519/520). -/
theorem recon_intermediateGoal_4999_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4999
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs8473, hs8474⟩ := twoTp_gather _ _ intermediateGoal_4998 4998 8473 8474
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4998_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4998 : (denoteGraph_ringAttn sm initSM 4998).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8473])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4999
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4998) :=
    ringAttn_reduce1_pm_opaque sm initSM 229
      { rank := 0, op := "OpName.FW_reshape", ins := [4998], outs := [4999], params := [4096, 512] }
      4998 4999 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4998 4999)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8475
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8473) :=
    ringAttn_reduce1_pm_opaque pm initPM 519
      { rank := 0, op := "OpName.FW_reshape", ins := [8473], outs := [8475], params := [2048, 512] }
      8473 8475 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8473 8475)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8476
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8474) :=
    ringAttn_reduce1_pm_opaque pm initPM 520
      { rank := 1, op := "OpName.FW_reshape", ins := [8474], outs := [8476], params := [2048, 512] }
      8474 8476 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8474 8476)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8475 = denoteGraph_ringAttn pm initPM 8473 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8473]
  have h18 : denoteGraph_ringAttn pm initPM 8476 = denoteGraph_ringAttn pm initPM 8474 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8474]
  have hval : denoteGraph_ringAttn sm initSM 4999
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8475, denoteGraph_ringAttn pm initPM 8476] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4998, hval36, hnr, ← h17, ← h18]
  have hs8475 : (denoteGraph_ringAttn pm initPM 8475).shape = [2048, 512] := by rw [h17]; exact hs8473
  have hs8476 : (denoteGraph_ringAttn pm initPM 8476).shape = [2048, 512] := by rw [h18]; exact hs8474
  have hs4999 : (denoteGraph_ringAttn sm initSM 4999).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4998]; exact hs4998
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4999 4999 8475 8476 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4999 hs8475 hs8476

/-- 5001 — 2-tp `fw_linear(4999, 5000)`, weight `5000 : [1024, 512]` → `[4096, 1024]`
    (SM node 230, PM 521/522). -/
theorem recon_intermediateGoal_5001_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5001
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs8475, hs8476⟩ := twoTp_gather _ _ intermediateGoal_4999 4999 8475 8476
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4999_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5000 : denoteGraph_ringAttn sm initSM 5000 = denoteGraph_ringAttn pm initPM 5000 :=
    veq_weight_ring initSM initPM hInit initGoal_5000 (by native_decide) 5000
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5000 : (denoteGraph_ringAttn pm initPM 5000).shape = [1024, 512] := by
    rw [← hw5000]
    exact shape_weight_ring initSM initPM hInit initGoal_5000 (by native_decide) 5000 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5001
      = fw_linear (denoteGraph_ringAttn sm initSM 4999) (denoteGraph_ringAttn sm initSM 5000) :=
    ringAttn_reduce2_pm_opaque sm initSM 230
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4999, 5000], outs := [5001] }
      4999 5000 5001 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4999 5000 5001)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8481
      = fw_linear (denoteGraph_ringAttn pm initPM 8475) (denoteGraph_ringAttn pm initPM 5000) :=
    ringAttn_reduce2_pm_opaque pm initPM 521
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8475, 5000], outs := [8481] }
      8475 5000 8481 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8475 5000 8481)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8482
      = fw_linear (denoteGraph_ringAttn pm initPM 8476) (denoteGraph_ringAttn pm initPM 5000) :=
    ringAttn_reduce2_pm_opaque pm initPM 522
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8476, 5000], outs := [8482] }
      8476 5000 8482 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8476 5000 8482)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5001
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8481, denoteGraph_ringAttn pm initPM 8482] := by
    rw [rSM, hval37, hw5000, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs8475 hs8476 hpw5000,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8481).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8475 hpw5000
  have hsp1 : (denoteGraph_ringAttn pm initPM 8482).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8476 hpw5000
  have hshape : (denoteGraph_ringAttn sm initSM 5001).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5001 5001 8481 8482 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5002 — 2-tp identity view of `5001` → `[4096, 1024]` (SM node 231, PM 523/524). -/
theorem recon_intermediateGoal_5002_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5002
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs8481, hs8482⟩ := twoTp_gather _ _ intermediateGoal_5001 5001 8481 8482
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5001_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5001 : (denoteGraph_ringAttn sm initSM 5001).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8481])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5002
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5001) :=
    ringAttn_reduce1_pm_opaque sm initSM 231
      { rank := 0, op := "OpName.FW_view", ins := [5001], outs := [5002], params := [4096, 1024] }
      5001 5002 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5001 5002)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8491
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8481) :=
    ringAttn_reduce1_pm_opaque pm initPM 523
      { rank := 0, op := "OpName.FW_view", ins := [8481], outs := [8491], params := [2048, 1024] }
      8481 8491 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8481 8491)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8492
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8482) :=
    ringAttn_reduce1_pm_opaque pm initPM 524
      { rank := 1, op := "OpName.FW_view", ins := [8482], outs := [8492], params := [2048, 1024] }
      8482 8492 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8482 8492)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 8491 = denoteGraph_ringAttn pm initPM 8481 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8481]
  have h34 : denoteGraph_ringAttn pm initPM 8492 = denoteGraph_ringAttn pm initPM 8482 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8482]
  have hval : denoteGraph_ringAttn sm initSM 5002
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8491, denoteGraph_ringAttn pm initPM 8492] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5001, hval39, hnr, ← h33, ← h34]
  have hs8491 : (denoteGraph_ringAttn pm initPM 8491).shape = [2048, 1024] := by rw [h33]; exact hs8481
  have hs8492 : (denoteGraph_ringAttn pm initPM 8492).shape = [2048, 1024] := by rw [h34]; exact hs8482
  have hs5002 : (denoteGraph_ringAttn sm initSM 5002).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5001]; exact hs5001
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5002 5002 8491 8492 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5002 hs8491 hs8492

/-- 5003 — 2-tp broadcast `mul(4989, 5002)` → `[4096, 1024]` (SM node 232, PM 525/526). -/
theorem recon_intermediateGoal_5003_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5003
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_4989 4989 8435 8436
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4989_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_5002 5002 8491 8492
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5002_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5003
      = elemwiseMul (denoteGraph_ringAttn sm initSM 4989) (denoteGraph_ringAttn sm initSM 5002) :=
    ringAttn_reduce2_pm_opaque sm initSM 232
      { rank := 0, op := "OpName.FW_mul", ins := [4989, 5002], outs := [5003] }
      4989 5002 5003 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 4989 5002 5003)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8495
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8435) (denoteGraph_ringAttn pm initPM 8491) :=
    ringAttn_reduce2_pm_opaque pm initPM 525
      { rank := 0, op := "OpName.FW_mul", ins := [8435, 8491], outs := [8495] }
      8435 8491 8495 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 8435 8491 8495)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8496
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8436) (denoteGraph_ringAttn pm initPM 8492) :=
    ringAttn_reduce2_pm_opaque pm initPM 526
      { rank := 1, op := "OpName.FW_mul", ins := [8436, 8492], outs := [8496] }
      8436 8492 8496 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 8436 8492 8496)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5003
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8495, denoteGraph_ringAttn pm initPM 8496] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 5003).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 4989).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 5002).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 8495).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 8496).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5003 5003 8495 8496 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 4984 — layer-6 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 4984 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`8421`), rank 1 →
    `[32, 64)` (`8422`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `8413`/`8414` are expert-local (the
    `wf4984_hdisjA/B` fields).  Token input `7679 = mref5-pos1(4975)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 226, PM nodes 513/516). -/
theorem recon_intermediateGoal_4984_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4984
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 7679 = mref5-pos1(4975).
  obtain ⟨hbr13, hs8401, hs8402⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7679 : denoteGraph_ringAttn sm initSM 7679 = id (denoteGraph_ringAttn sm initSM 4975) :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975],
        outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7679 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15078 : denoteGraph_ringAttn pm initPM 15078 = id (denoteGraph_ringAttn pm initPM 8401) :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401],
        outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15078 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15101 : denoteGraph_ringAttn pm initPM 15101 = id (denoteGraph_ringAttn pm initPM 8402) :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402],
        outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15101 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7679 p15078 p15101
  have hsInA : (denoteGraph_ringAttn pm initPM 15078).shape = [2048, 1024] := by
    rw [p15078]; exact hs8401
  have hsInB : (denoteGraph_ringAttn pm initPM 15101).shape = [2048, 1024] := by
    rw [p15101]; exact hs8402
  have hbrIn : denoteGraph_ringAttn sm initSM 7679
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 15078, denoteGraph_ringAttn pm initPM 15101] := by
    rw [s7679, hbr13, hnr, ← p15078, ← p15101]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_4979 4979 8411 8412
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4979_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_4980 4980 8413 8414
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4980_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 4979
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8411, denoteGraph_ringAttn pm initPM 8412] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 4980
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8413, denoteGraph_ringAttn pm initPM 8414] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_4982
    (by native_decide) 4982 8417 8418 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_4983
    (by native_decide) 4983 8419 8420 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 8417).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4982 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4982, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8417 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 8418).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4982 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4982, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8418 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 8419).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4983 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4983, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8419 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 8420).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4983 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4983, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8420 (by native_decide)]; exact hs.2
  -- SM 4984 = full-range all2all (SM node 226).
  have hSMout : denoteGraph_ringAttn sm initSM 4984
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7679)
          (denoteGraph_ringAttn sm initSM 4979) (denoteGraph_ringAttn sm initSM 4980)
          (denoteGraph_ringAttn sm initSM 4982) (denoteGraph_ringAttn sm initSM 4983)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 226
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7679, 4979, 4980, 4982, 4983],
        outs := [4984], params := [64, 0, 64, 8] }
      7679 4979 4980 4982 4983 4984
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7679 4979 4980 4982 4983 4984 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8421 = rank-0 sharded-range all2all (PM node 513).
  have hP0 : denoteGraph_ringAttn pm initPM 8421
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15078)
          (denoteGraph_ringAttn pm initPM 8411) (denoteGraph_ringAttn pm initPM 8413)
          (denoteGraph_ringAttn pm initPM 8417) (denoteGraph_ringAttn pm initPM 8419)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 513
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15078, 8411, 8413, 8417, 8419],
        outs := [8421], params := [64, 0, 32, 8] }
      15078 8411 8413 8417 8419 8421
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 15078 8411 8413 8417 8419 8421 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8422 = rank-1 sharded-range all2all (PM node 516).
  have hP1 : denoteGraph_ringAttn pm initPM 8422
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15101)
          (denoteGraph_ringAttn pm initPM 8412) (denoteGraph_ringAttn pm initPM 8414)
          (denoteGraph_ringAttn pm initPM 8418) (denoteGraph_ringAttn pm initPM 8420)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 516
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15101, 8412, 8414, 8418, 8420],
        outs := [8422], params := [64, 32, 64, 8] }
      15101 8412 8414 8418 8420 8422
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 15101 8412 8414 8418 8420 8422 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 15078) (denoteGraph_ringAttn pm initPM 15101)
      (denoteGraph_ringAttn pm initPM 8411) (denoteGraph_ringAttn pm initPM 8412)
      (denoteGraph_ringAttn pm initPM 8413) (denoteGraph_ringAttn pm initPM 8414)
      (denoteGraph_ringAttn pm initPM 8417) (denoteGraph_ringAttn pm initPM 8418)
      (denoteGraph_ringAttn pm initPM 8419) (denoteGraph_ringAttn pm initPM 8420)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf4984_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf4984_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 4984
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8421, denoteGraph_ringAttn pm initPM 8422] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8421).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8422).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 4984).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4984 4984 8421 8422 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L6 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7668 — second position of the L6 pre-MoE residual `mref2(4973)` (2-tp, PM
    shards `15059`/`15067`).  Unlike L2's `7616` there is no gather-to-full/chunk
    because `4973` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 211, PM nodes 477/478). -/
theorem recon_intermediateGoal_7668_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7668
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8397, hs8398⟩ := twoTp_gather _ _ intermediateGoal_4973 4973 8397 8398
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4973_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7668 : denoteGraph_ringAttn sm initSM 7668 = id (denoteGraph_ringAttn sm initSM 4973) :=
    ringAttn_reduce1_pm_opaque sm initSM 211
      { rank := 0, op := "OpName.FW_multiref", ins := [4973], outs := [7664, 7668], params := [2] }
      4973 7668 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4973 7664 7668 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15059 : denoteGraph_ringAttn pm initPM 15059 = id (denoteGraph_ringAttn pm initPM 8397) :=
    ringAttn_reduce1_pm_opaque pm initPM 483
      { rank := 0, op := "OpName.FW_multiref", ins := [8397], outs := [15055, 15059], params := [2] }
      8397 15059 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8397 15055 15059 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15067 : denoteGraph_ringAttn pm initPM 15067 = id (denoteGraph_ringAttn pm initPM 8398) :=
    ringAttn_reduce1_pm_opaque pm initPM 484
      { rank := 1, op := "OpName.FW_multiref", ins := [8398], outs := [15063, 15067], params := [2] }
      8398 15067 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8398 15063 15067 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7668 p15059 p15067
  have hsp0 : (denoteGraph_ringAttn pm initPM 15059).shape = [2048, 1024] := by
    rw [p15059]; exact hs8397
  have hsp1 : (denoteGraph_ringAttn pm initPM 15067).shape = [2048, 1024] := by
    rw [p15067]; exact hs8398
  have hval : denoteGraph_ringAttn sm initSM 7668
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15059, denoteGraph_ringAttn pm initPM 15067] := by
    rw [s7668, hbr11, ← p15059, ← p15067]
  have hshape : (denoteGraph_ringAttn sm initSM 7668).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7668 7668 15059 15067 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5004 — post-MoE residual add `4984 + 5003` (2-tp, PM `8499`/`8500`). -/
theorem recon_intermediateGoal_5004_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5004
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs8421, hs8422⟩ := twoTp_gather _ _ intermediateGoal_4984 4984 8421 8422
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4984_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs8495, hs8496⟩ := twoTp_gather _ _ intermediateGoal_5003 5003 8495 8496
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5003_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5004
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 4984) (denoteGraph_ringAttn sm initSM 5003) :=
    ringAttn_reduce2_pm_opaque sm initSM 233
      { rank := 0, op := "OpName.FW_add", ins := [4984, 5003], outs := [5004] }
      4984 5003 5004 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 4984 5003 5004)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8499
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8421) (denoteGraph_ringAttn pm initPM 8495) :=
    ringAttn_reduce2_pm_opaque pm initPM 527
      { rank := 0, op := "OpName.FW_add", ins := [8421, 8495], outs := [8499] }
      8421 8495 8499 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 8421 8495 8499)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8500
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8422) (denoteGraph_ringAttn pm initPM 8496) :=
    ringAttn_reduce2_pm_opaque pm initPM 528
      { rank := 1, op := "OpName.FW_add", ins := [8422, 8496], outs := [8500] }
      8422 8496 8500 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 8422 8496 8500)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5004
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8499, denoteGraph_ringAttn pm initPM 8500] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs8421 hs8422 hs8495 hs8496,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8499).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8421 hs8495
  have hsp1 : (denoteGraph_ringAttn pm initPM 8500).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8422 hs8496
  have hshape : (denoteGraph_ringAttn sm initSM 5004).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5004 5004 8499 8500 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5005 — `FW_float(5004)` (identity, 2-tp PM `8505`/`8506`). -/
theorem recon_intermediateGoal_5005_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5005
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs8499, hs8500⟩ := twoTp_gather _ _ intermediateGoal_5004 5004 8499 8500
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5004_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5005 = id (denoteGraph_ringAttn sm initSM 5004) :=
    ringAttn_reduce1_pm_opaque sm initSM 234
      { rank := 0, op := "OpName.FW_float", ins := [5004], outs := [5005] }
      5004 5005 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5004 5005 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8505 = id (denoteGraph_ringAttn pm initPM 8499) :=
    ringAttn_reduce1_pm_opaque pm initPM 529
      { rank := 0, op := "OpName.FW_float", ins := [8499], outs := [8505] }
      8499 8505 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8499 8505 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8506 = id (denoteGraph_ringAttn pm initPM 8500) :=
    ringAttn_reduce1_pm_opaque pm initPM 530
      { rank := 1, op := "OpName.FW_float", ins := [8500], outs := [8506] }
      8500 8506 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8500 8506 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5005
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8505, denoteGraph_ringAttn pm initPM 8506] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8505).shape = [2048, 1024] := by rw [rP0]; exact hs8499
  have hsp1 : (denoteGraph_ringAttn pm initPM 8506).shape = [2048, 1024] := by rw [rP1]; exact hs8500
  have hshape : (denoteGraph_ringAttn sm initSM 5005).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5005 5005 8505 8506 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5006 — cross-block residual add `7668 + 5005` (2-tp, PM `8509`/`8510`). -/
theorem recon_intermediateGoal_5006_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5006
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs15059, hs15067⟩ := twoTp_gather _ _ intermediateGoal_7668 7668 15059 15067
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7668_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs8505, hs8506⟩ := twoTp_gather _ _ intermediateGoal_5005 5005 8505 8506
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5005_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5006
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7668) (denoteGraph_ringAttn sm initSM 5005) :=
    ringAttn_reduce2_pm_opaque sm initSM 235
      { rank := 0, op := "OpName.FW_add", ins := [7668, 5005], outs := [5006] }
      7668 5005 5006 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7668 5005 5006)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8509
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15059) (denoteGraph_ringAttn pm initPM 8505) :=
    ringAttn_reduce2_pm_opaque pm initPM 531
      { rank := 0, op := "OpName.FW_add", ins := [15059, 8505], outs := [8509] }
      15059 8505 8509 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15059 8505 8509)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8510
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15067) (denoteGraph_ringAttn pm initPM 8506) :=
    ringAttn_reduce2_pm_opaque pm initPM 532
      { rank := 1, op := "OpName.FW_add", ins := [15067, 8506], outs := [8510] }
      15067 8506 8510 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15067 8506 8510)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5006
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8509, denoteGraph_ringAttn pm initPM 8510] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15059 hs15067 hs8505 hs8506,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8509).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15059 hs8505
  have hsp1 : (denoteGraph_ringAttn pm initPM 8510).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15067 hs8506
  have hshape : (denoteGraph_ringAttn sm initSM 5006).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5006 5006 8509 8510 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5008 — RMSNorm of `mref2-first(5006)` with replicated weight `5007`
    (2-tp, PM `8513`/`8514`). -/
theorem recon_intermediateGoal_5008_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5008
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs8509, hs8510⟩ := twoTp_gather _ _ intermediateGoal_5006 5006 8509 8510
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5006_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7695 : denoteGraph_ringAttn sm initSM 7695 = id (denoteGraph_ringAttn sm initSM 5006) :=
    ringAttn_reduce1_pm_opaque sm initSM 236
      { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699], params := [2] }
      5006 7695 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5006 7695 7699)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15117 : denoteGraph_ringAttn pm initPM 15117 = id (denoteGraph_ringAttn pm initPM 8509) :=
    ringAttn_reduce1_pm_opaque pm initPM 533
      { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121], params := [2] }
      8509 15117 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8509 15117 15121)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15125 : denoteGraph_ringAttn pm initPM 15125 = id (denoteGraph_ringAttn pm initPM 8510) :=
    ringAttn_reduce1_pm_opaque pm initPM 534
      { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129], params := [2] }
      8510 15125 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8510 15125 15129)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7695 p15117 p15125
  have hs15117 : (denoteGraph_ringAttn pm initPM 15117).shape = [2048, 1024] := by
    rw [p15117]; exact hs8509
  have hs15125 : (denoteGraph_ringAttn pm initPM 15125).shape = [2048, 1024] := by
    rw [p15125]; exact hs8510
  have hbr39 : denoteGraph_ringAttn sm initSM 7695
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15117, denoteGraph_ringAttn pm initPM 15125] := by
    rw [s7695, hbr44, ← p15117, ← p15125]
  have hw5007 : denoteGraph_ringAttn sm initSM 5007 = denoteGraph_ringAttn pm initPM 5007 :=
    veq_weight_ring initSM initPM hInit initGoal_5007 (by native_decide) 5007
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5008
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7695) (denoteGraph_ringAttn sm initSM 5007) :=
    ringAttn_reduce2_pm_opaque sm initSM 237
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7695, 5007], outs := [5008] }
      7695 5007 5008 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7695 5007 5008)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8513
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15117) (denoteGraph_ringAttn pm initPM 5007) :=
    ringAttn_reduce2_pm_opaque pm initPM 535
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15117, 5007], outs := [8513] }
      15117 5007 8513 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15117 5007 8513)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8514
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15125) (denoteGraph_ringAttn pm initPM 5007) :=
    ringAttn_reduce2_pm_opaque pm initPM 536
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15125, 5007], outs := [8514] }
      15125 5007 8514 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15125 5007 8514)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5008
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8513, denoteGraph_ringAttn pm initPM 8514] := by
    rw [rSM, hbr39, hw5007, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15117 hs15125,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8513).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15117
  have hsp1 : (denoteGraph_ringAttn pm initPM 8514).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15125
  have hshape : (denoteGraph_ringAttn sm initSM 5008).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5008 5008 8513 8514 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5010 — per-head Q projection `fw_per_head_linear(mref3₀(5008), 5009)`
    (2-tp, PM `8515`/`8516`, weight `5009 : [16,64,1024]`). -/
theorem recon_intermediateGoal_5010_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5010
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8513, hs8514⟩ := twoTp_gather _ _ intermediateGoal_5008 5008 8513 8514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5008_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7704 : denoteGraph_ringAttn sm initSM 7704 = id (denoteGraph_ringAttn sm initSM 5008) :=
    ringAttn_reduce1_pm_opaque sm initSM 238
      { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
      5008 7704 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5008 7704 7708 7712)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15134 : denoteGraph_ringAttn pm initPM 15134 = id (denoteGraph_ringAttn pm initPM 8513) :=
    ringAttn_reduce1_pm_opaque pm initPM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
      8513 15134 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8513 15134 15138 15142)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15147 : denoteGraph_ringAttn pm initPM 15147 = id (denoteGraph_ringAttn pm initPM 8514) :=
    ringAttn_reduce1_pm_opaque pm initPM 538
      { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
      8514 15147 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8514 15147 15151 15155)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7704 p15134 p15147
  have hs15134 : (denoteGraph_ringAttn pm initPM 15134).shape = [2048, 1024] := by
    rw [p15134]; exact hs8513
  have hs15147 : (denoteGraph_ringAttn pm initPM 15147).shape = [2048, 1024] := by
    rw [p15147]; exact hs8514
  have hbr48 : denoteGraph_ringAttn sm initSM 7704
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15134, denoteGraph_ringAttn pm initPM 15147] := by
    rw [s7704, hbr46, ← p15134, ← p15147]
  have hw5009 : denoteGraph_ringAttn sm initSM 5009 = denoteGraph_ringAttn pm initPM 5009 :=
    veq_weight_ring initSM initPM hInit initGoal_5009 (by native_decide) 5009
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5009 : (denoteGraph_ringAttn sm initSM 5009).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5009 (by native_decide) 5009 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5009 : (denoteGraph_ringAttn pm initPM 5009).shape = [16, 64, 1024] := by
    rw [← hw5009]; exact hsw5009
  have rSM : denoteGraph_ringAttn sm initSM 5010
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7704) (denoteGraph_ringAttn sm initSM 5009) :=
    ringAttn_reduce2_pm_opaque sm initSM 239
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7704, 5009], outs := [5010] }
      7704 5009 5010 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7704 5009 5010 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8515
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15134) (denoteGraph_ringAttn pm initPM 5009) :=
    ringAttn_reduce2_pm_opaque pm initPM 539
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15134, 5009], outs := [8515] }
      15134 5009 8515 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15134 5009 8515 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8516
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15147) (denoteGraph_ringAttn pm initPM 5009) :=
    ringAttn_reduce2_pm_opaque pm initPM 542
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15147, 5009], outs := [8516] }
      15147 5009 8516 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15147 5009 8516 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5010
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8515, denoteGraph_ringAttn pm initPM 8516] := by
    rw [rSM, hbr48, hw5009, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs15134 hs15147 hpw5009,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8515).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15134 hpw5009
  have hsp1 : (denoteGraph_ringAttn pm initPM 8516).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15147 hpw5009
  have hshape : (denoteGraph_ringAttn sm initSM 5010).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5010 5010 8515 8516 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5012 — per-head K projection `fw_per_head_linear(mref3₁(5008), 5011)`
    (2-tp, PM `8527`/`8528`, weight `5011 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5012_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5012
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8513, hs8514⟩ := twoTp_gather _ _ intermediateGoal_5008 5008 8513 8514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5008_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7708 : denoteGraph_ringAttn sm initSM 7708 = id (denoteGraph_ringAttn sm initSM 5008) :=
    ringAttn_reduce1_pm_opaque sm initSM 238
      { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
      5008 7708 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5008 7704 7708 7712 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15138 : denoteGraph_ringAttn pm initPM 15138 = id (denoteGraph_ringAttn pm initPM 8513) :=
    ringAttn_reduce1_pm_opaque pm initPM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
      8513 15138 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8513 15134 15138 15142 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15151 : denoteGraph_ringAttn pm initPM 15151 = id (denoteGraph_ringAttn pm initPM 8514) :=
    ringAttn_reduce1_pm_opaque pm initPM 538
      { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
      8514 15151 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8514 15147 15151 15155 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7708 p15138 p15151
  have hs15138 : (denoteGraph_ringAttn pm initPM 15138).shape = [2048, 1024] := by
    rw [p15138]; exact hs8513
  have hs15151 : (denoteGraph_ringAttn pm initPM 15151).shape = [2048, 1024] := by
    rw [p15151]; exact hs8514
  have hbr52 : denoteGraph_ringAttn sm initSM 7708
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15138, denoteGraph_ringAttn pm initPM 15151] := by
    rw [s7708, hbr46, ← p15138, ← p15151]
  have hw5011 : denoteGraph_ringAttn sm initSM 5011 = denoteGraph_ringAttn pm initPM 5011 :=
    veq_weight_ring initSM initPM hInit initGoal_5011 (by native_decide) 5011
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5011 : (denoteGraph_ringAttn sm initSM 5011).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5011 (by native_decide) 5011 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5011 : (denoteGraph_ringAttn pm initPM 5011).shape = [4, 64, 1024] := by
    rw [← hw5011]; exact hsw5011
  have rSM : denoteGraph_ringAttn sm initSM 5012
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7708) (denoteGraph_ringAttn sm initSM 5011) :=
    ringAttn_reduce2_pm_opaque sm initSM 240
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7708, 5011], outs := [5012] }
      7708 5011 5012 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7708 5011 5012 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8527
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15138) (denoteGraph_ringAttn pm initPM 5011) :=
    ringAttn_reduce2_pm_opaque pm initPM 540
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15138, 5011], outs := [8527] }
      15138 5011 8527 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15138 5011 8527 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8528
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15151) (denoteGraph_ringAttn pm initPM 5011) :=
    ringAttn_reduce2_pm_opaque pm initPM 543
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15151, 5011], outs := [8528] }
      15151 5011 8528 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15151 5011 8528 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5012
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8527, denoteGraph_ringAttn pm initPM 8528] := by
    rw [rSM, hbr52, hw5011, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15138 hs15151 hpw5011,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8527).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15138 hpw5011
  have hsp1 : (denoteGraph_ringAttn pm initPM 8528).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15151 hpw5011
  have hshape : (denoteGraph_ringAttn sm initSM 5012).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5012 5012 8527 8528 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5014 — per-head V projection `fw_per_head_linear(mref3₂(5008), 5013)`
    (2-tp, PM `8537`/`8538`, weight `5013 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5014_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5014
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8513, hs8514⟩ := twoTp_gather _ _ intermediateGoal_5008 5008 8513 8514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5008_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7712 : denoteGraph_ringAttn sm initSM 7712 = id (denoteGraph_ringAttn sm initSM 5008) :=
    ringAttn_reduce1_pm_opaque sm initSM 238
      { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
      5008 7712 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5008 7704 7708 7712 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15142 : denoteGraph_ringAttn pm initPM 15142 = id (denoteGraph_ringAttn pm initPM 8513) :=
    ringAttn_reduce1_pm_opaque pm initPM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
      8513 15142 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8513 15134 15138 15142 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15155 : denoteGraph_ringAttn pm initPM 15155 = id (denoteGraph_ringAttn pm initPM 8514) :=
    ringAttn_reduce1_pm_opaque pm initPM 538
      { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
      8514 15155 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8514 15147 15151 15155 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7712 p15142 p15155
  have hs15142 : (denoteGraph_ringAttn pm initPM 15142).shape = [2048, 1024] := by
    rw [p15142]; exact hs8513
  have hs15155 : (denoteGraph_ringAttn pm initPM 15155).shape = [2048, 1024] := by
    rw [p15155]; exact hs8514
  have hbr56 : denoteGraph_ringAttn sm initSM 7712
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15142, denoteGraph_ringAttn pm initPM 15155] := by
    rw [s7712, hbr46, ← p15142, ← p15155]
  have hw5013 : denoteGraph_ringAttn sm initSM 5013 = denoteGraph_ringAttn pm initPM 5013 :=
    veq_weight_ring initSM initPM hInit initGoal_5013 (by native_decide) 5013
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5013 : (denoteGraph_ringAttn sm initSM 5013).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5013 (by native_decide) 5013 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5013 : (denoteGraph_ringAttn pm initPM 5013).shape = [4, 64, 1024] := by
    rw [← hw5013]; exact hsw5013
  have rSM : denoteGraph_ringAttn sm initSM 5014
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7712) (denoteGraph_ringAttn sm initSM 5013) :=
    ringAttn_reduce2_pm_opaque sm initSM 241
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7712, 5013], outs := [5014] }
      7712 5013 5014 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7712 5013 5014 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8537
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15142) (denoteGraph_ringAttn pm initPM 5013) :=
    ringAttn_reduce2_pm_opaque pm initPM 541
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15142, 5013], outs := [8537] }
      15142 5013 8537 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15142 5013 8537 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8538
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15155) (denoteGraph_ringAttn pm initPM 5013) :=
    ringAttn_reduce2_pm_opaque pm initPM 544
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15155, 5013], outs := [8538] }
      15155 5013 8538 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15155 5013 8538 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5014
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8537, denoteGraph_ringAttn pm initPM 8538] := by
    rw [rSM, hbr56, hw5013, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15142 hs15155 hpw5013,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8537).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15142 hpw5013
  have hsp1 : (denoteGraph_ringAttn pm initPM 8538).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15155 hpw5013
  have hshape : (denoteGraph_ringAttn sm initSM 5014).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5014 5014 8537 8538 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L6 rotary cos/sin cache agreement: `sm 4691 = pm 11859` (`= 11853 + 3`). -/
theorem hcache_4691_11859 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11859 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11859 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11859 6 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 5016 — rotary-embedding Q output `rotary(4691, 5015, 5010, 5012).1`
    (2-tp, PM `8549`/`8550`; positions `5015 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_5016_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5016
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs8515, hs8516⟩ := twoTp_gather _ _ intermediateGoal_5010 5010 8515 8516
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5010_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_5012 5012 8527 8528
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5012_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11859 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5015 = denoteGraph_ringAttn pm initPM 5015 :=
    veq_weight_ring initSM initPM hInit initGoal_5015 (by native_decide) 5015
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5015 : (denoteGraph_ringAttn sm initSM 5015).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5015 (by native_decide) 5015 [4096]
      rfl rfl (by native_decide)
  have c8547 : denoteGraph_ringAttn pm initPM 8547
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5015) :=
    ringAttn_reduce1_pm_opaque pm initPM 6
      { rank := 0, op := "OpName.ChunkPrim", ins := [5015], outs := [8547], params := [0] }
      5015 8547 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5015 8547 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8548 : denoteGraph_ringAttn pm initPM 8548
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5015) :=
    ringAttn_reduce1_pm_opaque pm initPM 19
      { rank := 1, op := "OpName.ChunkPrim", ins := [5015], outs := [8548], params := [0] }
      5015 8548 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5015 8548 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5016
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5015)
          (denoteGraph_ringAttn sm initSM 5010) (denoteGraph_ringAttn sm initSM 5012) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 242
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5015, 5010, 5012], outs := [5016, 5017], params := [16, 4] }
          5016 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 242 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 242 5015 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 242 5010 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 242 5012 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8549
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11859) (denoteGraph_ringAttn pm initPM 8547)
          (denoteGraph_ringAttn pm initPM 8515) (denoteGraph_ringAttn pm initPM 8527) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 545
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11859, 8547, 8515, 8527], outs := [8549, 8551], params := [16, 4] }
          8549 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 545 11859 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 545 8547 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 545 8515 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 545 8527 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8550
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11859) (denoteGraph_ringAttn pm initPM 8548)
          (denoteGraph_ringAttn pm initPM 8516) (denoteGraph_ringAttn pm initPM 8528) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 546
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11859, 8548, 8516, 8528], outs := [8550, 8552], params := [16, 4] }
          8550 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 546 11859 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 546 8548 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 546 8516 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 546 8528 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5016
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8549, denoteGraph_ringAttn pm initPM 8550] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5015) (denoteGraph_ringAttn pm initPM 8515)
          (denoteGraph_ringAttn pm initPM 8516) 2048 16 64 (by omega) (by omega) (by omega)
          hsp5015 hs8515 hs8516,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8547
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5015) from c8547),
        ← (show denoteGraph_ringAttn pm initPM 8548
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5015) from c8548),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8549).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8515
  have hsp1 : (denoteGraph_ringAttn pm initPM 8550).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8516
  have hshape : (denoteGraph_ringAttn sm initSM 5016).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5016 5016 8549 8550 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 5017 — rotary-embedding K output `rotary(4691, 5015, 5010, 5012).2`
    (2-tp, PM `8551`/`8552`). -/
theorem recon_intermediateGoal_5017_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5017
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_5010 5010 8515 8516
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5010_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs8527, hs8528⟩ := twoTp_gather _ _ intermediateGoal_5012 5012 8527 8528
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5012_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11859 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5015 = denoteGraph_ringAttn pm initPM 5015 :=
    veq_weight_ring initSM initPM hInit initGoal_5015 (by native_decide) 5015
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5015 : (denoteGraph_ringAttn sm initSM 5015).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5015 (by native_decide) 5015 [4096]
      rfl rfl (by native_decide)
  have c8547 : denoteGraph_ringAttn pm initPM 8547
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5015) :=
    ringAttn_reduce1_pm_opaque pm initPM 6
      { rank := 0, op := "OpName.ChunkPrim", ins := [5015], outs := [8547], params := [0] }
      5015 8547 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5015 8547 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8548 : denoteGraph_ringAttn pm initPM 8548
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5015) :=
    ringAttn_reduce1_pm_opaque pm initPM 19
      { rank := 1, op := "OpName.ChunkPrim", ins := [5015], outs := [8548], params := [0] }
      5015 8548 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5015 8548 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5017
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5015)
          (denoteGraph_ringAttn sm initSM 5010) (denoteGraph_ringAttn sm initSM 5012) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 242
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5015, 5010, 5012], outs := [5016, 5017], params := [16, 4] }
          5017 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5015 5010 5012 5016 5017 (by decide),
        ringAttn_prefix_read_pm sm initSM 242 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 242 5015 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 242 5010 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 242 5012 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8551
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11859) (denoteGraph_ringAttn pm initPM 8547)
          (denoteGraph_ringAttn pm initPM 8515) (denoteGraph_ringAttn pm initPM 8527) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 545
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11859, 8547, 8515, 8527], outs := [8549, 8551], params := [16, 4] }
          8551 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11859 8547 8515 8527 8549 8551 (by decide),
        ringAttn_prefix_read_pm pm initPM 545 11859 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 545 8547 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 545 8515 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 545 8527 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8552
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11859) (denoteGraph_ringAttn pm initPM 8548)
          (denoteGraph_ringAttn pm initPM 8516) (denoteGraph_ringAttn pm initPM 8528) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 546
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11859, 8548, 8516, 8528], outs := [8550, 8552], params := [16, 4] }
          8552 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11859 8548 8516 8528 8550 8552 (by decide),
        ringAttn_prefix_read_pm pm initPM 546 11859 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 546 8548 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 546 8516 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 546 8528 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5017
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8551, denoteGraph_ringAttn pm initPM 8552] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5015) (denoteGraph_ringAttn pm initPM 8527)
          (denoteGraph_ringAttn pm initPM 8528) 2048 4 64 (by omega) (by omega) (by omega)
          hsp5015 hs8527 hs8528,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8547
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5015) from c8547),
        ← (show denoteGraph_ringAttn pm initPM 8548
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5015) from c8548),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8551).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8527
  have hsp1 : (denoteGraph_ringAttn pm initPM 8552).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8528
  have hshape : (denoteGraph_ringAttn sm initSM 5017).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5017 5017 8551 8552 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
