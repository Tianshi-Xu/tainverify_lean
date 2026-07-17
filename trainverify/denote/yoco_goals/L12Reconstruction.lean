/- Worker #24 — Layer-12 reconstruction cascade over `denoteGraph_ringAttn`
   (PERIODIC BULK, tids 5291..5330).

   Chains forward from `recon_intermediateGoal_5290_ringAttn` (the layer-12
   sliding-window attention output, unconditional-given-WF) through the
   periodic portion of the layer-12 MoE/residual forward block. Produced by a
   position-wise numeric extrapolation of `L11Reconstruction` (per-position
   delta constant across L9->L10->L11, verified), then validated node-by-node
   by `native_decide` in every theorem.

   L12 is the LAST MoE layer: its boundary tail (tids 5332,5334,5336,5338,5340,
   5342,5343,5344) diverges from the periodic +54 pattern (replicated
   single-rank goals `tid==ts`, new ops `FW_maybe_shuffle`/`FW_to`), so those
   are NOT generated here; they are handled directly in `L12BoundaryTail`.

   Every L12 periodic intermediate is a genuine 2-tp SHARDED goal
   (`tps = [{0,r0},{1,r1}]`), reusing the L2 phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, per-op allGather-commute lemmas). -/
import denote.yoco_goals.L11Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 5291 — 2-tp reshape of the L12 attention output `5290 : [4096,16,64]` to
    `[4096,1024]` (SM node 205, PM nodes 471/472). -/
theorem recon_intermediateGoal_5291_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5291
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval4, hs9483, hs9484⟩ := twoTp_gather _ _ intermediateGoal_5290 5290 9483 9484
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5290_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5291
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5290) :=
    ringAttn_reshape_reduce_pm sm initSM 439 0 5290 5291 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9485
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9483) :=
    ringAttn_reshape_reduce_pm pm initPM 939 0 9483 9485 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9486
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9484) :=
    ringAttn_reshape_reduce_pm pm initPM 940 1 9484 9486 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5291
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9485, denoteGraph_ringAttn pm initPM 9486] := by
    rw [rSM, hval4, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs9483 hs9484
  have hs9485 : (denoteGraph_ringAttn pm initPM 9485).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9486 : (denoteGraph_ringAttn pm initPM 9486).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5291 : (denoteGraph_ringAttn sm initSM 5291).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5291 5291 9485 9486 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5291 hs9485 hs9486

/-- 5292 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 206, PM
    nodes 473/474). -/
theorem recon_intermediateGoal_5292_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5292
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval5, hs9485, hs9486⟩ := twoTp_gather _ _ intermediateGoal_5291 5291 9485 9486
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5291_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5291 : (denoteGraph_ringAttn sm initSM 5291).shape = [4096, 1024] := by
    rw [hval5, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9485])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5292
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5291) :=
    ringAttn_reshape_reduce_pm sm initSM 440 0 5291 5292 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9491
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9485) :=
    ringAttn_reshape_reduce_pm pm initPM 941 0 9485 9491 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9492
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9486) :=
    ringAttn_reshape_reduce_pm pm initPM 942 1 9486 9492 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 9491 = denoteGraph_ringAttn pm initPM 9485 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9485]
  have h18 : denoteGraph_ringAttn pm initPM 9492 = denoteGraph_ringAttn pm initPM 9486 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9486]
  have hval : denoteGraph_ringAttn sm initSM 5292
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9491, denoteGraph_ringAttn pm initPM 9492] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5291, hval5, hnr, ← h17, ← h18]
  have hs9491 : (denoteGraph_ringAttn pm initPM 9491).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9492 : (denoteGraph_ringAttn pm initPM 9492).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5292 : (denoteGraph_ringAttn sm initSM 5292).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5292 5292 9491 9492 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5292 hs9491 hs9492

/-- 5294 — 2-tp down-projection `fw_linear(5292, 5293)` (weight `5293 : [1024,1024]`,
    SM node 207, PM nodes 475/476). -/
theorem recon_intermediateGoal_5294_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5294
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval6, hs9491, hs9492⟩ := twoTp_gather _ _ intermediateGoal_5292 5292 9491 9492
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5292_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5293 : denoteGraph_ringAttn sm initSM 5293 = denoteGraph_ringAttn pm initPM 5293 :=
    veq_weight_ring initSM initPM hInit initGoal_5293 (by native_decide) 5293
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5293 : (denoteGraph_ringAttn sm initSM 5293).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5293 (by native_decide) 5293 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw5293 : (denoteGraph_ringAttn pm initPM 5293).shape = [1024, 1024] := by
    rw [← hw5293]; exact hsw5293
  have rSM : denoteGraph_ringAttn sm initSM 5294
      = fw_linear (denoteGraph_ringAttn sm initSM 5292) (denoteGraph_ringAttn sm initSM 5293) :=
    ringAttn_reduce2_pm_opaque sm initSM 441
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5292, 5293], outs := [5294] }
      5292 5293 5294 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5292 5293 5294)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9495
      = fw_linear (denoteGraph_ringAttn pm initPM 9491) (denoteGraph_ringAttn pm initPM 5293) :=
    ringAttn_reduce2_pm_opaque pm initPM 943
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9491, 5293], outs := [9495] }
      9491 5293 9495 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9491 5293 9495)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9496
      = fw_linear (denoteGraph_ringAttn pm initPM 9492) (denoteGraph_ringAttn pm initPM 5293) :=
    ringAttn_reduce2_pm_opaque pm initPM 944
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9492, 5293], outs := [9496] }
      9492 5293 9496 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9492 5293 9496)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5294
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9495, denoteGraph_ringAttn pm initPM 9496] := by
    rw [rSM, hval6, hw5293, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs9491 hs9492 hpw5293,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9495).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9491 hpw5293
  have hsp1 : (denoteGraph_ringAttn pm initPM 9496).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9492 hpw5293
  have hshape : (denoteGraph_ringAttn sm initSM 5294).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5294 5294 9495 9496 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5295 — 2-tp identity view of `5294` (SM node 208, PM nodes 477/478). -/
theorem recon_intermediateGoal_5295_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5295
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval8, hs9495, hs9496⟩ := twoTp_gather _ _ intermediateGoal_5294 5294 9495 9496
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5294_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5294 : (denoteGraph_ringAttn sm initSM 5294).shape = [4096, 1024] := by
    rw [hval8, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9495])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5295
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5294) :=
    ringAttn_reduce1_pm_opaque sm initSM 442
      { rank := 0, op := "OpName.FW_view", ins := [5294], outs := [5295], params := [4096, 1024] }
      5294 5295 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5294 5295)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9505
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9495) :=
    ringAttn_reduce1_pm_opaque pm initPM 945
      { rank := 0, op := "OpName.FW_view", ins := [9495], outs := [9505], params := [2048, 1024] }
      9495 9505 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9495 9505)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9506
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9496) :=
    ringAttn_reduce1_pm_opaque pm initPM 946
      { rank := 1, op := "OpName.FW_view", ins := [9496], outs := [9506], params := [2048, 1024] }
      9496 9506 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9496 9506)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 9505 = denoteGraph_ringAttn pm initPM 9495 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9495]
  have h32 : denoteGraph_ringAttn pm initPM 9506 = denoteGraph_ringAttn pm initPM 9496 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9496]
  have hval : denoteGraph_ringAttn sm initSM 5295
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9505, denoteGraph_ringAttn pm initPM 9506] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5294, hval8, hnr, ← h31, ← h32]
  have hs9505 : (denoteGraph_ringAttn pm initPM 9505).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9506 : (denoteGraph_ringAttn pm initPM 9506).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5295 : (denoteGraph_ringAttn sm initSM 5295).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5295 5295 9505 9506 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5295 hs9505 hs9506

/-- 5296 — 2-tp `FW_float(5295)` (identity, SM node 209, PM nodes 479/480). -/
theorem recon_intermediateGoal_5296_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5296
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr9, hs9505, hs9506⟩ := twoTp_gather _ _ intermediateGoal_5295 5295 9505 9506
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5295_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5296 = id (denoteGraph_ringAttn sm initSM 5295) :=
    ringAttn_reduce1_pm_opaque sm initSM 443
      { rank := 0, op := "OpName.FW_float", ins := [5295], outs := [5296] }
      5295 5296 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5295 5296 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9509 = id (denoteGraph_ringAttn pm initPM 9505) :=
    ringAttn_reduce1_pm_opaque pm initPM 947
      { rank := 0, op := "OpName.FW_float", ins := [9505], outs := [9509] }
      9505 9509 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9505 9509 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9510 = id (denoteGraph_ringAttn pm initPM 9506) :=
    ringAttn_reduce1_pm_opaque pm initPM 948
      { rank := 1, op := "OpName.FW_float", ins := [9506], outs := [9510] }
      9506 9510 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9506 9510 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5296
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9509, denoteGraph_ringAttn pm initPM 9510] := by
    rw [rSM, hbr9, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9509).shape = [2048, 1024] := by rw [rP0]; exact hs9505
  have hsp1 : (denoteGraph_ringAttn pm initPM 9510).shape = [2048, 1024] := by rw [rP1]; exact hs9506
  have hshape : (denoteGraph_ringAttn sm initSM 5296).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5296 5296 9509 9510 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7959 — 2-tp `mref2`-second copy of the L2 residual `5276` (SM node 197,
    PM nodes 455/456), carried into the L12 residual add. -/
theorem recon_intermediateGoal_7959_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7959
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs9439, hs9440⟩ := twoTp_gather _ _ intermediateGoal_5276 5276 9439 9440
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5276_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8495 : denoteGraph_ringAttn sm initSM 7959 = id (denoteGraph_ringAttn sm initSM 5276) :=
    ringAttn_reduce1_pm_opaque sm initSM 431
      { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959], params := [2] }
      5276 7959 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5276 7955 7959 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15641 : denoteGraph_ringAttn pm initPM 15641 = id (denoteGraph_ringAttn pm initPM 9439) :=
    ringAttn_reduce1_pm_opaque pm initPM 923
      { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641], params := [2] }
      9439 15641 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9439 15637 15641 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15649 : denoteGraph_ringAttn pm initPM 15649 = id (denoteGraph_ringAttn pm initPM 9440) :=
    ringAttn_reduce1_pm_opaque pm initPM 924
      { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649], params := [2] }
      9440 15649 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9440 15645 15649 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8495 p15641 p15649
  have hsp0 : (denoteGraph_ringAttn pm initPM 15641).shape = [2048, 1024] := by
    rw [p15641]; exact hs9439
  have hsp1 : (denoteGraph_ringAttn pm initPM 15649).shape = [2048, 1024] := by
    rw [p15649]; exact hs9440
  have hval : denoteGraph_ringAttn sm initSM 7959
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15641, denoteGraph_ringAttn pm initPM 15649] := by
    rw [s8495, hbr90, ← p15641, ← p15649]
  have hshape : (denoteGraph_ringAttn sm initSM 7959).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7959 7959 15641 15649 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5297 — 2-tp L12 residual add `7959 + 5296` (SM node 210, PM nodes 481/482). -/
theorem recon_intermediateGoal_5297_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5297
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs15641, hs15649⟩ := twoTp_gather _ _ intermediateGoal_7959 7959 15641 15649
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7959_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs9509, hs9510⟩ := twoTp_gather _ _ intermediateGoal_5296 5296 9509 9510
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5296_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5297
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7959) (denoteGraph_ringAttn sm initSM 5296) :=
    ringAttn_reduce2_pm_opaque sm initSM 444
      { rank := 0, op := "OpName.FW_add", ins := [7959, 5296], outs := [5297] }
      7959 5296 5297 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7959 5296 5297)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9513
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15641) (denoteGraph_ringAttn pm initPM 9509) :=
    ringAttn_reduce2_pm_opaque pm initPM 949
      { rank := 0, op := "OpName.FW_add", ins := [15641, 9509], outs := [9513] }
      15641 9509 9513 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15641 9509 9513)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9514
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15649) (denoteGraph_ringAttn pm initPM 9510) :=
    ringAttn_reduce2_pm_opaque pm initPM 950
      { rank := 1, op := "OpName.FW_add", ins := [15649, 9510], outs := [9514] }
      15649 9510 9514 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15649 9510 9514)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5297
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9513, denoteGraph_ringAttn pm initPM 9514] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15641 hs15649 hs9509 hs9510,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9513).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15641 hs9509
  have hsp1 : (denoteGraph_ringAttn pm initPM 9514).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15649 hs9510
  have hshape : (denoteGraph_ringAttn sm initSM 5297).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5297 5297 9513 9514 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5299 — 2-tp RMSNorm of `mref2-first(5297)` with replicated weight
    `5298 : [1024]` (SM node 212, PM nodes 485/486). -/
theorem recon_intermediateGoal_5299_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5299
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs9513, hs9514⟩ := twoTp_gather _ _ intermediateGoal_5297 5297 9513 9514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5297_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7976 : denoteGraph_ringAttn sm initSM 7976 = id (denoteGraph_ringAttn sm initSM 5297) :=
    ringAttn_reduce1_pm_opaque sm initSM 445
      { rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] }
      5297 7976 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5297 7976 7980)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15679 : denoteGraph_ringAttn pm initPM 15679 = id (denoteGraph_ringAttn pm initPM 9513) :=
    ringAttn_reduce1_pm_opaque pm initPM 951
      { rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683], params := [2] }
      9513 15679 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9513 15679 15683)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15687 : denoteGraph_ringAttn pm initPM 15687 = id (denoteGraph_ringAttn pm initPM 9514) :=
    ringAttn_reduce1_pm_opaque pm initPM 952
      { rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691], params := [2] }
      9514 15687 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9514 15687 15691)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7976 p15679 p15687
  have hs15679 : (denoteGraph_ringAttn pm initPM 15679).shape = [2048, 1024] := by
    rw [p15679]; exact hs9513
  have hs15687 : (denoteGraph_ringAttn pm initPM 15687).shape = [2048, 1024] := by
    rw [p15687]; exact hs9514
  have hbr8 : denoteGraph_ringAttn sm initSM 7976
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15679, denoteGraph_ringAttn pm initPM 15687] := by
    rw [s7976, hbr11, ← p15679, ← p15687]
  have hw5298 : denoteGraph_ringAttn sm initSM 5298 = denoteGraph_ringAttn pm initPM 5298 :=
    veq_weight_ring initSM initPM hInit initGoal_5298 (by native_decide) 5298
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5299
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7976) (denoteGraph_ringAttn sm initSM 5298) :=
    ringAttn_reduce2_pm_opaque sm initSM 446
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7976, 5298], outs := [5299] }
      7976 5298 5299 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7976 5298 5299)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9517
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15679) (denoteGraph_ringAttn pm initPM 5298) :=
    ringAttn_reduce2_pm_opaque pm initPM 953
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15679, 5298], outs := [9517] }
      15679 5298 9517 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15679 5298 9517)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9518
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15687) (denoteGraph_ringAttn pm initPM 5298) :=
    ringAttn_reduce2_pm_opaque pm initPM 954
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15687, 5298], outs := [9518] }
      15687 5298 9518 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15687 5298 9518)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5299
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9517, denoteGraph_ringAttn pm initPM 9518] := by
    rw [rSM, hbr8, hw5298, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15679 hs15687,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9517).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15679
  have hsp1 : (denoteGraph_ringAttn pm initPM 9518).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15687
  have hshape : (denoteGraph_ringAttn sm initSM 5299).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5299 5299 9517 9518 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5300 — 2-tp `FW_float(mref5-first(5299))` (identity, SM node 214,
    PM nodes 489/493; mref5-first via SM node 213, PM 487/488). -/
theorem recon_intermediateGoal_5300_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5300
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9517, hs9518⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7987 : denoteGraph_ringAttn sm initSM 7987 = id (denoteGraph_ringAttn sm initSM 5299) :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299],
        outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7987 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 5299 7987 [7991, 7995, 7999, 8003])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15698 : denoteGraph_ringAttn pm initPM 15698 = id (denoteGraph_ringAttn pm initPM 9517) :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517],
        outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15698 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 9517 15698 [15702, 15706, 15710, 15714])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15721 : denoteGraph_ringAttn pm initPM 15721 = id (denoteGraph_ringAttn pm initPM 9518) :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518],
        outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15721 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 9518 15721 [15725, 15729, 15733, 15737])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7987 p15698 p15721
  have hbrm : denoteGraph_ringAttn sm initSM 7987
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15698, denoteGraph_ringAttn pm initPM 15721] := by
    rw [s7987, hbr13, ← p15698, ← p15721]
  have rSM : denoteGraph_ringAttn sm initSM 5300 = id (denoteGraph_ringAttn sm initSM 7987) :=
    ringAttn_reduce1_pm_opaque sm initSM 448
      { rank := 0, op := "OpName.FW_float", ins := [7987], outs := [5300] }
      7987 5300 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7987 5300 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9519 = id (denoteGraph_ringAttn pm initPM 15698) :=
    ringAttn_reduce1_pm_opaque pm initPM 957
      { rank := 0, op := "OpName.FW_float", ins := [15698], outs := [9519] }
      15698 9519 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 15698 9519 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9520 = id (denoteGraph_ringAttn pm initPM 15721) :=
    ringAttn_reduce1_pm_opaque pm initPM 961
      { rank := 1, op := "OpName.FW_float", ins := [15721], outs := [9520] }
      15721 9520 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 15721 9520 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs15698 : (denoteGraph_ringAttn pm initPM 15698).shape = [2048, 1024] := by
    rw [p15698]; exact hs9517
  have hs15721 : (denoteGraph_ringAttn pm initPM 15721).shape = [2048, 1024] := by
    rw [p15721]; exact hs9518
  have hval : denoteGraph_ringAttn sm initSM 5300
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9519, denoteGraph_ringAttn pm initPM 9520] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9519).shape = [2048, 1024] := by
    rw [rP0]; exact hs15698
  have hsp1 : (denoteGraph_ringAttn pm initPM 9520).shape = [2048, 1024] := by
    rw [rP1]; exact hs15721
  have hshape : (denoteGraph_ringAttn sm initSM 5300).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5300 5300 9519 9520 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5302 — 2-tp router logits `fw_norm_linear(5300, 5301)` with weight
    `5301 : [64, 1024]` → `[4096, 64]` (SM node 218, PM nodes 497/501). -/
theorem recon_intermediateGoal_5302_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5302
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs9519, hs9520⟩ := twoTp_gather _ _ intermediateGoal_5300 5300 9519 9520
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5300_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5301 : denoteGraph_ringAttn sm initSM 5301 = denoteGraph_ringAttn pm initPM 5301 :=
    veq_weight_ring initSM initPM hInit initGoal_5301 (by native_decide) 5301
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5301 : (denoteGraph_ringAttn sm initSM 5301).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5301 (by native_decide) 5301 [64, 1024]
      rfl rfl (by native_decide)
  have hpw5301 : (denoteGraph_ringAttn pm initPM 5301).shape = [64, 1024] := by
    rw [← hw5301]; exact hsw5301
  have rSM : denoteGraph_ringAttn sm initSM 5302
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 5300) (denoteGraph_ringAttn sm initSM 5301) :=
    ringAttn_reduce2_pm_opaque sm initSM 452
      { rank := 0, op := "OpName.FW_norm_linear", ins := [5300, 5301], outs := [5302] }
      5300 5301 5302 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 5300 5301 5302)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9525
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9519) (denoteGraph_ringAttn pm initPM 5301) :=
    ringAttn_reduce2_pm_opaque pm initPM 965
      { rank := 0, op := "OpName.FW_norm_linear", ins := [9519, 5301], outs := [9525] }
      9519 5301 9525 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 9519 5301 9525)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9526
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9520) (denoteGraph_ringAttn pm initPM 5301) :=
    ringAttn_reduce2_pm_opaque pm initPM 969
      { rank := 1, op := "OpName.FW_norm_linear", ins := [9520, 5301], outs := [9526] }
      9520 5301 9526 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 9520 5301 9526)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5302
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9525, denoteGraph_ringAttn pm initPM 9526] := by
    rw [rSM, hval14, hw5301, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs9519 hs9520 hpw5301,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9525).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs9519 hpw5301
  have hsp1 : (denoteGraph_ringAttn pm initPM 9526).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs9520 hpw5301
  have hshape : (denoteGraph_ringAttn sm initSM 5302).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5302 5302 9525 9526 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L12 top-k routing (`5303`/`5304`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`9525`/`9526`) directly. -/

/-- Shared L12 top-k core: `5302` (full logits) is the dim-0 gather of the two
    per-rank shards `9525`/`9526`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L12 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 5302
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 9525, denoteGraph_ringAttn pm initPM 9526]
      ∧ (denoteGraph_ringAttn sm initSM 5302).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 9525).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 9526).shape = [2048, 64]
      ∧ ((sm.nodes.take 456).foldl (applyNodeRingAttn sm) initSM 5302).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 973).foldl (applyNodeRingAttn pm) initPM 9525).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 977).foldl (applyNodeRingAttn pm) initPM 9526).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs9525, hs9526⟩ := twoTp_gather _ _ intermediateGoal_5302 5302 9525 9526
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5302_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs5302sm : (denoteGraph_ringAttn sm initSM 5302).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs9525])]
    simp [List.set, List.getD]
  have hpre5302sm : denoteGraph_ringAttn sm initSM 5302
      = (sm.nodes.take 456).foldl (applyNodeRingAttn sm) initSM 5302 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5302 456 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 456).foldl (applyNodeRingAttn sm) initSM 5302).shape.reverse.head? = some 64 := by
    rw [← hpre5302sm, hs5302sm]; rfl
  have hpre9525 : denoteGraph_ringAttn pm initPM 9525
      = (pm.nodes.take 973).foldl (applyNodeRingAttn pm) initPM 9525 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9525 973 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 973).foldl (applyNodeRingAttn pm) initPM 9525).shape.reverse.head? = some 64 := by
    rw [← hpre9525, hs9525]; rfl
  have hpre9526 : denoteGraph_ringAttn pm initPM 9526
      = (pm.nodes.take 977).foldl (applyNodeRingAttn pm) initPM 9526 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9526 977 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 977).foldl (applyNodeRingAttn pm) initPM 9526).shape.reverse.head? = some 64 := by
    rw [← hpre9526, hs9526]; rfl
  exact ⟨hbr16, hs5302sm, hs9525, hs9526, hlastSM, hlast271, hlast275⟩

/-- 5303 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5303_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5303
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5302sm, hs9525, hs9526, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L12 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5303
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5302) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 456
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5302], outs := [5303, 5304, 5305], params := [8, 1] }
      5302 5303 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 456).foldl (applyNodeRingAttn sm) initSM) 0 5302 5303 5304 5305 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9527
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9525) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 973
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9525], outs := [9527, 9529, 9531], params := [8, 1] }
      9525 9527 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 973).foldl (applyNodeRingAttn pm) initPM) 0 9525 9527 9529 9531 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9528
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9526) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 977
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9526], outs := [9528, 9530, 9532], params := [8, 1] }
      9526 9528 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 977).foldl (applyNodeRingAttn pm) initPM) 1 9526 9528 9530 9532 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5303
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9527, denoteGraph_ringAttn pm initPM 9528] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9525 hs9526,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5303).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs5302sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9527).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9525]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9528).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9526]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5303 5303 9527 9528 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5304 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5304_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5304
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5302sm, hs9525, hs9526, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L12 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5304
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5302) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 456
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5302], outs := [5303, 5304, 5305], params := [8, 1] }
      5302 5304 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 456).foldl (applyNodeRingAttn sm) initSM) 0 5302 5303 5304 5305 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9529
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9525) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 973
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9525], outs := [9527, 9529, 9531], params := [8, 1] }
      9525 9529 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 973).foldl (applyNodeRingAttn pm) initPM) 0 9525 9527 9529 9531 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9530
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9526) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 977
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9526], outs := [9528, 9530, 9532], params := [8, 1] }
      9526 9530 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 977).foldl (applyNodeRingAttn pm) initPM) 1 9526 9528 9530 9532 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5304
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9529, denoteGraph_ringAttn pm initPM 9530] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9525 hs9526,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5304).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs5302sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9529).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9525]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9530).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9526]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5304 5304 9529 9530 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L12 router expert branches — reshape (`5309`/`5314`/`5318`) of the
    `mref5` copies (positions 2/3/4) of `5299`, all identity 2-tp views. -/

/-- 5309 — 2-tp identity reshape of `mref5-pos2(5299)` (SM node 215, PM 490/494). -/
theorem recon_intermediateGoal_5309_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5309
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9517, hs9518⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5299sm : (denoteGraph_ringAttn sm initSM 5299).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9517])]
    simp [List.set, List.getD]
  have s7995 : denoteGraph_ringAttn sm initSM 7995 = id (denoteGraph_ringAttn sm initSM 5299) :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299],
        outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7995 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15706 : denoteGraph_ringAttn pm initPM 15706 = id (denoteGraph_ringAttn pm initPM 9517) :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517],
        outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15706 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15729 : denoteGraph_ringAttn pm initPM 15729 = id (denoteGraph_ringAttn pm initPM 9518) :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518],
        outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15729 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7995 p15706 p15729
  have hs7995 : (denoteGraph_ringAttn sm initSM 7995).shape = [4096, 1024] := by rw [s7995]; exact hs5299sm
  have hs15706 : (denoteGraph_ringAttn pm initPM 15706).shape = [2048, 1024] := by rw [p15706]; exact hs9517
  have hs15729 : (denoteGraph_ringAttn pm initPM 15729).shape = [2048, 1024] := by rw [p15729]; exact hs9518
  have hbrm : denoteGraph_ringAttn sm initSM 7995
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15706, denoteGraph_ringAttn pm initPM 15729] := by
    rw [s7995, hbr13, ← p15706, ← p15729]
  have rSM : denoteGraph_ringAttn sm initSM 5309
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7995) :=
    ringAttn_reduce1_pm_opaque sm initSM 449
      { rank := 0, op := "OpName.FW_reshape", ins := [7995], outs := [5309], params := [4096, 1024] }
      7995 5309 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7995 5309)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9539
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15706) :=
    ringAttn_reduce1_pm_opaque pm initPM 958
      { rank := 0, op := "OpName.FW_reshape", ins := [15706], outs := [9539], params := [2048, 1024] }
      15706 9539 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15706 9539)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9540
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15729) :=
    ringAttn_reduce1_pm_opaque pm initPM 962
      { rank := 1, op := "OpName.FW_reshape", ins := [15729], outs := [9540], params := [2048, 1024] }
      15729 9540 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15729 9540)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 9539 = denoteGraph_ringAttn pm initPM 15706 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15706]
  have h66 : denoteGraph_ringAttn pm initPM 9540 = denoteGraph_ringAttn pm initPM 15729 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15729]
  have hval : denoteGraph_ringAttn sm initSM 5309
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9539, denoteGraph_ringAttn pm initPM 9540] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7995, hbrm, hnr, ← h65, ← h66]
  have hs9539 : (denoteGraph_ringAttn pm initPM 9539).shape = [2048, 1024] := by rw [h65]; exact hs15706
  have hs9540 : (denoteGraph_ringAttn pm initPM 9540).shape = [2048, 1024] := by rw [h66]; exact hs15729
  have hs5309 : (denoteGraph_ringAttn sm initSM 5309).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7995]; exact hs7995
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5309 5309 9539 9540 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5309 hs9539 hs9540

/-- 5314 — 2-tp identity reshape of `mref5-pos3(5299)` (SM node 216, PM 491/495). -/
theorem recon_intermediateGoal_5314_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5314
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9517, hs9518⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5299sm : (denoteGraph_ringAttn sm initSM 5299).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9517])]
    simp [List.set, List.getD]
  have s7999 : denoteGraph_ringAttn sm initSM 7999 = id (denoteGraph_ringAttn sm initSM 5299) :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299],
        outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7999 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15710 : denoteGraph_ringAttn pm initPM 15710 = id (denoteGraph_ringAttn pm initPM 9517) :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517],
        outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15710 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15733 : denoteGraph_ringAttn pm initPM 15733 = id (denoteGraph_ringAttn pm initPM 9518) :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518],
        outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15733 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7999 p15710 p15733
  have hs7999 : (denoteGraph_ringAttn sm initSM 7999).shape = [4096, 1024] := by rw [s7999]; exact hs5299sm
  have hs15710 : (denoteGraph_ringAttn pm initPM 15710).shape = [2048, 1024] := by rw [p15710]; exact hs9517
  have hs15733 : (denoteGraph_ringAttn pm initPM 15733).shape = [2048, 1024] := by rw [p15733]; exact hs9518
  have hbrm : denoteGraph_ringAttn sm initSM 7999
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15710, denoteGraph_ringAttn pm initPM 15733] := by
    rw [s7999, hbr13, ← p15710, ← p15733]
  have rSM : denoteGraph_ringAttn sm initSM 5314
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7999) :=
    ringAttn_reduce1_pm_opaque sm initSM 450
      { rank := 0, op := "OpName.FW_reshape", ins := [7999], outs := [5314], params := [4096, 1024] }
      7999 5314 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7999 5314)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9553
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15710) :=
    ringAttn_reduce1_pm_opaque pm initPM 959
      { rank := 0, op := "OpName.FW_reshape", ins := [15710], outs := [9553], params := [2048, 1024] }
      15710 9553 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15710 9553)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9554
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15733) :=
    ringAttn_reduce1_pm_opaque pm initPM 963
      { rank := 1, op := "OpName.FW_reshape", ins := [15733], outs := [9554], params := [2048, 1024] }
      15733 9554 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15733 9554)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 9553 = denoteGraph_ringAttn pm initPM 15710 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15710]
  have h80 : denoteGraph_ringAttn pm initPM 9554 = denoteGraph_ringAttn pm initPM 15733 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15733]
  have hval : denoteGraph_ringAttn sm initSM 5314
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9553, denoteGraph_ringAttn pm initPM 9554] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7999, hbrm, hnr, ← h79, ← h80]
  have hs9553 : (denoteGraph_ringAttn pm initPM 9553).shape = [2048, 1024] := by rw [h79]; exact hs15710
  have hs9554 : (denoteGraph_ringAttn pm initPM 9554).shape = [2048, 1024] := by rw [h80]; exact hs15733
  have hs5314 : (denoteGraph_ringAttn sm initSM 5314).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7999]; exact hs7999
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5314 5314 9553 9554 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5314 hs9553 hs9554

/-- 5318 — 2-tp identity reshape of `mref5-pos4(5299)` (SM node 217, PM 492/496). -/
theorem recon_intermediateGoal_5318_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5318
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9517, hs9518⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5299sm : (denoteGraph_ringAttn sm initSM 5299).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9517])]
    simp [List.set, List.getD]
  have s8003 : denoteGraph_ringAttn sm initSM 8003 = id (denoteGraph_ringAttn sm initSM 5299) :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299],
        outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 8003 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15714 : denoteGraph_ringAttn pm initPM 15714 = id (denoteGraph_ringAttn pm initPM 9517) :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517],
        outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15714 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15737 : denoteGraph_ringAttn pm initPM 15737 = id (denoteGraph_ringAttn pm initPM 9518) :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518],
        outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15737 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8003 p15714 p15737
  have hs8003 : (denoteGraph_ringAttn sm initSM 8003).shape = [4096, 1024] := by rw [s8003]; exact hs5299sm
  have hs15714 : (denoteGraph_ringAttn pm initPM 15714).shape = [2048, 1024] := by rw [p15714]; exact hs9517
  have hs15737 : (denoteGraph_ringAttn pm initPM 15737).shape = [2048, 1024] := by rw [p15737]; exact hs9518
  have hbrm : denoteGraph_ringAttn sm initSM 8003
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15714, denoteGraph_ringAttn pm initPM 15737] := by
    rw [s8003, hbr13, ← p15714, ← p15737]
  have rSM : denoteGraph_ringAttn sm initSM 5318
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 8003) :=
    ringAttn_reduce1_pm_opaque sm initSM 451
      { rank := 0, op := "OpName.FW_reshape", ins := [8003], outs := [5318], params := [4096, 1024] }
      8003 5318 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 8003 5318)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9571
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15714) :=
    ringAttn_reduce1_pm_opaque pm initPM 960
      { rank := 0, op := "OpName.FW_reshape", ins := [15714], outs := [9571], params := [2048, 1024] }
      15714 9571 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15714 9571)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9572
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15737) :=
    ringAttn_reduce1_pm_opaque pm initPM 964
      { rank := 1, op := "OpName.FW_reshape", ins := [15737], outs := [9572], params := [2048, 1024] }
      15737 9572 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15737 9572)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 9571 = denoteGraph_ringAttn pm initPM 15714 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15714]
  have h98 : denoteGraph_ringAttn pm initPM 9572 = denoteGraph_ringAttn pm initPM 15737 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15737]
  have hval : denoteGraph_ringAttn sm initSM 5318
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9571, denoteGraph_ringAttn pm initPM 9572] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs8003, hbrm, hnr, ← h97, ← h98]
  have hs9571 : (denoteGraph_ringAttn pm initPM 9571).shape = [2048, 1024] := by rw [h97]; exact hs15714
  have hs9572 : (denoteGraph_ringAttn pm initPM 9572).shape = [2048, 1024] := by rw [h98]; exact hs15737
  have hs5318 : (denoteGraph_ringAttn sm initSM 5318).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs8003]; exact hs8003
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5318 5318 9571 9572 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5318 hs9571 hs9572

/-! ### L12 router expert mixlins (`5311`/`5316`/`5320`), 2-tp. -/

/-- 5311 — 2-tp `fw_linear(5309, 5310)`, weight `5310 : [1, 1024]` → `[4096, 1]`
    (SM node 219, PM nodes 498/502). -/
theorem recon_intermediateGoal_5311_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5311
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs9539, hs9540⟩ := twoTp_gather _ _ intermediateGoal_5309 5309 9539 9540
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5309_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5310 : denoteGraph_ringAttn sm initSM 5310 = denoteGraph_ringAttn pm initPM 5310 :=
    veq_weight_ring initSM initPM hInit initGoal_5310 (by native_decide) 5310
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5310 : (denoteGraph_ringAttn pm initPM 5310).shape = [1, 1024] := by
    rw [← hw5310]
    exact shape_weight_ring initSM initPM hInit initGoal_5310 (by native_decide) 5310 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5311
      = fw_linear (denoteGraph_ringAttn sm initSM 5309) (denoteGraph_ringAttn sm initSM 5310) :=
    ringAttn_reduce2_pm_opaque sm initSM 453
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5309, 5310], outs := [5311] }
      5309 5310 5311 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5309 5310 5311)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9543
      = fw_linear (denoteGraph_ringAttn pm initPM 9539) (denoteGraph_ringAttn pm initPM 5310) :=
    ringAttn_reduce2_pm_opaque pm initPM 966
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9539, 5310], outs := [9543] }
      9539 5310 9543 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9539 5310 9543)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9544
      = fw_linear (denoteGraph_ringAttn pm initPM 9540) (denoteGraph_ringAttn pm initPM 5310) :=
    ringAttn_reduce2_pm_opaque pm initPM 970
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9540, 5310], outs := [9544] }
      9540 5310 9544 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9540 5310 9544)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5311
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9543, denoteGraph_ringAttn pm initPM 9544] := by
    rw [rSM, hval23, hw5310, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs9539 hs9540 hpw5310,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9543).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9539 hpw5310
  have hsp1 : (denoteGraph_ringAttn pm initPM 9544).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9540 hpw5310
  have hshape : (denoteGraph_ringAttn sm initSM 5311).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5311 5311 9543 9544 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5316 — 2-tp `fw_linear(5314, 5315)`, weight `5315 : [512, 1024]` → `[4096, 512]`
    (SM node 220, PM nodes 499/503). -/
theorem recon_intermediateGoal_5316_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5316
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs9553, hs9554⟩ := twoTp_gather _ _ intermediateGoal_5314 5314 9553 9554
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5314_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5315 : denoteGraph_ringAttn sm initSM 5315 = denoteGraph_ringAttn pm initPM 5315 :=
    veq_weight_ring initSM initPM hInit initGoal_5315 (by native_decide) 5315
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5315 : (denoteGraph_ringAttn pm initPM 5315).shape = [512, 1024] := by
    rw [← hw5315]
    exact shape_weight_ring initSM initPM hInit initGoal_5315 (by native_decide) 5315 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5316
      = fw_linear (denoteGraph_ringAttn sm initSM 5314) (denoteGraph_ringAttn sm initSM 5315) :=
    ringAttn_reduce2_pm_opaque sm initSM 454
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5314, 5315], outs := [5316] }
      5314 5315 5316 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5314 5315 5316)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9557
      = fw_linear (denoteGraph_ringAttn pm initPM 9553) (denoteGraph_ringAttn pm initPM 5315) :=
    ringAttn_reduce2_pm_opaque pm initPM 967
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9553, 5315], outs := [9557] }
      9553 5315 9557 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9553 5315 9557)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9558
      = fw_linear (denoteGraph_ringAttn pm initPM 9554) (denoteGraph_ringAttn pm initPM 5315) :=
    ringAttn_reduce2_pm_opaque pm initPM 971
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9554, 5315], outs := [9558] }
      9554 5315 9558 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9554 5315 9558)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5316
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9557, denoteGraph_ringAttn pm initPM 9558] := by
    rw [rSM, hval28, hw5315, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs9553 hs9554 hpw5315,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9557).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9553 hpw5315
  have hsp1 : (denoteGraph_ringAttn pm initPM 9558).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9554 hpw5315
  have hshape : (denoteGraph_ringAttn sm initSM 5316).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5316 5316 9557 9558 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5320 — 2-tp `fw_linear(5318, 5319)`, weight `5319 : [512, 1024]` → `[4096, 512]`
    (SM node 221, PM nodes 500/504). -/
theorem recon_intermediateGoal_5320_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5320
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs9571, hs9572⟩ := twoTp_gather _ _ intermediateGoal_5318 5318 9571 9572
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5318_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5319 : denoteGraph_ringAttn sm initSM 5319 = denoteGraph_ringAttn pm initPM 5319 :=
    veq_weight_ring initSM initPM hInit initGoal_5319 (by native_decide) 5319
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5319 : (denoteGraph_ringAttn pm initPM 5319).shape = [512, 1024] := by
    rw [← hw5319]
    exact shape_weight_ring initSM initPM hInit initGoal_5319 (by native_decide) 5319 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5320
      = fw_linear (denoteGraph_ringAttn sm initSM 5318) (denoteGraph_ringAttn sm initSM 5319) :=
    ringAttn_reduce2_pm_opaque sm initSM 455
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5318, 5319], outs := [5320] }
      5318 5319 5320 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5318 5319 5320)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9575
      = fw_linear (denoteGraph_ringAttn pm initPM 9571) (denoteGraph_ringAttn pm initPM 5319) :=
    ringAttn_reduce2_pm_opaque pm initPM 968
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9571, 5319], outs := [9575] }
      9571 5319 9575 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9571 5319 9575)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9576
      = fw_linear (denoteGraph_ringAttn pm initPM 9572) (denoteGraph_ringAttn pm initPM 5319) :=
    ringAttn_reduce2_pm_opaque pm initPM 972
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9572, 5319], outs := [9576] }
      9572 5319 9576 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9572 5319 9576)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5320
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9575, denoteGraph_ringAttn pm initPM 9576] := by
    rw [rSM, hval32, hw5319, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs9571 hs9572 hpw5319,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9575).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9571 hpw5319
  have hsp1 : (denoteGraph_ringAttn pm initPM 9576).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9572 hpw5319
  have hshape : (denoteGraph_ringAttn sm initSM 5320).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5320 5320 9575 9576 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L12 router expert views (`5312`/`5317`/`5321`), identity 2-tp views. -/

/-- 5312 — 2-tp identity view of `5311` → `[4096, 1]` (SM node 223, PM 506/510). -/
theorem recon_intermediateGoal_5312_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5312
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs9543, hs9544⟩ := twoTp_gather _ _ intermediateGoal_5311 5311 9543 9544
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5311_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5311 : (denoteGraph_ringAttn sm initSM 5311).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs9543])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5312
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 5311) :=
    ringAttn_reduce1_pm_opaque sm initSM 457
      { rank := 0, op := "OpName.FW_view", ins := [5311], outs := [5312], params := [4096, 1] }
      5311 5312 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 5311 5312)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9549
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9543) :=
    ringAttn_reduce1_pm_opaque pm initPM 974
      { rank := 0, op := "OpName.FW_view", ins := [9543], outs := [9549], params := [2048, 1] }
      9543 9549 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 9543 9549)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9550
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9544) :=
    ringAttn_reduce1_pm_opaque pm initPM 978
      { rank := 1, op := "OpName.FW_view", ins := [9544], outs := [9550], params := [2048, 1] }
      9544 9550 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 9544 9550)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 9549 = denoteGraph_ringAttn pm initPM 9543 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs9543]
  have h76 : denoteGraph_ringAttn pm initPM 9550 = denoteGraph_ringAttn pm initPM 9544 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs9544]
  have hval : denoteGraph_ringAttn sm initSM 5312
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9549, denoteGraph_ringAttn pm initPM 9550] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5311, hval25, hnr, ← h75, ← h76]
  have hs9549 : (denoteGraph_ringAttn pm initPM 9549).shape = [2048, 1] := by rw [h75]; exact hs9543
  have hs9550 : (denoteGraph_ringAttn pm initPM 9550).shape = [2048, 1] := by rw [h76]; exact hs9544
  have hs5312 : (denoteGraph_ringAttn sm initSM 5312).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5311]; exact hs5311
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5312 5312 9549 9550 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5312 hs9549 hs9550

/-- 5317 — 2-tp identity view of `5316` → `[4096, 512]` (SM node 224, PM 507/511). -/
theorem recon_intermediateGoal_5317_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5317
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs9557, hs9558⟩ := twoTp_gather _ _ intermediateGoal_5316 5316 9557 9558
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5316_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5316 : (denoteGraph_ringAttn sm initSM 5316).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9557])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5317
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5316) :=
    ringAttn_reduce1_pm_opaque sm initSM 458
      { rank := 0, op := "OpName.FW_view", ins := [5316], outs := [5317], params := [4096, 512] }
      5316 5317 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5316 5317)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9567
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9557) :=
    ringAttn_reduce1_pm_opaque pm initPM 975
      { rank := 0, op := "OpName.FW_view", ins := [9557], outs := [9567], params := [2048, 512] }
      9557 9567 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9557 9567)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9568
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9558) :=
    ringAttn_reduce1_pm_opaque pm initPM 979
      { rank := 1, op := "OpName.FW_view", ins := [9558], outs := [9568], params := [2048, 512] }
      9558 9568 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9558 9568)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 9567 = denoteGraph_ringAttn pm initPM 9557 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9557]
  have h94 : denoteGraph_ringAttn pm initPM 9568 = denoteGraph_ringAttn pm initPM 9558 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9558]
  have hval : denoteGraph_ringAttn sm initSM 5317
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9567, denoteGraph_ringAttn pm initPM 9568] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5316, hval30, hnr, ← h93, ← h94]
  have hs9567 : (denoteGraph_ringAttn pm initPM 9567).shape = [2048, 512] := by rw [h93]; exact hs9557
  have hs9568 : (denoteGraph_ringAttn pm initPM 9568).shape = [2048, 512] := by rw [h94]; exact hs9558
  have hs5317 : (denoteGraph_ringAttn sm initSM 5317).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5316]; exact hs5316
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5317 5317 9567 9568 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5317 hs9567 hs9568

/-- 5321 — 2-tp identity view of `5320` → `[4096, 512]` (SM node 225, PM 508/512). -/
theorem recon_intermediateGoal_5321_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5321
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs9575, hs9576⟩ := twoTp_gather _ _ intermediateGoal_5320 5320 9575 9576
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5320_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5320 : (denoteGraph_ringAttn sm initSM 5320).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9575])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5321
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5320) :=
    ringAttn_reduce1_pm_opaque sm initSM 459
      { rank := 0, op := "OpName.FW_view", ins := [5320], outs := [5321], params := [4096, 512] }
      5320 5321 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5320 5321)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9585
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9575) :=
    ringAttn_reduce1_pm_opaque pm initPM 976
      { rank := 0, op := "OpName.FW_view", ins := [9575], outs := [9585], params := [2048, 512] }
      9575 9585 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9575 9585)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9586
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9576) :=
    ringAttn_reduce1_pm_opaque pm initPM 980
      { rank := 1, op := "OpName.FW_view", ins := [9576], outs := [9586], params := [2048, 512] }
      9576 9586 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9576 9586)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 9585 = denoteGraph_ringAttn pm initPM 9575 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9575]
  have h12 : denoteGraph_ringAttn pm initPM 9586 = denoteGraph_ringAttn pm initPM 9576 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9576]
  have hval : denoteGraph_ringAttn sm initSM 5321
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9585, denoteGraph_ringAttn pm initPM 9586] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5320, hval34, hnr, ← h11, ← h12]
  have hs9585 : (denoteGraph_ringAttn pm initPM 9585).shape = [2048, 512] := by rw [h11]; exact hs9575
  have hs9586 : (denoteGraph_ringAttn pm initPM 9586).shape = [2048, 512] := by rw [h12]; exact hs9576
  have hs5321 : (denoteGraph_ringAttn sm initSM 5321).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5320]; exact hs5320
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5321 5321 9585 9586 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5321 hs9585 hs9586

/-! ### L12 MoE gate/expert branch (`5313` sigmoid, `5322` swiglu, `5323` reshape,
    `5325` mixlin, `5326` view, `5327` broadcast-mul), all 2-tp shard-direct. -/

/-- 5313 — 2-tp `fw_sigmoid(5312)` → `[4096, 1]` (SM node 227, PM 514/517). -/
theorem recon_intermediateGoal_5313_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5313
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs9549, hs9550⟩ := twoTp_gather _ _ intermediateGoal_5312 5312 9549 9550
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5312_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5313 = fw_sigmoid (denoteGraph_ringAttn sm initSM 5312) :=
    ringAttn_reduce1_pm_opaque sm initSM 461
      { rank := 0, op := "OpName.FW_sigmoid", ins := [5312], outs := [5313] }
      5312 5313 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 5312 5313 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9551 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9549) :=
    ringAttn_reduce1_pm_opaque pm initPM 982
      { rank := 0, op := "OpName.FW_sigmoid", ins := [9549], outs := [9551] }
      9549 9551 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 9549 9551 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9552 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9550) :=
    ringAttn_reduce1_pm_opaque pm initPM 985
      { rank := 1, op := "OpName.FW_sigmoid", ins := [9550], outs := [9552] }
      9550 9552 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 9550 9552 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5313
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9551, denoteGraph_ringAttn pm initPM 9552] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs9549 hs9550, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5313).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs9549])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9551).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs9549
  have hsp1 : (denoteGraph_ringAttn pm initPM 9552).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs9550
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5313 5313 9551 9552 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5322 — 2-tp `fw_swiglu(5317, 5321)` → `[4096, 512]` (SM node 228, PM 515/518). -/
theorem recon_intermediateGoal_5322_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5322
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs9567, hs9568⟩ := twoTp_gather _ _ intermediateGoal_5317 5317 9567 9568
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5317_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs9585, hs9586⟩ := twoTp_gather _ _ intermediateGoal_5321 5321 9585 9586
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5321_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5322
      = fw_swiglu (denoteGraph_ringAttn sm initSM 5317) (denoteGraph_ringAttn sm initSM 5321) :=
    ringAttn_reduce2_pm_opaque sm initSM 462
      { rank := 0, op := "OpName.FW_swiglu", ins := [5317, 5321], outs := [5322] }
      5317 5321 5322 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 5317 5321 5322 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9589
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9567) (denoteGraph_ringAttn pm initPM 9585) :=
    ringAttn_reduce2_pm_opaque pm initPM 983
      { rank := 0, op := "OpName.FW_swiglu", ins := [9567, 9585], outs := [9589] }
      9567 9585 9589 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 9567 9585 9589 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9590
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9568) (denoteGraph_ringAttn pm initPM 9586) :=
    ringAttn_reduce2_pm_opaque pm initPM 986
      { rank := 1, op := "OpName.FW_swiglu", ins := [9568, 9586], outs := [9590] }
      9568 9586 9590 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 9568 9586 9590 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5322
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9589, denoteGraph_ringAttn pm initPM 9590] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs9567 hs9568 hs9585 hs9586,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5322).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9585])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9589).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9585
  have hsp1 : (denoteGraph_ringAttn pm initPM 9590).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9586
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5322 5322 9589 9590 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5323 — 2-tp identity reshape of `5322` → `[4096, 512]` (SM node 229, PM 519/520). -/
theorem recon_intermediateGoal_5323_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5323
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs9589, hs9590⟩ := twoTp_gather _ _ intermediateGoal_5322 5322 9589 9590
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5322_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5322 : (denoteGraph_ringAttn sm initSM 5322).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9589])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5323
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5322) :=
    ringAttn_reduce1_pm_opaque sm initSM 463
      { rank := 0, op := "OpName.FW_reshape", ins := [5322], outs := [5323], params := [4096, 512] }
      5322 5323 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5322 5323)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9591
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9589) :=
    ringAttn_reduce1_pm_opaque pm initPM 987
      { rank := 0, op := "OpName.FW_reshape", ins := [9589], outs := [9591], params := [2048, 512] }
      9589 9591 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9589 9591)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9592
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9590) :=
    ringAttn_reduce1_pm_opaque pm initPM 988
      { rank := 1, op := "OpName.FW_reshape", ins := [9590], outs := [9592], params := [2048, 512] }
      9590 9592 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9590 9592)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 9591 = denoteGraph_ringAttn pm initPM 9589 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9589]
  have h18 : denoteGraph_ringAttn pm initPM 9592 = denoteGraph_ringAttn pm initPM 9590 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9590]
  have hval : denoteGraph_ringAttn sm initSM 5323
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9591, denoteGraph_ringAttn pm initPM 9592] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5322, hval36, hnr, ← h17, ← h18]
  have hs9591 : (denoteGraph_ringAttn pm initPM 9591).shape = [2048, 512] := by rw [h17]; exact hs9589
  have hs9592 : (denoteGraph_ringAttn pm initPM 9592).shape = [2048, 512] := by rw [h18]; exact hs9590
  have hs5323 : (denoteGraph_ringAttn sm initSM 5323).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5322]; exact hs5322
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5323 5323 9591 9592 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5323 hs9591 hs9592

/-- 5325 — 2-tp `fw_linear(5323, 5324)`, weight `5324 : [1024, 512]` → `[4096, 1024]`
    (SM node 230, PM 521/522). -/
theorem recon_intermediateGoal_5325_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5325
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs9591, hs9592⟩ := twoTp_gather _ _ intermediateGoal_5323 5323 9591 9592
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5323_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5324 : denoteGraph_ringAttn sm initSM 5324 = denoteGraph_ringAttn pm initPM 5324 :=
    veq_weight_ring initSM initPM hInit initGoal_5324 (by native_decide) 5324
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5324 : (denoteGraph_ringAttn pm initPM 5324).shape = [1024, 512] := by
    rw [← hw5324]
    exact shape_weight_ring initSM initPM hInit initGoal_5324 (by native_decide) 5324 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5325
      = fw_linear (denoteGraph_ringAttn sm initSM 5323) (denoteGraph_ringAttn sm initSM 5324) :=
    ringAttn_reduce2_pm_opaque sm initSM 464
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5323, 5324], outs := [5325] }
      5323 5324 5325 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5323 5324 5325)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9597
      = fw_linear (denoteGraph_ringAttn pm initPM 9591) (denoteGraph_ringAttn pm initPM 5324) :=
    ringAttn_reduce2_pm_opaque pm initPM 989
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9591, 5324], outs := [9597] }
      9591 5324 9597 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9591 5324 9597)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9598
      = fw_linear (denoteGraph_ringAttn pm initPM 9592) (denoteGraph_ringAttn pm initPM 5324) :=
    ringAttn_reduce2_pm_opaque pm initPM 990
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9592, 5324], outs := [9598] }
      9592 5324 9598 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9592 5324 9598)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5325
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9597, denoteGraph_ringAttn pm initPM 9598] := by
    rw [rSM, hval37, hw5324, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs9591 hs9592 hpw5324,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9597).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9591 hpw5324
  have hsp1 : (denoteGraph_ringAttn pm initPM 9598).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9592 hpw5324
  have hshape : (denoteGraph_ringAttn sm initSM 5325).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5325 5325 9597 9598 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5326 — 2-tp identity view of `5325` → `[4096, 1024]` (SM node 231, PM 523/524). -/
theorem recon_intermediateGoal_5326_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5326
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs9597, hs9598⟩ := twoTp_gather _ _ intermediateGoal_5325 5325 9597 9598
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5325_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5325 : (denoteGraph_ringAttn sm initSM 5325).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9597])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5326
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5325) :=
    ringAttn_reduce1_pm_opaque sm initSM 465
      { rank := 0, op := "OpName.FW_view", ins := [5325], outs := [5326], params := [4096, 1024] }
      5325 5326 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5325 5326)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9607
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9597) :=
    ringAttn_reduce1_pm_opaque pm initPM 991
      { rank := 0, op := "OpName.FW_view", ins := [9597], outs := [9607], params := [2048, 1024] }
      9597 9607 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9597 9607)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9608
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9598) :=
    ringAttn_reduce1_pm_opaque pm initPM 992
      { rank := 1, op := "OpName.FW_view", ins := [9598], outs := [9608], params := [2048, 1024] }
      9598 9608 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9598 9608)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 9607 = denoteGraph_ringAttn pm initPM 9597 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9597]
  have h34 : denoteGraph_ringAttn pm initPM 9608 = denoteGraph_ringAttn pm initPM 9598 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9598]
  have hval : denoteGraph_ringAttn sm initSM 5326
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9607, denoteGraph_ringAttn pm initPM 9608] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5325, hval39, hnr, ← h33, ← h34]
  have hs9607 : (denoteGraph_ringAttn pm initPM 9607).shape = [2048, 1024] := by rw [h33]; exact hs9597
  have hs9608 : (denoteGraph_ringAttn pm initPM 9608).shape = [2048, 1024] := by rw [h34]; exact hs9598
  have hs5326 : (denoteGraph_ringAttn sm initSM 5326).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5325]; exact hs5325
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5326 5326 9607 9608 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5326 hs9607 hs9608

/-- 5327 — 2-tp broadcast `mul(5313, 5326)` → `[4096, 1024]` (SM node 232, PM 525/526). -/
theorem recon_intermediateGoal_5327_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5327
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_5313 5313 9551 9552
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5313_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_5326 5326 9607 9608
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5326_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5327
      = elemwiseMul (denoteGraph_ringAttn sm initSM 5313) (denoteGraph_ringAttn sm initSM 5326) :=
    ringAttn_reduce2_pm_opaque sm initSM 466
      { rank := 0, op := "OpName.FW_mul", ins := [5313, 5326], outs := [5327] }
      5313 5326 5327 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 5313 5326 5327)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9611
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9551) (denoteGraph_ringAttn pm initPM 9607) :=
    ringAttn_reduce2_pm_opaque pm initPM 993
      { rank := 0, op := "OpName.FW_mul", ins := [9551, 9607], outs := [9611] }
      9551 9607 9611 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 9551 9607 9611)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9612
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9552) (denoteGraph_ringAttn pm initPM 9608) :=
    ringAttn_reduce2_pm_opaque pm initPM 994
      { rank := 1, op := "OpName.FW_mul", ins := [9552, 9608], outs := [9612] }
      9552 9608 9612 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 9552 9608 9612)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5327
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9611, denoteGraph_ringAttn pm initPM 9612] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 5327).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 5313).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 5326).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 9611).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 9612).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5327 5327 9611 9612 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 5308 — layer-12 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 5308 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`9537`), rank 1 →
    `[32, 64)` (`9538`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `9529`/`9530` are expert-local (the
    `wf5308_hdisjA/B` fields).  Token input `7991 = mref5-pos1(5299)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 226, PM nodes 513/516). -/
theorem recon_intermediateGoal_5308_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5308
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 8661 = mref5-pos1(5299).
  obtain ⟨hbr13, hs9517, hs9518⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8661 : denoteGraph_ringAttn sm initSM 7991 = id (denoteGraph_ringAttn sm initSM 5299) :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299],
        outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7991 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15702 : denoteGraph_ringAttn pm initPM 15702 = id (denoteGraph_ringAttn pm initPM 9517) :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517],
        outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15702 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15725 : denoteGraph_ringAttn pm initPM 15725 = id (denoteGraph_ringAttn pm initPM 9518) :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518],
        outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15725 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8661 p15702 p15725
  have hsInA : (denoteGraph_ringAttn pm initPM 15702).shape = [2048, 1024] := by
    rw [p15702]; exact hs9517
  have hsInB : (denoteGraph_ringAttn pm initPM 15725).shape = [2048, 1024] := by
    rw [p15725]; exact hs9518
  have hbrIn : denoteGraph_ringAttn sm initSM 7991
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 15702, denoteGraph_ringAttn pm initPM 15725] := by
    rw [s8661, hbr13, hnr, ← p15702, ← p15725]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_5303 5303 9527 9528
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5303_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_5304 5304 9529 9530
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5304_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 5303
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9527, denoteGraph_ringAttn pm initPM 9528] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 5304
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9529, denoteGraph_ringAttn pm initPM 9530] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_5306
    (by native_decide) 5306 9533 9534 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_5307
    (by native_decide) 5307 9535 9536 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 9533).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5306 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5306, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9533 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 9534).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5306 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5306, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9534 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 9535).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5307 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5307, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9535 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 9536).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5307 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5307, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9536 (by native_decide)]; exact hs.2
  -- SM 5308 = full-range all2all (SM node 226).
  have hSMout : denoteGraph_ringAttn sm initSM 5308
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7991)
          (denoteGraph_ringAttn sm initSM 5303) (denoteGraph_ringAttn sm initSM 5304)
          (denoteGraph_ringAttn sm initSM 5306) (denoteGraph_ringAttn sm initSM 5307)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 460
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7991, 5303, 5304, 5306, 5307],
        outs := [5308], params := [64, 0, 64, 8] }
      7991 5303 5304 5306 5307 5308
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7991 5303 5304 5306 5307 5308 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9537 = rank-0 sharded-range all2all (PM node 513).
  have hP0 : denoteGraph_ringAttn pm initPM 9537
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15702)
          (denoteGraph_ringAttn pm initPM 9527) (denoteGraph_ringAttn pm initPM 9529)
          (denoteGraph_ringAttn pm initPM 9533) (denoteGraph_ringAttn pm initPM 9535)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 981
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15702, 9527, 9529, 9533, 9535],
        outs := [9537], params := [64, 0, 32, 8] }
      15702 9527 9529 9533 9535 9537
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 15702 9527 9529 9533 9535 9537 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9538 = rank-1 sharded-range all2all (PM node 516).
  have hP1 : denoteGraph_ringAttn pm initPM 9538
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15725)
          (denoteGraph_ringAttn pm initPM 9528) (denoteGraph_ringAttn pm initPM 9530)
          (denoteGraph_ringAttn pm initPM 9534) (denoteGraph_ringAttn pm initPM 9536)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 984
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15725, 9528, 9530, 9534, 9536],
        outs := [9538], params := [64, 32, 64, 8] }
      15725 9528 9530 9534 9536 9538
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 15725 9528 9530 9534 9536 9538 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 15702) (denoteGraph_ringAttn pm initPM 15725)
      (denoteGraph_ringAttn pm initPM 9527) (denoteGraph_ringAttn pm initPM 9528)
      (denoteGraph_ringAttn pm initPM 9529) (denoteGraph_ringAttn pm initPM 9530)
      (denoteGraph_ringAttn pm initPM 9533) (denoteGraph_ringAttn pm initPM 9534)
      (denoteGraph_ringAttn pm initPM 9535) (denoteGraph_ringAttn pm initPM 9536)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf5308_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf5308_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 5308
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9537, denoteGraph_ringAttn pm initPM 9538] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9537).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9538).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 5308).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5308 5308 9537 9538 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L12 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7980 — second position of the L12 pre-MoE residual `mref2(5297)` (2-tp, PM
    shards `15683`/`15691`).  Unlike L2's `7928` there is no gather-to-full/chunk
    because `5297` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 211, PM nodes 477/478). -/
theorem recon_intermediateGoal_7980_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7980
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs9513, hs9514⟩ := twoTp_gather _ _ intermediateGoal_5297 5297 9513 9514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5297_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8516 : denoteGraph_ringAttn sm initSM 7980 = id (denoteGraph_ringAttn sm initSM 5297) :=
    ringAttn_reduce1_pm_opaque sm initSM 445
      { rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] }
      5297 7980 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5297 7976 7980 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15683 : denoteGraph_ringAttn pm initPM 15683 = id (denoteGraph_ringAttn pm initPM 9513) :=
    ringAttn_reduce1_pm_opaque pm initPM 951
      { rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683], params := [2] }
      9513 15683 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9513 15679 15683 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15691 : denoteGraph_ringAttn pm initPM 15691 = id (denoteGraph_ringAttn pm initPM 9514) :=
    ringAttn_reduce1_pm_opaque pm initPM 952
      { rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691], params := [2] }
      9514 15691 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9514 15687 15691 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8516 p15683 p15691
  have hsp0 : (denoteGraph_ringAttn pm initPM 15683).shape = [2048, 1024] := by
    rw [p15683]; exact hs9513
  have hsp1 : (denoteGraph_ringAttn pm initPM 15691).shape = [2048, 1024] := by
    rw [p15691]; exact hs9514
  have hval : denoteGraph_ringAttn sm initSM 7980
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15683, denoteGraph_ringAttn pm initPM 15691] := by
    rw [s8516, hbr11, ← p15683, ← p15691]
  have hshape : (denoteGraph_ringAttn sm initSM 7980).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7980 7980 15683 15691 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5328 — post-MoE residual add `5308 + 5327` (2-tp, PM `9615`/`9616`). -/
theorem recon_intermediateGoal_5328_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5328
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs9537, hs9538⟩ := twoTp_gather _ _ intermediateGoal_5308 5308 9537 9538
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5308_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs9611, hs9612⟩ := twoTp_gather _ _ intermediateGoal_5327 5327 9611 9612
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5327_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5328
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 5308) (denoteGraph_ringAttn sm initSM 5327) :=
    ringAttn_reduce2_pm_opaque sm initSM 467
      { rank := 0, op := "OpName.FW_add", ins := [5308, 5327], outs := [5328] }
      5308 5327 5328 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 5308 5327 5328)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9615
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9537) (denoteGraph_ringAttn pm initPM 9611) :=
    ringAttn_reduce2_pm_opaque pm initPM 995
      { rank := 0, op := "OpName.FW_add", ins := [9537, 9611], outs := [9615] }
      9537 9611 9615 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 9537 9611 9615)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9616
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9538) (denoteGraph_ringAttn pm initPM 9612) :=
    ringAttn_reduce2_pm_opaque pm initPM 996
      { rank := 1, op := "OpName.FW_add", ins := [9538, 9612], outs := [9616] }
      9538 9612 9616 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 9538 9612 9616)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5328
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9615, denoteGraph_ringAttn pm initPM 9616] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs9537 hs9538 hs9611 hs9612,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9615).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9537 hs9611
  have hsp1 : (denoteGraph_ringAttn pm initPM 9616).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9538 hs9612
  have hshape : (denoteGraph_ringAttn sm initSM 5328).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5328 5328 9615 9616 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5329 — `FW_float(5328)` (identity, 2-tp PM `9621`/`9622`). -/
theorem recon_intermediateGoal_5329_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5329
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs9615, hs9616⟩ := twoTp_gather _ _ intermediateGoal_5328 5328 9615 9616
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5328_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5329 = id (denoteGraph_ringAttn sm initSM 5328) :=
    ringAttn_reduce1_pm_opaque sm initSM 468
      { rank := 0, op := "OpName.FW_float", ins := [5328], outs := [5329] }
      5328 5329 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5328 5329 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9621 = id (denoteGraph_ringAttn pm initPM 9615) :=
    ringAttn_reduce1_pm_opaque pm initPM 997
      { rank := 0, op := "OpName.FW_float", ins := [9615], outs := [9621] }
      9615 9621 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9615 9621 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9622 = id (denoteGraph_ringAttn pm initPM 9616) :=
    ringAttn_reduce1_pm_opaque pm initPM 998
      { rank := 1, op := "OpName.FW_float", ins := [9616], outs := [9622] }
      9616 9622 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9616 9622 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5329
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9621, denoteGraph_ringAttn pm initPM 9622] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9621).shape = [2048, 1024] := by rw [rP0]; exact hs9615
  have hsp1 : (denoteGraph_ringAttn pm initPM 9622).shape = [2048, 1024] := by rw [rP1]; exact hs9616
  have hshape : (denoteGraph_ringAttn sm initSM 5329).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5329 5329 9621 9622 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5330 — cross-block residual add `7980 + 5329` (2-tp, PM `9625`/`9626`). -/
theorem recon_intermediateGoal_5330_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5330
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs15683, hs15691⟩ := twoTp_gather _ _ intermediateGoal_7980 7980 15683 15691
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7980_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs9621, hs9622⟩ := twoTp_gather _ _ intermediateGoal_5329 5329 9621 9622
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5329_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5330
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7980) (denoteGraph_ringAttn sm initSM 5329) :=
    ringAttn_reduce2_pm_opaque sm initSM 469
      { rank := 0, op := "OpName.FW_add", ins := [7980, 5329], outs := [5330] }
      7980 5329 5330 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7980 5329 5330)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9625
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15683) (denoteGraph_ringAttn pm initPM 9621) :=
    ringAttn_reduce2_pm_opaque pm initPM 999
      { rank := 0, op := "OpName.FW_add", ins := [15683, 9621], outs := [9625] }
      15683 9621 9625 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15683 9621 9625)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9626
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15691) (denoteGraph_ringAttn pm initPM 9622) :=
    ringAttn_reduce2_pm_opaque pm initPM 1000
      { rank := 1, op := "OpName.FW_add", ins := [15691, 9622], outs := [9626] }
      15691 9622 9626 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15691 9622 9626)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5330
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9625, denoteGraph_ringAttn pm initPM 9626] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15683 hs15691 hs9621 hs9622,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9625).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15683 hs9621
  have hsp1 : (denoteGraph_ringAttn pm initPM 9626).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15691 hs9622
  have hshape : (denoteGraph_ringAttn sm initSM 5330).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5330 5330 9625 9626 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
