/- Worker #23 — Layer-8 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_5074_ringAttn` (the layer-8
   sliding-window attention output, unconditional-given-WF) through the layer-8
   forward block.

   Unlike L2, the L8 block has NO gather-to-full node (L2's PM node 228
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L8
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_5078` targets `[8751, 8752]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L7Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 5075 — 2-tp reshape of the L8 attention output `5074 : [4096,16,64]` to
    `[4096,1024]` (SM node 205, PM nodes 471/472). -/
theorem recon_intermediateGoal_5075_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5075
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs8739, hs8740⟩ := twoTp_gather _ _ intermediateGoal_5074 5074 8739 8740
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5074_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5075
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5074) :=
    ringAttn_reshape_reduce_pm sm initSM 283 0 5074 5075 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8741
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8739) :=
    ringAttn_reshape_reduce_pm pm initPM 627 0 8739 8741 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8742
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8740) :=
    ringAttn_reshape_reduce_pm pm initPM 628 1 8740 8742 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5075
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8741, denoteGraph_ringAttn pm initPM 8742] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs8739 hs8740
  have hs8741 : (denoteGraph_ringAttn pm initPM 8741).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8742 : (denoteGraph_ringAttn pm initPM 8742).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5075 : (denoteGraph_ringAttn sm initSM 5075).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5075 5075 8741 8742 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5075 hs8741 hs8742

/-- 5076 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 206, PM
    nodes 473/474). -/
theorem recon_intermediateGoal_5076_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5076
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs8741, hs8742⟩ := twoTp_gather _ _ intermediateGoal_5075 5075 8741 8742
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5075_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5075 : (denoteGraph_ringAttn sm initSM 5075).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8741])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5076
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5075) :=
    ringAttn_reshape_reduce_pm sm initSM 284 0 5075 5076 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8747
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8741) :=
    ringAttn_reshape_reduce_pm pm initPM 629 0 8741 8747 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8748
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8742) :=
    ringAttn_reshape_reduce_pm pm initPM 630 1 8742 8748 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8747 = denoteGraph_ringAttn pm initPM 8741 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8741]
  have h18 : denoteGraph_ringAttn pm initPM 8748 = denoteGraph_ringAttn pm initPM 8742 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8742]
  have hval : denoteGraph_ringAttn sm initSM 5076
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8747, denoteGraph_ringAttn pm initPM 8748] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5075, hval05, hnr, ← h17, ← h18]
  have hs8747 : (denoteGraph_ringAttn pm initPM 8747).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8748 : (denoteGraph_ringAttn pm initPM 8748).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5076 : (denoteGraph_ringAttn sm initSM 5076).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5076 5076 8747 8748 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5076 hs8747 hs8748

/-- 5078 — 2-tp down-projection `fw_linear(5076, 5077)` (weight `5077 : [1024,1024]`,
    SM node 207, PM nodes 475/476). -/
theorem recon_intermediateGoal_5078_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5078
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs8747, hs8748⟩ := twoTp_gather _ _ intermediateGoal_5076 5076 8747 8748
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5076_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5077 : denoteGraph_ringAttn sm initSM 5077 = denoteGraph_ringAttn pm initPM 5077 :=
    veq_weight_ring initSM initPM hInit initGoal_5077 (by native_decide) 5077
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5077 : (denoteGraph_ringAttn sm initSM 5077).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5077 (by native_decide) 5077 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw5077 : (denoteGraph_ringAttn pm initPM 5077).shape = [1024, 1024] := by
    rw [← hw5077]; exact hsw5077
  have rSM : denoteGraph_ringAttn sm initSM 5078
      = fw_linear (denoteGraph_ringAttn sm initSM 5076) (denoteGraph_ringAttn sm initSM 5077) :=
    ringAttn_reduce2_pm_opaque sm initSM 285
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5076, 5077], outs := [5078] }
      5076 5077 5078 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5076 5077 5078)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8751
      = fw_linear (denoteGraph_ringAttn pm initPM 8747) (denoteGraph_ringAttn pm initPM 5077) :=
    ringAttn_reduce2_pm_opaque pm initPM 631
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8747, 5077], outs := [8751] }
      8747 5077 8751 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8747 5077 8751)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8752
      = fw_linear (denoteGraph_ringAttn pm initPM 8748) (denoteGraph_ringAttn pm initPM 5077) :=
    ringAttn_reduce2_pm_opaque pm initPM 632
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8748, 5077], outs := [8752] }
      8748 5077 8752 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8748 5077 8752)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5078
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8751, denoteGraph_ringAttn pm initPM 8752] := by
    rw [rSM, hval06, hw5077, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs8747 hs8748 hpw5077,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8751).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8747 hpw5077
  have hsp1 : (denoteGraph_ringAttn pm initPM 8752).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8748 hpw5077
  have hshape : (denoteGraph_ringAttn sm initSM 5078).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5078 5078 8751 8752 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5079 — 2-tp identity view of `5078` (SM node 208, PM nodes 477/478). -/
theorem recon_intermediateGoal_5079_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5079
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs8751, hs8752⟩ := twoTp_gather _ _ intermediateGoal_5078 5078 8751 8752
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5078_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5078 : (denoteGraph_ringAttn sm initSM 5078).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8751])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5079
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5078) :=
    ringAttn_reduce1_pm_opaque sm initSM 286
      { rank := 0, op := "OpName.FW_view", ins := [5078], outs := [5079], params := [4096, 1024] }
      5078 5079 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5078 5079)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8761
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8751) :=
    ringAttn_reduce1_pm_opaque pm initPM 633
      { rank := 0, op := "OpName.FW_view", ins := [8751], outs := [8761], params := [2048, 1024] }
      8751 8761 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8751 8761)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8762
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8752) :=
    ringAttn_reduce1_pm_opaque pm initPM 634
      { rank := 1, op := "OpName.FW_view", ins := [8752], outs := [8762], params := [2048, 1024] }
      8752 8762 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8752 8762)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 8761 = denoteGraph_ringAttn pm initPM 8751 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8751]
  have h32 : denoteGraph_ringAttn pm initPM 8762 = denoteGraph_ringAttn pm initPM 8752 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8752]
  have hval : denoteGraph_ringAttn sm initSM 5079
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8761, denoteGraph_ringAttn pm initPM 8762] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5078, hval08, hnr, ← h31, ← h32]
  have hs8761 : (denoteGraph_ringAttn pm initPM 8761).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8762 : (denoteGraph_ringAttn pm initPM 8762).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5079 : (denoteGraph_ringAttn sm initSM 5079).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5079 5079 8761 8762 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5079 hs8761 hs8762

/-- 5080 — 2-tp `FW_float(5079)` (identity, SM node 209, PM nodes 479/480). -/
theorem recon_intermediateGoal_5080_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5080
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs8761, hs8762⟩ := twoTp_gather _ _ intermediateGoal_5079 5079 8761 8762
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5079_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5080 = id (denoteGraph_ringAttn sm initSM 5079) :=
    ringAttn_reduce1_pm_opaque sm initSM 287
      { rank := 0, op := "OpName.FW_float", ins := [5079], outs := [5080] }
      5079 5080 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5079 5080 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8765 = id (denoteGraph_ringAttn pm initPM 8761) :=
    ringAttn_reduce1_pm_opaque pm initPM 635
      { rank := 0, op := "OpName.FW_float", ins := [8761], outs := [8765] }
      8761 8765 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8761 8765 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8766 = id (denoteGraph_ringAttn pm initPM 8762) :=
    ringAttn_reduce1_pm_opaque pm initPM 636
      { rank := 1, op := "OpName.FW_float", ins := [8762], outs := [8766] }
      8762 8766 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8762 8766 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5080
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8765, denoteGraph_ringAttn pm initPM 8766] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8765).shape = [2048, 1024] := by rw [rP0]; exact hs8761
  have hsp1 : (denoteGraph_ringAttn pm initPM 8766).shape = [2048, 1024] := by rw [rP1]; exact hs8762
  have hshape : (denoteGraph_ringAttn sm initSM 5080).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5080 5080 8765 8766 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7751 — 2-tp `mref2`-second copy of the L2 residual `5060` (SM node 197,
    PM nodes 455/456), carried into the L8 residual add. -/
theorem recon_intermediateGoal_7751_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7751
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs8695, hs8696⟩ := twoTp_gather _ _ intermediateGoal_5060 5060 8695 8696
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5060_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7751 : denoteGraph_ringAttn sm initSM 7751 = id (denoteGraph_ringAttn sm initSM 5060) :=
    ringAttn_reduce1_pm_opaque sm initSM 275
      { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751], params := [2] }
      5060 7751 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5060 7747 7751 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15225 : denoteGraph_ringAttn pm initPM 15225 = id (denoteGraph_ringAttn pm initPM 8695) :=
    ringAttn_reduce1_pm_opaque pm initPM 611
      { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225], params := [2] }
      8695 15225 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8695 15221 15225 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15233 : denoteGraph_ringAttn pm initPM 15233 = id (denoteGraph_ringAttn pm initPM 8696) :=
    ringAttn_reduce1_pm_opaque pm initPM 612
      { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233], params := [2] }
      8696 15233 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8696 15229 15233 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7751 p15225 p15233
  have hsp0 : (denoteGraph_ringAttn pm initPM 15225).shape = [2048, 1024] := by
    rw [p15225]; exact hs8695
  have hsp1 : (denoteGraph_ringAttn pm initPM 15233).shape = [2048, 1024] := by
    rw [p15233]; exact hs8696
  have hval : denoteGraph_ringAttn sm initSM 7751
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15225, denoteGraph_ringAttn pm initPM 15233] := by
    rw [s7751, hbr90, ← p15225, ← p15233]
  have hshape : (denoteGraph_ringAttn sm initSM 7751).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7751 7751 15225 15233 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5081 — 2-tp L8 residual add `7751 + 5080` (SM node 210, PM nodes 481/482). -/
theorem recon_intermediateGoal_5081_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5081
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs15225, hs15233⟩ := twoTp_gather _ _ intermediateGoal_7751 7751 15225 15233
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7751_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs8765, hs8766⟩ := twoTp_gather _ _ intermediateGoal_5080 5080 8765 8766
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5080_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5081
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7751) (denoteGraph_ringAttn sm initSM 5080) :=
    ringAttn_reduce2_pm_opaque sm initSM 288
      { rank := 0, op := "OpName.FW_add", ins := [7751, 5080], outs := [5081] }
      7751 5080 5081 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7751 5080 5081)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8769
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15225) (denoteGraph_ringAttn pm initPM 8765) :=
    ringAttn_reduce2_pm_opaque pm initPM 637
      { rank := 0, op := "OpName.FW_add", ins := [15225, 8765], outs := [8769] }
      15225 8765 8769 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15225 8765 8769)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8770
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15233) (denoteGraph_ringAttn pm initPM 8766) :=
    ringAttn_reduce2_pm_opaque pm initPM 638
      { rank := 1, op := "OpName.FW_add", ins := [15233, 8766], outs := [8770] }
      15233 8766 8770 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15233 8766 8770)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5081
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8769, denoteGraph_ringAttn pm initPM 8770] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15225 hs15233 hs8765 hs8766,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8769).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15225 hs8765
  have hsp1 : (denoteGraph_ringAttn pm initPM 8770).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15233 hs8766
  have hshape : (denoteGraph_ringAttn sm initSM 5081).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5081 5081 8769 8770 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5083 — 2-tp RMSNorm of `mref2-first(5081)` with replicated weight
    `5082 : [1024]` (SM node 212, PM nodes 485/486). -/
theorem recon_intermediateGoal_5083_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5083
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8769, hs8770⟩ := twoTp_gather _ _ intermediateGoal_5081 5081 8769 8770
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5081_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7768 : denoteGraph_ringAttn sm initSM 7768 = id (denoteGraph_ringAttn sm initSM 5081) :=
    ringAttn_reduce1_pm_opaque sm initSM 289
      { rank := 0, op := "OpName.FW_multiref", ins := [5081], outs := [7768, 7772], params := [2] }
      5081 7768 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5081 7768 7772)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15263 : denoteGraph_ringAttn pm initPM 15263 = id (denoteGraph_ringAttn pm initPM 8769) :=
    ringAttn_reduce1_pm_opaque pm initPM 639
      { rank := 0, op := "OpName.FW_multiref", ins := [8769], outs := [15263, 15267], params := [2] }
      8769 15263 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8769 15263 15267)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15271 : denoteGraph_ringAttn pm initPM 15271 = id (denoteGraph_ringAttn pm initPM 8770) :=
    ringAttn_reduce1_pm_opaque pm initPM 640
      { rank := 1, op := "OpName.FW_multiref", ins := [8770], outs := [15271, 15275], params := [2] }
      8770 15271 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8770 15271 15275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7768 p15263 p15271
  have hs15263 : (denoteGraph_ringAttn pm initPM 15263).shape = [2048, 1024] := by
    rw [p15263]; exact hs8769
  have hs15271 : (denoteGraph_ringAttn pm initPM 15271).shape = [2048, 1024] := by
    rw [p15271]; exact hs8770
  have hbr08 : denoteGraph_ringAttn sm initSM 7768
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15263, denoteGraph_ringAttn pm initPM 15271] := by
    rw [s7768, hbr11, ← p15263, ← p15271]
  have hw5082 : denoteGraph_ringAttn sm initSM 5082 = denoteGraph_ringAttn pm initPM 5082 :=
    veq_weight_ring initSM initPM hInit initGoal_5082 (by native_decide) 5082
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5083
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7768) (denoteGraph_ringAttn sm initSM 5082) :=
    ringAttn_reduce2_pm_opaque sm initSM 290
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7768, 5082], outs := [5083] }
      7768 5082 5083 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7768 5082 5083)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8773
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15263) (denoteGraph_ringAttn pm initPM 5082) :=
    ringAttn_reduce2_pm_opaque pm initPM 641
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15263, 5082], outs := [8773] }
      15263 5082 8773 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15263 5082 8773)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8774
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15271) (denoteGraph_ringAttn pm initPM 5082) :=
    ringAttn_reduce2_pm_opaque pm initPM 642
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15271, 5082], outs := [8774] }
      15271 5082 8774 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15271 5082 8774)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5083
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8773, denoteGraph_ringAttn pm initPM 8774] := by
    rw [rSM, hbr08, hw5082, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15263 hs15271,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8773).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15263
  have hsp1 : (denoteGraph_ringAttn pm initPM 8774).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15271
  have hshape : (denoteGraph_ringAttn sm initSM 5083).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5083 5083 8773 8774 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5084 — 2-tp `FW_float(mref5-first(5083))` (identity, SM node 214,
    PM nodes 489/493; mref5-first via SM node 213, PM 487/488). -/
theorem recon_intermediateGoal_5084_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5084
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8773, hs8774⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7779 : denoteGraph_ringAttn sm initSM 7779 = id (denoteGraph_ringAttn sm initSM 5083) :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083],
        outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7779 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 5083 7779 [7783, 7787, 7791, 7795])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15282 : denoteGraph_ringAttn pm initPM 15282 = id (denoteGraph_ringAttn pm initPM 8773) :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773],
        outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15282 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 8773 15282 [15286, 15290, 15294, 15298])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15305 : denoteGraph_ringAttn pm initPM 15305 = id (denoteGraph_ringAttn pm initPM 8774) :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774],
        outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15305 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 8774 15305 [15309, 15313, 15317, 15321])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7779 p15282 p15305
  have hbrm : denoteGraph_ringAttn sm initSM 7779
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15282, denoteGraph_ringAttn pm initPM 15305] := by
    rw [s7779, hbr13, ← p15282, ← p15305]
  have rSM : denoteGraph_ringAttn sm initSM 5084 = id (denoteGraph_ringAttn sm initSM 7779) :=
    ringAttn_reduce1_pm_opaque sm initSM 292
      { rank := 0, op := "OpName.FW_float", ins := [7779], outs := [5084] }
      7779 5084 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7779 5084 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8775 = id (denoteGraph_ringAttn pm initPM 15282) :=
    ringAttn_reduce1_pm_opaque pm initPM 645
      { rank := 0, op := "OpName.FW_float", ins := [15282], outs := [8775] }
      15282 8775 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 15282 8775 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8776 = id (denoteGraph_ringAttn pm initPM 15305) :=
    ringAttn_reduce1_pm_opaque pm initPM 649
      { rank := 1, op := "OpName.FW_float", ins := [15305], outs := [8776] }
      15305 8776 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 15305 8776 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs15282 : (denoteGraph_ringAttn pm initPM 15282).shape = [2048, 1024] := by
    rw [p15282]; exact hs8773
  have hs15305 : (denoteGraph_ringAttn pm initPM 15305).shape = [2048, 1024] := by
    rw [p15305]; exact hs8774
  have hval : denoteGraph_ringAttn sm initSM 5084
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8775, denoteGraph_ringAttn pm initPM 8776] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8775).shape = [2048, 1024] := by
    rw [rP0]; exact hs15282
  have hsp1 : (denoteGraph_ringAttn pm initPM 8776).shape = [2048, 1024] := by
    rw [rP1]; exact hs15305
  have hshape : (denoteGraph_ringAttn sm initSM 5084).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5084 5084 8775 8776 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5086 — 2-tp router logits `fw_norm_linear(5084, 5085)` with weight
    `5085 : [64, 1024]` → `[4096, 64]` (SM node 218, PM nodes 497/501). -/
theorem recon_intermediateGoal_5086_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5086
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs8775, hs8776⟩ := twoTp_gather _ _ intermediateGoal_5084 5084 8775 8776
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5084_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5085 : denoteGraph_ringAttn sm initSM 5085 = denoteGraph_ringAttn pm initPM 5085 :=
    veq_weight_ring initSM initPM hInit initGoal_5085 (by native_decide) 5085
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5085 : (denoteGraph_ringAttn sm initSM 5085).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5085 (by native_decide) 5085 [64, 1024]
      rfl rfl (by native_decide)
  have hpw5085 : (denoteGraph_ringAttn pm initPM 5085).shape = [64, 1024] := by
    rw [← hw5085]; exact hsw5085
  have rSM : denoteGraph_ringAttn sm initSM 5086
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 5084) (denoteGraph_ringAttn sm initSM 5085) :=
    ringAttn_reduce2_pm_opaque sm initSM 296
      { rank := 0, op := "OpName.FW_norm_linear", ins := [5084, 5085], outs := [5086] }
      5084 5085 5086 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 5084 5085 5086)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8781
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8775) (denoteGraph_ringAttn pm initPM 5085) :=
    ringAttn_reduce2_pm_opaque pm initPM 653
      { rank := 0, op := "OpName.FW_norm_linear", ins := [8775, 5085], outs := [8781] }
      8775 5085 8781 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 8775 5085 8781)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8782
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8776) (denoteGraph_ringAttn pm initPM 5085) :=
    ringAttn_reduce2_pm_opaque pm initPM 657
      { rank := 1, op := "OpName.FW_norm_linear", ins := [8776, 5085], outs := [8782] }
      8776 5085 8782 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 8776 5085 8782)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5086
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8781, denoteGraph_ringAttn pm initPM 8782] := by
    rw [rSM, hval14, hw5085, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs8775 hs8776 hpw5085,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8781).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8775 hpw5085
  have hsp1 : (denoteGraph_ringAttn pm initPM 8782).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8776 hpw5085
  have hshape : (denoteGraph_ringAttn sm initSM 5086).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5086 5086 8781 8782 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L8 top-k routing (`5087`/`5088`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`8781`/`8782`) directly. -/

/-- Shared L8 top-k core: `5086` (full logits) is the dim-0 gather of the two
    per-rank shards `8781`/`8782`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L8 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 5086
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 8781, denoteGraph_ringAttn pm initPM 8782]
      ∧ (denoteGraph_ringAttn sm initSM 5086).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8781).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8782).shape = [2048, 64]
      ∧ ((sm.nodes.take 300).foldl (applyNodeRingAttn sm) initSM 5086).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 661).foldl (applyNodeRingAttn pm) initPM 8781).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 665).foldl (applyNodeRingAttn pm) initPM 8782).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs8781, hs8782⟩ := twoTp_gather _ _ intermediateGoal_5086 5086 8781 8782
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5086_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs5086sm : (denoteGraph_ringAttn sm initSM 5086).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs8781])]
    simp [List.set, List.getD]
  have hpre5086sm : denoteGraph_ringAttn sm initSM 5086
      = (sm.nodes.take 300).foldl (applyNodeRingAttn sm) initSM 5086 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5086 300 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 300).foldl (applyNodeRingAttn sm) initSM 5086).shape.reverse.head? = some 64 := by
    rw [← hpre5086sm, hs5086sm]; rfl
  have hpre8781 : denoteGraph_ringAttn pm initPM 8781
      = (pm.nodes.take 661).foldl (applyNodeRingAttn pm) initPM 8781 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8781 661 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 661).foldl (applyNodeRingAttn pm) initPM 8781).shape.reverse.head? = some 64 := by
    rw [← hpre8781, hs8781]; rfl
  have hpre8782 : denoteGraph_ringAttn pm initPM 8782
      = (pm.nodes.take 665).foldl (applyNodeRingAttn pm) initPM 8782 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8782 665 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 665).foldl (applyNodeRingAttn pm) initPM 8782).shape.reverse.head? = some 64 := by
    rw [← hpre8782, hs8782]; rfl
  exact ⟨hbr16, hs5086sm, hs8781, hs8782, hlastSM, hlast271, hlast275⟩

/-- 5087 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5087_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5087
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5086sm, hs8781, hs8782, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L8 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5087
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5086) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 300
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5086], outs := [5087, 5088, 5089], params := [8, 1] }
      5086 5087 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 300).foldl (applyNodeRingAttn sm) initSM) 0 5086 5087 5088 5089 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8783
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8781) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 661
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8781], outs := [8783, 8785, 8787], params := [8, 1] }
      8781 8783 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 661).foldl (applyNodeRingAttn pm) initPM) 0 8781 8783 8785 8787 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8784
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8782) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 665
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8782], outs := [8784, 8786, 8788], params := [8, 1] }
      8782 8784 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 665).foldl (applyNodeRingAttn pm) initPM) 1 8782 8784 8786 8788 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5087
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8783, denoteGraph_ringAttn pm initPM 8784] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8781 hs8782,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5087).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs5086sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8783).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8781]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8784).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8782]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5087 5087 8783 8784 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5088 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5088_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5088
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5086sm, hs8781, hs8782, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L8 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5088
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5086) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 300
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5086], outs := [5087, 5088, 5089], params := [8, 1] }
      5086 5088 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 300).foldl (applyNodeRingAttn sm) initSM) 0 5086 5087 5088 5089 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8785
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8781) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 661
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8781], outs := [8783, 8785, 8787], params := [8, 1] }
      8781 8785 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 661).foldl (applyNodeRingAttn pm) initPM) 0 8781 8783 8785 8787 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8786
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8782) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 665
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8782], outs := [8784, 8786, 8788], params := [8, 1] }
      8782 8786 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 665).foldl (applyNodeRingAttn pm) initPM) 1 8782 8784 8786 8788 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5088
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8785, denoteGraph_ringAttn pm initPM 8786] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8781 hs8782,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5088).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs5086sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8785).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8781]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8786).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8782]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5088 5088 8785 8786 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L8 router expert branches — reshape (`5093`/`5098`/`5102`) of the
    `mref5` copies (positions 2/3/4) of `5083`, all identity 2-tp views. -/

/-- 5093 — 2-tp identity reshape of `mref5-pos2(5083)` (SM node 215, PM 490/494). -/
theorem recon_intermediateGoal_5093_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5093
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8773, hs8774⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5083sm : (denoteGraph_ringAttn sm initSM 5083).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8773])]
    simp [List.set, List.getD]
  have s7787 : denoteGraph_ringAttn sm initSM 7787 = id (denoteGraph_ringAttn sm initSM 5083) :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083],
        outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7787 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15290 : denoteGraph_ringAttn pm initPM 15290 = id (denoteGraph_ringAttn pm initPM 8773) :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773],
        outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15290 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15313 : denoteGraph_ringAttn pm initPM 15313 = id (denoteGraph_ringAttn pm initPM 8774) :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774],
        outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15313 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7787 p15290 p15313
  have hs7787 : (denoteGraph_ringAttn sm initSM 7787).shape = [4096, 1024] := by rw [s7787]; exact hs5083sm
  have hs15290 : (denoteGraph_ringAttn pm initPM 15290).shape = [2048, 1024] := by rw [p15290]; exact hs8773
  have hs15313 : (denoteGraph_ringAttn pm initPM 15313).shape = [2048, 1024] := by rw [p15313]; exact hs8774
  have hbrm : denoteGraph_ringAttn sm initSM 7787
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15290, denoteGraph_ringAttn pm initPM 15313] := by
    rw [s7787, hbr13, ← p15290, ← p15313]
  have rSM : denoteGraph_ringAttn sm initSM 5093
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7787) :=
    ringAttn_reduce1_pm_opaque sm initSM 293
      { rank := 0, op := "OpName.FW_reshape", ins := [7787], outs := [5093], params := [4096, 1024] }
      7787 5093 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7787 5093)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8795
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15290) :=
    ringAttn_reduce1_pm_opaque pm initPM 646
      { rank := 0, op := "OpName.FW_reshape", ins := [15290], outs := [8795], params := [2048, 1024] }
      15290 8795 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15290 8795)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8796
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15313) :=
    ringAttn_reduce1_pm_opaque pm initPM 650
      { rank := 1, op := "OpName.FW_reshape", ins := [15313], outs := [8796], params := [2048, 1024] }
      15313 8796 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15313 8796)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 8795 = denoteGraph_ringAttn pm initPM 15290 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15290]
  have h66 : denoteGraph_ringAttn pm initPM 8796 = denoteGraph_ringAttn pm initPM 15313 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15313]
  have hval : denoteGraph_ringAttn sm initSM 5093
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8795, denoteGraph_ringAttn pm initPM 8796] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7787, hbrm, hnr, ← h65, ← h66]
  have hs8795 : (denoteGraph_ringAttn pm initPM 8795).shape = [2048, 1024] := by rw [h65]; exact hs15290
  have hs8796 : (denoteGraph_ringAttn pm initPM 8796).shape = [2048, 1024] := by rw [h66]; exact hs15313
  have hs5093 : (denoteGraph_ringAttn sm initSM 5093).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7787]; exact hs7787
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5093 5093 8795 8796 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5093 hs8795 hs8796

/-- 5098 — 2-tp identity reshape of `mref5-pos3(5083)` (SM node 216, PM 491/495). -/
theorem recon_intermediateGoal_5098_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5098
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8773, hs8774⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5083sm : (denoteGraph_ringAttn sm initSM 5083).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8773])]
    simp [List.set, List.getD]
  have s7791 : denoteGraph_ringAttn sm initSM 7791 = id (denoteGraph_ringAttn sm initSM 5083) :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083],
        outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7791 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15294 : denoteGraph_ringAttn pm initPM 15294 = id (denoteGraph_ringAttn pm initPM 8773) :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773],
        outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15294 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15317 : denoteGraph_ringAttn pm initPM 15317 = id (denoteGraph_ringAttn pm initPM 8774) :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774],
        outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15317 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7791 p15294 p15317
  have hs7791 : (denoteGraph_ringAttn sm initSM 7791).shape = [4096, 1024] := by rw [s7791]; exact hs5083sm
  have hs15294 : (denoteGraph_ringAttn pm initPM 15294).shape = [2048, 1024] := by rw [p15294]; exact hs8773
  have hs15317 : (denoteGraph_ringAttn pm initPM 15317).shape = [2048, 1024] := by rw [p15317]; exact hs8774
  have hbrm : denoteGraph_ringAttn sm initSM 7791
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15294, denoteGraph_ringAttn pm initPM 15317] := by
    rw [s7791, hbr13, ← p15294, ← p15317]
  have rSM : denoteGraph_ringAttn sm initSM 5098
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7791) :=
    ringAttn_reduce1_pm_opaque sm initSM 294
      { rank := 0, op := "OpName.FW_reshape", ins := [7791], outs := [5098], params := [4096, 1024] }
      7791 5098 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7791 5098)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8809
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15294) :=
    ringAttn_reduce1_pm_opaque pm initPM 647
      { rank := 0, op := "OpName.FW_reshape", ins := [15294], outs := [8809], params := [2048, 1024] }
      15294 8809 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15294 8809)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8810
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15317) :=
    ringAttn_reduce1_pm_opaque pm initPM 651
      { rank := 1, op := "OpName.FW_reshape", ins := [15317], outs := [8810], params := [2048, 1024] }
      15317 8810 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15317 8810)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 8809 = denoteGraph_ringAttn pm initPM 15294 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15294]
  have h80 : denoteGraph_ringAttn pm initPM 8810 = denoteGraph_ringAttn pm initPM 15317 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15317]
  have hval : denoteGraph_ringAttn sm initSM 5098
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8809, denoteGraph_ringAttn pm initPM 8810] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7791, hbrm, hnr, ← h79, ← h80]
  have hs8809 : (denoteGraph_ringAttn pm initPM 8809).shape = [2048, 1024] := by rw [h79]; exact hs15294
  have hs8810 : (denoteGraph_ringAttn pm initPM 8810).shape = [2048, 1024] := by rw [h80]; exact hs15317
  have hs5098 : (denoteGraph_ringAttn sm initSM 5098).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7791]; exact hs7791
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5098 5098 8809 8810 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5098 hs8809 hs8810

/-- 5102 — 2-tp identity reshape of `mref5-pos4(5083)` (SM node 217, PM 492/496). -/
theorem recon_intermediateGoal_5102_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5102
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8773, hs8774⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5083sm : (denoteGraph_ringAttn sm initSM 5083).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8773])]
    simp [List.set, List.getD]
  have s7795 : denoteGraph_ringAttn sm initSM 7795 = id (denoteGraph_ringAttn sm initSM 5083) :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083],
        outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7795 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15298 : denoteGraph_ringAttn pm initPM 15298 = id (denoteGraph_ringAttn pm initPM 8773) :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773],
        outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15298 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15321 : denoteGraph_ringAttn pm initPM 15321 = id (denoteGraph_ringAttn pm initPM 8774) :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774],
        outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15321 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7795 p15298 p15321
  have hs7795 : (denoteGraph_ringAttn sm initSM 7795).shape = [4096, 1024] := by rw [s7795]; exact hs5083sm
  have hs15298 : (denoteGraph_ringAttn pm initPM 15298).shape = [2048, 1024] := by rw [p15298]; exact hs8773
  have hs15321 : (denoteGraph_ringAttn pm initPM 15321).shape = [2048, 1024] := by rw [p15321]; exact hs8774
  have hbrm : denoteGraph_ringAttn sm initSM 7795
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15298, denoteGraph_ringAttn pm initPM 15321] := by
    rw [s7795, hbr13, ← p15298, ← p15321]
  have rSM : denoteGraph_ringAttn sm initSM 5102
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7795) :=
    ringAttn_reduce1_pm_opaque sm initSM 295
      { rank := 0, op := "OpName.FW_reshape", ins := [7795], outs := [5102], params := [4096, 1024] }
      7795 5102 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7795 5102)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8827
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15298) :=
    ringAttn_reduce1_pm_opaque pm initPM 648
      { rank := 0, op := "OpName.FW_reshape", ins := [15298], outs := [8827], params := [2048, 1024] }
      15298 8827 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15298 8827)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8828
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15321) :=
    ringAttn_reduce1_pm_opaque pm initPM 652
      { rank := 1, op := "OpName.FW_reshape", ins := [15321], outs := [8828], params := [2048, 1024] }
      15321 8828 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15321 8828)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 8827 = denoteGraph_ringAttn pm initPM 15298 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15298]
  have h98 : denoteGraph_ringAttn pm initPM 8828 = denoteGraph_ringAttn pm initPM 15321 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15321]
  have hval : denoteGraph_ringAttn sm initSM 5102
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8827, denoteGraph_ringAttn pm initPM 8828] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7795, hbrm, hnr, ← h97, ← h98]
  have hs8827 : (denoteGraph_ringAttn pm initPM 8827).shape = [2048, 1024] := by rw [h97]; exact hs15298
  have hs8828 : (denoteGraph_ringAttn pm initPM 8828).shape = [2048, 1024] := by rw [h98]; exact hs15321
  have hs5102 : (denoteGraph_ringAttn sm initSM 5102).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7795]; exact hs7795
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5102 5102 8827 8828 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5102 hs8827 hs8828

/-! ### L8 router expert mixlins (`5095`/`5100`/`5104`), 2-tp. -/

/-- 5095 — 2-tp `fw_linear(5093, 5094)`, weight `5094 : [1, 1024]` → `[4096, 1]`
    (SM node 219, PM nodes 498/502). -/
theorem recon_intermediateGoal_5095_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5095
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs8795, hs8796⟩ := twoTp_gather _ _ intermediateGoal_5093 5093 8795 8796
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5093_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5094 : denoteGraph_ringAttn sm initSM 5094 = denoteGraph_ringAttn pm initPM 5094 :=
    veq_weight_ring initSM initPM hInit initGoal_5094 (by native_decide) 5094
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5094 : (denoteGraph_ringAttn pm initPM 5094).shape = [1, 1024] := by
    rw [← hw5094]
    exact shape_weight_ring initSM initPM hInit initGoal_5094 (by native_decide) 5094 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5095
      = fw_linear (denoteGraph_ringAttn sm initSM 5093) (denoteGraph_ringAttn sm initSM 5094) :=
    ringAttn_reduce2_pm_opaque sm initSM 297
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5093, 5094], outs := [5095] }
      5093 5094 5095 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5093 5094 5095)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8799
      = fw_linear (denoteGraph_ringAttn pm initPM 8795) (denoteGraph_ringAttn pm initPM 5094) :=
    ringAttn_reduce2_pm_opaque pm initPM 654
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8795, 5094], outs := [8799] }
      8795 5094 8799 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8795 5094 8799)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8800
      = fw_linear (denoteGraph_ringAttn pm initPM 8796) (denoteGraph_ringAttn pm initPM 5094) :=
    ringAttn_reduce2_pm_opaque pm initPM 658
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8796, 5094], outs := [8800] }
      8796 5094 8800 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8796 5094 8800)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5095
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8799, denoteGraph_ringAttn pm initPM 8800] := by
    rw [rSM, hval23, hw5094, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs8795 hs8796 hpw5094,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8799).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8795 hpw5094
  have hsp1 : (denoteGraph_ringAttn pm initPM 8800).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8796 hpw5094
  have hshape : (denoteGraph_ringAttn sm initSM 5095).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5095 5095 8799 8800 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5100 — 2-tp `fw_linear(5098, 5099)`, weight `5099 : [512, 1024]` → `[4096, 512]`
    (SM node 220, PM nodes 499/503). -/
theorem recon_intermediateGoal_5100_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5100
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs8809, hs8810⟩ := twoTp_gather _ _ intermediateGoal_5098 5098 8809 8810
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5098_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5099 : denoteGraph_ringAttn sm initSM 5099 = denoteGraph_ringAttn pm initPM 5099 :=
    veq_weight_ring initSM initPM hInit initGoal_5099 (by native_decide) 5099
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5099 : (denoteGraph_ringAttn pm initPM 5099).shape = [512, 1024] := by
    rw [← hw5099]
    exact shape_weight_ring initSM initPM hInit initGoal_5099 (by native_decide) 5099 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5100
      = fw_linear (denoteGraph_ringAttn sm initSM 5098) (denoteGraph_ringAttn sm initSM 5099) :=
    ringAttn_reduce2_pm_opaque sm initSM 298
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5098, 5099], outs := [5100] }
      5098 5099 5100 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5098 5099 5100)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8813
      = fw_linear (denoteGraph_ringAttn pm initPM 8809) (denoteGraph_ringAttn pm initPM 5099) :=
    ringAttn_reduce2_pm_opaque pm initPM 655
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8809, 5099], outs := [8813] }
      8809 5099 8813 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8809 5099 8813)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8814
      = fw_linear (denoteGraph_ringAttn pm initPM 8810) (denoteGraph_ringAttn pm initPM 5099) :=
    ringAttn_reduce2_pm_opaque pm initPM 659
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8810, 5099], outs := [8814] }
      8810 5099 8814 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8810 5099 8814)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5100
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8813, denoteGraph_ringAttn pm initPM 8814] := by
    rw [rSM, hval28, hw5099, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8809 hs8810 hpw5099,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8813).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8809 hpw5099
  have hsp1 : (denoteGraph_ringAttn pm initPM 8814).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8810 hpw5099
  have hshape : (denoteGraph_ringAttn sm initSM 5100).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5100 5100 8813 8814 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5104 — 2-tp `fw_linear(5102, 5103)`, weight `5103 : [512, 1024]` → `[4096, 512]`
    (SM node 221, PM nodes 500/504). -/
theorem recon_intermediateGoal_5104_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5104
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs8827, hs8828⟩ := twoTp_gather _ _ intermediateGoal_5102 5102 8827 8828
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5102_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5103 : denoteGraph_ringAttn sm initSM 5103 = denoteGraph_ringAttn pm initPM 5103 :=
    veq_weight_ring initSM initPM hInit initGoal_5103 (by native_decide) 5103
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5103 : (denoteGraph_ringAttn pm initPM 5103).shape = [512, 1024] := by
    rw [← hw5103]
    exact shape_weight_ring initSM initPM hInit initGoal_5103 (by native_decide) 5103 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5104
      = fw_linear (denoteGraph_ringAttn sm initSM 5102) (denoteGraph_ringAttn sm initSM 5103) :=
    ringAttn_reduce2_pm_opaque sm initSM 299
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5102, 5103], outs := [5104] }
      5102 5103 5104 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5102 5103 5104)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8831
      = fw_linear (denoteGraph_ringAttn pm initPM 8827) (denoteGraph_ringAttn pm initPM 5103) :=
    ringAttn_reduce2_pm_opaque pm initPM 656
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8827, 5103], outs := [8831] }
      8827 5103 8831 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8827 5103 8831)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8832
      = fw_linear (denoteGraph_ringAttn pm initPM 8828) (denoteGraph_ringAttn pm initPM 5103) :=
    ringAttn_reduce2_pm_opaque pm initPM 660
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8828, 5103], outs := [8832] }
      8828 5103 8832 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8828 5103 8832)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5104
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8831, denoteGraph_ringAttn pm initPM 8832] := by
    rw [rSM, hval32, hw5103, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8827 hs8828 hpw5103,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8831).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8827 hpw5103
  have hsp1 : (denoteGraph_ringAttn pm initPM 8832).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8828 hpw5103
  have hshape : (denoteGraph_ringAttn sm initSM 5104).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5104 5104 8831 8832 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L8 router expert views (`5096`/`5101`/`5105`), identity 2-tp views. -/

/-- 5096 — 2-tp identity view of `5095` → `[4096, 1]` (SM node 223, PM 506/510). -/
theorem recon_intermediateGoal_5096_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5096
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs8799, hs8800⟩ := twoTp_gather _ _ intermediateGoal_5095 5095 8799 8800
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5095_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5095 : (denoteGraph_ringAttn sm initSM 5095).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8799])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5096
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 5095) :=
    ringAttn_reduce1_pm_opaque sm initSM 301
      { rank := 0, op := "OpName.FW_view", ins := [5095], outs := [5096], params := [4096, 1] }
      5095 5096 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 5095 5096)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8805
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8799) :=
    ringAttn_reduce1_pm_opaque pm initPM 662
      { rank := 0, op := "OpName.FW_view", ins := [8799], outs := [8805], params := [2048, 1] }
      8799 8805 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 8799 8805)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8806
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8800) :=
    ringAttn_reduce1_pm_opaque pm initPM 666
      { rank := 1, op := "OpName.FW_view", ins := [8800], outs := [8806], params := [2048, 1] }
      8800 8806 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 8800 8806)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 8805 = denoteGraph_ringAttn pm initPM 8799 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs8799]
  have h76 : denoteGraph_ringAttn pm initPM 8806 = denoteGraph_ringAttn pm initPM 8800 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs8800]
  have hval : denoteGraph_ringAttn sm initSM 5096
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8805, denoteGraph_ringAttn pm initPM 8806] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5095, hval25, hnr, ← h75, ← h76]
  have hs8805 : (denoteGraph_ringAttn pm initPM 8805).shape = [2048, 1] := by rw [h75]; exact hs8799
  have hs8806 : (denoteGraph_ringAttn pm initPM 8806).shape = [2048, 1] := by rw [h76]; exact hs8800
  have hs5096 : (denoteGraph_ringAttn sm initSM 5096).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5095]; exact hs5095
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5096 5096 8805 8806 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5096 hs8805 hs8806

/-- 5101 — 2-tp identity view of `5100` → `[4096, 512]` (SM node 224, PM 507/511). -/
theorem recon_intermediateGoal_5101_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5101
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs8813, hs8814⟩ := twoTp_gather _ _ intermediateGoal_5100 5100 8813 8814
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5100_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5100 : (denoteGraph_ringAttn sm initSM 5100).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8813])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5101
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5100) :=
    ringAttn_reduce1_pm_opaque sm initSM 302
      { rank := 0, op := "OpName.FW_view", ins := [5100], outs := [5101], params := [4096, 512] }
      5100 5101 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5100 5101)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8823
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8813) :=
    ringAttn_reduce1_pm_opaque pm initPM 663
      { rank := 0, op := "OpName.FW_view", ins := [8813], outs := [8823], params := [2048, 512] }
      8813 8823 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8813 8823)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8824
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8814) :=
    ringAttn_reduce1_pm_opaque pm initPM 667
      { rank := 1, op := "OpName.FW_view", ins := [8814], outs := [8824], params := [2048, 512] }
      8814 8824 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8814 8824)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 8823 = denoteGraph_ringAttn pm initPM 8813 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8813]
  have h94 : denoteGraph_ringAttn pm initPM 8824 = denoteGraph_ringAttn pm initPM 8814 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8814]
  have hval : denoteGraph_ringAttn sm initSM 5101
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8823, denoteGraph_ringAttn pm initPM 8824] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5100, hval30, hnr, ← h93, ← h94]
  have hs8823 : (denoteGraph_ringAttn pm initPM 8823).shape = [2048, 512] := by rw [h93]; exact hs8813
  have hs8824 : (denoteGraph_ringAttn pm initPM 8824).shape = [2048, 512] := by rw [h94]; exact hs8814
  have hs5101 : (denoteGraph_ringAttn sm initSM 5101).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5100]; exact hs5100
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5101 5101 8823 8824 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5101 hs8823 hs8824

/-- 5105 — 2-tp identity view of `5104` → `[4096, 512]` (SM node 225, PM 508/512). -/
theorem recon_intermediateGoal_5105_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5105
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs8831, hs8832⟩ := twoTp_gather _ _ intermediateGoal_5104 5104 8831 8832
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5104_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5104 : (denoteGraph_ringAttn sm initSM 5104).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8831])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5105
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5104) :=
    ringAttn_reduce1_pm_opaque sm initSM 303
      { rank := 0, op := "OpName.FW_view", ins := [5104], outs := [5105], params := [4096, 512] }
      5104 5105 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5104 5105)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8841
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8831) :=
    ringAttn_reduce1_pm_opaque pm initPM 664
      { rank := 0, op := "OpName.FW_view", ins := [8831], outs := [8841], params := [2048, 512] }
      8831 8841 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8831 8841)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8842
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8832) :=
    ringAttn_reduce1_pm_opaque pm initPM 668
      { rank := 1, op := "OpName.FW_view", ins := [8832], outs := [8842], params := [2048, 512] }
      8832 8842 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8832 8842)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 8841 = denoteGraph_ringAttn pm initPM 8831 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8831]
  have h12 : denoteGraph_ringAttn pm initPM 8842 = denoteGraph_ringAttn pm initPM 8832 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8832]
  have hval : denoteGraph_ringAttn sm initSM 5105
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8841, denoteGraph_ringAttn pm initPM 8842] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5104, hval34, hnr, ← h11, ← h12]
  have hs8841 : (denoteGraph_ringAttn pm initPM 8841).shape = [2048, 512] := by rw [h11]; exact hs8831
  have hs8842 : (denoteGraph_ringAttn pm initPM 8842).shape = [2048, 512] := by rw [h12]; exact hs8832
  have hs5105 : (denoteGraph_ringAttn sm initSM 5105).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5104]; exact hs5104
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5105 5105 8841 8842 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5105 hs8841 hs8842

/-! ### L8 MoE gate/expert branch (`5097` sigmoid, `5106` swiglu, `5107` reshape,
    `5109` mixlin, `5110` view, `5111` broadcast-mul), all 2-tp shard-direct. -/

/-- 5097 — 2-tp `fw_sigmoid(5096)` → `[4096, 1]` (SM node 227, PM 514/517). -/
theorem recon_intermediateGoal_5097_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5097
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs8805, hs8806⟩ := twoTp_gather _ _ intermediateGoal_5096 5096 8805 8806
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5096_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5097 = fw_sigmoid (denoteGraph_ringAttn sm initSM 5096) :=
    ringAttn_reduce1_pm_opaque sm initSM 305
      { rank := 0, op := "OpName.FW_sigmoid", ins := [5096], outs := [5097] }
      5096 5097 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 5096 5097 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8807 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8805) :=
    ringAttn_reduce1_pm_opaque pm initPM 670
      { rank := 0, op := "OpName.FW_sigmoid", ins := [8805], outs := [8807] }
      8805 8807 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 8805 8807 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8808 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8806) :=
    ringAttn_reduce1_pm_opaque pm initPM 673
      { rank := 1, op := "OpName.FW_sigmoid", ins := [8806], outs := [8808] }
      8806 8808 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 8806 8808 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5097
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8807, denoteGraph_ringAttn pm initPM 8808] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs8805 hs8806, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5097).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8805])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8807).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs8805
  have hsp1 : (denoteGraph_ringAttn pm initPM 8808).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs8806
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5097 5097 8807 8808 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5106 — 2-tp `fw_swiglu(5101, 5105)` → `[4096, 512]` (SM node 228, PM 515/518). -/
theorem recon_intermediateGoal_5106_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5106
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs8823, hs8824⟩ := twoTp_gather _ _ intermediateGoal_5101 5101 8823 8824
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5101_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs8841, hs8842⟩ := twoTp_gather _ _ intermediateGoal_5105 5105 8841 8842
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5105_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5106
      = fw_swiglu (denoteGraph_ringAttn sm initSM 5101) (denoteGraph_ringAttn sm initSM 5105) :=
    ringAttn_reduce2_pm_opaque sm initSM 306
      { rank := 0, op := "OpName.FW_swiglu", ins := [5101, 5105], outs := [5106] }
      5101 5105 5106 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 5101 5105 5106 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8845
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8823) (denoteGraph_ringAttn pm initPM 8841) :=
    ringAttn_reduce2_pm_opaque pm initPM 671
      { rank := 0, op := "OpName.FW_swiglu", ins := [8823, 8841], outs := [8845] }
      8823 8841 8845 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 8823 8841 8845 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8846
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8824) (denoteGraph_ringAttn pm initPM 8842) :=
    ringAttn_reduce2_pm_opaque pm initPM 674
      { rank := 1, op := "OpName.FW_swiglu", ins := [8824, 8842], outs := [8846] }
      8824 8842 8846 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 8824 8842 8846 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5106
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8845, denoteGraph_ringAttn pm initPM 8846] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs8823 hs8824 hs8841 hs8842,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5106).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8841])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8845).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8841
  have hsp1 : (denoteGraph_ringAttn pm initPM 8846).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8842
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5106 5106 8845 8846 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5107 — 2-tp identity reshape of `5106` → `[4096, 512]` (SM node 229, PM 519/520). -/
theorem recon_intermediateGoal_5107_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5107
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs8845, hs8846⟩ := twoTp_gather _ _ intermediateGoal_5106 5106 8845 8846
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5106_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5106 : (denoteGraph_ringAttn sm initSM 5106).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8845])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5107
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5106) :=
    ringAttn_reduce1_pm_opaque sm initSM 307
      { rank := 0, op := "OpName.FW_reshape", ins := [5106], outs := [5107], params := [4096, 512] }
      5106 5107 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5106 5107)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8847
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8845) :=
    ringAttn_reduce1_pm_opaque pm initPM 675
      { rank := 0, op := "OpName.FW_reshape", ins := [8845], outs := [8847], params := [2048, 512] }
      8845 8847 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8845 8847)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8848
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8846) :=
    ringAttn_reduce1_pm_opaque pm initPM 676
      { rank := 1, op := "OpName.FW_reshape", ins := [8846], outs := [8848], params := [2048, 512] }
      8846 8848 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8846 8848)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8847 = denoteGraph_ringAttn pm initPM 8845 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8845]
  have h18 : denoteGraph_ringAttn pm initPM 8848 = denoteGraph_ringAttn pm initPM 8846 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8846]
  have hval : denoteGraph_ringAttn sm initSM 5107
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8847, denoteGraph_ringAttn pm initPM 8848] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5106, hval36, hnr, ← h17, ← h18]
  have hs8847 : (denoteGraph_ringAttn pm initPM 8847).shape = [2048, 512] := by rw [h17]; exact hs8845
  have hs8848 : (denoteGraph_ringAttn pm initPM 8848).shape = [2048, 512] := by rw [h18]; exact hs8846
  have hs5107 : (denoteGraph_ringAttn sm initSM 5107).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5106]; exact hs5106
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5107 5107 8847 8848 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5107 hs8847 hs8848

/-- 5109 — 2-tp `fw_linear(5107, 5108)`, weight `5108 : [1024, 512]` → `[4096, 1024]`
    (SM node 230, PM 521/522). -/
theorem recon_intermediateGoal_5109_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5109
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs8847, hs8848⟩ := twoTp_gather _ _ intermediateGoal_5107 5107 8847 8848
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5107_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5108 : denoteGraph_ringAttn sm initSM 5108 = denoteGraph_ringAttn pm initPM 5108 :=
    veq_weight_ring initSM initPM hInit initGoal_5108 (by native_decide) 5108
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5108 : (denoteGraph_ringAttn pm initPM 5108).shape = [1024, 512] := by
    rw [← hw5108]
    exact shape_weight_ring initSM initPM hInit initGoal_5108 (by native_decide) 5108 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5109
      = fw_linear (denoteGraph_ringAttn sm initSM 5107) (denoteGraph_ringAttn sm initSM 5108) :=
    ringAttn_reduce2_pm_opaque sm initSM 308
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5107, 5108], outs := [5109] }
      5107 5108 5109 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5107 5108 5109)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8853
      = fw_linear (denoteGraph_ringAttn pm initPM 8847) (denoteGraph_ringAttn pm initPM 5108) :=
    ringAttn_reduce2_pm_opaque pm initPM 677
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8847, 5108], outs := [8853] }
      8847 5108 8853 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8847 5108 8853)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8854
      = fw_linear (denoteGraph_ringAttn pm initPM 8848) (denoteGraph_ringAttn pm initPM 5108) :=
    ringAttn_reduce2_pm_opaque pm initPM 678
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8848, 5108], outs := [8854] }
      8848 5108 8854 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8848 5108 8854)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5109
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8853, denoteGraph_ringAttn pm initPM 8854] := by
    rw [rSM, hval37, hw5108, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs8847 hs8848 hpw5108,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8853).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8847 hpw5108
  have hsp1 : (denoteGraph_ringAttn pm initPM 8854).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8848 hpw5108
  have hshape : (denoteGraph_ringAttn sm initSM 5109).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5109 5109 8853 8854 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5110 — 2-tp identity view of `5109` → `[4096, 1024]` (SM node 231, PM 523/524). -/
theorem recon_intermediateGoal_5110_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5110
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs8853, hs8854⟩ := twoTp_gather _ _ intermediateGoal_5109 5109 8853 8854
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5109_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5109 : (denoteGraph_ringAttn sm initSM 5109).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8853])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5110
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5109) :=
    ringAttn_reduce1_pm_opaque sm initSM 309
      { rank := 0, op := "OpName.FW_view", ins := [5109], outs := [5110], params := [4096, 1024] }
      5109 5110 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5109 5110)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8863
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8853) :=
    ringAttn_reduce1_pm_opaque pm initPM 679
      { rank := 0, op := "OpName.FW_view", ins := [8853], outs := [8863], params := [2048, 1024] }
      8853 8863 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8853 8863)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8864
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8854) :=
    ringAttn_reduce1_pm_opaque pm initPM 680
      { rank := 1, op := "OpName.FW_view", ins := [8854], outs := [8864], params := [2048, 1024] }
      8854 8864 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8854 8864)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 8863 = denoteGraph_ringAttn pm initPM 8853 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8853]
  have h34 : denoteGraph_ringAttn pm initPM 8864 = denoteGraph_ringAttn pm initPM 8854 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8854]
  have hval : denoteGraph_ringAttn sm initSM 5110
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8863, denoteGraph_ringAttn pm initPM 8864] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5109, hval39, hnr, ← h33, ← h34]
  have hs8863 : (denoteGraph_ringAttn pm initPM 8863).shape = [2048, 1024] := by rw [h33]; exact hs8853
  have hs8864 : (denoteGraph_ringAttn pm initPM 8864).shape = [2048, 1024] := by rw [h34]; exact hs8854
  have hs5110 : (denoteGraph_ringAttn sm initSM 5110).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5109]; exact hs5109
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5110 5110 8863 8864 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5110 hs8863 hs8864

/-- 5111 — 2-tp broadcast `mul(5097, 5110)` → `[4096, 1024]` (SM node 232, PM 525/526). -/
theorem recon_intermediateGoal_5111_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5111
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_5097 5097 8807 8808
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5097_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_5110 5110 8863 8864
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5110_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5111
      = elemwiseMul (denoteGraph_ringAttn sm initSM 5097) (denoteGraph_ringAttn sm initSM 5110) :=
    ringAttn_reduce2_pm_opaque sm initSM 310
      { rank := 0, op := "OpName.FW_mul", ins := [5097, 5110], outs := [5111] }
      5097 5110 5111 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 5097 5110 5111)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8867
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8807) (denoteGraph_ringAttn pm initPM 8863) :=
    ringAttn_reduce2_pm_opaque pm initPM 681
      { rank := 0, op := "OpName.FW_mul", ins := [8807, 8863], outs := [8867] }
      8807 8863 8867 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 8807 8863 8867)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8868
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8808) (denoteGraph_ringAttn pm initPM 8864) :=
    ringAttn_reduce2_pm_opaque pm initPM 682
      { rank := 1, op := "OpName.FW_mul", ins := [8808, 8864], outs := [8868] }
      8808 8864 8868 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 8808 8864 8868)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5111
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8867, denoteGraph_ringAttn pm initPM 8868] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 5111).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 5097).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 5110).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 8867).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 8868).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5111 5111 8867 8868 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 5092 — layer-8 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 5092 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`8793`), rank 1 →
    `[32, 64)` (`8794`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `8785`/`8786` are expert-local (the
    `wf5092_hdisjA/B` fields).  Token input `7783 = mref5-pos1(5083)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 226, PM nodes 513/516). -/
theorem recon_intermediateGoal_5092_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5092
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 7917 = mref5-pos1(5083).
  obtain ⟨hbr13, hs8773, hs8774⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7917 : denoteGraph_ringAttn sm initSM 7783 = id (denoteGraph_ringAttn sm initSM 5083) :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083],
        outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7783 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15286 : denoteGraph_ringAttn pm initPM 15286 = id (denoteGraph_ringAttn pm initPM 8773) :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773],
        outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15286 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15309 : denoteGraph_ringAttn pm initPM 15309 = id (denoteGraph_ringAttn pm initPM 8774) :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774],
        outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15309 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7917 p15286 p15309
  have hsInA : (denoteGraph_ringAttn pm initPM 15286).shape = [2048, 1024] := by
    rw [p15286]; exact hs8773
  have hsInB : (denoteGraph_ringAttn pm initPM 15309).shape = [2048, 1024] := by
    rw [p15309]; exact hs8774
  have hbrIn : denoteGraph_ringAttn sm initSM 7783
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 15286, denoteGraph_ringAttn pm initPM 15309] := by
    rw [s7917, hbr13, hnr, ← p15286, ← p15309]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_5087 5087 8783 8784
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5087_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_5088 5088 8785 8786
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5088_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 5087
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8783, denoteGraph_ringAttn pm initPM 8784] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 5088
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8785, denoteGraph_ringAttn pm initPM 8786] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_5090
    (by native_decide) 5090 8789 8790 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_5091
    (by native_decide) 5091 8791 8792 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 8789).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5090 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5090, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8789 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 8790).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5090 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5090, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8790 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 8791).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5091 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5091, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8791 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 8792).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5091 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5091, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8792 (by native_decide)]; exact hs.2
  -- SM 5092 = full-range all2all (SM node 226).
  have hSMout : denoteGraph_ringAttn sm initSM 5092
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7783)
          (denoteGraph_ringAttn sm initSM 5087) (denoteGraph_ringAttn sm initSM 5088)
          (denoteGraph_ringAttn sm initSM 5090) (denoteGraph_ringAttn sm initSM 5091)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 304
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7783, 5087, 5088, 5090, 5091],
        outs := [5092], params := [64, 0, 64, 8] }
      7783 5087 5088 5090 5091 5092
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7783 5087 5088 5090 5091 5092 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8793 = rank-0 sharded-range all2all (PM node 513).
  have hP0 : denoteGraph_ringAttn pm initPM 8793
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15286)
          (denoteGraph_ringAttn pm initPM 8783) (denoteGraph_ringAttn pm initPM 8785)
          (denoteGraph_ringAttn pm initPM 8789) (denoteGraph_ringAttn pm initPM 8791)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 669
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15286, 8783, 8785, 8789, 8791],
        outs := [8793], params := [64, 0, 32, 8] }
      15286 8783 8785 8789 8791 8793
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 15286 8783 8785 8789 8791 8793 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8794 = rank-1 sharded-range all2all (PM node 516).
  have hP1 : denoteGraph_ringAttn pm initPM 8794
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15309)
          (denoteGraph_ringAttn pm initPM 8784) (denoteGraph_ringAttn pm initPM 8786)
          (denoteGraph_ringAttn pm initPM 8790) (denoteGraph_ringAttn pm initPM 8792)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 672
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15309, 8784, 8786, 8790, 8792],
        outs := [8794], params := [64, 32, 64, 8] }
      15309 8784 8786 8790 8792 8794
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 15309 8784 8786 8790 8792 8794 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 15286) (denoteGraph_ringAttn pm initPM 15309)
      (denoteGraph_ringAttn pm initPM 8783) (denoteGraph_ringAttn pm initPM 8784)
      (denoteGraph_ringAttn pm initPM 8785) (denoteGraph_ringAttn pm initPM 8786)
      (denoteGraph_ringAttn pm initPM 8789) (denoteGraph_ringAttn pm initPM 8790)
      (denoteGraph_ringAttn pm initPM 8791) (denoteGraph_ringAttn pm initPM 8792)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf5092_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf5092_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 5092
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8793, denoteGraph_ringAttn pm initPM 8794] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8793).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8794).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 5092).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5092 5092 8793 8794 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L8 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7772 — second position of the L8 pre-MoE residual `mref2(5081)` (2-tp, PM
    shards `15267`/`15275`).  Unlike L2's `7720` there is no gather-to-full/chunk
    because `5081` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 211, PM nodes 477/478). -/
theorem recon_intermediateGoal_7772_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7772
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8769, hs8770⟩ := twoTp_gather _ _ intermediateGoal_5081 5081 8769 8770
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5081_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7772 : denoteGraph_ringAttn sm initSM 7772 = id (denoteGraph_ringAttn sm initSM 5081) :=
    ringAttn_reduce1_pm_opaque sm initSM 289
      { rank := 0, op := "OpName.FW_multiref", ins := [5081], outs := [7768, 7772], params := [2] }
      5081 7772 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5081 7768 7772 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15267 : denoteGraph_ringAttn pm initPM 15267 = id (denoteGraph_ringAttn pm initPM 8769) :=
    ringAttn_reduce1_pm_opaque pm initPM 639
      { rank := 0, op := "OpName.FW_multiref", ins := [8769], outs := [15263, 15267], params := [2] }
      8769 15267 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8769 15263 15267 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15275 : denoteGraph_ringAttn pm initPM 15275 = id (denoteGraph_ringAttn pm initPM 8770) :=
    ringAttn_reduce1_pm_opaque pm initPM 640
      { rank := 1, op := "OpName.FW_multiref", ins := [8770], outs := [15271, 15275], params := [2] }
      8770 15275 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8770 15271 15275 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7772 p15267 p15275
  have hsp0 : (denoteGraph_ringAttn pm initPM 15267).shape = [2048, 1024] := by
    rw [p15267]; exact hs8769
  have hsp1 : (denoteGraph_ringAttn pm initPM 15275).shape = [2048, 1024] := by
    rw [p15275]; exact hs8770
  have hval : denoteGraph_ringAttn sm initSM 7772
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15267, denoteGraph_ringAttn pm initPM 15275] := by
    rw [s7772, hbr11, ← p15267, ← p15275]
  have hshape : (denoteGraph_ringAttn sm initSM 7772).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7772 7772 15267 15275 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5112 — post-MoE residual add `5092 + 5111` (2-tp, PM `8871`/`8872`). -/
theorem recon_intermediateGoal_5112_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5112
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs8793, hs8794⟩ := twoTp_gather _ _ intermediateGoal_5092 5092 8793 8794
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5092_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs8867, hs8868⟩ := twoTp_gather _ _ intermediateGoal_5111 5111 8867 8868
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5111_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5112
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 5092) (denoteGraph_ringAttn sm initSM 5111) :=
    ringAttn_reduce2_pm_opaque sm initSM 311
      { rank := 0, op := "OpName.FW_add", ins := [5092, 5111], outs := [5112] }
      5092 5111 5112 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 5092 5111 5112)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8871
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8793) (denoteGraph_ringAttn pm initPM 8867) :=
    ringAttn_reduce2_pm_opaque pm initPM 683
      { rank := 0, op := "OpName.FW_add", ins := [8793, 8867], outs := [8871] }
      8793 8867 8871 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 8793 8867 8871)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8872
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8794) (denoteGraph_ringAttn pm initPM 8868) :=
    ringAttn_reduce2_pm_opaque pm initPM 684
      { rank := 1, op := "OpName.FW_add", ins := [8794, 8868], outs := [8872] }
      8794 8868 8872 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 8794 8868 8872)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5112
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8871, denoteGraph_ringAttn pm initPM 8872] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs8793 hs8794 hs8867 hs8868,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8871).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8793 hs8867
  have hsp1 : (denoteGraph_ringAttn pm initPM 8872).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8794 hs8868
  have hshape : (denoteGraph_ringAttn sm initSM 5112).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5112 5112 8871 8872 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5113 — `FW_float(5112)` (identity, 2-tp PM `8877`/`8878`). -/
theorem recon_intermediateGoal_5113_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5113
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs8871, hs8872⟩ := twoTp_gather _ _ intermediateGoal_5112 5112 8871 8872
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5112_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5113 = id (denoteGraph_ringAttn sm initSM 5112) :=
    ringAttn_reduce1_pm_opaque sm initSM 312
      { rank := 0, op := "OpName.FW_float", ins := [5112], outs := [5113] }
      5112 5113 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5112 5113 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8877 = id (denoteGraph_ringAttn pm initPM 8871) :=
    ringAttn_reduce1_pm_opaque pm initPM 685
      { rank := 0, op := "OpName.FW_float", ins := [8871], outs := [8877] }
      8871 8877 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8871 8877 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8878 = id (denoteGraph_ringAttn pm initPM 8872) :=
    ringAttn_reduce1_pm_opaque pm initPM 686
      { rank := 1, op := "OpName.FW_float", ins := [8872], outs := [8878] }
      8872 8878 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8872 8878 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5113
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8877, denoteGraph_ringAttn pm initPM 8878] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8877).shape = [2048, 1024] := by rw [rP0]; exact hs8871
  have hsp1 : (denoteGraph_ringAttn pm initPM 8878).shape = [2048, 1024] := by rw [rP1]; exact hs8872
  have hshape : (denoteGraph_ringAttn sm initSM 5113).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5113 5113 8877 8878 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5114 — cross-block residual add `7772 + 5113` (2-tp, PM `8881`/`8882`). -/
theorem recon_intermediateGoal_5114_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5114
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs15267, hs15275⟩ := twoTp_gather _ _ intermediateGoal_7772 7772 15267 15275
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7772_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs8877, hs8878⟩ := twoTp_gather _ _ intermediateGoal_5113 5113 8877 8878
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5113_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5114
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7772) (denoteGraph_ringAttn sm initSM 5113) :=
    ringAttn_reduce2_pm_opaque sm initSM 313
      { rank := 0, op := "OpName.FW_add", ins := [7772, 5113], outs := [5114] }
      7772 5113 5114 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7772 5113 5114)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8881
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15267) (denoteGraph_ringAttn pm initPM 8877) :=
    ringAttn_reduce2_pm_opaque pm initPM 687
      { rank := 0, op := "OpName.FW_add", ins := [15267, 8877], outs := [8881] }
      15267 8877 8881 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15267 8877 8881)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8882
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15275) (denoteGraph_ringAttn pm initPM 8878) :=
    ringAttn_reduce2_pm_opaque pm initPM 688
      { rank := 1, op := "OpName.FW_add", ins := [15275, 8878], outs := [8882] }
      15275 8878 8882 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15275 8878 8882)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5114
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8881, denoteGraph_ringAttn pm initPM 8882] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15267 hs15275 hs8877 hs8878,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8881).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15267 hs8877
  have hsp1 : (denoteGraph_ringAttn pm initPM 8882).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15275 hs8878
  have hshape : (denoteGraph_ringAttn sm initSM 5114).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5114 5114 8881 8882 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5116 — RMSNorm of `mref2-first(5114)` with replicated weight `5115`
    (2-tp, PM `8885`/`8886`). -/
theorem recon_intermediateGoal_5116_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5116
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs8881, hs8882⟩ := twoTp_gather _ _ intermediateGoal_5114 5114 8881 8882
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5114_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7933 : denoteGraph_ringAttn sm initSM 7799 = id (denoteGraph_ringAttn sm initSM 5114) :=
    ringAttn_reduce1_pm_opaque sm initSM 314
      { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803], params := [2] }
      5114 7799 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5114 7799 7803)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15325 : denoteGraph_ringAttn pm initPM 15325 = id (denoteGraph_ringAttn pm initPM 8881) :=
    ringAttn_reduce1_pm_opaque pm initPM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329], params := [2] }
      8881 15325 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8881 15325 15329)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15333 : denoteGraph_ringAttn pm initPM 15333 = id (denoteGraph_ringAttn pm initPM 8882) :=
    ringAttn_reduce1_pm_opaque pm initPM 690
      { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337], params := [2] }
      8882 15333 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8882 15333 15337)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7933 p15325 p15333
  have hs15325 : (denoteGraph_ringAttn pm initPM 15325).shape = [2048, 1024] := by
    rw [p15325]; exact hs8881
  have hs15333 : (denoteGraph_ringAttn pm initPM 15333).shape = [2048, 1024] := by
    rw [p15333]; exact hs8882
  have hbr39 : denoteGraph_ringAttn sm initSM 7799
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15325, denoteGraph_ringAttn pm initPM 15333] := by
    rw [s7933, hbr44, ← p15325, ← p15333]
  have hw5115 : denoteGraph_ringAttn sm initSM 5115 = denoteGraph_ringAttn pm initPM 5115 :=
    veq_weight_ring initSM initPM hInit initGoal_5115 (by native_decide) 5115
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5116
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7799) (denoteGraph_ringAttn sm initSM 5115) :=
    ringAttn_reduce2_pm_opaque sm initSM 315
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7799, 5115], outs := [5116] }
      7799 5115 5116 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7799 5115 5116)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8885
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15325) (denoteGraph_ringAttn pm initPM 5115) :=
    ringAttn_reduce2_pm_opaque pm initPM 691
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15325, 5115], outs := [8885] }
      15325 5115 8885 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15325 5115 8885)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8886
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15333) (denoteGraph_ringAttn pm initPM 5115) :=
    ringAttn_reduce2_pm_opaque pm initPM 692
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15333, 5115], outs := [8886] }
      15333 5115 8886 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15333 5115 8886)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5116
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8885, denoteGraph_ringAttn pm initPM 8886] := by
    rw [rSM, hbr39, hw5115, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15325 hs15333,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8885).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15325
  have hsp1 : (denoteGraph_ringAttn pm initPM 8886).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15333
  have hshape : (denoteGraph_ringAttn sm initSM 5116).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5116 5116 8885 8886 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5118 — per-head Q projection `fw_per_head_linear(mref3₀(5116), 5117)`
    (2-tp, PM `8887`/`8888`, weight `5117 : [16,64,1024]`). -/
theorem recon_intermediateGoal_5118_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5118
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8885, hs8886⟩ := twoTp_gather _ _ intermediateGoal_5116 5116 8885 8886
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5116_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7942 : denoteGraph_ringAttn sm initSM 7808 = id (denoteGraph_ringAttn sm initSM 5116) :=
    ringAttn_reduce1_pm_opaque sm initSM 316
      { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
      5116 7808 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5116 7808 7812 7816)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15342 : denoteGraph_ringAttn pm initPM 15342 = id (denoteGraph_ringAttn pm initPM 8885) :=
    ringAttn_reduce1_pm_opaque pm initPM 693
      { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
      8885 15342 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8885 15342 15346 15350)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15355 : denoteGraph_ringAttn pm initPM 15355 = id (denoteGraph_ringAttn pm initPM 8886) :=
    ringAttn_reduce1_pm_opaque pm initPM 694
      { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
      8886 15355 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8886 15355 15359 15363)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7942 p15342 p15355
  have hs15342 : (denoteGraph_ringAttn pm initPM 15342).shape = [2048, 1024] := by
    rw [p15342]; exact hs8885
  have hs15355 : (denoteGraph_ringAttn pm initPM 15355).shape = [2048, 1024] := by
    rw [p15355]; exact hs8886
  have hbr48 : denoteGraph_ringAttn sm initSM 7808
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15342, denoteGraph_ringAttn pm initPM 15355] := by
    rw [s7942, hbr46, ← p15342, ← p15355]
  have hw5117 : denoteGraph_ringAttn sm initSM 5117 = denoteGraph_ringAttn pm initPM 5117 :=
    veq_weight_ring initSM initPM hInit initGoal_5117 (by native_decide) 5117
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5117 : (denoteGraph_ringAttn sm initSM 5117).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5117 (by native_decide) 5117 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5117 : (denoteGraph_ringAttn pm initPM 5117).shape = [16, 64, 1024] := by
    rw [← hw5117]; exact hsw5117
  have rSM : denoteGraph_ringAttn sm initSM 5118
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7808) (denoteGraph_ringAttn sm initSM 5117) :=
    ringAttn_reduce2_pm_opaque sm initSM 317
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7808, 5117], outs := [5118] }
      7808 5117 5118 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7808 5117 5118 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8887
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15342) (denoteGraph_ringAttn pm initPM 5117) :=
    ringAttn_reduce2_pm_opaque pm initPM 695
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15342, 5117], outs := [8887] }
      15342 5117 8887 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15342 5117 8887 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8888
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15355) (denoteGraph_ringAttn pm initPM 5117) :=
    ringAttn_reduce2_pm_opaque pm initPM 698
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15355, 5117], outs := [8888] }
      15355 5117 8888 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15355 5117 8888 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5118
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8887, denoteGraph_ringAttn pm initPM 8888] := by
    rw [rSM, hbr48, hw5117, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs15342 hs15355 hpw5117,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8887).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15342 hpw5117
  have hsp1 : (denoteGraph_ringAttn pm initPM 8888).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15355 hpw5117
  have hshape : (denoteGraph_ringAttn sm initSM 5118).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5118 5118 8887 8888 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5120 — per-head K projection `fw_per_head_linear(mref3₁(5116), 5119)`
    (2-tp, PM `8899`/`8900`, weight `5119 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5120_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5120
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8885, hs8886⟩ := twoTp_gather _ _ intermediateGoal_5116 5116 8885 8886
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5116_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7812 : denoteGraph_ringAttn sm initSM 7812 = id (denoteGraph_ringAttn sm initSM 5116) :=
    ringAttn_reduce1_pm_opaque sm initSM 316
      { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
      5116 7812 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5116 7808 7812 7816 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15346 : denoteGraph_ringAttn pm initPM 15346 = id (denoteGraph_ringAttn pm initPM 8885) :=
    ringAttn_reduce1_pm_opaque pm initPM 693
      { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
      8885 15346 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8885 15342 15346 15350 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15359 : denoteGraph_ringAttn pm initPM 15359 = id (denoteGraph_ringAttn pm initPM 8886) :=
    ringAttn_reduce1_pm_opaque pm initPM 694
      { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
      8886 15359 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8886 15355 15359 15363 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7812 p15346 p15359
  have hs15346 : (denoteGraph_ringAttn pm initPM 15346).shape = [2048, 1024] := by
    rw [p15346]; exact hs8885
  have hs15359 : (denoteGraph_ringAttn pm initPM 15359).shape = [2048, 1024] := by
    rw [p15359]; exact hs8886
  have hbr52 : denoteGraph_ringAttn sm initSM 7812
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15346, denoteGraph_ringAttn pm initPM 15359] := by
    rw [s7812, hbr46, ← p15346, ← p15359]
  have hw5119 : denoteGraph_ringAttn sm initSM 5119 = denoteGraph_ringAttn pm initPM 5119 :=
    veq_weight_ring initSM initPM hInit initGoal_5119 (by native_decide) 5119
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5119 : (denoteGraph_ringAttn sm initSM 5119).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5119 (by native_decide) 5119 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5119 : (denoteGraph_ringAttn pm initPM 5119).shape = [4, 64, 1024] := by
    rw [← hw5119]; exact hsw5119
  have rSM : denoteGraph_ringAttn sm initSM 5120
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7812) (denoteGraph_ringAttn sm initSM 5119) :=
    ringAttn_reduce2_pm_opaque sm initSM 318
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7812, 5119], outs := [5120] }
      7812 5119 5120 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7812 5119 5120 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8899
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15346) (denoteGraph_ringAttn pm initPM 5119) :=
    ringAttn_reduce2_pm_opaque pm initPM 696
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15346, 5119], outs := [8899] }
      15346 5119 8899 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15346 5119 8899 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8900
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15359) (denoteGraph_ringAttn pm initPM 5119) :=
    ringAttn_reduce2_pm_opaque pm initPM 699
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15359, 5119], outs := [8900] }
      15359 5119 8900 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15359 5119 8900 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5120
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8899, denoteGraph_ringAttn pm initPM 8900] := by
    rw [rSM, hbr52, hw5119, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15346 hs15359 hpw5119,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8899).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15346 hpw5119
  have hsp1 : (denoteGraph_ringAttn pm initPM 8900).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15359 hpw5119
  have hshape : (denoteGraph_ringAttn sm initSM 5120).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5120 5120 8899 8900 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5122 — per-head V projection `fw_per_head_linear(mref3₂(5116), 5121)`
    (2-tp, PM `8909`/`8910`, weight `5121 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5122_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5122
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8885, hs8886⟩ := twoTp_gather _ _ intermediateGoal_5116 5116 8885 8886
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5116_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7816 : denoteGraph_ringAttn sm initSM 7816 = id (denoteGraph_ringAttn sm initSM 5116) :=
    ringAttn_reduce1_pm_opaque sm initSM 316
      { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
      5116 7816 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5116 7808 7812 7816 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15350 : denoteGraph_ringAttn pm initPM 15350 = id (denoteGraph_ringAttn pm initPM 8885) :=
    ringAttn_reduce1_pm_opaque pm initPM 693
      { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
      8885 15350 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8885 15342 15346 15350 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15363 : denoteGraph_ringAttn pm initPM 15363 = id (denoteGraph_ringAttn pm initPM 8886) :=
    ringAttn_reduce1_pm_opaque pm initPM 694
      { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
      8886 15363 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8886 15355 15359 15363 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7816 p15350 p15363
  have hs15350 : (denoteGraph_ringAttn pm initPM 15350).shape = [2048, 1024] := by
    rw [p15350]; exact hs8885
  have hs15363 : (denoteGraph_ringAttn pm initPM 15363).shape = [2048, 1024] := by
    rw [p15363]; exact hs8886
  have hbr56 : denoteGraph_ringAttn sm initSM 7816
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15350, denoteGraph_ringAttn pm initPM 15363] := by
    rw [s7816, hbr46, ← p15350, ← p15363]
  have hw5121 : denoteGraph_ringAttn sm initSM 5121 = denoteGraph_ringAttn pm initPM 5121 :=
    veq_weight_ring initSM initPM hInit initGoal_5121 (by native_decide) 5121
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5121 : (denoteGraph_ringAttn sm initSM 5121).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5121 (by native_decide) 5121 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5121 : (denoteGraph_ringAttn pm initPM 5121).shape = [4, 64, 1024] := by
    rw [← hw5121]; exact hsw5121
  have rSM : denoteGraph_ringAttn sm initSM 5122
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7816) (denoteGraph_ringAttn sm initSM 5121) :=
    ringAttn_reduce2_pm_opaque sm initSM 319
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7816, 5121], outs := [5122] }
      7816 5121 5122 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7816 5121 5122 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8909
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15350) (denoteGraph_ringAttn pm initPM 5121) :=
    ringAttn_reduce2_pm_opaque pm initPM 697
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15350, 5121], outs := [8909] }
      15350 5121 8909 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15350 5121 8909 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8910
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15363) (denoteGraph_ringAttn pm initPM 5121) :=
    ringAttn_reduce2_pm_opaque pm initPM 700
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15363, 5121], outs := [8910] }
      15363 5121 8910 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15363 5121 8910 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5122
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8909, denoteGraph_ringAttn pm initPM 8910] := by
    rw [rSM, hbr56, hw5121, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15350 hs15363 hpw5121,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8909).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15350 hpw5121
  have hsp1 : (denoteGraph_ringAttn pm initPM 8910).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15363 hpw5121
  have hshape : (denoteGraph_ringAttn sm initSM 5122).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5122 5122 8909 8910 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L8 rotary cos/sin cache agreement: `sm 4691 = pm 11861` (`= 11853 + 3`). -/
theorem hcache_4691_11861 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11861 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11861 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11861 8 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 5124 — rotary-embedding Q output `rotary(4691, 5123, 5118, 5120).1`
    (2-tp, PM `8921`/`8922`; positions `5123 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_5124_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5124
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs8887, hs8888⟩ := twoTp_gather _ _ intermediateGoal_5118 5118 8887 8888
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5118_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_5120 5120 8899 8900
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5120_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11861 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5123 = denoteGraph_ringAttn pm initPM 5123 :=
    veq_weight_ring initSM initPM hInit initGoal_5123 (by native_decide) 5123
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5123 : (denoteGraph_ringAttn sm initSM 5123).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5123 (by native_decide) 5123 [4096]
      rfl rfl (by native_decide)
  have c8919 : denoteGraph_ringAttn pm initPM 8919
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5123) :=
    ringAttn_reduce1_pm_opaque pm initPM 8
      { rank := 0, op := "OpName.ChunkPrim", ins := [5123], outs := [8919], params := [0] }
      5123 8919 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5123 8919 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8920 : denoteGraph_ringAttn pm initPM 8920
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5123) :=
    ringAttn_reduce1_pm_opaque pm initPM 21
      { rank := 1, op := "OpName.ChunkPrim", ins := [5123], outs := [8920], params := [0] }
      5123 8920 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5123 8920 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5124
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5123)
          (denoteGraph_ringAttn sm initSM 5118) (denoteGraph_ringAttn sm initSM 5120) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 320
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5123, 5118, 5120], outs := [5124, 5125], params := [16, 4] }
          5124 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 320 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 320 5123 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 320 5118 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 320 5120 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8921
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11861) (denoteGraph_ringAttn pm initPM 8919)
          (denoteGraph_ringAttn pm initPM 8887) (denoteGraph_ringAttn pm initPM 8899) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 701
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11861, 8919, 8887, 8899], outs := [8921, 8923], params := [16, 4] }
          8921 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 701 11861 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 701 8919 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 701 8887 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 701 8899 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8922
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11861) (denoteGraph_ringAttn pm initPM 8920)
          (denoteGraph_ringAttn pm initPM 8888) (denoteGraph_ringAttn pm initPM 8900) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 702
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11861, 8920, 8888, 8900], outs := [8922, 8924], params := [16, 4] }
          8922 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 702 11861 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 702 8920 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 702 8888 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 702 8900 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5124
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8921, denoteGraph_ringAttn pm initPM 8922] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5123) (denoteGraph_ringAttn pm initPM 8887)
          (denoteGraph_ringAttn pm initPM 8888) 2048 16 64 (by omega) (by omega) (by omega)
          hsp5123 hs8887 hs8888,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8919
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5123) from c8919),
        ← (show denoteGraph_ringAttn pm initPM 8920
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5123) from c8920),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8921).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8887
  have hsp1 : (denoteGraph_ringAttn pm initPM 8922).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8888
  have hshape : (denoteGraph_ringAttn sm initSM 5124).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5124 5124 8921 8922 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 5125 — rotary-embedding K output `rotary(4691, 5123, 5118, 5120).2`
    (2-tp, PM `8923`/`8924`). -/
theorem recon_intermediateGoal_5125_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5125
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_5118 5118 8887 8888
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5118_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs8899, hs8900⟩ := twoTp_gather _ _ intermediateGoal_5120 5120 8899 8900
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5120_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11861 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5123 = denoteGraph_ringAttn pm initPM 5123 :=
    veq_weight_ring initSM initPM hInit initGoal_5123 (by native_decide) 5123
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5123 : (denoteGraph_ringAttn sm initSM 5123).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5123 (by native_decide) 5123 [4096]
      rfl rfl (by native_decide)
  have c8919 : denoteGraph_ringAttn pm initPM 8919
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5123) :=
    ringAttn_reduce1_pm_opaque pm initPM 8
      { rank := 0, op := "OpName.ChunkPrim", ins := [5123], outs := [8919], params := [0] }
      5123 8919 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5123 8919 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8920 : denoteGraph_ringAttn pm initPM 8920
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5123) :=
    ringAttn_reduce1_pm_opaque pm initPM 21
      { rank := 1, op := "OpName.ChunkPrim", ins := [5123], outs := [8920], params := [0] }
      5123 8920 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5123 8920 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5125
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5123)
          (denoteGraph_ringAttn sm initSM 5118) (denoteGraph_ringAttn sm initSM 5120) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 320
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5123, 5118, 5120], outs := [5124, 5125], params := [16, 4] }
          5125 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5123 5118 5120 5124 5125 (by decide),
        ringAttn_prefix_read_pm sm initSM 320 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 320 5123 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 320 5118 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 320 5120 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8923
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11861) (denoteGraph_ringAttn pm initPM 8919)
          (denoteGraph_ringAttn pm initPM 8887) (denoteGraph_ringAttn pm initPM 8899) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 701
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11861, 8919, 8887, 8899], outs := [8921, 8923], params := [16, 4] }
          8923 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11861 8919 8887 8899 8921 8923 (by decide),
        ringAttn_prefix_read_pm pm initPM 701 11861 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 701 8919 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 701 8887 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 701 8899 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8924
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11861) (denoteGraph_ringAttn pm initPM 8920)
          (denoteGraph_ringAttn pm initPM 8888) (denoteGraph_ringAttn pm initPM 8900) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 702
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11861, 8920, 8888, 8900], outs := [8922, 8924], params := [16, 4] }
          8924 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11861 8920 8888 8900 8922 8924 (by decide),
        ringAttn_prefix_read_pm pm initPM 702 11861 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 702 8920 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 702 8888 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 702 8900 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5125
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8923, denoteGraph_ringAttn pm initPM 8924] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5123) (denoteGraph_ringAttn pm initPM 8899)
          (denoteGraph_ringAttn pm initPM 8900) 2048 4 64 (by omega) (by omega) (by omega)
          hsp5123 hs8899 hs8900,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8919
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5123) from c8919),
        ← (show denoteGraph_ringAttn pm initPM 8920
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5123) from c8920),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8923).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8899
  have hsp1 : (denoteGraph_ringAttn pm initPM 8924).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8900
  have hshape : (denoteGraph_ringAttn sm initSM 5125).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5125 5125 8923 8924 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
