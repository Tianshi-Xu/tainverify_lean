/- Worker #23 — Layer-4 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_4858_ringAttn` (the layer-4
   sliding-window attention output, unconditional-given-WF) through the layer-4
   forward block.

   Unlike L2, the L4 block has NO gather-to-full node (L2's PM node 150
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L4
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_4862` targets `[8007, 8008]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L3Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 4859 — 2-tp reshape of the L4 attention output `4858 : [4096,16,64]` to
    `[4096,1024]` (SM node 127, PM nodes 315/316). -/
theorem recon_intermediateGoal_4859_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4859
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs7995, hs7996⟩ := twoTp_gather _ _ intermediateGoal_4858 4858 7995 7996
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4858_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4859
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4858) :=
    ringAttn_reshape_reduce_pm sm initSM 127 0 4858 4859 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7997
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7995) :=
    ringAttn_reshape_reduce_pm pm initPM 315 0 7995 7997 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7998
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7996) :=
    ringAttn_reshape_reduce_pm pm initPM 316 1 7996 7998 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4859
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7997, denoteGraph_ringAttn pm initPM 7998] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs7995 hs7996
  have hs7997 : (denoteGraph_ringAttn pm initPM 7997).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs7998 : (denoteGraph_ringAttn pm initPM 7998).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4859 : (denoteGraph_ringAttn sm initSM 4859).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4859 4859 7997 7998 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4859 hs7997 hs7998

/-- 4860 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 128, PM
    nodes 317/318). -/
theorem recon_intermediateGoal_4860_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4860
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs7997, hs7998⟩ := twoTp_gather _ _ intermediateGoal_4859 4859 7997 7998
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4859_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4859 : (denoteGraph_ringAttn sm initSM 4859).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs7997])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4860
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4859) :=
    ringAttn_reshape_reduce_pm sm initSM 128 0 4859 4860 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8003
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7997) :=
    ringAttn_reshape_reduce_pm pm initPM 317 0 7997 8003 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8004
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7998) :=
    ringAttn_reshape_reduce_pm pm initPM 318 1 7998 8004 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8003 = denoteGraph_ringAttn pm initPM 7997 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs7997]
  have h18 : denoteGraph_ringAttn pm initPM 8004 = denoteGraph_ringAttn pm initPM 7998 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs7998]
  have hval : denoteGraph_ringAttn sm initSM 4860
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8003, denoteGraph_ringAttn pm initPM 8004] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4859, hval05, hnr, ← h17, ← h18]
  have hs8003 : (denoteGraph_ringAttn pm initPM 8003).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8004 : (denoteGraph_ringAttn pm initPM 8004).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4860 : (denoteGraph_ringAttn sm initSM 4860).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4860 4860 8003 8004 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4860 hs8003 hs8004

/-- 4862 — 2-tp down-projection `fw_linear(4860, 4861)` (weight `4861 : [1024,1024]`,
    SM node 129, PM nodes 319/320). -/
theorem recon_intermediateGoal_4862_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4862
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs8003, hs8004⟩ := twoTp_gather _ _ intermediateGoal_4860 4860 8003 8004
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4860_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4861 : denoteGraph_ringAttn sm initSM 4861 = denoteGraph_ringAttn pm initPM 4861 :=
    veq_weight_ring initSM initPM hInit initGoal_4861 (by native_decide) 4861
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4861 : (denoteGraph_ringAttn sm initSM 4861).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4861 (by native_decide) 4861 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw4861 : (denoteGraph_ringAttn pm initPM 4861).shape = [1024, 1024] := by
    rw [← hw4861]; exact hsw4861
  have rSM : denoteGraph_ringAttn sm initSM 4862
      = fw_linear (denoteGraph_ringAttn sm initSM 4860) (denoteGraph_ringAttn sm initSM 4861) :=
    ringAttn_reduce2_pm_opaque sm initSM 129
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4860, 4861], outs := [4862] }
      4860 4861 4862 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4860 4861 4862)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8007
      = fw_linear (denoteGraph_ringAttn pm initPM 8003) (denoteGraph_ringAttn pm initPM 4861) :=
    ringAttn_reduce2_pm_opaque pm initPM 319
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8003, 4861], outs := [8007] }
      8003 4861 8007 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8003 4861 8007)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8008
      = fw_linear (denoteGraph_ringAttn pm initPM 8004) (denoteGraph_ringAttn pm initPM 4861) :=
    ringAttn_reduce2_pm_opaque pm initPM 320
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8004, 4861], outs := [8008] }
      8004 4861 8008 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8004 4861 8008)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4862
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8007, denoteGraph_ringAttn pm initPM 8008] := by
    rw [rSM, hval06, hw4861, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs8003 hs8004 hpw4861,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8007).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8003 hpw4861
  have hsp1 : (denoteGraph_ringAttn pm initPM 8008).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8004 hpw4861
  have hshape : (denoteGraph_ringAttn sm initSM 4862).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4862 4862 8007 8008 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4863 — 2-tp identity view of `4862` (SM node 130, PM nodes 321/322). -/
theorem recon_intermediateGoal_4863_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4863
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs8007, hs8008⟩ := twoTp_gather _ _ intermediateGoal_4862 4862 8007 8008
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4862_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4862 : (denoteGraph_ringAttn sm initSM 4862).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8007])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4863
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4862) :=
    ringAttn_reduce1_pm_opaque sm initSM 130
      { rank := 0, op := "OpName.FW_view", ins := [4862], outs := [4863], params := [4096, 1024] }
      4862 4863 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4862 4863)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8017
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8007) :=
    ringAttn_reduce1_pm_opaque pm initPM 321
      { rank := 0, op := "OpName.FW_view", ins := [8007], outs := [8017], params := [2048, 1024] }
      8007 8017 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8007 8017)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8018
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8008) :=
    ringAttn_reduce1_pm_opaque pm initPM 322
      { rank := 1, op := "OpName.FW_view", ins := [8008], outs := [8018], params := [2048, 1024] }
      8008 8018 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8008 8018)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 8017 = denoteGraph_ringAttn pm initPM 8007 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8007]
  have h32 : denoteGraph_ringAttn pm initPM 8018 = denoteGraph_ringAttn pm initPM 8008 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8008]
  have hval : denoteGraph_ringAttn sm initSM 4863
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8017, denoteGraph_ringAttn pm initPM 8018] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4862, hval08, hnr, ← h31, ← h32]
  have hs8017 : (denoteGraph_ringAttn pm initPM 8017).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8018 : (denoteGraph_ringAttn pm initPM 8018).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4863 : (denoteGraph_ringAttn sm initSM 4863).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4863 4863 8017 8018 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4863 hs8017 hs8018

/-- 4864 — 2-tp `FW_float(4863)` (identity, SM node 131, PM nodes 323/324). -/
theorem recon_intermediateGoal_4864_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4864
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs8017, hs8018⟩ := twoTp_gather _ _ intermediateGoal_4863 4863 8017 8018
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4863_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4864 = id (denoteGraph_ringAttn sm initSM 4863) :=
    ringAttn_reduce1_pm_opaque sm initSM 131
      { rank := 0, op := "OpName.FW_float", ins := [4863], outs := [4864] }
      4863 4864 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4863 4864 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8021 = id (denoteGraph_ringAttn pm initPM 8017) :=
    ringAttn_reduce1_pm_opaque pm initPM 323
      { rank := 0, op := "OpName.FW_float", ins := [8017], outs := [8021] }
      8017 8021 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8017 8021 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8022 = id (denoteGraph_ringAttn pm initPM 8018) :=
    ringAttn_reduce1_pm_opaque pm initPM 324
      { rank := 1, op := "OpName.FW_float", ins := [8018], outs := [8022] }
      8018 8022 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8018 8022 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 4864
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8021, denoteGraph_ringAttn pm initPM 8022] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8021).shape = [2048, 1024] := by rw [rP0]; exact hs8017
  have hsp1 : (denoteGraph_ringAttn pm initPM 8022).shape = [2048, 1024] := by rw [rP1]; exact hs8018
  have hshape : (denoteGraph_ringAttn sm initSM 4864).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4864 4864 8021 8022 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7543 — 2-tp `mref2`-second copy of the L2 residual `4844` (SM node 119,
    PM nodes 299/300), carried into the L4 residual add. -/
theorem recon_intermediateGoal_7543_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7543
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs7951, hs7952⟩ := twoTp_gather _ _ intermediateGoal_4844 4844 7951 7952
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4844_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7543 : denoteGraph_ringAttn sm initSM 7543 = id (denoteGraph_ringAttn sm initSM 4844) :=
    ringAttn_reduce1_pm_opaque sm initSM 119
      { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543], params := [2] }
      4844 7543 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4844 7539 7543 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14809 : denoteGraph_ringAttn pm initPM 14809 = id (denoteGraph_ringAttn pm initPM 7951) :=
    ringAttn_reduce1_pm_opaque pm initPM 299
      { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809], params := [2] }
      7951 14809 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 7951 14805 14809 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14817 : denoteGraph_ringAttn pm initPM 14817 = id (denoteGraph_ringAttn pm initPM 7952) :=
    ringAttn_reduce1_pm_opaque pm initPM 300
      { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817], params := [2] }
      7952 14817 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 7952 14813 14817 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7543 p14809 p14817
  have hsp0 : (denoteGraph_ringAttn pm initPM 14809).shape = [2048, 1024] := by
    rw [p14809]; exact hs7951
  have hsp1 : (denoteGraph_ringAttn pm initPM 14817).shape = [2048, 1024] := by
    rw [p14817]; exact hs7952
  have hval : denoteGraph_ringAttn sm initSM 7543
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14809, denoteGraph_ringAttn pm initPM 14817] := by
    rw [s7543, hbr90, ← p14809, ← p14817]
  have hshape : (denoteGraph_ringAttn sm initSM 7543).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7543 7543 14809 14817 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4865 — 2-tp L4 residual add `7543 + 4864` (SM node 132, PM nodes 325/326). -/
theorem recon_intermediateGoal_4865_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4865
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs14809, hs14817⟩ := twoTp_gather _ _ intermediateGoal_7543 7543 14809 14817
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7543_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs8021, hs8022⟩ := twoTp_gather _ _ intermediateGoal_4864 4864 8021 8022
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4864_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4865
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7543) (denoteGraph_ringAttn sm initSM 4864) :=
    ringAttn_reduce2_pm_opaque sm initSM 132
      { rank := 0, op := "OpName.FW_add", ins := [7543, 4864], outs := [4865] }
      7543 4864 4865 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7543 4864 4865)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8025
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14809) (denoteGraph_ringAttn pm initPM 8021) :=
    ringAttn_reduce2_pm_opaque pm initPM 325
      { rank := 0, op := "OpName.FW_add", ins := [14809, 8021], outs := [8025] }
      14809 8021 8025 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 14809 8021 8025)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8026
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14817) (denoteGraph_ringAttn pm initPM 8022) :=
    ringAttn_reduce2_pm_opaque pm initPM 326
      { rank := 1, op := "OpName.FW_add", ins := [14817, 8022], outs := [8026] }
      14817 8022 8026 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14817 8022 8026)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4865
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8025, denoteGraph_ringAttn pm initPM 8026] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs14809 hs14817 hs8021 hs8022,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8025).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14809 hs8021
  have hsp1 : (denoteGraph_ringAttn pm initPM 8026).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14817 hs8022
  have hshape : (denoteGraph_ringAttn sm initSM 4865).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4865 4865 8025 8026 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4867 — 2-tp RMSNorm of `mref2-first(4865)` with replicated weight
    `4866 : [1024]` (SM node 134, PM nodes 329/330). -/
theorem recon_intermediateGoal_4867_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4867
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8025, hs8026⟩ := twoTp_gather _ _ intermediateGoal_4865 4865 8025 8026
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4865_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7560 : denoteGraph_ringAttn sm initSM 7560 = id (denoteGraph_ringAttn sm initSM 4865) :=
    ringAttn_reduce1_pm_opaque sm initSM 133
      { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564], params := [2] }
      4865 7560 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4865 7560 7564)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14847 : denoteGraph_ringAttn pm initPM 14847 = id (denoteGraph_ringAttn pm initPM 8025) :=
    ringAttn_reduce1_pm_opaque pm initPM 327
      { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851], params := [2] }
      8025 14847 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8025 14847 14851)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14855 : denoteGraph_ringAttn pm initPM 14855 = id (denoteGraph_ringAttn pm initPM 8026) :=
    ringAttn_reduce1_pm_opaque pm initPM 328
      { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859], params := [2] }
      8026 14855 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8026 14855 14859)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7560 p14847 p14855
  have hs14847 : (denoteGraph_ringAttn pm initPM 14847).shape = [2048, 1024] := by
    rw [p14847]; exact hs8025
  have hs14855 : (denoteGraph_ringAttn pm initPM 14855).shape = [2048, 1024] := by
    rw [p14855]; exact hs8026
  have hbr08 : denoteGraph_ringAttn sm initSM 7560
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14847, denoteGraph_ringAttn pm initPM 14855] := by
    rw [s7560, hbr11, ← p14847, ← p14855]
  have hw4866 : denoteGraph_ringAttn sm initSM 4866 = denoteGraph_ringAttn pm initPM 4866 :=
    veq_weight_ring initSM initPM hInit initGoal_4866 (by native_decide) 4866
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4867
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7560) (denoteGraph_ringAttn sm initSM 4866) :=
    ringAttn_reduce2_pm_opaque sm initSM 134
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7560, 4866], outs := [4867] }
      7560 4866 4867 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7560 4866 4867)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8029
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14847) (denoteGraph_ringAttn pm initPM 4866) :=
    ringAttn_reduce2_pm_opaque pm initPM 329
      { rank := 0, op := "OpName.FW_rms_norm", ins := [14847, 4866], outs := [8029] }
      14847 4866 8029 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 14847 4866 8029)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8030
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14855) (denoteGraph_ringAttn pm initPM 4866) :=
    ringAttn_reduce2_pm_opaque pm initPM 330
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14855, 4866], outs := [8030] }
      14855 4866 8030 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14855 4866 8030)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4867
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8029, denoteGraph_ringAttn pm initPM 8030] := by
    rw [rSM, hbr08, hw4866, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs14847 hs14855,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8029).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14847
  have hsp1 : (denoteGraph_ringAttn pm initPM 8030).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14855
  have hshape : (denoteGraph_ringAttn sm initSM 4867).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4867 4867 8029 8030 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4868 — 2-tp `FW_float(mref5-first(4867))` (identity, SM node 136,
    PM nodes 333/337; mref5-first via SM node 135, PM 331/332). -/
theorem recon_intermediateGoal_4868_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4868
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8029, hs8030⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7571 : denoteGraph_ringAttn sm initSM 7571 = id (denoteGraph_ringAttn sm initSM 4867) :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867],
        outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7571 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 4867 7571 [7575, 7579, 7583, 7587])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14866 : denoteGraph_ringAttn pm initPM 14866 = id (denoteGraph_ringAttn pm initPM 8029) :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029],
        outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14866 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 8029 14866 [14870, 14874, 14878, 14882])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14889 : denoteGraph_ringAttn pm initPM 14889 = id (denoteGraph_ringAttn pm initPM 8030) :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030],
        outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14889 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 8030 14889 [14893, 14897, 14901, 14905])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7571 p14866 p14889
  have hbrm : denoteGraph_ringAttn sm initSM 7571
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14866, denoteGraph_ringAttn pm initPM 14889] := by
    rw [s7571, hbr13, ← p14866, ← p14889]
  have rSM : denoteGraph_ringAttn sm initSM 4868 = id (denoteGraph_ringAttn sm initSM 7571) :=
    ringAttn_reduce1_pm_opaque sm initSM 136
      { rank := 0, op := "OpName.FW_float", ins := [7571], outs := [4868] }
      7571 4868 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7571 4868 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8031 = id (denoteGraph_ringAttn pm initPM 14866) :=
    ringAttn_reduce1_pm_opaque pm initPM 333
      { rank := 0, op := "OpName.FW_float", ins := [14866], outs := [8031] }
      14866 8031 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 14866 8031 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8032 = id (denoteGraph_ringAttn pm initPM 14889) :=
    ringAttn_reduce1_pm_opaque pm initPM 337
      { rank := 1, op := "OpName.FW_float", ins := [14889], outs := [8032] }
      14889 8032 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 14889 8032 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs14866 : (denoteGraph_ringAttn pm initPM 14866).shape = [2048, 1024] := by
    rw [p14866]; exact hs8029
  have hs14889 : (denoteGraph_ringAttn pm initPM 14889).shape = [2048, 1024] := by
    rw [p14889]; exact hs8030
  have hval : denoteGraph_ringAttn sm initSM 4868
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8031, denoteGraph_ringAttn pm initPM 8032] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8031).shape = [2048, 1024] := by
    rw [rP0]; exact hs14866
  have hsp1 : (denoteGraph_ringAttn pm initPM 8032).shape = [2048, 1024] := by
    rw [rP1]; exact hs14889
  have hshape : (denoteGraph_ringAttn sm initSM 4868).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4868 4868 8031 8032 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4870 — 2-tp router logits `fw_norm_linear(4868, 4869)` with weight
    `4869 : [64, 1024]` → `[4096, 64]` (SM node 140, PM nodes 341/345). -/
theorem recon_intermediateGoal_4870_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4870
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs8031, hs8032⟩ := twoTp_gather _ _ intermediateGoal_4868 4868 8031 8032
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4868_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4869 : denoteGraph_ringAttn sm initSM 4869 = denoteGraph_ringAttn pm initPM 4869 :=
    veq_weight_ring initSM initPM hInit initGoal_4869 (by native_decide) 4869
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4869 : (denoteGraph_ringAttn sm initSM 4869).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4869 (by native_decide) 4869 [64, 1024]
      rfl rfl (by native_decide)
  have hpw4869 : (denoteGraph_ringAttn pm initPM 4869).shape = [64, 1024] := by
    rw [← hw4869]; exact hsw4869
  have rSM : denoteGraph_ringAttn sm initSM 4870
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 4868) (denoteGraph_ringAttn sm initSM 4869) :=
    ringAttn_reduce2_pm_opaque sm initSM 140
      { rank := 0, op := "OpName.FW_norm_linear", ins := [4868, 4869], outs := [4870] }
      4868 4869 4870 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 4868 4869 4870)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8037
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8031) (denoteGraph_ringAttn pm initPM 4869) :=
    ringAttn_reduce2_pm_opaque pm initPM 341
      { rank := 0, op := "OpName.FW_norm_linear", ins := [8031, 4869], outs := [8037] }
      8031 4869 8037 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 8031 4869 8037)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8038
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8032) (denoteGraph_ringAttn pm initPM 4869) :=
    ringAttn_reduce2_pm_opaque pm initPM 345
      { rank := 1, op := "OpName.FW_norm_linear", ins := [8032, 4869], outs := [8038] }
      8032 4869 8038 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 8032 4869 8038)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4870
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8037, denoteGraph_ringAttn pm initPM 8038] := by
    rw [rSM, hval14, hw4869, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs8031 hs8032 hpw4869,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8037).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8031 hpw4869
  have hsp1 : (denoteGraph_ringAttn pm initPM 8038).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8032 hpw4869
  have hshape : (denoteGraph_ringAttn sm initSM 4870).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4870 4870 8037 8038 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L4 top-k routing (`4871`/`4872`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`8037`/`8038`) directly. -/

/-- Shared L4 top-k core: `4870` (full logits) is the dim-0 gather of the two
    per-rank shards `8037`/`8038`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L4 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 4870
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 8037, denoteGraph_ringAttn pm initPM 8038]
      ∧ (denoteGraph_ringAttn sm initSM 4870).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8037).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8038).shape = [2048, 64]
      ∧ ((sm.nodes.take 144).foldl (applyNodeRingAttn sm) initSM 4870).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 349).foldl (applyNodeRingAttn pm) initPM 8037).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 353).foldl (applyNodeRingAttn pm) initPM 8038).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs8037, hs8038⟩ := twoTp_gather _ _ intermediateGoal_4870 4870 8037 8038
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4870_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs4870sm : (denoteGraph_ringAttn sm initSM 4870).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs8037])]
    simp [List.set, List.getD]
  have hpre4870sm : denoteGraph_ringAttn sm initSM 4870
      = (sm.nodes.take 144).foldl (applyNodeRingAttn sm) initSM 4870 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 4870 144 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 144).foldl (applyNodeRingAttn sm) initSM 4870).shape.reverse.head? = some 64 := by
    rw [← hpre4870sm, hs4870sm]; rfl
  have hpre8037 : denoteGraph_ringAttn pm initPM 8037
      = (pm.nodes.take 349).foldl (applyNodeRingAttn pm) initPM 8037 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8037 349 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 349).foldl (applyNodeRingAttn pm) initPM 8037).shape.reverse.head? = some 64 := by
    rw [← hpre8037, hs8037]; rfl
  have hpre8038 : denoteGraph_ringAttn pm initPM 8038
      = (pm.nodes.take 353).foldl (applyNodeRingAttn pm) initPM 8038 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8038 353 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 353).foldl (applyNodeRingAttn pm) initPM 8038).shape.reverse.head? = some 64 := by
    rw [← hpre8038, hs8038]; rfl
  exact ⟨hbr16, hs4870sm, hs8037, hs8038, hlastSM, hlast271, hlast275⟩

/-- 4871 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4871_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4871
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4870sm, hs8037, hs8038, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L4 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4871
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4870) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 144
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4870], outs := [4871, 4872, 4873], params := [8, 1] }
      4870 4871 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 144).foldl (applyNodeRingAttn sm) initSM) 0 4870 4871 4872 4873 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8039
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8037) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 349
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8037], outs := [8039, 8041, 8043], params := [8, 1] }
      8037 8039 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 349).foldl (applyNodeRingAttn pm) initPM) 0 8037 8039 8041 8043 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8040
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8038) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 353
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8038], outs := [8040, 8042, 8044], params := [8, 1] }
      8038 8040 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 353).foldl (applyNodeRingAttn pm) initPM) 1 8038 8040 8042 8044 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4871
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8039, denoteGraph_ringAttn pm initPM 8040] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8037 hs8038,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4871).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs4870sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8039).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8037]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8040).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8038]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4871 4871 8039 8040 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4872 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4872_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4872
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4870sm, hs8037, hs8038, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L4 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4872
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4870) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 144
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4870], outs := [4871, 4872, 4873], params := [8, 1] }
      4870 4872 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 144).foldl (applyNodeRingAttn sm) initSM) 0 4870 4871 4872 4873 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8041
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8037) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 349
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8037], outs := [8039, 8041, 8043], params := [8, 1] }
      8037 8041 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 349).foldl (applyNodeRingAttn pm) initPM) 0 8037 8039 8041 8043 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8042
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8038) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 353
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8038], outs := [8040, 8042, 8044], params := [8, 1] }
      8038 8042 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 353).foldl (applyNodeRingAttn pm) initPM) 1 8038 8040 8042 8044 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4872
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8041, denoteGraph_ringAttn pm initPM 8042] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8037 hs8038,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4872).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs4870sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8041).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8037]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8042).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8038]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4872 4872 8041 8042 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L4 router expert branches — reshape (`4877`/`4882`/`4886`) of the
    `mref5` copies (positions 2/3/4) of `4867`, all identity 2-tp views. -/

/-- 4877 — 2-tp identity reshape of `mref5-pos2(4867)` (SM node 137, PM 334/338). -/
theorem recon_intermediateGoal_4877_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4877
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8029, hs8030⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4867sm : (denoteGraph_ringAttn sm initSM 4867).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8029])]
    simp [List.set, List.getD]
  have s7579 : denoteGraph_ringAttn sm initSM 7579 = id (denoteGraph_ringAttn sm initSM 4867) :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867],
        outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7579 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14874 : denoteGraph_ringAttn pm initPM 14874 = id (denoteGraph_ringAttn pm initPM 8029) :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029],
        outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14874 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14897 : denoteGraph_ringAttn pm initPM 14897 = id (denoteGraph_ringAttn pm initPM 8030) :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030],
        outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14897 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7579 p14874 p14897
  have hs7579 : (denoteGraph_ringAttn sm initSM 7579).shape = [4096, 1024] := by rw [s7579]; exact hs4867sm
  have hs14874 : (denoteGraph_ringAttn pm initPM 14874).shape = [2048, 1024] := by rw [p14874]; exact hs8029
  have hs14897 : (denoteGraph_ringAttn pm initPM 14897).shape = [2048, 1024] := by rw [p14897]; exact hs8030
  have hbrm : denoteGraph_ringAttn sm initSM 7579
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14874, denoteGraph_ringAttn pm initPM 14897] := by
    rw [s7579, hbr13, ← p14874, ← p14897]
  have rSM : denoteGraph_ringAttn sm initSM 4877
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7579) :=
    ringAttn_reduce1_pm_opaque sm initSM 137
      { rank := 0, op := "OpName.FW_reshape", ins := [7579], outs := [4877], params := [4096, 1024] }
      7579 4877 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7579 4877)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8051
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14874) :=
    ringAttn_reduce1_pm_opaque pm initPM 334
      { rank := 0, op := "OpName.FW_reshape", ins := [14874], outs := [8051], params := [2048, 1024] }
      14874 8051 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14874 8051)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8052
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14897) :=
    ringAttn_reduce1_pm_opaque pm initPM 338
      { rank := 1, op := "OpName.FW_reshape", ins := [14897], outs := [8052], params := [2048, 1024] }
      14897 8052 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 14897 8052)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 8051 = denoteGraph_ringAttn pm initPM 14874 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14874]
  have h66 : denoteGraph_ringAttn pm initPM 8052 = denoteGraph_ringAttn pm initPM 14897 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs14897]
  have hval : denoteGraph_ringAttn sm initSM 4877
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8051, denoteGraph_ringAttn pm initPM 8052] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7579, hbrm, hnr, ← h65, ← h66]
  have hs8051 : (denoteGraph_ringAttn pm initPM 8051).shape = [2048, 1024] := by rw [h65]; exact hs14874
  have hs8052 : (denoteGraph_ringAttn pm initPM 8052).shape = [2048, 1024] := by rw [h66]; exact hs14897
  have hs4877 : (denoteGraph_ringAttn sm initSM 4877).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7579]; exact hs7579
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4877 4877 8051 8052 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4877 hs8051 hs8052

/-- 4882 — 2-tp identity reshape of `mref5-pos3(4867)` (SM node 138, PM 335/339). -/
theorem recon_intermediateGoal_4882_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4882
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8029, hs8030⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4867sm : (denoteGraph_ringAttn sm initSM 4867).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8029])]
    simp [List.set, List.getD]
  have s7583 : denoteGraph_ringAttn sm initSM 7583 = id (denoteGraph_ringAttn sm initSM 4867) :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867],
        outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7583 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14878 : denoteGraph_ringAttn pm initPM 14878 = id (denoteGraph_ringAttn pm initPM 8029) :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029],
        outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14878 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14901 : denoteGraph_ringAttn pm initPM 14901 = id (denoteGraph_ringAttn pm initPM 8030) :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030],
        outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14901 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7583 p14878 p14901
  have hs7583 : (denoteGraph_ringAttn sm initSM 7583).shape = [4096, 1024] := by rw [s7583]; exact hs4867sm
  have hs14878 : (denoteGraph_ringAttn pm initPM 14878).shape = [2048, 1024] := by rw [p14878]; exact hs8029
  have hs14901 : (denoteGraph_ringAttn pm initPM 14901).shape = [2048, 1024] := by rw [p14901]; exact hs8030
  have hbrm : denoteGraph_ringAttn sm initSM 7583
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14878, denoteGraph_ringAttn pm initPM 14901] := by
    rw [s7583, hbr13, ← p14878, ← p14901]
  have rSM : denoteGraph_ringAttn sm initSM 4882
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7583) :=
    ringAttn_reduce1_pm_opaque sm initSM 138
      { rank := 0, op := "OpName.FW_reshape", ins := [7583], outs := [4882], params := [4096, 1024] }
      7583 4882 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7583 4882)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8065
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14878) :=
    ringAttn_reduce1_pm_opaque pm initPM 335
      { rank := 0, op := "OpName.FW_reshape", ins := [14878], outs := [8065], params := [2048, 1024] }
      14878 8065 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14878 8065)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8066
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14901) :=
    ringAttn_reduce1_pm_opaque pm initPM 339
      { rank := 1, op := "OpName.FW_reshape", ins := [14901], outs := [8066], params := [2048, 1024] }
      14901 8066 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 14901 8066)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 8065 = denoteGraph_ringAttn pm initPM 14878 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14878]
  have h80 : denoteGraph_ringAttn pm initPM 8066 = denoteGraph_ringAttn pm initPM 14901 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs14901]
  have hval : denoteGraph_ringAttn sm initSM 4882
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8065, denoteGraph_ringAttn pm initPM 8066] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7583, hbrm, hnr, ← h79, ← h80]
  have hs8065 : (denoteGraph_ringAttn pm initPM 8065).shape = [2048, 1024] := by rw [h79]; exact hs14878
  have hs8066 : (denoteGraph_ringAttn pm initPM 8066).shape = [2048, 1024] := by rw [h80]; exact hs14901
  have hs4882 : (denoteGraph_ringAttn sm initSM 4882).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7583]; exact hs7583
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4882 4882 8065 8066 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4882 hs8065 hs8066

/-- 4886 — 2-tp identity reshape of `mref5-pos4(4867)` (SM node 139, PM 336/340). -/
theorem recon_intermediateGoal_4886_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4886
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8029, hs8030⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4867sm : (denoteGraph_ringAttn sm initSM 4867).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8029])]
    simp [List.set, List.getD]
  have s7587 : denoteGraph_ringAttn sm initSM 7587 = id (denoteGraph_ringAttn sm initSM 4867) :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867],
        outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7587 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14882 : denoteGraph_ringAttn pm initPM 14882 = id (denoteGraph_ringAttn pm initPM 8029) :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029],
        outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14882 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14905 : denoteGraph_ringAttn pm initPM 14905 = id (denoteGraph_ringAttn pm initPM 8030) :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030],
        outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14905 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7587 p14882 p14905
  have hs7587 : (denoteGraph_ringAttn sm initSM 7587).shape = [4096, 1024] := by rw [s7587]; exact hs4867sm
  have hs14882 : (denoteGraph_ringAttn pm initPM 14882).shape = [2048, 1024] := by rw [p14882]; exact hs8029
  have hs14905 : (denoteGraph_ringAttn pm initPM 14905).shape = [2048, 1024] := by rw [p14905]; exact hs8030
  have hbrm : denoteGraph_ringAttn sm initSM 7587
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14882, denoteGraph_ringAttn pm initPM 14905] := by
    rw [s7587, hbr13, ← p14882, ← p14905]
  have rSM : denoteGraph_ringAttn sm initSM 4886
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7587) :=
    ringAttn_reduce1_pm_opaque sm initSM 139
      { rank := 0, op := "OpName.FW_reshape", ins := [7587], outs := [4886], params := [4096, 1024] }
      7587 4886 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7587 4886)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8083
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14882) :=
    ringAttn_reduce1_pm_opaque pm initPM 336
      { rank := 0, op := "OpName.FW_reshape", ins := [14882], outs := [8083], params := [2048, 1024] }
      14882 8083 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14882 8083)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8084
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14905) :=
    ringAttn_reduce1_pm_opaque pm initPM 340
      { rank := 1, op := "OpName.FW_reshape", ins := [14905], outs := [8084], params := [2048, 1024] }
      14905 8084 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 14905 8084)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 8083 = denoteGraph_ringAttn pm initPM 14882 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14882]
  have h98 : denoteGraph_ringAttn pm initPM 8084 = denoteGraph_ringAttn pm initPM 14905 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs14905]
  have hval : denoteGraph_ringAttn sm initSM 4886
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8083, denoteGraph_ringAttn pm initPM 8084] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7587, hbrm, hnr, ← h97, ← h98]
  have hs8083 : (denoteGraph_ringAttn pm initPM 8083).shape = [2048, 1024] := by rw [h97]; exact hs14882
  have hs8084 : (denoteGraph_ringAttn pm initPM 8084).shape = [2048, 1024] := by rw [h98]; exact hs14905
  have hs4886 : (denoteGraph_ringAttn sm initSM 4886).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7587]; exact hs7587
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4886 4886 8083 8084 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4886 hs8083 hs8084

/-! ### L4 router expert mixlins (`4879`/`4884`/`4888`), 2-tp. -/

/-- 4879 — 2-tp `fw_linear(4877, 4878)`, weight `4878 : [1, 1024]` → `[4096, 1]`
    (SM node 141, PM nodes 342/346). -/
theorem recon_intermediateGoal_4879_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4879
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs8051, hs8052⟩ := twoTp_gather _ _ intermediateGoal_4877 4877 8051 8052
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4877_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4878 : denoteGraph_ringAttn sm initSM 4878 = denoteGraph_ringAttn pm initPM 4878 :=
    veq_weight_ring initSM initPM hInit initGoal_4878 (by native_decide) 4878
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4878 : (denoteGraph_ringAttn pm initPM 4878).shape = [1, 1024] := by
    rw [← hw4878]
    exact shape_weight_ring initSM initPM hInit initGoal_4878 (by native_decide) 4878 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4879
      = fw_linear (denoteGraph_ringAttn sm initSM 4877) (denoteGraph_ringAttn sm initSM 4878) :=
    ringAttn_reduce2_pm_opaque sm initSM 141
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4877, 4878], outs := [4879] }
      4877 4878 4879 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4877 4878 4879)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8055
      = fw_linear (denoteGraph_ringAttn pm initPM 8051) (denoteGraph_ringAttn pm initPM 4878) :=
    ringAttn_reduce2_pm_opaque pm initPM 342
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8051, 4878], outs := [8055] }
      8051 4878 8055 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8051 4878 8055)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8056
      = fw_linear (denoteGraph_ringAttn pm initPM 8052) (denoteGraph_ringAttn pm initPM 4878) :=
    ringAttn_reduce2_pm_opaque pm initPM 346
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8052, 4878], outs := [8056] }
      8052 4878 8056 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8052 4878 8056)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4879
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8055, denoteGraph_ringAttn pm initPM 8056] := by
    rw [rSM, hval23, hw4878, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs8051 hs8052 hpw4878,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8055).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8051 hpw4878
  have hsp1 : (denoteGraph_ringAttn pm initPM 8056).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8052 hpw4878
  have hshape : (denoteGraph_ringAttn sm initSM 4879).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4879 4879 8055 8056 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4884 — 2-tp `fw_linear(4882, 4883)`, weight `4883 : [512, 1024]` → `[4096, 512]`
    (SM node 142, PM nodes 343/347). -/
theorem recon_intermediateGoal_4884_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4884
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs8065, hs8066⟩ := twoTp_gather _ _ intermediateGoal_4882 4882 8065 8066
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4882_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4883 : denoteGraph_ringAttn sm initSM 4883 = denoteGraph_ringAttn pm initPM 4883 :=
    veq_weight_ring initSM initPM hInit initGoal_4883 (by native_decide) 4883
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4883 : (denoteGraph_ringAttn pm initPM 4883).shape = [512, 1024] := by
    rw [← hw4883]
    exact shape_weight_ring initSM initPM hInit initGoal_4883 (by native_decide) 4883 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4884
      = fw_linear (denoteGraph_ringAttn sm initSM 4882) (denoteGraph_ringAttn sm initSM 4883) :=
    ringAttn_reduce2_pm_opaque sm initSM 142
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4882, 4883], outs := [4884] }
      4882 4883 4884 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4882 4883 4884)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8069
      = fw_linear (denoteGraph_ringAttn pm initPM 8065) (denoteGraph_ringAttn pm initPM 4883) :=
    ringAttn_reduce2_pm_opaque pm initPM 343
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8065, 4883], outs := [8069] }
      8065 4883 8069 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8065 4883 8069)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8070
      = fw_linear (denoteGraph_ringAttn pm initPM 8066) (denoteGraph_ringAttn pm initPM 4883) :=
    ringAttn_reduce2_pm_opaque pm initPM 347
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8066, 4883], outs := [8070] }
      8066 4883 8070 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8066 4883 8070)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4884
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8069, denoteGraph_ringAttn pm initPM 8070] := by
    rw [rSM, hval28, hw4883, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8065 hs8066 hpw4883,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8069).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8065 hpw4883
  have hsp1 : (denoteGraph_ringAttn pm initPM 8070).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8066 hpw4883
  have hshape : (denoteGraph_ringAttn sm initSM 4884).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4884 4884 8069 8070 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4888 — 2-tp `fw_linear(4886, 4887)`, weight `4887 : [512, 1024]` → `[4096, 512]`
    (SM node 143, PM nodes 344/348). -/
theorem recon_intermediateGoal_4888_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4888
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs8083, hs8084⟩ := twoTp_gather _ _ intermediateGoal_4886 4886 8083 8084
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4886_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4887 : denoteGraph_ringAttn sm initSM 4887 = denoteGraph_ringAttn pm initPM 4887 :=
    veq_weight_ring initSM initPM hInit initGoal_4887 (by native_decide) 4887
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4887 : (denoteGraph_ringAttn pm initPM 4887).shape = [512, 1024] := by
    rw [← hw4887]
    exact shape_weight_ring initSM initPM hInit initGoal_4887 (by native_decide) 4887 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4888
      = fw_linear (denoteGraph_ringAttn sm initSM 4886) (denoteGraph_ringAttn sm initSM 4887) :=
    ringAttn_reduce2_pm_opaque sm initSM 143
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4886, 4887], outs := [4888] }
      4886 4887 4888 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4886 4887 4888)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8087
      = fw_linear (denoteGraph_ringAttn pm initPM 8083) (denoteGraph_ringAttn pm initPM 4887) :=
    ringAttn_reduce2_pm_opaque pm initPM 344
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8083, 4887], outs := [8087] }
      8083 4887 8087 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8083 4887 8087)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8088
      = fw_linear (denoteGraph_ringAttn pm initPM 8084) (denoteGraph_ringAttn pm initPM 4887) :=
    ringAttn_reduce2_pm_opaque pm initPM 348
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8084, 4887], outs := [8088] }
      8084 4887 8088 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8084 4887 8088)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4888
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8087, denoteGraph_ringAttn pm initPM 8088] := by
    rw [rSM, hval32, hw4887, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8083 hs8084 hpw4887,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8087).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8083 hpw4887
  have hsp1 : (denoteGraph_ringAttn pm initPM 8088).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8084 hpw4887
  have hshape : (denoteGraph_ringAttn sm initSM 4888).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4888 4888 8087 8088 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L4 router expert views (`4880`/`4885`/`4889`), identity 2-tp views. -/

/-- 4880 — 2-tp identity view of `4879` → `[4096, 1]` (SM node 145, PM 350/354). -/
theorem recon_intermediateGoal_4880_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4880
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs8055, hs8056⟩ := twoTp_gather _ _ intermediateGoal_4879 4879 8055 8056
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4879_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4879 : (denoteGraph_ringAttn sm initSM 4879).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8055])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4880
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 4879) :=
    ringAttn_reduce1_pm_opaque sm initSM 145
      { rank := 0, op := "OpName.FW_view", ins := [4879], outs := [4880], params := [4096, 1] }
      4879 4880 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 4879 4880)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8061
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8055) :=
    ringAttn_reduce1_pm_opaque pm initPM 350
      { rank := 0, op := "OpName.FW_view", ins := [8055], outs := [8061], params := [2048, 1] }
      8055 8061 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 8055 8061)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8062
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8056) :=
    ringAttn_reduce1_pm_opaque pm initPM 354
      { rank := 1, op := "OpName.FW_view", ins := [8056], outs := [8062], params := [2048, 1] }
      8056 8062 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 8056 8062)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 8061 = denoteGraph_ringAttn pm initPM 8055 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs8055]
  have h76 : denoteGraph_ringAttn pm initPM 8062 = denoteGraph_ringAttn pm initPM 8056 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs8056]
  have hval : denoteGraph_ringAttn sm initSM 4880
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8061, denoteGraph_ringAttn pm initPM 8062] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4879, hval25, hnr, ← h75, ← h76]
  have hs8061 : (denoteGraph_ringAttn pm initPM 8061).shape = [2048, 1] := by rw [h75]; exact hs8055
  have hs8062 : (denoteGraph_ringAttn pm initPM 8062).shape = [2048, 1] := by rw [h76]; exact hs8056
  have hs4880 : (denoteGraph_ringAttn sm initSM 4880).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4879]; exact hs4879
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4880 4880 8061 8062 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4880 hs8061 hs8062

/-- 4885 — 2-tp identity view of `4884` → `[4096, 512]` (SM node 146, PM 351/355). -/
theorem recon_intermediateGoal_4885_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4885
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs8069, hs8070⟩ := twoTp_gather _ _ intermediateGoal_4884 4884 8069 8070
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4884_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4884 : (denoteGraph_ringAttn sm initSM 4884).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8069])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4885
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4884) :=
    ringAttn_reduce1_pm_opaque sm initSM 146
      { rank := 0, op := "OpName.FW_view", ins := [4884], outs := [4885], params := [4096, 512] }
      4884 4885 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4884 4885)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8079
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8069) :=
    ringAttn_reduce1_pm_opaque pm initPM 351
      { rank := 0, op := "OpName.FW_view", ins := [8069], outs := [8079], params := [2048, 512] }
      8069 8079 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8069 8079)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8080
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8070) :=
    ringAttn_reduce1_pm_opaque pm initPM 355
      { rank := 1, op := "OpName.FW_view", ins := [8070], outs := [8080], params := [2048, 512] }
      8070 8080 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8070 8080)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 8079 = denoteGraph_ringAttn pm initPM 8069 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8069]
  have h94 : denoteGraph_ringAttn pm initPM 8080 = denoteGraph_ringAttn pm initPM 8070 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8070]
  have hval : denoteGraph_ringAttn sm initSM 4885
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8079, denoteGraph_ringAttn pm initPM 8080] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4884, hval30, hnr, ← h93, ← h94]
  have hs8079 : (denoteGraph_ringAttn pm initPM 8079).shape = [2048, 512] := by rw [h93]; exact hs8069
  have hs8080 : (denoteGraph_ringAttn pm initPM 8080).shape = [2048, 512] := by rw [h94]; exact hs8070
  have hs4885 : (denoteGraph_ringAttn sm initSM 4885).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4884]; exact hs4884
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4885 4885 8079 8080 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4885 hs8079 hs8080

/-- 4889 — 2-tp identity view of `4888` → `[4096, 512]` (SM node 147, PM 352/356). -/
theorem recon_intermediateGoal_4889_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4889
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs8087, hs8088⟩ := twoTp_gather _ _ intermediateGoal_4888 4888 8087 8088
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4888_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4888 : (denoteGraph_ringAttn sm initSM 4888).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8087])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4889
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4888) :=
    ringAttn_reduce1_pm_opaque sm initSM 147
      { rank := 0, op := "OpName.FW_view", ins := [4888], outs := [4889], params := [4096, 512] }
      4888 4889 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4888 4889)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8097
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8087) :=
    ringAttn_reduce1_pm_opaque pm initPM 352
      { rank := 0, op := "OpName.FW_view", ins := [8087], outs := [8097], params := [2048, 512] }
      8087 8097 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8087 8097)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8098
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8088) :=
    ringAttn_reduce1_pm_opaque pm initPM 356
      { rank := 1, op := "OpName.FW_view", ins := [8088], outs := [8098], params := [2048, 512] }
      8088 8098 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8088 8098)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 8097 = denoteGraph_ringAttn pm initPM 8087 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8087]
  have h12 : denoteGraph_ringAttn pm initPM 8098 = denoteGraph_ringAttn pm initPM 8088 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8088]
  have hval : denoteGraph_ringAttn sm initSM 4889
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8097, denoteGraph_ringAttn pm initPM 8098] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4888, hval34, hnr, ← h11, ← h12]
  have hs8097 : (denoteGraph_ringAttn pm initPM 8097).shape = [2048, 512] := by rw [h11]; exact hs8087
  have hs8098 : (denoteGraph_ringAttn pm initPM 8098).shape = [2048, 512] := by rw [h12]; exact hs8088
  have hs4889 : (denoteGraph_ringAttn sm initSM 4889).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4888]; exact hs4888
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4889 4889 8097 8098 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4889 hs8097 hs8098

/-! ### L4 MoE gate/expert branch (`4881` sigmoid, `4890` swiglu, `4891` reshape,
    `4893` mixlin, `4894` view, `4895` broadcast-mul), all 2-tp shard-direct. -/

/-- 4881 — 2-tp `fw_sigmoid(4880)` → `[4096, 1]` (SM node 149, PM 358/361). -/
theorem recon_intermediateGoal_4881_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4881
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs8061, hs8062⟩ := twoTp_gather _ _ intermediateGoal_4880 4880 8061 8062
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4880_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4881 = fw_sigmoid (denoteGraph_ringAttn sm initSM 4880) :=
    ringAttn_reduce1_pm_opaque sm initSM 149
      { rank := 0, op := "OpName.FW_sigmoid", ins := [4880], outs := [4881] }
      4880 4881 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 4880 4881 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8063 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8061) :=
    ringAttn_reduce1_pm_opaque pm initPM 358
      { rank := 0, op := "OpName.FW_sigmoid", ins := [8061], outs := [8063] }
      8061 8063 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 8061 8063 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8064 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8062) :=
    ringAttn_reduce1_pm_opaque pm initPM 361
      { rank := 1, op := "OpName.FW_sigmoid", ins := [8062], outs := [8064] }
      8062 8064 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 8062 8064 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4881
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8063, denoteGraph_ringAttn pm initPM 8064] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs8061 hs8062, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4881).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8061])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8063).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs8061
  have hsp1 : (denoteGraph_ringAttn pm initPM 8064).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs8062
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4881 4881 8063 8064 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4890 — 2-tp `fw_swiglu(4885, 4889)` → `[4096, 512]` (SM node 150, PM 359/362). -/
theorem recon_intermediateGoal_4890_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4890
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs8079, hs8080⟩ := twoTp_gather _ _ intermediateGoal_4885 4885 8079 8080
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4885_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs8097, hs8098⟩ := twoTp_gather _ _ intermediateGoal_4889 4889 8097 8098
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4889_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4890
      = fw_swiglu (denoteGraph_ringAttn sm initSM 4885) (denoteGraph_ringAttn sm initSM 4889) :=
    ringAttn_reduce2_pm_opaque sm initSM 150
      { rank := 0, op := "OpName.FW_swiglu", ins := [4885, 4889], outs := [4890] }
      4885 4889 4890 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 4885 4889 4890 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8101
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8079) (denoteGraph_ringAttn pm initPM 8097) :=
    ringAttn_reduce2_pm_opaque pm initPM 359
      { rank := 0, op := "OpName.FW_swiglu", ins := [8079, 8097], outs := [8101] }
      8079 8097 8101 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 8079 8097 8101 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8102
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8080) (denoteGraph_ringAttn pm initPM 8098) :=
    ringAttn_reduce2_pm_opaque pm initPM 362
      { rank := 1, op := "OpName.FW_swiglu", ins := [8080, 8098], outs := [8102] }
      8080 8098 8102 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 8080 8098 8102 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4890
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8101, denoteGraph_ringAttn pm initPM 8102] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs8079 hs8080 hs8097 hs8098,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4890).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8097])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8101).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8097
  have hsp1 : (denoteGraph_ringAttn pm initPM 8102).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8098
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4890 4890 8101 8102 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4891 — 2-tp identity reshape of `4890` → `[4096, 512]` (SM node 151, PM 363/364). -/
theorem recon_intermediateGoal_4891_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4891
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs8101, hs8102⟩ := twoTp_gather _ _ intermediateGoal_4890 4890 8101 8102
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4890_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4890 : (denoteGraph_ringAttn sm initSM 4890).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8101])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4891
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4890) :=
    ringAttn_reduce1_pm_opaque sm initSM 151
      { rank := 0, op := "OpName.FW_reshape", ins := [4890], outs := [4891], params := [4096, 512] }
      4890 4891 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4890 4891)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8103
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8101) :=
    ringAttn_reduce1_pm_opaque pm initPM 363
      { rank := 0, op := "OpName.FW_reshape", ins := [8101], outs := [8103], params := [2048, 512] }
      8101 8103 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8101 8103)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8104
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8102) :=
    ringAttn_reduce1_pm_opaque pm initPM 364
      { rank := 1, op := "OpName.FW_reshape", ins := [8102], outs := [8104], params := [2048, 512] }
      8102 8104 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8102 8104)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8103 = denoteGraph_ringAttn pm initPM 8101 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8101]
  have h18 : denoteGraph_ringAttn pm initPM 8104 = denoteGraph_ringAttn pm initPM 8102 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8102]
  have hval : denoteGraph_ringAttn sm initSM 4891
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8103, denoteGraph_ringAttn pm initPM 8104] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4890, hval36, hnr, ← h17, ← h18]
  have hs8103 : (denoteGraph_ringAttn pm initPM 8103).shape = [2048, 512] := by rw [h17]; exact hs8101
  have hs8104 : (denoteGraph_ringAttn pm initPM 8104).shape = [2048, 512] := by rw [h18]; exact hs8102
  have hs4891 : (denoteGraph_ringAttn sm initSM 4891).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4890]; exact hs4890
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4891 4891 8103 8104 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4891 hs8103 hs8104

/-- 4893 — 2-tp `fw_linear(4891, 4892)`, weight `4892 : [1024, 512]` → `[4096, 1024]`
    (SM node 152, PM 365/366). -/
theorem recon_intermediateGoal_4893_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4893
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs8103, hs8104⟩ := twoTp_gather _ _ intermediateGoal_4891 4891 8103 8104
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4891_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4892 : denoteGraph_ringAttn sm initSM 4892 = denoteGraph_ringAttn pm initPM 4892 :=
    veq_weight_ring initSM initPM hInit initGoal_4892 (by native_decide) 4892
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4892 : (denoteGraph_ringAttn pm initPM 4892).shape = [1024, 512] := by
    rw [← hw4892]
    exact shape_weight_ring initSM initPM hInit initGoal_4892 (by native_decide) 4892 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4893
      = fw_linear (denoteGraph_ringAttn sm initSM 4891) (denoteGraph_ringAttn sm initSM 4892) :=
    ringAttn_reduce2_pm_opaque sm initSM 152
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4891, 4892], outs := [4893] }
      4891 4892 4893 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4891 4892 4893)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8109
      = fw_linear (denoteGraph_ringAttn pm initPM 8103) (denoteGraph_ringAttn pm initPM 4892) :=
    ringAttn_reduce2_pm_opaque pm initPM 365
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8103, 4892], outs := [8109] }
      8103 4892 8109 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8103 4892 8109)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8110
      = fw_linear (denoteGraph_ringAttn pm initPM 8104) (denoteGraph_ringAttn pm initPM 4892) :=
    ringAttn_reduce2_pm_opaque pm initPM 366
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8104, 4892], outs := [8110] }
      8104 4892 8110 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8104 4892 8110)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4893
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8109, denoteGraph_ringAttn pm initPM 8110] := by
    rw [rSM, hval37, hw4892, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs8103 hs8104 hpw4892,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8109).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8103 hpw4892
  have hsp1 : (denoteGraph_ringAttn pm initPM 8110).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8104 hpw4892
  have hshape : (denoteGraph_ringAttn sm initSM 4893).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4893 4893 8109 8110 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4894 — 2-tp identity view of `4893` → `[4096, 1024]` (SM node 153, PM 367/368). -/
theorem recon_intermediateGoal_4894_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4894
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs8109, hs8110⟩ := twoTp_gather _ _ intermediateGoal_4893 4893 8109 8110
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4893_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4893 : (denoteGraph_ringAttn sm initSM 4893).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8109])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4894
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4893) :=
    ringAttn_reduce1_pm_opaque sm initSM 153
      { rank := 0, op := "OpName.FW_view", ins := [4893], outs := [4894], params := [4096, 1024] }
      4893 4894 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4893 4894)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8119
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8109) :=
    ringAttn_reduce1_pm_opaque pm initPM 367
      { rank := 0, op := "OpName.FW_view", ins := [8109], outs := [8119], params := [2048, 1024] }
      8109 8119 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8109 8119)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8120
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8110) :=
    ringAttn_reduce1_pm_opaque pm initPM 368
      { rank := 1, op := "OpName.FW_view", ins := [8110], outs := [8120], params := [2048, 1024] }
      8110 8120 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8110 8120)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 8119 = denoteGraph_ringAttn pm initPM 8109 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8109]
  have h34 : denoteGraph_ringAttn pm initPM 8120 = denoteGraph_ringAttn pm initPM 8110 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8110]
  have hval : denoteGraph_ringAttn sm initSM 4894
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8119, denoteGraph_ringAttn pm initPM 8120] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4893, hval39, hnr, ← h33, ← h34]
  have hs8119 : (denoteGraph_ringAttn pm initPM 8119).shape = [2048, 1024] := by rw [h33]; exact hs8109
  have hs8120 : (denoteGraph_ringAttn pm initPM 8120).shape = [2048, 1024] := by rw [h34]; exact hs8110
  have hs4894 : (denoteGraph_ringAttn sm initSM 4894).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4893]; exact hs4893
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4894 4894 8119 8120 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4894 hs8119 hs8120

/-- 4895 — 2-tp broadcast `mul(4881, 4894)` → `[4096, 1024]` (SM node 154, PM 369/370). -/
theorem recon_intermediateGoal_4895_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4895
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_4881 4881 8063 8064
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4881_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_4894 4894 8119 8120
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4894_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4895
      = elemwiseMul (denoteGraph_ringAttn sm initSM 4881) (denoteGraph_ringAttn sm initSM 4894) :=
    ringAttn_reduce2_pm_opaque sm initSM 154
      { rank := 0, op := "OpName.FW_mul", ins := [4881, 4894], outs := [4895] }
      4881 4894 4895 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 4881 4894 4895)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8123
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8063) (denoteGraph_ringAttn pm initPM 8119) :=
    ringAttn_reduce2_pm_opaque pm initPM 369
      { rank := 0, op := "OpName.FW_mul", ins := [8063, 8119], outs := [8123] }
      8063 8119 8123 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 8063 8119 8123)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8124
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8064) (denoteGraph_ringAttn pm initPM 8120) :=
    ringAttn_reduce2_pm_opaque pm initPM 370
      { rank := 1, op := "OpName.FW_mul", ins := [8064, 8120], outs := [8124] }
      8064 8120 8124 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 8064 8120 8124)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4895
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8123, denoteGraph_ringAttn pm initPM 8124] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 4895).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 4881).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 4894).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 8123).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 8124).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4895 4895 8123 8124 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 4876 — layer-4 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 4876 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`8049`), rank 1 →
    `[32, 64)` (`8050`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `8041`/`8042` are expert-local (the
    `wf4876_hdisjA/B` fields).  Token input `7575 = mref5-pos1(4867)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 148, PM nodes 357/360). -/
theorem recon_intermediateGoal_4876_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4876
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 7575 = mref5-pos1(4867).
  obtain ⟨hbr13, hs8029, hs8030⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7575 : denoteGraph_ringAttn sm initSM 7575 = id (denoteGraph_ringAttn sm initSM 4867) :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867],
        outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7575 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14870 : denoteGraph_ringAttn pm initPM 14870 = id (denoteGraph_ringAttn pm initPM 8029) :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029],
        outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14870 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14893 : denoteGraph_ringAttn pm initPM 14893 = id (denoteGraph_ringAttn pm initPM 8030) :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030],
        outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14893 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7575 p14870 p14893
  have hsInA : (denoteGraph_ringAttn pm initPM 14870).shape = [2048, 1024] := by
    rw [p14870]; exact hs8029
  have hsInB : (denoteGraph_ringAttn pm initPM 14893).shape = [2048, 1024] := by
    rw [p14893]; exact hs8030
  have hbrIn : denoteGraph_ringAttn sm initSM 7575
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 14870, denoteGraph_ringAttn pm initPM 14893] := by
    rw [s7575, hbr13, hnr, ← p14870, ← p14893]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_4871 4871 8039 8040
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4871_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_4872 4872 8041 8042
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4872_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 4871
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8039, denoteGraph_ringAttn pm initPM 8040] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 4872
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8041, denoteGraph_ringAttn pm initPM 8042] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_4874
    (by native_decide) 4874 8045 8046 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_4875
    (by native_decide) 4875 8047 8048 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 8045).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4874 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4874, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8045 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 8046).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4874 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4874, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8046 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 8047).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4875 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4875, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8047 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 8048).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4875 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4875, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8048 (by native_decide)]; exact hs.2
  -- SM 4876 = full-range all2all (SM node 148).
  have hSMout : denoteGraph_ringAttn sm initSM 4876
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7575)
          (denoteGraph_ringAttn sm initSM 4871) (denoteGraph_ringAttn sm initSM 4872)
          (denoteGraph_ringAttn sm initSM 4874) (denoteGraph_ringAttn sm initSM 4875)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 148
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7575, 4871, 4872, 4874, 4875],
        outs := [4876], params := [64, 0, 64, 8] }
      7575 4871 4872 4874 4875 4876
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7575 4871 4872 4874 4875 4876 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8049 = rank-0 sharded-range all2all (PM node 357).
  have hP0 : denoteGraph_ringAttn pm initPM 8049
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 14870)
          (denoteGraph_ringAttn pm initPM 8039) (denoteGraph_ringAttn pm initPM 8041)
          (denoteGraph_ringAttn pm initPM 8045) (denoteGraph_ringAttn pm initPM 8047)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 357
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14870, 8039, 8041, 8045, 8047],
        outs := [8049], params := [64, 0, 32, 8] }
      14870 8039 8041 8045 8047 8049
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 14870 8039 8041 8045 8047 8049 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8050 = rank-1 sharded-range all2all (PM node 360).
  have hP1 : denoteGraph_ringAttn pm initPM 8050
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 14893)
          (denoteGraph_ringAttn pm initPM 8040) (denoteGraph_ringAttn pm initPM 8042)
          (denoteGraph_ringAttn pm initPM 8046) (denoteGraph_ringAttn pm initPM 8048)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 360
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14893, 8040, 8042, 8046, 8048],
        outs := [8050], params := [64, 32, 64, 8] }
      14893 8040 8042 8046 8048 8050
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 14893 8040 8042 8046 8048 8050 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 14870) (denoteGraph_ringAttn pm initPM 14893)
      (denoteGraph_ringAttn pm initPM 8039) (denoteGraph_ringAttn pm initPM 8040)
      (denoteGraph_ringAttn pm initPM 8041) (denoteGraph_ringAttn pm initPM 8042)
      (denoteGraph_ringAttn pm initPM 8045) (denoteGraph_ringAttn pm initPM 8046)
      (denoteGraph_ringAttn pm initPM 8047) (denoteGraph_ringAttn pm initPM 8048)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf4876_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf4876_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 4876
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8049, denoteGraph_ringAttn pm initPM 8050] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8049).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8050).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 4876).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4876 4876 8049 8050 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L4 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7564 — second position of the L4 pre-MoE residual `mref2(4865)` (2-tp, PM
    shards `14851`/`14859`).  Unlike L2's `7512` there is no gather-to-full/chunk
    because `4865` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 133, PM nodes 321/322). -/
theorem recon_intermediateGoal_7564_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7564
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8025, hs8026⟩ := twoTp_gather _ _ intermediateGoal_4865 4865 8025 8026
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4865_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7564 : denoteGraph_ringAttn sm initSM 7564 = id (denoteGraph_ringAttn sm initSM 4865) :=
    ringAttn_reduce1_pm_opaque sm initSM 133
      { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564], params := [2] }
      4865 7564 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4865 7560 7564 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14851 : denoteGraph_ringAttn pm initPM 14851 = id (denoteGraph_ringAttn pm initPM 8025) :=
    ringAttn_reduce1_pm_opaque pm initPM 327
      { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851], params := [2] }
      8025 14851 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8025 14847 14851 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14859 : denoteGraph_ringAttn pm initPM 14859 = id (denoteGraph_ringAttn pm initPM 8026) :=
    ringAttn_reduce1_pm_opaque pm initPM 328
      { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859], params := [2] }
      8026 14859 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8026 14855 14859 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7564 p14851 p14859
  have hsp0 : (denoteGraph_ringAttn pm initPM 14851).shape = [2048, 1024] := by
    rw [p14851]; exact hs8025
  have hsp1 : (denoteGraph_ringAttn pm initPM 14859).shape = [2048, 1024] := by
    rw [p14859]; exact hs8026
  have hval : denoteGraph_ringAttn sm initSM 7564
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14851, denoteGraph_ringAttn pm initPM 14859] := by
    rw [s7564, hbr11, ← p14851, ← p14859]
  have hshape : (denoteGraph_ringAttn sm initSM 7564).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7564 7564 14851 14859 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4896 — post-MoE residual add `4876 + 4895` (2-tp, PM `8127`/`8128`). -/
theorem recon_intermediateGoal_4896_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4896
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs8049, hs8050⟩ := twoTp_gather _ _ intermediateGoal_4876 4876 8049 8050
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4876_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs8123, hs8124⟩ := twoTp_gather _ _ intermediateGoal_4895 4895 8123 8124
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4895_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4896
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 4876) (denoteGraph_ringAttn sm initSM 4895) :=
    ringAttn_reduce2_pm_opaque sm initSM 155
      { rank := 0, op := "OpName.FW_add", ins := [4876, 4895], outs := [4896] }
      4876 4895 4896 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 4876 4895 4896)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8127
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8049) (denoteGraph_ringAttn pm initPM 8123) :=
    ringAttn_reduce2_pm_opaque pm initPM 371
      { rank := 0, op := "OpName.FW_add", ins := [8049, 8123], outs := [8127] }
      8049 8123 8127 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 8049 8123 8127)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8128
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8050) (denoteGraph_ringAttn pm initPM 8124) :=
    ringAttn_reduce2_pm_opaque pm initPM 372
      { rank := 1, op := "OpName.FW_add", ins := [8050, 8124], outs := [8128] }
      8050 8124 8128 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 8050 8124 8128)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4896
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8127, denoteGraph_ringAttn pm initPM 8128] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs8049 hs8050 hs8123 hs8124,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8127).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8049 hs8123
  have hsp1 : (denoteGraph_ringAttn pm initPM 8128).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8050 hs8124
  have hshape : (denoteGraph_ringAttn sm initSM 4896).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4896 4896 8127 8128 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4897 — `FW_float(4896)` (identity, 2-tp PM `8133`/`8134`). -/
theorem recon_intermediateGoal_4897_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4897
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs8127, hs8128⟩ := twoTp_gather _ _ intermediateGoal_4896 4896 8127 8128
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4896_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4897 = id (denoteGraph_ringAttn sm initSM 4896) :=
    ringAttn_reduce1_pm_opaque sm initSM 156
      { rank := 0, op := "OpName.FW_float", ins := [4896], outs := [4897] }
      4896 4897 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4896 4897 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8133 = id (denoteGraph_ringAttn pm initPM 8127) :=
    ringAttn_reduce1_pm_opaque pm initPM 373
      { rank := 0, op := "OpName.FW_float", ins := [8127], outs := [8133] }
      8127 8133 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8127 8133 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8134 = id (denoteGraph_ringAttn pm initPM 8128) :=
    ringAttn_reduce1_pm_opaque pm initPM 374
      { rank := 1, op := "OpName.FW_float", ins := [8128], outs := [8134] }
      8128 8134 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8128 8134 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 4897
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8133, denoteGraph_ringAttn pm initPM 8134] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8133).shape = [2048, 1024] := by rw [rP0]; exact hs8127
  have hsp1 : (denoteGraph_ringAttn pm initPM 8134).shape = [2048, 1024] := by rw [rP1]; exact hs8128
  have hshape : (denoteGraph_ringAttn sm initSM 4897).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4897 4897 8133 8134 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4898 — cross-block residual add `7564 + 4897` (2-tp, PM `8137`/`8138`). -/
theorem recon_intermediateGoal_4898_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4898
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs14851, hs14859⟩ := twoTp_gather _ _ intermediateGoal_7564 7564 14851 14859
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7564_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs8133, hs8134⟩ := twoTp_gather _ _ intermediateGoal_4897 4897 8133 8134
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4897_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4898
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7564) (denoteGraph_ringAttn sm initSM 4897) :=
    ringAttn_reduce2_pm_opaque sm initSM 157
      { rank := 0, op := "OpName.FW_add", ins := [7564, 4897], outs := [4898] }
      7564 4897 4898 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7564 4897 4898)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8137
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14851) (denoteGraph_ringAttn pm initPM 8133) :=
    ringAttn_reduce2_pm_opaque pm initPM 375
      { rank := 0, op := "OpName.FW_add", ins := [14851, 8133], outs := [8137] }
      14851 8133 8137 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 14851 8133 8137)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8138
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14859) (denoteGraph_ringAttn pm initPM 8134) :=
    ringAttn_reduce2_pm_opaque pm initPM 376
      { rank := 1, op := "OpName.FW_add", ins := [14859, 8134], outs := [8138] }
      14859 8134 8138 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14859 8134 8138)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4898
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8137, denoteGraph_ringAttn pm initPM 8138] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs14851 hs14859 hs8133 hs8134,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8137).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14851 hs8133
  have hsp1 : (denoteGraph_ringAttn pm initPM 8138).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14859 hs8134
  have hshape : (denoteGraph_ringAttn sm initSM 4898).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4898 4898 8137 8138 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4900 — RMSNorm of `mref2-first(4898)` with replicated weight `4899`
    (2-tp, PM `8141`/`8142`). -/
theorem recon_intermediateGoal_4900_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4900
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs8137, hs8138⟩ := twoTp_gather _ _ intermediateGoal_4898 4898 8137 8138
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4898_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7591 : denoteGraph_ringAttn sm initSM 7591 = id (denoteGraph_ringAttn sm initSM 4898) :=
    ringAttn_reduce1_pm_opaque sm initSM 158
      { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595], params := [2] }
      4898 7591 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4898 7591 7595)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14909 : denoteGraph_ringAttn pm initPM 14909 = id (denoteGraph_ringAttn pm initPM 8137) :=
    ringAttn_reduce1_pm_opaque pm initPM 377
      { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913], params := [2] }
      8137 14909 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8137 14909 14913)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14917 : denoteGraph_ringAttn pm initPM 14917 = id (denoteGraph_ringAttn pm initPM 8138) :=
    ringAttn_reduce1_pm_opaque pm initPM 378
      { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921], params := [2] }
      8138 14917 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8138 14917 14921)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7591 p14909 p14917
  have hs14909 : (denoteGraph_ringAttn pm initPM 14909).shape = [2048, 1024] := by
    rw [p14909]; exact hs8137
  have hs14917 : (denoteGraph_ringAttn pm initPM 14917).shape = [2048, 1024] := by
    rw [p14917]; exact hs8138
  have hbr39 : denoteGraph_ringAttn sm initSM 7591
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14909, denoteGraph_ringAttn pm initPM 14917] := by
    rw [s7591, hbr44, ← p14909, ← p14917]
  have hw4899 : denoteGraph_ringAttn sm initSM 4899 = denoteGraph_ringAttn pm initPM 4899 :=
    veq_weight_ring initSM initPM hInit initGoal_4899 (by native_decide) 4899
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4900
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7591) (denoteGraph_ringAttn sm initSM 4899) :=
    ringAttn_reduce2_pm_opaque sm initSM 159
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7591, 4899], outs := [4900] }
      7591 4899 4900 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7591 4899 4900)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8141
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14909) (denoteGraph_ringAttn pm initPM 4899) :=
    ringAttn_reduce2_pm_opaque pm initPM 379
      { rank := 0, op := "OpName.FW_rms_norm", ins := [14909, 4899], outs := [8141] }
      14909 4899 8141 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 14909 4899 8141)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8142
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14917) (denoteGraph_ringAttn pm initPM 4899) :=
    ringAttn_reduce2_pm_opaque pm initPM 380
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14917, 4899], outs := [8142] }
      14917 4899 8142 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14917 4899 8142)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4900
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8141, denoteGraph_ringAttn pm initPM 8142] := by
    rw [rSM, hbr39, hw4899, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs14909 hs14917,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8141).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14909
  have hsp1 : (denoteGraph_ringAttn pm initPM 8142).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14917
  have hshape : (denoteGraph_ringAttn sm initSM 4900).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4900 4900 8141 8142 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4902 — per-head Q projection `fw_per_head_linear(mref3₀(4900), 4901)`
    (2-tp, PM `8143`/`8144`, weight `4901 : [16,64,1024]`). -/
theorem recon_intermediateGoal_4902_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4902
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8141, hs8142⟩ := twoTp_gather _ _ intermediateGoal_4900 4900 8141 8142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4900_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7600 : denoteGraph_ringAttn sm initSM 7600 = id (denoteGraph_ringAttn sm initSM 4900) :=
    ringAttn_reduce1_pm_opaque sm initSM 160
      { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
      4900 7600 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4900 7600 7604 7608)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14926 : denoteGraph_ringAttn pm initPM 14926 = id (denoteGraph_ringAttn pm initPM 8141) :=
    ringAttn_reduce1_pm_opaque pm initPM 381
      { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
      8141 14926 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8141 14926 14930 14934)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14939 : denoteGraph_ringAttn pm initPM 14939 = id (denoteGraph_ringAttn pm initPM 8142) :=
    ringAttn_reduce1_pm_opaque pm initPM 382
      { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
      8142 14939 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8142 14939 14943 14947)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7600 p14926 p14939
  have hs14926 : (denoteGraph_ringAttn pm initPM 14926).shape = [2048, 1024] := by
    rw [p14926]; exact hs8141
  have hs14939 : (denoteGraph_ringAttn pm initPM 14939).shape = [2048, 1024] := by
    rw [p14939]; exact hs8142
  have hbr48 : denoteGraph_ringAttn sm initSM 7600
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14926, denoteGraph_ringAttn pm initPM 14939] := by
    rw [s7600, hbr46, ← p14926, ← p14939]
  have hw4901 : denoteGraph_ringAttn sm initSM 4901 = denoteGraph_ringAttn pm initPM 4901 :=
    veq_weight_ring initSM initPM hInit initGoal_4901 (by native_decide) 4901
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4901 : (denoteGraph_ringAttn sm initSM 4901).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4901 (by native_decide) 4901 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4901 : (denoteGraph_ringAttn pm initPM 4901).shape = [16, 64, 1024] := by
    rw [← hw4901]; exact hsw4901
  have rSM : denoteGraph_ringAttn sm initSM 4902
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7600) (denoteGraph_ringAttn sm initSM 4901) :=
    ringAttn_reduce2_pm_opaque sm initSM 161
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7600, 4901], outs := [4902] }
      7600 4901 4902 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7600 4901 4902 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8143
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14926) (denoteGraph_ringAttn pm initPM 4901) :=
    ringAttn_reduce2_pm_opaque pm initPM 383
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14926, 4901], outs := [8143] }
      14926 4901 8143 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 14926 4901 8143 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8144
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14939) (denoteGraph_ringAttn pm initPM 4901) :=
    ringAttn_reduce2_pm_opaque pm initPM 386
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14939, 4901], outs := [8144] }
      14939 4901 8144 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14939 4901 8144 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4902
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8143, denoteGraph_ringAttn pm initPM 8144] := by
    rw [rSM, hbr48, hw4901, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs14926 hs14939 hpw4901,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8143).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs14926 hpw4901
  have hsp1 : (denoteGraph_ringAttn pm initPM 8144).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs14939 hpw4901
  have hshape : (denoteGraph_ringAttn sm initSM 4902).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4902 4902 8143 8144 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4904 — per-head K projection `fw_per_head_linear(mref3₁(4900), 4903)`
    (2-tp, PM `8155`/`8156`, weight `4903 : [4,64,1024]`). -/
theorem recon_intermediateGoal_4904_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4904
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8141, hs8142⟩ := twoTp_gather _ _ intermediateGoal_4900 4900 8141 8142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4900_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7604 : denoteGraph_ringAttn sm initSM 7604 = id (denoteGraph_ringAttn sm initSM 4900) :=
    ringAttn_reduce1_pm_opaque sm initSM 160
      { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
      4900 7604 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4900 7600 7604 7608 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14930 : denoteGraph_ringAttn pm initPM 14930 = id (denoteGraph_ringAttn pm initPM 8141) :=
    ringAttn_reduce1_pm_opaque pm initPM 381
      { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
      8141 14930 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8141 14926 14930 14934 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14943 : denoteGraph_ringAttn pm initPM 14943 = id (denoteGraph_ringAttn pm initPM 8142) :=
    ringAttn_reduce1_pm_opaque pm initPM 382
      { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
      8142 14943 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8142 14939 14943 14947 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7604 p14930 p14943
  have hs14930 : (denoteGraph_ringAttn pm initPM 14930).shape = [2048, 1024] := by
    rw [p14930]; exact hs8141
  have hs14943 : (denoteGraph_ringAttn pm initPM 14943).shape = [2048, 1024] := by
    rw [p14943]; exact hs8142
  have hbr52 : denoteGraph_ringAttn sm initSM 7604
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14930, denoteGraph_ringAttn pm initPM 14943] := by
    rw [s7604, hbr46, ← p14930, ← p14943]
  have hw4903 : denoteGraph_ringAttn sm initSM 4903 = denoteGraph_ringAttn pm initPM 4903 :=
    veq_weight_ring initSM initPM hInit initGoal_4903 (by native_decide) 4903
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4903 : (denoteGraph_ringAttn sm initSM 4903).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4903 (by native_decide) 4903 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4903 : (denoteGraph_ringAttn pm initPM 4903).shape = [4, 64, 1024] := by
    rw [← hw4903]; exact hsw4903
  have rSM : denoteGraph_ringAttn sm initSM 4904
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7604) (denoteGraph_ringAttn sm initSM 4903) :=
    ringAttn_reduce2_pm_opaque sm initSM 162
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7604, 4903], outs := [4904] }
      7604 4903 4904 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7604 4903 4904 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8155
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14930) (denoteGraph_ringAttn pm initPM 4903) :=
    ringAttn_reduce2_pm_opaque pm initPM 384
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14930, 4903], outs := [8155] }
      14930 4903 8155 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 14930 4903 8155 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8156
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14943) (denoteGraph_ringAttn pm initPM 4903) :=
    ringAttn_reduce2_pm_opaque pm initPM 387
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14943, 4903], outs := [8156] }
      14943 4903 8156 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14943 4903 8156 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4904
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8155, denoteGraph_ringAttn pm initPM 8156] := by
    rw [rSM, hbr52, hw4903, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs14930 hs14943 hpw4903,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8155).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14930 hpw4903
  have hsp1 : (denoteGraph_ringAttn pm initPM 8156).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14943 hpw4903
  have hshape : (denoteGraph_ringAttn sm initSM 4904).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4904 4904 8155 8156 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4906 — per-head V projection `fw_per_head_linear(mref3₂(4900), 4905)`
    (2-tp, PM `8165`/`8166`, weight `4905 : [4,64,1024]`). -/
theorem recon_intermediateGoal_4906_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4906
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8141, hs8142⟩ := twoTp_gather _ _ intermediateGoal_4900 4900 8141 8142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4900_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7608 : denoteGraph_ringAttn sm initSM 7608 = id (denoteGraph_ringAttn sm initSM 4900) :=
    ringAttn_reduce1_pm_opaque sm initSM 160
      { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
      4900 7608 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4900 7600 7604 7608 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14934 : denoteGraph_ringAttn pm initPM 14934 = id (denoteGraph_ringAttn pm initPM 8141) :=
    ringAttn_reduce1_pm_opaque pm initPM 381
      { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
      8141 14934 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8141 14926 14930 14934 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14947 : denoteGraph_ringAttn pm initPM 14947 = id (denoteGraph_ringAttn pm initPM 8142) :=
    ringAttn_reduce1_pm_opaque pm initPM 382
      { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
      8142 14947 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8142 14939 14943 14947 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7608 p14934 p14947
  have hs14934 : (denoteGraph_ringAttn pm initPM 14934).shape = [2048, 1024] := by
    rw [p14934]; exact hs8141
  have hs14947 : (denoteGraph_ringAttn pm initPM 14947).shape = [2048, 1024] := by
    rw [p14947]; exact hs8142
  have hbr56 : denoteGraph_ringAttn sm initSM 7608
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14934, denoteGraph_ringAttn pm initPM 14947] := by
    rw [s7608, hbr46, ← p14934, ← p14947]
  have hw4905 : denoteGraph_ringAttn sm initSM 4905 = denoteGraph_ringAttn pm initPM 4905 :=
    veq_weight_ring initSM initPM hInit initGoal_4905 (by native_decide) 4905
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4905 : (denoteGraph_ringAttn sm initSM 4905).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4905 (by native_decide) 4905 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4905 : (denoteGraph_ringAttn pm initPM 4905).shape = [4, 64, 1024] := by
    rw [← hw4905]; exact hsw4905
  have rSM : denoteGraph_ringAttn sm initSM 4906
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7608) (denoteGraph_ringAttn sm initSM 4905) :=
    ringAttn_reduce2_pm_opaque sm initSM 163
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7608, 4905], outs := [4906] }
      7608 4905 4906 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7608 4905 4906 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8165
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14934) (denoteGraph_ringAttn pm initPM 4905) :=
    ringAttn_reduce2_pm_opaque pm initPM 385
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14934, 4905], outs := [8165] }
      14934 4905 8165 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 14934 4905 8165 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8166
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14947) (denoteGraph_ringAttn pm initPM 4905) :=
    ringAttn_reduce2_pm_opaque pm initPM 388
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14947, 4905], outs := [8166] }
      14947 4905 8166 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14947 4905 8166 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4906
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8165, denoteGraph_ringAttn pm initPM 8166] := by
    rw [rSM, hbr56, hw4905, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs14934 hs14947 hpw4905,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8165).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14934 hpw4905
  have hsp1 : (denoteGraph_ringAttn pm initPM 8166).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14947 hpw4905
  have hshape : (denoteGraph_ringAttn sm initSM 4906).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4906 4906 8165 8166 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L4 rotary cos/sin cache agreement: `sm 4691 = pm 11857` (`= 11853 + 3`). -/
theorem hcache_4691_11857 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11857 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11857 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11857 4 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 4908 — rotary-embedding Q output `rotary(4691, 4907, 4902, 4904).1`
    (2-tp, PM `8177`/`8178`; positions `4907 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_4908_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4908
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs8143, hs8144⟩ := twoTp_gather _ _ intermediateGoal_4902 4902 8143 8144
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4902_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_4904 4904 8155 8156
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4904_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11857 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 4907 = denoteGraph_ringAttn pm initPM 4907 :=
    veq_weight_ring initSM initPM hInit initGoal_4907 (by native_decide) 4907
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp4907 : (denoteGraph_ringAttn sm initSM 4907).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_4907 (by native_decide) 4907 [4096]
      rfl rfl (by native_decide)
  have c8175 : denoteGraph_ringAttn pm initPM 8175
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4907) :=
    ringAttn_reduce1_pm_opaque pm initPM 4
      { rank := 0, op := "OpName.ChunkPrim", ins := [4907], outs := [8175], params := [0] }
      4907 8175 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4907 8175 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8176 : denoteGraph_ringAttn pm initPM 8176
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4907) :=
    ringAttn_reduce1_pm_opaque pm initPM 17
      { rank := 1, op := "OpName.ChunkPrim", ins := [4907], outs := [8176], params := [0] }
      4907 8176 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4907 8176 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4908
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4907)
          (denoteGraph_ringAttn sm initSM 4902) (denoteGraph_ringAttn sm initSM 4904) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 164
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4907, 4902, 4904], outs := [4908, 4909], params := [16, 4] }
          4908 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 164 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 164 4907 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 164 4902 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 164 4904 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8177
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11857) (denoteGraph_ringAttn pm initPM 8175)
          (denoteGraph_ringAttn pm initPM 8143) (denoteGraph_ringAttn pm initPM 8155) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 389
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11857, 8175, 8143, 8155], outs := [8177, 8179], params := [16, 4] }
          8177 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 389 11857 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 389 8175 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 389 8143 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 389 8155 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8178
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11857) (denoteGraph_ringAttn pm initPM 8176)
          (denoteGraph_ringAttn pm initPM 8144) (denoteGraph_ringAttn pm initPM 8156) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 390
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11857, 8176, 8144, 8156], outs := [8178, 8180], params := [16, 4] }
          8178 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 390 11857 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 390 8176 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 390 8144 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 390 8156 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4908
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8177, denoteGraph_ringAttn pm initPM 8178] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 4907) (denoteGraph_ringAttn pm initPM 8143)
          (denoteGraph_ringAttn pm initPM 8144) 2048 16 64 (by omega) (by omega) (by omega)
          hsp4907 hs8143 hs8144,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8175
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 4907) from c8175),
        ← (show denoteGraph_ringAttn pm initPM 8176
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 4907) from c8176),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8177).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8143
  have hsp1 : (denoteGraph_ringAttn pm initPM 8178).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8144
  have hshape : (denoteGraph_ringAttn sm initSM 4908).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4908 4908 8177 8178 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 4909 — rotary-embedding K output `rotary(4691, 4907, 4902, 4904).2`
    (2-tp, PM `8179`/`8180`). -/
theorem recon_intermediateGoal_4909_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4909
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_4902 4902 8143 8144
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4902_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs8155, hs8156⟩ := twoTp_gather _ _ intermediateGoal_4904 4904 8155 8156
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4904_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11857 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 4907 = denoteGraph_ringAttn pm initPM 4907 :=
    veq_weight_ring initSM initPM hInit initGoal_4907 (by native_decide) 4907
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp4907 : (denoteGraph_ringAttn sm initSM 4907).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_4907 (by native_decide) 4907 [4096]
      rfl rfl (by native_decide)
  have c8175 : denoteGraph_ringAttn pm initPM 8175
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4907) :=
    ringAttn_reduce1_pm_opaque pm initPM 4
      { rank := 0, op := "OpName.ChunkPrim", ins := [4907], outs := [8175], params := [0] }
      4907 8175 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4907 8175 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8176 : denoteGraph_ringAttn pm initPM 8176
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4907) :=
    ringAttn_reduce1_pm_opaque pm initPM 17
      { rank := 1, op := "OpName.ChunkPrim", ins := [4907], outs := [8176], params := [0] }
      4907 8176 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4907 8176 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4909
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4907)
          (denoteGraph_ringAttn sm initSM 4902) (denoteGraph_ringAttn sm initSM 4904) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 164
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4907, 4902, 4904], outs := [4908, 4909], params := [16, 4] }
          4909 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4907 4902 4904 4908 4909 (by decide),
        ringAttn_prefix_read_pm sm initSM 164 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 164 4907 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 164 4902 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 164 4904 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8179
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11857) (denoteGraph_ringAttn pm initPM 8175)
          (denoteGraph_ringAttn pm initPM 8143) (denoteGraph_ringAttn pm initPM 8155) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 389
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11857, 8175, 8143, 8155], outs := [8177, 8179], params := [16, 4] }
          8179 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11857 8175 8143 8155 8177 8179 (by decide),
        ringAttn_prefix_read_pm pm initPM 389 11857 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 389 8175 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 389 8143 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 389 8155 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8180
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11857) (denoteGraph_ringAttn pm initPM 8176)
          (denoteGraph_ringAttn pm initPM 8144) (denoteGraph_ringAttn pm initPM 8156) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 390
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11857, 8176, 8144, 8156], outs := [8178, 8180], params := [16, 4] }
          8180 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11857 8176 8144 8156 8178 8180 (by decide),
        ringAttn_prefix_read_pm pm initPM 390 11857 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 390 8176 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 390 8144 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 390 8156 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4909
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8179, denoteGraph_ringAttn pm initPM 8180] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 4907) (denoteGraph_ringAttn pm initPM 8155)
          (denoteGraph_ringAttn pm initPM 8156) 2048 4 64 (by omega) (by omega) (by omega)
          hsp4907 hs8155 hs8156,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8175
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 4907) from c8175),
        ← (show denoteGraph_ringAttn pm initPM 8176
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 4907) from c8176),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8179).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8155
  have hsp1 : (denoteGraph_ringAttn pm initPM 8180).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8156
  have hshape : (denoteGraph_ringAttn sm initSM 4909).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4909 4909 8179 8180 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
