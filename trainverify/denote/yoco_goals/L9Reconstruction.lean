/- Worker #23 — Layer-9 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_5128_ringAttn` (the layer-9
   sliding-window attention output, unconditional-given-WF) through the layer-9
   forward block.

   Unlike L2, the L9 block has NO gather-to-full node (L2's PM node 228
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L9
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_5132` targets `[8937, 8938]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L8Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 5129 — 2-tp reshape of the L9 attention output `5128 : [4096,16,64]` to
    `[4096,1024]` (SM node 205, PM nodes 471/472). -/
theorem recon_intermediateGoal_5129_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5129
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs8925, hs8926⟩ := twoTp_gather _ _ intermediateGoal_5128 5128 8925 8926
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5128_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5129
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5128) :=
    ringAttn_reshape_reduce_pm sm initSM 322 0 5128 5129 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8927
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8925) :=
    ringAttn_reshape_reduce_pm pm initPM 705 0 8925 8927 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8928
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8926) :=
    ringAttn_reshape_reduce_pm pm initPM 706 1 8926 8928 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5129
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8927, denoteGraph_ringAttn pm initPM 8928] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs8925 hs8926
  have hs8927 : (denoteGraph_ringAttn pm initPM 8927).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8928 : (denoteGraph_ringAttn pm initPM 8928).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5129 : (denoteGraph_ringAttn sm initSM 5129).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5129 5129 8927 8928 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5129 hs8927 hs8928

/-- 5130 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 206, PM
    nodes 473/474). -/
theorem recon_intermediateGoal_5130_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5130
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs8927, hs8928⟩ := twoTp_gather _ _ intermediateGoal_5129 5129 8927 8928
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5129_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5129 : (denoteGraph_ringAttn sm initSM 5129).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8927])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5130
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5129) :=
    ringAttn_reshape_reduce_pm sm initSM 323 0 5129 5130 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8933
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8927) :=
    ringAttn_reshape_reduce_pm pm initPM 707 0 8927 8933 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8934
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8928) :=
    ringAttn_reshape_reduce_pm pm initPM 708 1 8928 8934 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8933 = denoteGraph_ringAttn pm initPM 8927 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8927]
  have h18 : denoteGraph_ringAttn pm initPM 8934 = denoteGraph_ringAttn pm initPM 8928 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8928]
  have hval : denoteGraph_ringAttn sm initSM 5130
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8933, denoteGraph_ringAttn pm initPM 8934] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5129, hval05, hnr, ← h17, ← h18]
  have hs8933 : (denoteGraph_ringAttn pm initPM 8933).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8934 : (denoteGraph_ringAttn pm initPM 8934).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5130 : (denoteGraph_ringAttn sm initSM 5130).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5130 5130 8933 8934 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5130 hs8933 hs8934

/-- 5132 — 2-tp down-projection `fw_linear(5130, 5131)` (weight `5131 : [1024,1024]`,
    SM node 207, PM nodes 475/476). -/
theorem recon_intermediateGoal_5132_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5132
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs8933, hs8934⟩ := twoTp_gather _ _ intermediateGoal_5130 5130 8933 8934
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5130_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5131 : denoteGraph_ringAttn sm initSM 5131 = denoteGraph_ringAttn pm initPM 5131 :=
    veq_weight_ring initSM initPM hInit initGoal_5131 (by native_decide) 5131
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5131 : (denoteGraph_ringAttn sm initSM 5131).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5131 (by native_decide) 5131 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw5131 : (denoteGraph_ringAttn pm initPM 5131).shape = [1024, 1024] := by
    rw [← hw5131]; exact hsw5131
  have rSM : denoteGraph_ringAttn sm initSM 5132
      = fw_linear (denoteGraph_ringAttn sm initSM 5130) (denoteGraph_ringAttn sm initSM 5131) :=
    ringAttn_reduce2_pm_opaque sm initSM 324
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5130, 5131], outs := [5132] }
      5130 5131 5132 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5130 5131 5132)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8937
      = fw_linear (denoteGraph_ringAttn pm initPM 8933) (denoteGraph_ringAttn pm initPM 5131) :=
    ringAttn_reduce2_pm_opaque pm initPM 709
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8933, 5131], outs := [8937] }
      8933 5131 8937 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8933 5131 8937)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8938
      = fw_linear (denoteGraph_ringAttn pm initPM 8934) (denoteGraph_ringAttn pm initPM 5131) :=
    ringAttn_reduce2_pm_opaque pm initPM 710
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8934, 5131], outs := [8938] }
      8934 5131 8938 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8934 5131 8938)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5132
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8937, denoteGraph_ringAttn pm initPM 8938] := by
    rw [rSM, hval06, hw5131, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs8933 hs8934 hpw5131,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8937).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8933 hpw5131
  have hsp1 : (denoteGraph_ringAttn pm initPM 8938).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8934 hpw5131
  have hshape : (denoteGraph_ringAttn sm initSM 5132).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5132 5132 8937 8938 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5133 — 2-tp identity view of `5132` (SM node 208, PM nodes 477/478). -/
theorem recon_intermediateGoal_5133_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5133
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs8937, hs8938⟩ := twoTp_gather _ _ intermediateGoal_5132 5132 8937 8938
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5132_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5132 : (denoteGraph_ringAttn sm initSM 5132).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8937])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5133
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5132) :=
    ringAttn_reduce1_pm_opaque sm initSM 325
      { rank := 0, op := "OpName.FW_view", ins := [5132], outs := [5133], params := [4096, 1024] }
      5132 5133 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5132 5133)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8947
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8937) :=
    ringAttn_reduce1_pm_opaque pm initPM 711
      { rank := 0, op := "OpName.FW_view", ins := [8937], outs := [8947], params := [2048, 1024] }
      8937 8947 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8937 8947)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8948
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8938) :=
    ringAttn_reduce1_pm_opaque pm initPM 712
      { rank := 1, op := "OpName.FW_view", ins := [8938], outs := [8948], params := [2048, 1024] }
      8938 8948 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8938 8948)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 8947 = denoteGraph_ringAttn pm initPM 8937 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8937]
  have h32 : denoteGraph_ringAttn pm initPM 8948 = denoteGraph_ringAttn pm initPM 8938 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8938]
  have hval : denoteGraph_ringAttn sm initSM 5133
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8947, denoteGraph_ringAttn pm initPM 8948] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5132, hval08, hnr, ← h31, ← h32]
  have hs8947 : (denoteGraph_ringAttn pm initPM 8947).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8948 : (denoteGraph_ringAttn pm initPM 8948).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5133 : (denoteGraph_ringAttn sm initSM 5133).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5133 5133 8947 8948 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5133 hs8947 hs8948

/-- 5134 — 2-tp `FW_float(5133)` (identity, SM node 209, PM nodes 479/480). -/
theorem recon_intermediateGoal_5134_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5134
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs8947, hs8948⟩ := twoTp_gather _ _ intermediateGoal_5133 5133 8947 8948
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5133_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5134 = id (denoteGraph_ringAttn sm initSM 5133) :=
    ringAttn_reduce1_pm_opaque sm initSM 326
      { rank := 0, op := "OpName.FW_float", ins := [5133], outs := [5134] }
      5133 5134 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5133 5134 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8951 = id (denoteGraph_ringAttn pm initPM 8947) :=
    ringAttn_reduce1_pm_opaque pm initPM 713
      { rank := 0, op := "OpName.FW_float", ins := [8947], outs := [8951] }
      8947 8951 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8947 8951 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8952 = id (denoteGraph_ringAttn pm initPM 8948) :=
    ringAttn_reduce1_pm_opaque pm initPM 714
      { rank := 1, op := "OpName.FW_float", ins := [8948], outs := [8952] }
      8948 8952 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8948 8952 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5134
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8951, denoteGraph_ringAttn pm initPM 8952] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8951).shape = [2048, 1024] := by rw [rP0]; exact hs8947
  have hsp1 : (denoteGraph_ringAttn pm initPM 8952).shape = [2048, 1024] := by rw [rP1]; exact hs8948
  have hshape : (denoteGraph_ringAttn sm initSM 5134).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5134 5134 8951 8952 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7803 — 2-tp `mref2`-second copy of the L2 residual `5114` (SM node 197,
    PM nodes 455/456), carried into the L9 residual add. -/
theorem recon_intermediateGoal_7803_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7803
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs8881, hs8882⟩ := twoTp_gather _ _ intermediateGoal_5114 5114 8881 8882
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5114_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7937 : denoteGraph_ringAttn sm initSM 7803 = id (denoteGraph_ringAttn sm initSM 5114) :=
    ringAttn_reduce1_pm_opaque sm initSM 314
      { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803], params := [2] }
      5114 7803 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5114 7799 7803 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15329 : denoteGraph_ringAttn pm initPM 15329 = id (denoteGraph_ringAttn pm initPM 8881) :=
    ringAttn_reduce1_pm_opaque pm initPM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329], params := [2] }
      8881 15329 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8881 15325 15329 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15337 : denoteGraph_ringAttn pm initPM 15337 = id (denoteGraph_ringAttn pm initPM 8882) :=
    ringAttn_reduce1_pm_opaque pm initPM 690
      { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337], params := [2] }
      8882 15337 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8882 15333 15337 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7937 p15329 p15337
  have hsp0 : (denoteGraph_ringAttn pm initPM 15329).shape = [2048, 1024] := by
    rw [p15329]; exact hs8881
  have hsp1 : (denoteGraph_ringAttn pm initPM 15337).shape = [2048, 1024] := by
    rw [p15337]; exact hs8882
  have hval : denoteGraph_ringAttn sm initSM 7803
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15329, denoteGraph_ringAttn pm initPM 15337] := by
    rw [s7937, hbr90, ← p15329, ← p15337]
  have hshape : (denoteGraph_ringAttn sm initSM 7803).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7803 7803 15329 15337 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5135 — 2-tp L9 residual add `7803 + 5134` (SM node 210, PM nodes 481/482). -/
theorem recon_intermediateGoal_5135_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5135
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs15329, hs15337⟩ := twoTp_gather _ _ intermediateGoal_7803 7803 15329 15337
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7803_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs8951, hs8952⟩ := twoTp_gather _ _ intermediateGoal_5134 5134 8951 8952
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5134_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5135
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7803) (denoteGraph_ringAttn sm initSM 5134) :=
    ringAttn_reduce2_pm_opaque sm initSM 327
      { rank := 0, op := "OpName.FW_add", ins := [7803, 5134], outs := [5135] }
      7803 5134 5135 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7803 5134 5135)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8955
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15329) (denoteGraph_ringAttn pm initPM 8951) :=
    ringAttn_reduce2_pm_opaque pm initPM 715
      { rank := 0, op := "OpName.FW_add", ins := [15329, 8951], outs := [8955] }
      15329 8951 8955 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15329 8951 8955)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8956
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15337) (denoteGraph_ringAttn pm initPM 8952) :=
    ringAttn_reduce2_pm_opaque pm initPM 716
      { rank := 1, op := "OpName.FW_add", ins := [15337, 8952], outs := [8956] }
      15337 8952 8956 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15337 8952 8956)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5135
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8955, denoteGraph_ringAttn pm initPM 8956] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15329 hs15337 hs8951 hs8952,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8955).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15329 hs8951
  have hsp1 : (denoteGraph_ringAttn pm initPM 8956).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15337 hs8952
  have hshape : (denoteGraph_ringAttn sm initSM 5135).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5135 5135 8955 8956 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5137 — 2-tp RMSNorm of `mref2-first(5135)` with replicated weight
    `5136 : [1024]` (SM node 212, PM nodes 485/486). -/
theorem recon_intermediateGoal_5137_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5137
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8955, hs8956⟩ := twoTp_gather _ _ intermediateGoal_5135 5135 8955 8956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5135_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7820 : denoteGraph_ringAttn sm initSM 7820 = id (denoteGraph_ringAttn sm initSM 5135) :=
    ringAttn_reduce1_pm_opaque sm initSM 328
      { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824], params := [2] }
      5135 7820 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5135 7820 7824)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15367 : denoteGraph_ringAttn pm initPM 15367 = id (denoteGraph_ringAttn pm initPM 8955) :=
    ringAttn_reduce1_pm_opaque pm initPM 717
      { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371], params := [2] }
      8955 15367 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8955 15367 15371)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15375 : denoteGraph_ringAttn pm initPM 15375 = id (denoteGraph_ringAttn pm initPM 8956) :=
    ringAttn_reduce1_pm_opaque pm initPM 718
      { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379], params := [2] }
      8956 15375 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8956 15375 15379)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7820 p15367 p15375
  have hs15367 : (denoteGraph_ringAttn pm initPM 15367).shape = [2048, 1024] := by
    rw [p15367]; exact hs8955
  have hs15375 : (denoteGraph_ringAttn pm initPM 15375).shape = [2048, 1024] := by
    rw [p15375]; exact hs8956
  have hbr08 : denoteGraph_ringAttn sm initSM 7820
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15367, denoteGraph_ringAttn pm initPM 15375] := by
    rw [s7820, hbr11, ← p15367, ← p15375]
  have hw5136 : denoteGraph_ringAttn sm initSM 5136 = denoteGraph_ringAttn pm initPM 5136 :=
    veq_weight_ring initSM initPM hInit initGoal_5136 (by native_decide) 5136
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5137
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7820) (denoteGraph_ringAttn sm initSM 5136) :=
    ringAttn_reduce2_pm_opaque sm initSM 329
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7820, 5136], outs := [5137] }
      7820 5136 5137 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7820 5136 5137)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8959
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15367) (denoteGraph_ringAttn pm initPM 5136) :=
    ringAttn_reduce2_pm_opaque pm initPM 719
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15367, 5136], outs := [8959] }
      15367 5136 8959 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15367 5136 8959)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8960
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15375) (denoteGraph_ringAttn pm initPM 5136) :=
    ringAttn_reduce2_pm_opaque pm initPM 720
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15375, 5136], outs := [8960] }
      15375 5136 8960 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15375 5136 8960)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5137
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8959, denoteGraph_ringAttn pm initPM 8960] := by
    rw [rSM, hbr08, hw5136, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15367 hs15375,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8959).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15367
  have hsp1 : (denoteGraph_ringAttn pm initPM 8960).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15375
  have hshape : (denoteGraph_ringAttn sm initSM 5137).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5137 5137 8959 8960 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5138 — 2-tp `FW_float(mref5-first(5137))` (identity, SM node 214,
    PM nodes 489/493; mref5-first via SM node 213, PM 487/488). -/
theorem recon_intermediateGoal_5138_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5138
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8959, hs8960⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7831 : denoteGraph_ringAttn sm initSM 7831 = id (denoteGraph_ringAttn sm initSM 5137) :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137],
        outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7831 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 5137 7831 [7835, 7839, 7843, 7847])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15386 : denoteGraph_ringAttn pm initPM 15386 = id (denoteGraph_ringAttn pm initPM 8959) :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959],
        outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15386 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 8959 15386 [15390, 15394, 15398, 15402])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15409 : denoteGraph_ringAttn pm initPM 15409 = id (denoteGraph_ringAttn pm initPM 8960) :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960],
        outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15409 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 8960 15409 [15413, 15417, 15421, 15425])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7831 p15386 p15409
  have hbrm : denoteGraph_ringAttn sm initSM 7831
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15386, denoteGraph_ringAttn pm initPM 15409] := by
    rw [s7831, hbr13, ← p15386, ← p15409]
  have rSM : denoteGraph_ringAttn sm initSM 5138 = id (denoteGraph_ringAttn sm initSM 7831) :=
    ringAttn_reduce1_pm_opaque sm initSM 331
      { rank := 0, op := "OpName.FW_float", ins := [7831], outs := [5138] }
      7831 5138 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7831 5138 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8961 = id (denoteGraph_ringAttn pm initPM 15386) :=
    ringAttn_reduce1_pm_opaque pm initPM 723
      { rank := 0, op := "OpName.FW_float", ins := [15386], outs := [8961] }
      15386 8961 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 15386 8961 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8962 = id (denoteGraph_ringAttn pm initPM 15409) :=
    ringAttn_reduce1_pm_opaque pm initPM 727
      { rank := 1, op := "OpName.FW_float", ins := [15409], outs := [8962] }
      15409 8962 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 15409 8962 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs15386 : (denoteGraph_ringAttn pm initPM 15386).shape = [2048, 1024] := by
    rw [p15386]; exact hs8959
  have hs15409 : (denoteGraph_ringAttn pm initPM 15409).shape = [2048, 1024] := by
    rw [p15409]; exact hs8960
  have hval : denoteGraph_ringAttn sm initSM 5138
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8961, denoteGraph_ringAttn pm initPM 8962] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8961).shape = [2048, 1024] := by
    rw [rP0]; exact hs15386
  have hsp1 : (denoteGraph_ringAttn pm initPM 8962).shape = [2048, 1024] := by
    rw [rP1]; exact hs15409
  have hshape : (denoteGraph_ringAttn sm initSM 5138).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5138 5138 8961 8962 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5140 — 2-tp router logits `fw_norm_linear(5138, 5139)` with weight
    `5139 : [64, 1024]` → `[4096, 64]` (SM node 218, PM nodes 497/501). -/
theorem recon_intermediateGoal_5140_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5140
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs8961, hs8962⟩ := twoTp_gather _ _ intermediateGoal_5138 5138 8961 8962
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5138_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5139 : denoteGraph_ringAttn sm initSM 5139 = denoteGraph_ringAttn pm initPM 5139 :=
    veq_weight_ring initSM initPM hInit initGoal_5139 (by native_decide) 5139
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5139 : (denoteGraph_ringAttn sm initSM 5139).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5139 (by native_decide) 5139 [64, 1024]
      rfl rfl (by native_decide)
  have hpw5139 : (denoteGraph_ringAttn pm initPM 5139).shape = [64, 1024] := by
    rw [← hw5139]; exact hsw5139
  have rSM : denoteGraph_ringAttn sm initSM 5140
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 5138) (denoteGraph_ringAttn sm initSM 5139) :=
    ringAttn_reduce2_pm_opaque sm initSM 335
      { rank := 0, op := "OpName.FW_norm_linear", ins := [5138, 5139], outs := [5140] }
      5138 5139 5140 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 5138 5139 5140)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8967
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8961) (denoteGraph_ringAttn pm initPM 5139) :=
    ringAttn_reduce2_pm_opaque pm initPM 731
      { rank := 0, op := "OpName.FW_norm_linear", ins := [8961, 5139], outs := [8967] }
      8961 5139 8967 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 8961 5139 8967)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8968
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8962) (denoteGraph_ringAttn pm initPM 5139) :=
    ringAttn_reduce2_pm_opaque pm initPM 735
      { rank := 1, op := "OpName.FW_norm_linear", ins := [8962, 5139], outs := [8968] }
      8962 5139 8968 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 8962 5139 8968)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5140
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8967, denoteGraph_ringAttn pm initPM 8968] := by
    rw [rSM, hval14, hw5139, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs8961 hs8962 hpw5139,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8967).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8961 hpw5139
  have hsp1 : (denoteGraph_ringAttn pm initPM 8968).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8962 hpw5139
  have hshape : (denoteGraph_ringAttn sm initSM 5140).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5140 5140 8967 8968 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L9 top-k routing (`5141`/`5142`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`8967`/`8968`) directly. -/

/-- Shared L9 top-k core: `5140` (full logits) is the dim-0 gather of the two
    per-rank shards `8967`/`8968`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L9 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 5140
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 8967, denoteGraph_ringAttn pm initPM 8968]
      ∧ (denoteGraph_ringAttn sm initSM 5140).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8967).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8968).shape = [2048, 64]
      ∧ ((sm.nodes.take 339).foldl (applyNodeRingAttn sm) initSM 5140).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 739).foldl (applyNodeRingAttn pm) initPM 8967).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 743).foldl (applyNodeRingAttn pm) initPM 8968).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs8967, hs8968⟩ := twoTp_gather _ _ intermediateGoal_5140 5140 8967 8968
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5140_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs5140sm : (denoteGraph_ringAttn sm initSM 5140).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs8967])]
    simp [List.set, List.getD]
  have hpre5140sm : denoteGraph_ringAttn sm initSM 5140
      = (sm.nodes.take 339).foldl (applyNodeRingAttn sm) initSM 5140 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5140 339 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 339).foldl (applyNodeRingAttn sm) initSM 5140).shape.reverse.head? = some 64 := by
    rw [← hpre5140sm, hs5140sm]; rfl
  have hpre8967 : denoteGraph_ringAttn pm initPM 8967
      = (pm.nodes.take 739).foldl (applyNodeRingAttn pm) initPM 8967 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8967 739 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 739).foldl (applyNodeRingAttn pm) initPM 8967).shape.reverse.head? = some 64 := by
    rw [← hpre8967, hs8967]; rfl
  have hpre8968 : denoteGraph_ringAttn pm initPM 8968
      = (pm.nodes.take 743).foldl (applyNodeRingAttn pm) initPM 8968 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8968 743 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 743).foldl (applyNodeRingAttn pm) initPM 8968).shape.reverse.head? = some 64 := by
    rw [← hpre8968, hs8968]; rfl
  exact ⟨hbr16, hs5140sm, hs8967, hs8968, hlastSM, hlast271, hlast275⟩

/-- 5141 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5141_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5141
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5140sm, hs8967, hs8968, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L9 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5141
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5140) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 339
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5140], outs := [5141, 5142, 5143], params := [8, 1] }
      5140 5141 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 339).foldl (applyNodeRingAttn sm) initSM) 0 5140 5141 5142 5143 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8969
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8967) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 739
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8967], outs := [8969, 8971, 8973], params := [8, 1] }
      8967 8969 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 739).foldl (applyNodeRingAttn pm) initPM) 0 8967 8969 8971 8973 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8970
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8968) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 743
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8968], outs := [8970, 8972, 8974], params := [8, 1] }
      8968 8970 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 743).foldl (applyNodeRingAttn pm) initPM) 1 8968 8970 8972 8974 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5141
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8969, denoteGraph_ringAttn pm initPM 8970] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8967 hs8968,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5141).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs5140sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8969).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8967]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8970).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8968]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5141 5141 8969 8970 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5142 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5142_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5142
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5140sm, hs8967, hs8968, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L9 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5142
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5140) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 339
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5140], outs := [5141, 5142, 5143], params := [8, 1] }
      5140 5142 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 339).foldl (applyNodeRingAttn sm) initSM) 0 5140 5141 5142 5143 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8971
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8967) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 739
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8967], outs := [8969, 8971, 8973], params := [8, 1] }
      8967 8971 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 739).foldl (applyNodeRingAttn pm) initPM) 0 8967 8969 8971 8973 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8972
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8968) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 743
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8968], outs := [8970, 8972, 8974], params := [8, 1] }
      8968 8972 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 743).foldl (applyNodeRingAttn pm) initPM) 1 8968 8970 8972 8974 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5142
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8971, denoteGraph_ringAttn pm initPM 8972] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8967 hs8968,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5142).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs5140sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8971).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8967]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8972).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8968]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5142 5142 8971 8972 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L9 router expert branches — reshape (`5147`/`5152`/`5156`) of the
    `mref5` copies (positions 2/3/4) of `5137`, all identity 2-tp views. -/

/-- 5147 — 2-tp identity reshape of `mref5-pos2(5137)` (SM node 215, PM 490/494). -/
theorem recon_intermediateGoal_5147_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5147
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8959, hs8960⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5137sm : (denoteGraph_ringAttn sm initSM 5137).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8959])]
    simp [List.set, List.getD]
  have s7839 : denoteGraph_ringAttn sm initSM 7839 = id (denoteGraph_ringAttn sm initSM 5137) :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137],
        outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7839 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15394 : denoteGraph_ringAttn pm initPM 15394 = id (denoteGraph_ringAttn pm initPM 8959) :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959],
        outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15394 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15417 : denoteGraph_ringAttn pm initPM 15417 = id (denoteGraph_ringAttn pm initPM 8960) :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960],
        outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15417 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7839 p15394 p15417
  have hs7839 : (denoteGraph_ringAttn sm initSM 7839).shape = [4096, 1024] := by rw [s7839]; exact hs5137sm
  have hs15394 : (denoteGraph_ringAttn pm initPM 15394).shape = [2048, 1024] := by rw [p15394]; exact hs8959
  have hs15417 : (denoteGraph_ringAttn pm initPM 15417).shape = [2048, 1024] := by rw [p15417]; exact hs8960
  have hbrm : denoteGraph_ringAttn sm initSM 7839
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15394, denoteGraph_ringAttn pm initPM 15417] := by
    rw [s7839, hbr13, ← p15394, ← p15417]
  have rSM : denoteGraph_ringAttn sm initSM 5147
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7839) :=
    ringAttn_reduce1_pm_opaque sm initSM 332
      { rank := 0, op := "OpName.FW_reshape", ins := [7839], outs := [5147], params := [4096, 1024] }
      7839 5147 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7839 5147)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8981
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15394) :=
    ringAttn_reduce1_pm_opaque pm initPM 724
      { rank := 0, op := "OpName.FW_reshape", ins := [15394], outs := [8981], params := [2048, 1024] }
      15394 8981 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15394 8981)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8982
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15417) :=
    ringAttn_reduce1_pm_opaque pm initPM 728
      { rank := 1, op := "OpName.FW_reshape", ins := [15417], outs := [8982], params := [2048, 1024] }
      15417 8982 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15417 8982)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 8981 = denoteGraph_ringAttn pm initPM 15394 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15394]
  have h66 : denoteGraph_ringAttn pm initPM 8982 = denoteGraph_ringAttn pm initPM 15417 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15417]
  have hval : denoteGraph_ringAttn sm initSM 5147
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8981, denoteGraph_ringAttn pm initPM 8982] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7839, hbrm, hnr, ← h65, ← h66]
  have hs8981 : (denoteGraph_ringAttn pm initPM 8981).shape = [2048, 1024] := by rw [h65]; exact hs15394
  have hs8982 : (denoteGraph_ringAttn pm initPM 8982).shape = [2048, 1024] := by rw [h66]; exact hs15417
  have hs5147 : (denoteGraph_ringAttn sm initSM 5147).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7839]; exact hs7839
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5147 5147 8981 8982 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5147 hs8981 hs8982

/-- 5152 — 2-tp identity reshape of `mref5-pos3(5137)` (SM node 216, PM 491/495). -/
theorem recon_intermediateGoal_5152_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5152
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8959, hs8960⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5137sm : (denoteGraph_ringAttn sm initSM 5137).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8959])]
    simp [List.set, List.getD]
  have s7843 : denoteGraph_ringAttn sm initSM 7843 = id (denoteGraph_ringAttn sm initSM 5137) :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137],
        outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7843 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15398 : denoteGraph_ringAttn pm initPM 15398 = id (denoteGraph_ringAttn pm initPM 8959) :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959],
        outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15398 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15421 : denoteGraph_ringAttn pm initPM 15421 = id (denoteGraph_ringAttn pm initPM 8960) :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960],
        outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15421 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7843 p15398 p15421
  have hs7843 : (denoteGraph_ringAttn sm initSM 7843).shape = [4096, 1024] := by rw [s7843]; exact hs5137sm
  have hs15398 : (denoteGraph_ringAttn pm initPM 15398).shape = [2048, 1024] := by rw [p15398]; exact hs8959
  have hs15421 : (denoteGraph_ringAttn pm initPM 15421).shape = [2048, 1024] := by rw [p15421]; exact hs8960
  have hbrm : denoteGraph_ringAttn sm initSM 7843
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15398, denoteGraph_ringAttn pm initPM 15421] := by
    rw [s7843, hbr13, ← p15398, ← p15421]
  have rSM : denoteGraph_ringAttn sm initSM 5152
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7843) :=
    ringAttn_reduce1_pm_opaque sm initSM 333
      { rank := 0, op := "OpName.FW_reshape", ins := [7843], outs := [5152], params := [4096, 1024] }
      7843 5152 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7843 5152)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8995
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15398) :=
    ringAttn_reduce1_pm_opaque pm initPM 725
      { rank := 0, op := "OpName.FW_reshape", ins := [15398], outs := [8995], params := [2048, 1024] }
      15398 8995 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15398 8995)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8996
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15421) :=
    ringAttn_reduce1_pm_opaque pm initPM 729
      { rank := 1, op := "OpName.FW_reshape", ins := [15421], outs := [8996], params := [2048, 1024] }
      15421 8996 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15421 8996)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 8995 = denoteGraph_ringAttn pm initPM 15398 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15398]
  have h80 : denoteGraph_ringAttn pm initPM 8996 = denoteGraph_ringAttn pm initPM 15421 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15421]
  have hval : denoteGraph_ringAttn sm initSM 5152
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8995, denoteGraph_ringAttn pm initPM 8996] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7843, hbrm, hnr, ← h79, ← h80]
  have hs8995 : (denoteGraph_ringAttn pm initPM 8995).shape = [2048, 1024] := by rw [h79]; exact hs15398
  have hs8996 : (denoteGraph_ringAttn pm initPM 8996).shape = [2048, 1024] := by rw [h80]; exact hs15421
  have hs5152 : (denoteGraph_ringAttn sm initSM 5152).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7843]; exact hs7843
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5152 5152 8995 8996 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5152 hs8995 hs8996

/-- 5156 — 2-tp identity reshape of `mref5-pos4(5137)` (SM node 217, PM 492/496). -/
theorem recon_intermediateGoal_5156_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5156
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8959, hs8960⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5137sm : (denoteGraph_ringAttn sm initSM 5137).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8959])]
    simp [List.set, List.getD]
  have s7847 : denoteGraph_ringAttn sm initSM 7847 = id (denoteGraph_ringAttn sm initSM 5137) :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137],
        outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7847 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15402 : denoteGraph_ringAttn pm initPM 15402 = id (denoteGraph_ringAttn pm initPM 8959) :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959],
        outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15402 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15425 : denoteGraph_ringAttn pm initPM 15425 = id (denoteGraph_ringAttn pm initPM 8960) :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960],
        outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15425 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7847 p15402 p15425
  have hs7847 : (denoteGraph_ringAttn sm initSM 7847).shape = [4096, 1024] := by rw [s7847]; exact hs5137sm
  have hs15402 : (denoteGraph_ringAttn pm initPM 15402).shape = [2048, 1024] := by rw [p15402]; exact hs8959
  have hs15425 : (denoteGraph_ringAttn pm initPM 15425).shape = [2048, 1024] := by rw [p15425]; exact hs8960
  have hbrm : denoteGraph_ringAttn sm initSM 7847
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15402, denoteGraph_ringAttn pm initPM 15425] := by
    rw [s7847, hbr13, ← p15402, ← p15425]
  have rSM : denoteGraph_ringAttn sm initSM 5156
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7847) :=
    ringAttn_reduce1_pm_opaque sm initSM 334
      { rank := 0, op := "OpName.FW_reshape", ins := [7847], outs := [5156], params := [4096, 1024] }
      7847 5156 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7847 5156)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9013
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15402) :=
    ringAttn_reduce1_pm_opaque pm initPM 726
      { rank := 0, op := "OpName.FW_reshape", ins := [15402], outs := [9013], params := [2048, 1024] }
      15402 9013 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15402 9013)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9014
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15425) :=
    ringAttn_reduce1_pm_opaque pm initPM 730
      { rank := 1, op := "OpName.FW_reshape", ins := [15425], outs := [9014], params := [2048, 1024] }
      15425 9014 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15425 9014)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 9013 = denoteGraph_ringAttn pm initPM 15402 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15402]
  have h98 : denoteGraph_ringAttn pm initPM 9014 = denoteGraph_ringAttn pm initPM 15425 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15425]
  have hval : denoteGraph_ringAttn sm initSM 5156
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9013, denoteGraph_ringAttn pm initPM 9014] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7847, hbrm, hnr, ← h97, ← h98]
  have hs9013 : (denoteGraph_ringAttn pm initPM 9013).shape = [2048, 1024] := by rw [h97]; exact hs15402
  have hs9014 : (denoteGraph_ringAttn pm initPM 9014).shape = [2048, 1024] := by rw [h98]; exact hs15425
  have hs5156 : (denoteGraph_ringAttn sm initSM 5156).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7847]; exact hs7847
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5156 5156 9013 9014 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5156 hs9013 hs9014

/-! ### L9 router expert mixlins (`5149`/`5154`/`5158`), 2-tp. -/

/-- 5149 — 2-tp `fw_linear(5147, 5148)`, weight `5148 : [1, 1024]` → `[4096, 1]`
    (SM node 219, PM nodes 498/502). -/
theorem recon_intermediateGoal_5149_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5149
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs8981, hs8982⟩ := twoTp_gather _ _ intermediateGoal_5147 5147 8981 8982
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5147_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5148 : denoteGraph_ringAttn sm initSM 5148 = denoteGraph_ringAttn pm initPM 5148 :=
    veq_weight_ring initSM initPM hInit initGoal_5148 (by native_decide) 5148
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5148 : (denoteGraph_ringAttn pm initPM 5148).shape = [1, 1024] := by
    rw [← hw5148]
    exact shape_weight_ring initSM initPM hInit initGoal_5148 (by native_decide) 5148 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5149
      = fw_linear (denoteGraph_ringAttn sm initSM 5147) (denoteGraph_ringAttn sm initSM 5148) :=
    ringAttn_reduce2_pm_opaque sm initSM 336
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5147, 5148], outs := [5149] }
      5147 5148 5149 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5147 5148 5149)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8985
      = fw_linear (denoteGraph_ringAttn pm initPM 8981) (denoteGraph_ringAttn pm initPM 5148) :=
    ringAttn_reduce2_pm_opaque pm initPM 732
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8981, 5148], outs := [8985] }
      8981 5148 8985 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8981 5148 8985)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8986
      = fw_linear (denoteGraph_ringAttn pm initPM 8982) (denoteGraph_ringAttn pm initPM 5148) :=
    ringAttn_reduce2_pm_opaque pm initPM 736
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8982, 5148], outs := [8986] }
      8982 5148 8986 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8982 5148 8986)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5149
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8985, denoteGraph_ringAttn pm initPM 8986] := by
    rw [rSM, hval23, hw5148, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs8981 hs8982 hpw5148,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8985).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8981 hpw5148
  have hsp1 : (denoteGraph_ringAttn pm initPM 8986).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8982 hpw5148
  have hshape : (denoteGraph_ringAttn sm initSM 5149).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5149 5149 8985 8986 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5154 — 2-tp `fw_linear(5152, 5153)`, weight `5153 : [512, 1024]` → `[4096, 512]`
    (SM node 220, PM nodes 499/503). -/
theorem recon_intermediateGoal_5154_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5154
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs8995, hs8996⟩ := twoTp_gather _ _ intermediateGoal_5152 5152 8995 8996
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5152_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5153 : denoteGraph_ringAttn sm initSM 5153 = denoteGraph_ringAttn pm initPM 5153 :=
    veq_weight_ring initSM initPM hInit initGoal_5153 (by native_decide) 5153
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5153 : (denoteGraph_ringAttn pm initPM 5153).shape = [512, 1024] := by
    rw [← hw5153]
    exact shape_weight_ring initSM initPM hInit initGoal_5153 (by native_decide) 5153 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5154
      = fw_linear (denoteGraph_ringAttn sm initSM 5152) (denoteGraph_ringAttn sm initSM 5153) :=
    ringAttn_reduce2_pm_opaque sm initSM 337
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5152, 5153], outs := [5154] }
      5152 5153 5154 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5152 5153 5154)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8999
      = fw_linear (denoteGraph_ringAttn pm initPM 8995) (denoteGraph_ringAttn pm initPM 5153) :=
    ringAttn_reduce2_pm_opaque pm initPM 733
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8995, 5153], outs := [8999] }
      8995 5153 8999 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8995 5153 8999)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9000
      = fw_linear (denoteGraph_ringAttn pm initPM 8996) (denoteGraph_ringAttn pm initPM 5153) :=
    ringAttn_reduce2_pm_opaque pm initPM 737
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8996, 5153], outs := [9000] }
      8996 5153 9000 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8996 5153 9000)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5154
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8999, denoteGraph_ringAttn pm initPM 9000] := by
    rw [rSM, hval28, hw5153, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8995 hs8996 hpw5153,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8999).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8995 hpw5153
  have hsp1 : (denoteGraph_ringAttn pm initPM 9000).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8996 hpw5153
  have hshape : (denoteGraph_ringAttn sm initSM 5154).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5154 5154 8999 9000 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5158 — 2-tp `fw_linear(5156, 5157)`, weight `5157 : [512, 1024]` → `[4096, 512]`
    (SM node 221, PM nodes 500/504). -/
theorem recon_intermediateGoal_5158_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5158
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs9013, hs9014⟩ := twoTp_gather _ _ intermediateGoal_5156 5156 9013 9014
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5156_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5157 : denoteGraph_ringAttn sm initSM 5157 = denoteGraph_ringAttn pm initPM 5157 :=
    veq_weight_ring initSM initPM hInit initGoal_5157 (by native_decide) 5157
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5157 : (denoteGraph_ringAttn pm initPM 5157).shape = [512, 1024] := by
    rw [← hw5157]
    exact shape_weight_ring initSM initPM hInit initGoal_5157 (by native_decide) 5157 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5158
      = fw_linear (denoteGraph_ringAttn sm initSM 5156) (denoteGraph_ringAttn sm initSM 5157) :=
    ringAttn_reduce2_pm_opaque sm initSM 338
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5156, 5157], outs := [5158] }
      5156 5157 5158 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5156 5157 5158)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9017
      = fw_linear (denoteGraph_ringAttn pm initPM 9013) (denoteGraph_ringAttn pm initPM 5157) :=
    ringAttn_reduce2_pm_opaque pm initPM 734
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9013, 5157], outs := [9017] }
      9013 5157 9017 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9013 5157 9017)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9018
      = fw_linear (denoteGraph_ringAttn pm initPM 9014) (denoteGraph_ringAttn pm initPM 5157) :=
    ringAttn_reduce2_pm_opaque pm initPM 738
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9014, 5157], outs := [9018] }
      9014 5157 9018 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9014 5157 9018)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5158
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9017, denoteGraph_ringAttn pm initPM 9018] := by
    rw [rSM, hval32, hw5157, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs9013 hs9014 hpw5157,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9017).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9013 hpw5157
  have hsp1 : (denoteGraph_ringAttn pm initPM 9018).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9014 hpw5157
  have hshape : (denoteGraph_ringAttn sm initSM 5158).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5158 5158 9017 9018 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L9 router expert views (`5150`/`5155`/`5159`), identity 2-tp views. -/

/-- 5150 — 2-tp identity view of `5149` → `[4096, 1]` (SM node 223, PM 506/510). -/
theorem recon_intermediateGoal_5150_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5150
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs8985, hs8986⟩ := twoTp_gather _ _ intermediateGoal_5149 5149 8985 8986
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5149_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5149 : (denoteGraph_ringAttn sm initSM 5149).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8985])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5150
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 5149) :=
    ringAttn_reduce1_pm_opaque sm initSM 340
      { rank := 0, op := "OpName.FW_view", ins := [5149], outs := [5150], params := [4096, 1] }
      5149 5150 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 5149 5150)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8991
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8985) :=
    ringAttn_reduce1_pm_opaque pm initPM 740
      { rank := 0, op := "OpName.FW_view", ins := [8985], outs := [8991], params := [2048, 1] }
      8985 8991 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 8985 8991)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8992
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8986) :=
    ringAttn_reduce1_pm_opaque pm initPM 744
      { rank := 1, op := "OpName.FW_view", ins := [8986], outs := [8992], params := [2048, 1] }
      8986 8992 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 8986 8992)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 8991 = denoteGraph_ringAttn pm initPM 8985 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs8985]
  have h76 : denoteGraph_ringAttn pm initPM 8992 = denoteGraph_ringAttn pm initPM 8986 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs8986]
  have hval : denoteGraph_ringAttn sm initSM 5150
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8991, denoteGraph_ringAttn pm initPM 8992] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5149, hval25, hnr, ← h75, ← h76]
  have hs8991 : (denoteGraph_ringAttn pm initPM 8991).shape = [2048, 1] := by rw [h75]; exact hs8985
  have hs8992 : (denoteGraph_ringAttn pm initPM 8992).shape = [2048, 1] := by rw [h76]; exact hs8986
  have hs5150 : (denoteGraph_ringAttn sm initSM 5150).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5149]; exact hs5149
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5150 5150 8991 8992 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5150 hs8991 hs8992

/-- 5155 — 2-tp identity view of `5154` → `[4096, 512]` (SM node 224, PM 507/511). -/
theorem recon_intermediateGoal_5155_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5155
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs8999, hs9000⟩ := twoTp_gather _ _ intermediateGoal_5154 5154 8999 9000
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5154_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5154 : (denoteGraph_ringAttn sm initSM 5154).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8999])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5155
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5154) :=
    ringAttn_reduce1_pm_opaque sm initSM 341
      { rank := 0, op := "OpName.FW_view", ins := [5154], outs := [5155], params := [4096, 512] }
      5154 5155 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5154 5155)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9009
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8999) :=
    ringAttn_reduce1_pm_opaque pm initPM 741
      { rank := 0, op := "OpName.FW_view", ins := [8999], outs := [9009], params := [2048, 512] }
      8999 9009 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8999 9009)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9010
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9000) :=
    ringAttn_reduce1_pm_opaque pm initPM 745
      { rank := 1, op := "OpName.FW_view", ins := [9000], outs := [9010], params := [2048, 512] }
      9000 9010 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9000 9010)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 9009 = denoteGraph_ringAttn pm initPM 8999 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8999]
  have h94 : denoteGraph_ringAttn pm initPM 9010 = denoteGraph_ringAttn pm initPM 9000 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9000]
  have hval : denoteGraph_ringAttn sm initSM 5155
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9009, denoteGraph_ringAttn pm initPM 9010] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5154, hval30, hnr, ← h93, ← h94]
  have hs9009 : (denoteGraph_ringAttn pm initPM 9009).shape = [2048, 512] := by rw [h93]; exact hs8999
  have hs9010 : (denoteGraph_ringAttn pm initPM 9010).shape = [2048, 512] := by rw [h94]; exact hs9000
  have hs5155 : (denoteGraph_ringAttn sm initSM 5155).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5154]; exact hs5154
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5155 5155 9009 9010 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5155 hs9009 hs9010

/-- 5159 — 2-tp identity view of `5158` → `[4096, 512]` (SM node 225, PM 508/512). -/
theorem recon_intermediateGoal_5159_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5159
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs9017, hs9018⟩ := twoTp_gather _ _ intermediateGoal_5158 5158 9017 9018
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5158_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5158 : (denoteGraph_ringAttn sm initSM 5158).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9017])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5159
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5158) :=
    ringAttn_reduce1_pm_opaque sm initSM 342
      { rank := 0, op := "OpName.FW_view", ins := [5158], outs := [5159], params := [4096, 512] }
      5158 5159 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5158 5159)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9027
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9017) :=
    ringAttn_reduce1_pm_opaque pm initPM 742
      { rank := 0, op := "OpName.FW_view", ins := [9017], outs := [9027], params := [2048, 512] }
      9017 9027 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9017 9027)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9028
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9018) :=
    ringAttn_reduce1_pm_opaque pm initPM 746
      { rank := 1, op := "OpName.FW_view", ins := [9018], outs := [9028], params := [2048, 512] }
      9018 9028 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9018 9028)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 9027 = denoteGraph_ringAttn pm initPM 9017 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9017]
  have h12 : denoteGraph_ringAttn pm initPM 9028 = denoteGraph_ringAttn pm initPM 9018 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9018]
  have hval : denoteGraph_ringAttn sm initSM 5159
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9027, denoteGraph_ringAttn pm initPM 9028] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5158, hval34, hnr, ← h11, ← h12]
  have hs9027 : (denoteGraph_ringAttn pm initPM 9027).shape = [2048, 512] := by rw [h11]; exact hs9017
  have hs9028 : (denoteGraph_ringAttn pm initPM 9028).shape = [2048, 512] := by rw [h12]; exact hs9018
  have hs5159 : (denoteGraph_ringAttn sm initSM 5159).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5158]; exact hs5158
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5159 5159 9027 9028 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5159 hs9027 hs9028

/-! ### L9 MoE gate/expert branch (`5151` sigmoid, `5160` swiglu, `5161` reshape,
    `5163` mixlin, `5164` view, `5165` broadcast-mul), all 2-tp shard-direct. -/

/-- 5151 — 2-tp `fw_sigmoid(5150)` → `[4096, 1]` (SM node 227, PM 514/517). -/
theorem recon_intermediateGoal_5151_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5151
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs8991, hs8992⟩ := twoTp_gather _ _ intermediateGoal_5150 5150 8991 8992
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5150_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5151 = fw_sigmoid (denoteGraph_ringAttn sm initSM 5150) :=
    ringAttn_reduce1_pm_opaque sm initSM 344
      { rank := 0, op := "OpName.FW_sigmoid", ins := [5150], outs := [5151] }
      5150 5151 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 5150 5151 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8993 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8991) :=
    ringAttn_reduce1_pm_opaque pm initPM 748
      { rank := 0, op := "OpName.FW_sigmoid", ins := [8991], outs := [8993] }
      8991 8993 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 8991 8993 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8994 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8992) :=
    ringAttn_reduce1_pm_opaque pm initPM 751
      { rank := 1, op := "OpName.FW_sigmoid", ins := [8992], outs := [8994] }
      8992 8994 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 8992 8994 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5151
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8993, denoteGraph_ringAttn pm initPM 8994] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs8991 hs8992, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5151).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8991])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8993).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs8991
  have hsp1 : (denoteGraph_ringAttn pm initPM 8994).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs8992
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5151 5151 8993 8994 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5160 — 2-tp `fw_swiglu(5155, 5159)` → `[4096, 512]` (SM node 228, PM 515/518). -/
theorem recon_intermediateGoal_5160_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5160
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs9009, hs9010⟩ := twoTp_gather _ _ intermediateGoal_5155 5155 9009 9010
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5155_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs9027, hs9028⟩ := twoTp_gather _ _ intermediateGoal_5159 5159 9027 9028
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5159_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5160
      = fw_swiglu (denoteGraph_ringAttn sm initSM 5155) (denoteGraph_ringAttn sm initSM 5159) :=
    ringAttn_reduce2_pm_opaque sm initSM 345
      { rank := 0, op := "OpName.FW_swiglu", ins := [5155, 5159], outs := [5160] }
      5155 5159 5160 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 5155 5159 5160 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9031
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9009) (denoteGraph_ringAttn pm initPM 9027) :=
    ringAttn_reduce2_pm_opaque pm initPM 749
      { rank := 0, op := "OpName.FW_swiglu", ins := [9009, 9027], outs := [9031] }
      9009 9027 9031 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 9009 9027 9031 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9032
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9010) (denoteGraph_ringAttn pm initPM 9028) :=
    ringAttn_reduce2_pm_opaque pm initPM 752
      { rank := 1, op := "OpName.FW_swiglu", ins := [9010, 9028], outs := [9032] }
      9010 9028 9032 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 9010 9028 9032 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5160
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9031, denoteGraph_ringAttn pm initPM 9032] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs9009 hs9010 hs9027 hs9028,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5160).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9027])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9031).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9027
  have hsp1 : (denoteGraph_ringAttn pm initPM 9032).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9028
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5160 5160 9031 9032 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5161 — 2-tp identity reshape of `5160` → `[4096, 512]` (SM node 229, PM 519/520). -/
theorem recon_intermediateGoal_5161_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5161
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs9031, hs9032⟩ := twoTp_gather _ _ intermediateGoal_5160 5160 9031 9032
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5160_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5160 : (denoteGraph_ringAttn sm initSM 5160).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9031])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5161
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5160) :=
    ringAttn_reduce1_pm_opaque sm initSM 346
      { rank := 0, op := "OpName.FW_reshape", ins := [5160], outs := [5161], params := [4096, 512] }
      5160 5161 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5160 5161)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9033
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9031) :=
    ringAttn_reduce1_pm_opaque pm initPM 753
      { rank := 0, op := "OpName.FW_reshape", ins := [9031], outs := [9033], params := [2048, 512] }
      9031 9033 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9031 9033)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9034
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9032) :=
    ringAttn_reduce1_pm_opaque pm initPM 754
      { rank := 1, op := "OpName.FW_reshape", ins := [9032], outs := [9034], params := [2048, 512] }
      9032 9034 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9032 9034)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 9033 = denoteGraph_ringAttn pm initPM 9031 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9031]
  have h18 : denoteGraph_ringAttn pm initPM 9034 = denoteGraph_ringAttn pm initPM 9032 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9032]
  have hval : denoteGraph_ringAttn sm initSM 5161
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9033, denoteGraph_ringAttn pm initPM 9034] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5160, hval36, hnr, ← h17, ← h18]
  have hs9033 : (denoteGraph_ringAttn pm initPM 9033).shape = [2048, 512] := by rw [h17]; exact hs9031
  have hs9034 : (denoteGraph_ringAttn pm initPM 9034).shape = [2048, 512] := by rw [h18]; exact hs9032
  have hs5161 : (denoteGraph_ringAttn sm initSM 5161).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5160]; exact hs5160
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5161 5161 9033 9034 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5161 hs9033 hs9034

/-- 5163 — 2-tp `fw_linear(5161, 5162)`, weight `5162 : [1024, 512]` → `[4096, 1024]`
    (SM node 230, PM 521/522). -/
theorem recon_intermediateGoal_5163_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5163
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs9033, hs9034⟩ := twoTp_gather _ _ intermediateGoal_5161 5161 9033 9034
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5161_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5162 : denoteGraph_ringAttn sm initSM 5162 = denoteGraph_ringAttn pm initPM 5162 :=
    veq_weight_ring initSM initPM hInit initGoal_5162 (by native_decide) 5162
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5162 : (denoteGraph_ringAttn pm initPM 5162).shape = [1024, 512] := by
    rw [← hw5162]
    exact shape_weight_ring initSM initPM hInit initGoal_5162 (by native_decide) 5162 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5163
      = fw_linear (denoteGraph_ringAttn sm initSM 5161) (denoteGraph_ringAttn sm initSM 5162) :=
    ringAttn_reduce2_pm_opaque sm initSM 347
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5161, 5162], outs := [5163] }
      5161 5162 5163 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5161 5162 5163)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9039
      = fw_linear (denoteGraph_ringAttn pm initPM 9033) (denoteGraph_ringAttn pm initPM 5162) :=
    ringAttn_reduce2_pm_opaque pm initPM 755
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9033, 5162], outs := [9039] }
      9033 5162 9039 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9033 5162 9039)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9040
      = fw_linear (denoteGraph_ringAttn pm initPM 9034) (denoteGraph_ringAttn pm initPM 5162) :=
    ringAttn_reduce2_pm_opaque pm initPM 756
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9034, 5162], outs := [9040] }
      9034 5162 9040 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9034 5162 9040)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5163
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9039, denoteGraph_ringAttn pm initPM 9040] := by
    rw [rSM, hval37, hw5162, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs9033 hs9034 hpw5162,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9039).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9033 hpw5162
  have hsp1 : (denoteGraph_ringAttn pm initPM 9040).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9034 hpw5162
  have hshape : (denoteGraph_ringAttn sm initSM 5163).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5163 5163 9039 9040 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5164 — 2-tp identity view of `5163` → `[4096, 1024]` (SM node 231, PM 523/524). -/
theorem recon_intermediateGoal_5164_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5164
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs9039, hs9040⟩ := twoTp_gather _ _ intermediateGoal_5163 5163 9039 9040
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5163_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5163 : (denoteGraph_ringAttn sm initSM 5163).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9039])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5164
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5163) :=
    ringAttn_reduce1_pm_opaque sm initSM 348
      { rank := 0, op := "OpName.FW_view", ins := [5163], outs := [5164], params := [4096, 1024] }
      5163 5164 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5163 5164)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9049
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9039) :=
    ringAttn_reduce1_pm_opaque pm initPM 757
      { rank := 0, op := "OpName.FW_view", ins := [9039], outs := [9049], params := [2048, 1024] }
      9039 9049 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9039 9049)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9050
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9040) :=
    ringAttn_reduce1_pm_opaque pm initPM 758
      { rank := 1, op := "OpName.FW_view", ins := [9040], outs := [9050], params := [2048, 1024] }
      9040 9050 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9040 9050)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 9049 = denoteGraph_ringAttn pm initPM 9039 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9039]
  have h34 : denoteGraph_ringAttn pm initPM 9050 = denoteGraph_ringAttn pm initPM 9040 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9040]
  have hval : denoteGraph_ringAttn sm initSM 5164
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9049, denoteGraph_ringAttn pm initPM 9050] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5163, hval39, hnr, ← h33, ← h34]
  have hs9049 : (denoteGraph_ringAttn pm initPM 9049).shape = [2048, 1024] := by rw [h33]; exact hs9039
  have hs9050 : (denoteGraph_ringAttn pm initPM 9050).shape = [2048, 1024] := by rw [h34]; exact hs9040
  have hs5164 : (denoteGraph_ringAttn sm initSM 5164).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5163]; exact hs5163
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5164 5164 9049 9050 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5164 hs9049 hs9050

/-- 5165 — 2-tp broadcast `mul(5151, 5164)` → `[4096, 1024]` (SM node 232, PM 525/526). -/
theorem recon_intermediateGoal_5165_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5165
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_5151 5151 8993 8994
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5151_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_5164 5164 9049 9050
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5164_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5165
      = elemwiseMul (denoteGraph_ringAttn sm initSM 5151) (denoteGraph_ringAttn sm initSM 5164) :=
    ringAttn_reduce2_pm_opaque sm initSM 349
      { rank := 0, op := "OpName.FW_mul", ins := [5151, 5164], outs := [5165] }
      5151 5164 5165 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 5151 5164 5165)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9053
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8993) (denoteGraph_ringAttn pm initPM 9049) :=
    ringAttn_reduce2_pm_opaque pm initPM 759
      { rank := 0, op := "OpName.FW_mul", ins := [8993, 9049], outs := [9053] }
      8993 9049 9053 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 8993 9049 9053)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9054
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8994) (denoteGraph_ringAttn pm initPM 9050) :=
    ringAttn_reduce2_pm_opaque pm initPM 760
      { rank := 1, op := "OpName.FW_mul", ins := [8994, 9050], outs := [9054] }
      8994 9050 9054 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 8994 9050 9054)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5165
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9053, denoteGraph_ringAttn pm initPM 9054] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 5165).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 5151).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 5164).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 9053).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 9054).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5165 5165 9053 9054 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 5146 — layer-9 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 5146 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`8979`), rank 1 →
    `[32, 64)` (`8980`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `8971`/`8972` are expert-local (the
    `wf5146_hdisjA/B` fields).  Token input `7835 = mref5-pos1(5137)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 226, PM nodes 513/516). -/
theorem recon_intermediateGoal_5146_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5146
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 8103 = mref5-pos1(5137).
  obtain ⟨hbr13, hs8959, hs8960⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8103 : denoteGraph_ringAttn sm initSM 7835 = id (denoteGraph_ringAttn sm initSM 5137) :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137],
        outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7835 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15390 : denoteGraph_ringAttn pm initPM 15390 = id (denoteGraph_ringAttn pm initPM 8959) :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959],
        outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15390 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15413 : denoteGraph_ringAttn pm initPM 15413 = id (denoteGraph_ringAttn pm initPM 8960) :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960],
        outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15413 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8103 p15390 p15413
  have hsInA : (denoteGraph_ringAttn pm initPM 15390).shape = [2048, 1024] := by
    rw [p15390]; exact hs8959
  have hsInB : (denoteGraph_ringAttn pm initPM 15413).shape = [2048, 1024] := by
    rw [p15413]; exact hs8960
  have hbrIn : denoteGraph_ringAttn sm initSM 7835
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 15390, denoteGraph_ringAttn pm initPM 15413] := by
    rw [s8103, hbr13, hnr, ← p15390, ← p15413]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_5141 5141 8969 8970
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5141_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_5142 5142 8971 8972
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5142_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 5141
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8969, denoteGraph_ringAttn pm initPM 8970] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 5142
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8971, denoteGraph_ringAttn pm initPM 8972] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_5144
    (by native_decide) 5144 8975 8976 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_5145
    (by native_decide) 5145 8977 8978 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 8975).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5144 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5144, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8975 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 8976).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5144 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5144, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8976 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 8977).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5145 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5145, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8977 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 8978).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5145 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5145, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8978 (by native_decide)]; exact hs.2
  -- SM 5146 = full-range all2all (SM node 226).
  have hSMout : denoteGraph_ringAttn sm initSM 5146
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7835)
          (denoteGraph_ringAttn sm initSM 5141) (denoteGraph_ringAttn sm initSM 5142)
          (denoteGraph_ringAttn sm initSM 5144) (denoteGraph_ringAttn sm initSM 5145)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 343
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7835, 5141, 5142, 5144, 5145],
        outs := [5146], params := [64, 0, 64, 8] }
      7835 5141 5142 5144 5145 5146
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7835 5141 5142 5144 5145 5146 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8979 = rank-0 sharded-range all2all (PM node 513).
  have hP0 : denoteGraph_ringAttn pm initPM 8979
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15390)
          (denoteGraph_ringAttn pm initPM 8969) (denoteGraph_ringAttn pm initPM 8971)
          (denoteGraph_ringAttn pm initPM 8975) (denoteGraph_ringAttn pm initPM 8977)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 747
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15390, 8969, 8971, 8975, 8977],
        outs := [8979], params := [64, 0, 32, 8] }
      15390 8969 8971 8975 8977 8979
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 15390 8969 8971 8975 8977 8979 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8980 = rank-1 sharded-range all2all (PM node 516).
  have hP1 : denoteGraph_ringAttn pm initPM 8980
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15413)
          (denoteGraph_ringAttn pm initPM 8970) (denoteGraph_ringAttn pm initPM 8972)
          (denoteGraph_ringAttn pm initPM 8976) (denoteGraph_ringAttn pm initPM 8978)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 750
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15413, 8970, 8972, 8976, 8978],
        outs := [8980], params := [64, 32, 64, 8] }
      15413 8970 8972 8976 8978 8980
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 15413 8970 8972 8976 8978 8980 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 15390) (denoteGraph_ringAttn pm initPM 15413)
      (denoteGraph_ringAttn pm initPM 8969) (denoteGraph_ringAttn pm initPM 8970)
      (denoteGraph_ringAttn pm initPM 8971) (denoteGraph_ringAttn pm initPM 8972)
      (denoteGraph_ringAttn pm initPM 8975) (denoteGraph_ringAttn pm initPM 8976)
      (denoteGraph_ringAttn pm initPM 8977) (denoteGraph_ringAttn pm initPM 8978)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf5146_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf5146_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 5146
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8979, denoteGraph_ringAttn pm initPM 8980] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8979).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8980).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 5146).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5146 5146 8979 8980 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L9 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7824 — second position of the L9 pre-MoE residual `mref2(5135)` (2-tp, PM
    shards `15371`/`15379`).  Unlike L2's `7772` there is no gather-to-full/chunk
    because `5135` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 211, PM nodes 477/478). -/
theorem recon_intermediateGoal_7824_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7824
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8955, hs8956⟩ := twoTp_gather _ _ intermediateGoal_5135 5135 8955 8956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5135_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7958 : denoteGraph_ringAttn sm initSM 7824 = id (denoteGraph_ringAttn sm initSM 5135) :=
    ringAttn_reduce1_pm_opaque sm initSM 328
      { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824], params := [2] }
      5135 7824 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5135 7820 7824 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15371 : denoteGraph_ringAttn pm initPM 15371 = id (denoteGraph_ringAttn pm initPM 8955) :=
    ringAttn_reduce1_pm_opaque pm initPM 717
      { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371], params := [2] }
      8955 15371 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8955 15367 15371 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15379 : denoteGraph_ringAttn pm initPM 15379 = id (denoteGraph_ringAttn pm initPM 8956) :=
    ringAttn_reduce1_pm_opaque pm initPM 718
      { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379], params := [2] }
      8956 15379 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8956 15375 15379 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7958 p15371 p15379
  have hsp0 : (denoteGraph_ringAttn pm initPM 15371).shape = [2048, 1024] := by
    rw [p15371]; exact hs8955
  have hsp1 : (denoteGraph_ringAttn pm initPM 15379).shape = [2048, 1024] := by
    rw [p15379]; exact hs8956
  have hval : denoteGraph_ringAttn sm initSM 7824
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15371, denoteGraph_ringAttn pm initPM 15379] := by
    rw [s7958, hbr11, ← p15371, ← p15379]
  have hshape : (denoteGraph_ringAttn sm initSM 7824).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7824 7824 15371 15379 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5166 — post-MoE residual add `5146 + 5165` (2-tp, PM `9057`/`9058`). -/
theorem recon_intermediateGoal_5166_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5166
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs8979, hs8980⟩ := twoTp_gather _ _ intermediateGoal_5146 5146 8979 8980
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5146_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs9053, hs9054⟩ := twoTp_gather _ _ intermediateGoal_5165 5165 9053 9054
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5165_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5166
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 5146) (denoteGraph_ringAttn sm initSM 5165) :=
    ringAttn_reduce2_pm_opaque sm initSM 350
      { rank := 0, op := "OpName.FW_add", ins := [5146, 5165], outs := [5166] }
      5146 5165 5166 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 5146 5165 5166)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9057
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8979) (denoteGraph_ringAttn pm initPM 9053) :=
    ringAttn_reduce2_pm_opaque pm initPM 761
      { rank := 0, op := "OpName.FW_add", ins := [8979, 9053], outs := [9057] }
      8979 9053 9057 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 8979 9053 9057)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9058
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8980) (denoteGraph_ringAttn pm initPM 9054) :=
    ringAttn_reduce2_pm_opaque pm initPM 762
      { rank := 1, op := "OpName.FW_add", ins := [8980, 9054], outs := [9058] }
      8980 9054 9058 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 8980 9054 9058)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5166
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9057, denoteGraph_ringAttn pm initPM 9058] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs8979 hs8980 hs9053 hs9054,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9057).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8979 hs9053
  have hsp1 : (denoteGraph_ringAttn pm initPM 9058).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8980 hs9054
  have hshape : (denoteGraph_ringAttn sm initSM 5166).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5166 5166 9057 9058 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5167 — `FW_float(5166)` (identity, 2-tp PM `9063`/`9064`). -/
theorem recon_intermediateGoal_5167_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5167
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs9057, hs9058⟩ := twoTp_gather _ _ intermediateGoal_5166 5166 9057 9058
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5166_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5167 = id (denoteGraph_ringAttn sm initSM 5166) :=
    ringAttn_reduce1_pm_opaque sm initSM 351
      { rank := 0, op := "OpName.FW_float", ins := [5166], outs := [5167] }
      5166 5167 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5166 5167 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9063 = id (denoteGraph_ringAttn pm initPM 9057) :=
    ringAttn_reduce1_pm_opaque pm initPM 763
      { rank := 0, op := "OpName.FW_float", ins := [9057], outs := [9063] }
      9057 9063 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9057 9063 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9064 = id (denoteGraph_ringAttn pm initPM 9058) :=
    ringAttn_reduce1_pm_opaque pm initPM 764
      { rank := 1, op := "OpName.FW_float", ins := [9058], outs := [9064] }
      9058 9064 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9058 9064 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5167
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9063, denoteGraph_ringAttn pm initPM 9064] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9063).shape = [2048, 1024] := by rw [rP0]; exact hs9057
  have hsp1 : (denoteGraph_ringAttn pm initPM 9064).shape = [2048, 1024] := by rw [rP1]; exact hs9058
  have hshape : (denoteGraph_ringAttn sm initSM 5167).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5167 5167 9063 9064 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5168 — cross-block residual add `7824 + 5167` (2-tp, PM `9067`/`9068`). -/
theorem recon_intermediateGoal_5168_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5168
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs15371, hs15379⟩ := twoTp_gather _ _ intermediateGoal_7824 7824 15371 15379
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7824_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs9063, hs9064⟩ := twoTp_gather _ _ intermediateGoal_5167 5167 9063 9064
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5167_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5168
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7824) (denoteGraph_ringAttn sm initSM 5167) :=
    ringAttn_reduce2_pm_opaque sm initSM 352
      { rank := 0, op := "OpName.FW_add", ins := [7824, 5167], outs := [5168] }
      7824 5167 5168 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7824 5167 5168)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9067
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15371) (denoteGraph_ringAttn pm initPM 9063) :=
    ringAttn_reduce2_pm_opaque pm initPM 765
      { rank := 0, op := "OpName.FW_add", ins := [15371, 9063], outs := [9067] }
      15371 9063 9067 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15371 9063 9067)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9068
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15379) (denoteGraph_ringAttn pm initPM 9064) :=
    ringAttn_reduce2_pm_opaque pm initPM 766
      { rank := 1, op := "OpName.FW_add", ins := [15379, 9064], outs := [9068] }
      15379 9064 9068 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15379 9064 9068)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5168
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9067, denoteGraph_ringAttn pm initPM 9068] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15371 hs15379 hs9063 hs9064,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9067).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15371 hs9063
  have hsp1 : (denoteGraph_ringAttn pm initPM 9068).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15379 hs9064
  have hshape : (denoteGraph_ringAttn sm initSM 5168).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5168 5168 9067 9068 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5170 — RMSNorm of `mref2-first(5168)` with replicated weight `5169`
    (2-tp, PM `9071`/`9072`). -/
theorem recon_intermediateGoal_5170_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5170
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs9067, hs9068⟩ := twoTp_gather _ _ intermediateGoal_5168 5168 9067 9068
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5168_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8119 : denoteGraph_ringAttn sm initSM 7851 = id (denoteGraph_ringAttn sm initSM 5168) :=
    ringAttn_reduce1_pm_opaque sm initSM 353
      { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855], params := [2] }
      5168 7851 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5168 7851 7855)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15429 : denoteGraph_ringAttn pm initPM 15429 = id (denoteGraph_ringAttn pm initPM 9067) :=
    ringAttn_reduce1_pm_opaque pm initPM 767
      { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433], params := [2] }
      9067 15429 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9067 15429 15433)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15437 : denoteGraph_ringAttn pm initPM 15437 = id (denoteGraph_ringAttn pm initPM 9068) :=
    ringAttn_reduce1_pm_opaque pm initPM 768
      { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441], params := [2] }
      9068 15437 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9068 15437 15441)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8119 p15429 p15437
  have hs15429 : (denoteGraph_ringAttn pm initPM 15429).shape = [2048, 1024] := by
    rw [p15429]; exact hs9067
  have hs15437 : (denoteGraph_ringAttn pm initPM 15437).shape = [2048, 1024] := by
    rw [p15437]; exact hs9068
  have hbr39 : denoteGraph_ringAttn sm initSM 7851
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15429, denoteGraph_ringAttn pm initPM 15437] := by
    rw [s8119, hbr44, ← p15429, ← p15437]
  have hw5169 : denoteGraph_ringAttn sm initSM 5169 = denoteGraph_ringAttn pm initPM 5169 :=
    veq_weight_ring initSM initPM hInit initGoal_5169 (by native_decide) 5169
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5170
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7851) (denoteGraph_ringAttn sm initSM 5169) :=
    ringAttn_reduce2_pm_opaque sm initSM 354
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7851, 5169], outs := [5170] }
      7851 5169 5170 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7851 5169 5170)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9071
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15429) (denoteGraph_ringAttn pm initPM 5169) :=
    ringAttn_reduce2_pm_opaque pm initPM 769
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15429, 5169], outs := [9071] }
      15429 5169 9071 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15429 5169 9071)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9072
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15437) (denoteGraph_ringAttn pm initPM 5169) :=
    ringAttn_reduce2_pm_opaque pm initPM 770
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15437, 5169], outs := [9072] }
      15437 5169 9072 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15437 5169 9072)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5170
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9071, denoteGraph_ringAttn pm initPM 9072] := by
    rw [rSM, hbr39, hw5169, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15429 hs15437,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9071).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15429
  have hsp1 : (denoteGraph_ringAttn pm initPM 9072).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15437
  have hshape : (denoteGraph_ringAttn sm initSM 5170).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5170 5170 9071 9072 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5172 — per-head Q projection `fw_per_head_linear(mref3₀(5170), 5171)`
    (2-tp, PM `9073`/`9074`, weight `5171 : [16,64,1024]`). -/
theorem recon_intermediateGoal_5172_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5172
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9071, hs9072⟩ := twoTp_gather _ _ intermediateGoal_5170 5170 9071 9072
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5170_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8128 : denoteGraph_ringAttn sm initSM 7860 = id (denoteGraph_ringAttn sm initSM 5170) :=
    ringAttn_reduce1_pm_opaque sm initSM 355
      { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
      5170 7860 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5170 7860 7864 7868)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15446 : denoteGraph_ringAttn pm initPM 15446 = id (denoteGraph_ringAttn pm initPM 9071) :=
    ringAttn_reduce1_pm_opaque pm initPM 771
      { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
      9071 15446 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 9071 15446 15450 15454)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15459 : denoteGraph_ringAttn pm initPM 15459 = id (denoteGraph_ringAttn pm initPM 9072) :=
    ringAttn_reduce1_pm_opaque pm initPM 772
      { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
      9072 15459 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 9072 15459 15463 15467)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8128 p15446 p15459
  have hs15446 : (denoteGraph_ringAttn pm initPM 15446).shape = [2048, 1024] := by
    rw [p15446]; exact hs9071
  have hs15459 : (denoteGraph_ringAttn pm initPM 15459).shape = [2048, 1024] := by
    rw [p15459]; exact hs9072
  have hbr48 : denoteGraph_ringAttn sm initSM 7860
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15446, denoteGraph_ringAttn pm initPM 15459] := by
    rw [s8128, hbr46, ← p15446, ← p15459]
  have hw5171 : denoteGraph_ringAttn sm initSM 5171 = denoteGraph_ringAttn pm initPM 5171 :=
    veq_weight_ring initSM initPM hInit initGoal_5171 (by native_decide) 5171
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5171 : (denoteGraph_ringAttn sm initSM 5171).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5171 (by native_decide) 5171 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5171 : (denoteGraph_ringAttn pm initPM 5171).shape = [16, 64, 1024] := by
    rw [← hw5171]; exact hsw5171
  have rSM : denoteGraph_ringAttn sm initSM 5172
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7860) (denoteGraph_ringAttn sm initSM 5171) :=
    ringAttn_reduce2_pm_opaque sm initSM 356
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7860, 5171], outs := [5172] }
      7860 5171 5172 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7860 5171 5172 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9073
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15446) (denoteGraph_ringAttn pm initPM 5171) :=
    ringAttn_reduce2_pm_opaque pm initPM 773
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15446, 5171], outs := [9073] }
      15446 5171 9073 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15446 5171 9073 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9074
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15459) (denoteGraph_ringAttn pm initPM 5171) :=
    ringAttn_reduce2_pm_opaque pm initPM 776
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15459, 5171], outs := [9074] }
      15459 5171 9074 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15459 5171 9074 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5172
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9073, denoteGraph_ringAttn pm initPM 9074] := by
    rw [rSM, hbr48, hw5171, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs15446 hs15459 hpw5171,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9073).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15446 hpw5171
  have hsp1 : (denoteGraph_ringAttn pm initPM 9074).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15459 hpw5171
  have hshape : (denoteGraph_ringAttn sm initSM 5172).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5172 5172 9073 9074 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5174 — per-head K projection `fw_per_head_linear(mref3₁(5170), 5173)`
    (2-tp, PM `9085`/`9086`, weight `5173 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5174_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5174
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9071, hs9072⟩ := twoTp_gather _ _ intermediateGoal_5170 5170 9071 9072
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5170_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7998 : denoteGraph_ringAttn sm initSM 7864 = id (denoteGraph_ringAttn sm initSM 5170) :=
    ringAttn_reduce1_pm_opaque sm initSM 355
      { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
      5170 7864 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5170 7860 7864 7868 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15450 : denoteGraph_ringAttn pm initPM 15450 = id (denoteGraph_ringAttn pm initPM 9071) :=
    ringAttn_reduce1_pm_opaque pm initPM 771
      { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
      9071 15450 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 9071 15446 15450 15454 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15463 : denoteGraph_ringAttn pm initPM 15463 = id (denoteGraph_ringAttn pm initPM 9072) :=
    ringAttn_reduce1_pm_opaque pm initPM 772
      { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
      9072 15463 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 9072 15459 15463 15467 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7998 p15450 p15463
  have hs15450 : (denoteGraph_ringAttn pm initPM 15450).shape = [2048, 1024] := by
    rw [p15450]; exact hs9071
  have hs15463 : (denoteGraph_ringAttn pm initPM 15463).shape = [2048, 1024] := by
    rw [p15463]; exact hs9072
  have hbr52 : denoteGraph_ringAttn sm initSM 7864
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15450, denoteGraph_ringAttn pm initPM 15463] := by
    rw [s7998, hbr46, ← p15450, ← p15463]
  have hw5173 : denoteGraph_ringAttn sm initSM 5173 = denoteGraph_ringAttn pm initPM 5173 :=
    veq_weight_ring initSM initPM hInit initGoal_5173 (by native_decide) 5173
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5173 : (denoteGraph_ringAttn sm initSM 5173).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5173 (by native_decide) 5173 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5173 : (denoteGraph_ringAttn pm initPM 5173).shape = [4, 64, 1024] := by
    rw [← hw5173]; exact hsw5173
  have rSM : denoteGraph_ringAttn sm initSM 5174
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7864) (denoteGraph_ringAttn sm initSM 5173) :=
    ringAttn_reduce2_pm_opaque sm initSM 357
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7864, 5173], outs := [5174] }
      7864 5173 5174 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7864 5173 5174 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9085
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15450) (denoteGraph_ringAttn pm initPM 5173) :=
    ringAttn_reduce2_pm_opaque pm initPM 774
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15450, 5173], outs := [9085] }
      15450 5173 9085 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15450 5173 9085 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9086
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15463) (denoteGraph_ringAttn pm initPM 5173) :=
    ringAttn_reduce2_pm_opaque pm initPM 777
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15463, 5173], outs := [9086] }
      15463 5173 9086 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15463 5173 9086 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5174
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9085, denoteGraph_ringAttn pm initPM 9086] := by
    rw [rSM, hbr52, hw5173, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15450 hs15463 hpw5173,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9085).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15450 hpw5173
  have hsp1 : (denoteGraph_ringAttn pm initPM 9086).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15463 hpw5173
  have hshape : (denoteGraph_ringAttn sm initSM 5174).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5174 5174 9085 9086 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5176 — per-head V projection `fw_per_head_linear(mref3₂(5170), 5175)`
    (2-tp, PM `9095`/`9096`, weight `5175 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5176_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5176
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9071, hs9072⟩ := twoTp_gather _ _ intermediateGoal_5170 5170 9071 9072
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5170_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7868 : denoteGraph_ringAttn sm initSM 7868 = id (denoteGraph_ringAttn sm initSM 5170) :=
    ringAttn_reduce1_pm_opaque sm initSM 355
      { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
      5170 7868 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5170 7860 7864 7868 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15454 : denoteGraph_ringAttn pm initPM 15454 = id (denoteGraph_ringAttn pm initPM 9071) :=
    ringAttn_reduce1_pm_opaque pm initPM 771
      { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
      9071 15454 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 9071 15446 15450 15454 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15467 : denoteGraph_ringAttn pm initPM 15467 = id (denoteGraph_ringAttn pm initPM 9072) :=
    ringAttn_reduce1_pm_opaque pm initPM 772
      { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
      9072 15467 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 9072 15459 15463 15467 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7868 p15454 p15467
  have hs15454 : (denoteGraph_ringAttn pm initPM 15454).shape = [2048, 1024] := by
    rw [p15454]; exact hs9071
  have hs15467 : (denoteGraph_ringAttn pm initPM 15467).shape = [2048, 1024] := by
    rw [p15467]; exact hs9072
  have hbr56 : denoteGraph_ringAttn sm initSM 7868
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15454, denoteGraph_ringAttn pm initPM 15467] := by
    rw [s7868, hbr46, ← p15454, ← p15467]
  have hw5175 : denoteGraph_ringAttn sm initSM 5175 = denoteGraph_ringAttn pm initPM 5175 :=
    veq_weight_ring initSM initPM hInit initGoal_5175 (by native_decide) 5175
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5175 : (denoteGraph_ringAttn sm initSM 5175).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5175 (by native_decide) 5175 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5175 : (denoteGraph_ringAttn pm initPM 5175).shape = [4, 64, 1024] := by
    rw [← hw5175]; exact hsw5175
  have rSM : denoteGraph_ringAttn sm initSM 5176
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7868) (denoteGraph_ringAttn sm initSM 5175) :=
    ringAttn_reduce2_pm_opaque sm initSM 358
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7868, 5175], outs := [5176] }
      7868 5175 5176 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7868 5175 5176 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9095
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15454) (denoteGraph_ringAttn pm initPM 5175) :=
    ringAttn_reduce2_pm_opaque pm initPM 775
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15454, 5175], outs := [9095] }
      15454 5175 9095 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15454 5175 9095 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9096
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15467) (denoteGraph_ringAttn pm initPM 5175) :=
    ringAttn_reduce2_pm_opaque pm initPM 778
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15467, 5175], outs := [9096] }
      15467 5175 9096 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15467 5175 9096 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5176
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9095, denoteGraph_ringAttn pm initPM 9096] := by
    rw [rSM, hbr56, hw5175, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15454 hs15467 hpw5175,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9095).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15454 hpw5175
  have hsp1 : (denoteGraph_ringAttn pm initPM 9096).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15467 hpw5175
  have hshape : (denoteGraph_ringAttn sm initSM 5176).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5176 5176 9095 9096 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L9 rotary cos/sin cache agreement: `sm 4691 = pm 11862` (`= 11853 + 3`). -/
theorem hcache_4691_11862 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11862 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11862 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11862 9 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 5178 — rotary-embedding Q output `rotary(4691, 5177, 5172, 5174).1`
    (2-tp, PM `9107`/`9108`; positions `5177 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_5178_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5178
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs9073, hs9074⟩ := twoTp_gather _ _ intermediateGoal_5172 5172 9073 9074
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5172_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_5174 5174 9085 9086
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5174_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11862 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5177 = denoteGraph_ringAttn pm initPM 5177 :=
    veq_weight_ring initSM initPM hInit initGoal_5177 (by native_decide) 5177
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5177 : (denoteGraph_ringAttn sm initSM 5177).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5177 (by native_decide) 5177 [4096]
      rfl rfl (by native_decide)
  have c9105 : denoteGraph_ringAttn pm initPM 9105
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5177) :=
    ringAttn_reduce1_pm_opaque pm initPM 9
      { rank := 0, op := "OpName.ChunkPrim", ins := [5177], outs := [9105], params := [0] }
      5177 9105 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5177 9105 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c9106 : denoteGraph_ringAttn pm initPM 9106
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5177) :=
    ringAttn_reduce1_pm_opaque pm initPM 22
      { rank := 1, op := "OpName.ChunkPrim", ins := [5177], outs := [9106], params := [0] }
      5177 9106 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5177 9106 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5178
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5177)
          (denoteGraph_ringAttn sm initSM 5172) (denoteGraph_ringAttn sm initSM 5174) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 359
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5177, 5172, 5174], outs := [5178, 5179], params := [16, 4] }
          5178 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 359 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 359 5177 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 359 5172 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 359 5174 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 9107
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11862) (denoteGraph_ringAttn pm initPM 9105)
          (denoteGraph_ringAttn pm initPM 9073) (denoteGraph_ringAttn pm initPM 9085) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 779
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11862, 9105, 9073, 9085], outs := [9107, 9109], params := [16, 4] }
          9107 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 779 11862 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 779 9105 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 779 9073 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 779 9085 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 9108
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11862) (denoteGraph_ringAttn pm initPM 9106)
          (denoteGraph_ringAttn pm initPM 9074) (denoteGraph_ringAttn pm initPM 9086) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 780
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11862, 9106, 9074, 9086], outs := [9108, 9110], params := [16, 4] }
          9108 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 780 11862 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 780 9106 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 780 9074 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 780 9086 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5178
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9107, denoteGraph_ringAttn pm initPM 9108] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5177) (denoteGraph_ringAttn pm initPM 9073)
          (denoteGraph_ringAttn pm initPM 9074) 2048 16 64 (by omega) (by omega) (by omega)
          hsp5177 hs9073 hs9074,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 9105
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5177) from c9105),
        ← (show denoteGraph_ringAttn pm initPM 9106
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5177) from c9106),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9107).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs9073
  have hsp1 : (denoteGraph_ringAttn pm initPM 9108).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs9074
  have hshape : (denoteGraph_ringAttn sm initSM 5178).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5178 5178 9107 9108 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 5179 — rotary-embedding K output `rotary(4691, 5177, 5172, 5174).2`
    (2-tp, PM `9109`/`9110`). -/
theorem recon_intermediateGoal_5179_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5179
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_5172 5172 9073 9074
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5172_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs9085, hs9086⟩ := twoTp_gather _ _ intermediateGoal_5174 5174 9085 9086
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5174_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11862 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5177 = denoteGraph_ringAttn pm initPM 5177 :=
    veq_weight_ring initSM initPM hInit initGoal_5177 (by native_decide) 5177
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5177 : (denoteGraph_ringAttn sm initSM 5177).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5177 (by native_decide) 5177 [4096]
      rfl rfl (by native_decide)
  have c9105 : denoteGraph_ringAttn pm initPM 9105
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5177) :=
    ringAttn_reduce1_pm_opaque pm initPM 9
      { rank := 0, op := "OpName.ChunkPrim", ins := [5177], outs := [9105], params := [0] }
      5177 9105 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5177 9105 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c9106 : denoteGraph_ringAttn pm initPM 9106
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5177) :=
    ringAttn_reduce1_pm_opaque pm initPM 22
      { rank := 1, op := "OpName.ChunkPrim", ins := [5177], outs := [9106], params := [0] }
      5177 9106 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5177 9106 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5179
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5177)
          (denoteGraph_ringAttn sm initSM 5172) (denoteGraph_ringAttn sm initSM 5174) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 359
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5177, 5172, 5174], outs := [5178, 5179], params := [16, 4] }
          5179 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5177 5172 5174 5178 5179 (by decide),
        ringAttn_prefix_read_pm sm initSM 359 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 359 5177 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 359 5172 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 359 5174 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 9109
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11862) (denoteGraph_ringAttn pm initPM 9105)
          (denoteGraph_ringAttn pm initPM 9073) (denoteGraph_ringAttn pm initPM 9085) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 779
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11862, 9105, 9073, 9085], outs := [9107, 9109], params := [16, 4] }
          9109 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11862 9105 9073 9085 9107 9109 (by decide),
        ringAttn_prefix_read_pm pm initPM 779 11862 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 779 9105 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 779 9073 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 779 9085 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 9110
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11862) (denoteGraph_ringAttn pm initPM 9106)
          (denoteGraph_ringAttn pm initPM 9074) (denoteGraph_ringAttn pm initPM 9086) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 780
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11862, 9106, 9074, 9086], outs := [9108, 9110], params := [16, 4] }
          9110 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11862 9106 9074 9086 9108 9110 (by decide),
        ringAttn_prefix_read_pm pm initPM 780 11862 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 780 9106 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 780 9074 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 780 9086 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5179
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9109, denoteGraph_ringAttn pm initPM 9110] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5177) (denoteGraph_ringAttn pm initPM 9085)
          (denoteGraph_ringAttn pm initPM 9086) 2048 4 64 (by omega) (by omega) (by omega)
          hsp5177 hs9085 hs9086,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 9105
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5177) from c9105),
        ← (show denoteGraph_ringAttn pm initPM 9106
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5177) from c9106),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9109).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs9085
  have hsp1 : (denoteGraph_ringAttn pm initPM 9110).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs9086
  have hshape : (denoteGraph_ringAttn sm initSM 5179).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5179 5179 9109 9110 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
