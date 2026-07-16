/- Worker #23 — Layer-5 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_4912_ringAttn` (the layer-5
   sliding-window attention output, unconditional-given-WF) through the layer-5
   forward block.

   Unlike L2, the L5 block has NO gather-to-full node (L2's PM node 189
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L5
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_4916` targets `[8193, 8194]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L4Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 4913 — 2-tp reshape of the L5 attention output `4912 : [4096,16,64]` to
    `[4096,1024]` (SM node 166, PM nodes 393/394). -/
theorem recon_intermediateGoal_4913_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4913
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs8181, hs8182⟩ := twoTp_gather _ _ intermediateGoal_4912 4912 8181 8182
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4912_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4913
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4912) :=
    ringAttn_reshape_reduce_pm sm initSM 166 0 4912 4913 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8183
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8181) :=
    ringAttn_reshape_reduce_pm pm initPM 393 0 8181 8183 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8184
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8182) :=
    ringAttn_reshape_reduce_pm pm initPM 394 1 8182 8184 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4913
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8183, denoteGraph_ringAttn pm initPM 8184] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs8181 hs8182
  have hs8183 : (denoteGraph_ringAttn pm initPM 8183).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8184 : (denoteGraph_ringAttn pm initPM 8184).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4913 : (denoteGraph_ringAttn sm initSM 4913).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4913 4913 8183 8184 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4913 hs8183 hs8184

/-- 4914 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 167, PM
    nodes 395/396). -/
theorem recon_intermediateGoal_4914_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4914
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs8183, hs8184⟩ := twoTp_gather _ _ intermediateGoal_4913 4913 8183 8184
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4913_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4913 : (denoteGraph_ringAttn sm initSM 4913).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8183])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4914
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4913) :=
    ringAttn_reshape_reduce_pm sm initSM 167 0 4913 4914 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8189
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8183) :=
    ringAttn_reshape_reduce_pm pm initPM 395 0 8183 8189 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8190
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8184) :=
    ringAttn_reshape_reduce_pm pm initPM 396 1 8184 8190 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8189 = denoteGraph_ringAttn pm initPM 8183 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8183]
  have h18 : denoteGraph_ringAttn pm initPM 8190 = denoteGraph_ringAttn pm initPM 8184 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8184]
  have hval : denoteGraph_ringAttn sm initSM 4914
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8189, denoteGraph_ringAttn pm initPM 8190] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4913, hval05, hnr, ← h17, ← h18]
  have hs8189 : (denoteGraph_ringAttn pm initPM 8189).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8190 : (denoteGraph_ringAttn pm initPM 8190).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4914 : (denoteGraph_ringAttn sm initSM 4914).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4914 4914 8189 8190 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4914 hs8189 hs8190

/-- 4916 — 2-tp down-projection `fw_linear(4914, 4915)` (weight `4915 : [1024,1024]`,
    SM node 168, PM nodes 397/398). -/
theorem recon_intermediateGoal_4916_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4916
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs8189, hs8190⟩ := twoTp_gather _ _ intermediateGoal_4914 4914 8189 8190
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4914_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4915 : denoteGraph_ringAttn sm initSM 4915 = denoteGraph_ringAttn pm initPM 4915 :=
    veq_weight_ring initSM initPM hInit initGoal_4915 (by native_decide) 4915
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4915 : (denoteGraph_ringAttn sm initSM 4915).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4915 (by native_decide) 4915 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw4915 : (denoteGraph_ringAttn pm initPM 4915).shape = [1024, 1024] := by
    rw [← hw4915]; exact hsw4915
  have rSM : denoteGraph_ringAttn sm initSM 4916
      = fw_linear (denoteGraph_ringAttn sm initSM 4914) (denoteGraph_ringAttn sm initSM 4915) :=
    ringAttn_reduce2_pm_opaque sm initSM 168
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4914, 4915], outs := [4916] }
      4914 4915 4916 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4914 4915 4916)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8193
      = fw_linear (denoteGraph_ringAttn pm initPM 8189) (denoteGraph_ringAttn pm initPM 4915) :=
    ringAttn_reduce2_pm_opaque pm initPM 397
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8189, 4915], outs := [8193] }
      8189 4915 8193 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8189 4915 8193)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8194
      = fw_linear (denoteGraph_ringAttn pm initPM 8190) (denoteGraph_ringAttn pm initPM 4915) :=
    ringAttn_reduce2_pm_opaque pm initPM 398
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8190, 4915], outs := [8194] }
      8190 4915 8194 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8190 4915 8194)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4916
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8193, denoteGraph_ringAttn pm initPM 8194] := by
    rw [rSM, hval06, hw4915, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs8189 hs8190 hpw4915,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8193).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8189 hpw4915
  have hsp1 : (denoteGraph_ringAttn pm initPM 8194).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs8190 hpw4915
  have hshape : (denoteGraph_ringAttn sm initSM 4916).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4916 4916 8193 8194 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4917 — 2-tp identity view of `4916` (SM node 169, PM nodes 399/400). -/
theorem recon_intermediateGoal_4917_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4917
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs8193, hs8194⟩ := twoTp_gather _ _ intermediateGoal_4916 4916 8193 8194
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4916_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4916 : (denoteGraph_ringAttn sm initSM 4916).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8193])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4917
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4916) :=
    ringAttn_reduce1_pm_opaque sm initSM 169
      { rank := 0, op := "OpName.FW_view", ins := [4916], outs := [4917], params := [4096, 1024] }
      4916 4917 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4916 4917)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8203
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8193) :=
    ringAttn_reduce1_pm_opaque pm initPM 399
      { rank := 0, op := "OpName.FW_view", ins := [8193], outs := [8203], params := [2048, 1024] }
      8193 8203 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8193 8203)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8204
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8194) :=
    ringAttn_reduce1_pm_opaque pm initPM 400
      { rank := 1, op := "OpName.FW_view", ins := [8194], outs := [8204], params := [2048, 1024] }
      8194 8204 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8194 8204)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 8203 = denoteGraph_ringAttn pm initPM 8193 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8193]
  have h32 : denoteGraph_ringAttn pm initPM 8204 = denoteGraph_ringAttn pm initPM 8194 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8194]
  have hval : denoteGraph_ringAttn sm initSM 4917
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8203, denoteGraph_ringAttn pm initPM 8204] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4916, hval08, hnr, ← h31, ← h32]
  have hs8203 : (denoteGraph_ringAttn pm initPM 8203).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs8204 : (denoteGraph_ringAttn pm initPM 8204).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4917 : (denoteGraph_ringAttn sm initSM 4917).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4917 4917 8203 8204 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4917 hs8203 hs8204

/-- 4918 — 2-tp `FW_float(4917)` (identity, SM node 170, PM nodes 401/402). -/
theorem recon_intermediateGoal_4918_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4918
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs8203, hs8204⟩ := twoTp_gather _ _ intermediateGoal_4917 4917 8203 8204
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4917_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4918 = id (denoteGraph_ringAttn sm initSM 4917) :=
    ringAttn_reduce1_pm_opaque sm initSM 170
      { rank := 0, op := "OpName.FW_float", ins := [4917], outs := [4918] }
      4917 4918 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4917 4918 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8207 = id (denoteGraph_ringAttn pm initPM 8203) :=
    ringAttn_reduce1_pm_opaque pm initPM 401
      { rank := 0, op := "OpName.FW_float", ins := [8203], outs := [8207] }
      8203 8207 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8203 8207 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8208 = id (denoteGraph_ringAttn pm initPM 8204) :=
    ringAttn_reduce1_pm_opaque pm initPM 402
      { rank := 1, op := "OpName.FW_float", ins := [8204], outs := [8208] }
      8204 8208 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8204 8208 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 4918
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8207, denoteGraph_ringAttn pm initPM 8208] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8207).shape = [2048, 1024] := by rw [rP0]; exact hs8203
  have hsp1 : (denoteGraph_ringAttn pm initPM 8208).shape = [2048, 1024] := by rw [rP1]; exact hs8204
  have hshape : (denoteGraph_ringAttn sm initSM 4918).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4918 4918 8207 8208 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7595 — 2-tp `mref2`-second copy of the L2 residual `4898` (SM node 158,
    PM nodes 377/378), carried into the L5 residual add. -/
theorem recon_intermediateGoal_7595_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7595
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs8137, hs8138⟩ := twoTp_gather _ _ intermediateGoal_4898 4898 8137 8138
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4898_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7595 : denoteGraph_ringAttn sm initSM 7595 = id (denoteGraph_ringAttn sm initSM 4898) :=
    ringAttn_reduce1_pm_opaque sm initSM 158
      { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595], params := [2] }
      4898 7595 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4898 7591 7595 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14913 : denoteGraph_ringAttn pm initPM 14913 = id (denoteGraph_ringAttn pm initPM 8137) :=
    ringAttn_reduce1_pm_opaque pm initPM 377
      { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913], params := [2] }
      8137 14913 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8137 14909 14913 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14921 : denoteGraph_ringAttn pm initPM 14921 = id (denoteGraph_ringAttn pm initPM 8138) :=
    ringAttn_reduce1_pm_opaque pm initPM 378
      { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921], params := [2] }
      8138 14921 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8138 14917 14921 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7595 p14913 p14921
  have hsp0 : (denoteGraph_ringAttn pm initPM 14913).shape = [2048, 1024] := by
    rw [p14913]; exact hs8137
  have hsp1 : (denoteGraph_ringAttn pm initPM 14921).shape = [2048, 1024] := by
    rw [p14921]; exact hs8138
  have hval : denoteGraph_ringAttn sm initSM 7595
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14913, denoteGraph_ringAttn pm initPM 14921] := by
    rw [s7595, hbr90, ← p14913, ← p14921]
  have hshape : (denoteGraph_ringAttn sm initSM 7595).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7595 7595 14913 14921 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4919 — 2-tp L5 residual add `7595 + 4918` (SM node 171, PM nodes 403/404). -/
theorem recon_intermediateGoal_4919_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4919
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs14913, hs14921⟩ := twoTp_gather _ _ intermediateGoal_7595 7595 14913 14921
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7595_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs8207, hs8208⟩ := twoTp_gather _ _ intermediateGoal_4918 4918 8207 8208
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4918_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4919
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7595) (denoteGraph_ringAttn sm initSM 4918) :=
    ringAttn_reduce2_pm_opaque sm initSM 171
      { rank := 0, op := "OpName.FW_add", ins := [7595, 4918], outs := [4919] }
      7595 4918 4919 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7595 4918 4919)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8211
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14913) (denoteGraph_ringAttn pm initPM 8207) :=
    ringAttn_reduce2_pm_opaque pm initPM 403
      { rank := 0, op := "OpName.FW_add", ins := [14913, 8207], outs := [8211] }
      14913 8207 8211 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 14913 8207 8211)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8212
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14921) (denoteGraph_ringAttn pm initPM 8208) :=
    ringAttn_reduce2_pm_opaque pm initPM 404
      { rank := 1, op := "OpName.FW_add", ins := [14921, 8208], outs := [8212] }
      14921 8208 8212 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14921 8208 8212)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4919
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8211, denoteGraph_ringAttn pm initPM 8212] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs14913 hs14921 hs8207 hs8208,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8211).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14913 hs8207
  have hsp1 : (denoteGraph_ringAttn pm initPM 8212).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14921 hs8208
  have hshape : (denoteGraph_ringAttn sm initSM 4919).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4919 4919 8211 8212 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4921 — 2-tp RMSNorm of `mref2-first(4919)` with replicated weight
    `4920 : [1024]` (SM node 173, PM nodes 407/408). -/
theorem recon_intermediateGoal_4921_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4921
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8211, hs8212⟩ := twoTp_gather _ _ intermediateGoal_4919 4919 8211 8212
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4919_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7612 : denoteGraph_ringAttn sm initSM 7612 = id (denoteGraph_ringAttn sm initSM 4919) :=
    ringAttn_reduce1_pm_opaque sm initSM 172
      { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616], params := [2] }
      4919 7612 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4919 7612 7616)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14951 : denoteGraph_ringAttn pm initPM 14951 = id (denoteGraph_ringAttn pm initPM 8211) :=
    ringAttn_reduce1_pm_opaque pm initPM 405
      { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955], params := [2] }
      8211 14951 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8211 14951 14955)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14959 : denoteGraph_ringAttn pm initPM 14959 = id (denoteGraph_ringAttn pm initPM 8212) :=
    ringAttn_reduce1_pm_opaque pm initPM 406
      { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963], params := [2] }
      8212 14959 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8212 14959 14963)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7612 p14951 p14959
  have hs14951 : (denoteGraph_ringAttn pm initPM 14951).shape = [2048, 1024] := by
    rw [p14951]; exact hs8211
  have hs14959 : (denoteGraph_ringAttn pm initPM 14959).shape = [2048, 1024] := by
    rw [p14959]; exact hs8212
  have hbr08 : denoteGraph_ringAttn sm initSM 7612
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14951, denoteGraph_ringAttn pm initPM 14959] := by
    rw [s7612, hbr11, ← p14951, ← p14959]
  have hw4920 : denoteGraph_ringAttn sm initSM 4920 = denoteGraph_ringAttn pm initPM 4920 :=
    veq_weight_ring initSM initPM hInit initGoal_4920 (by native_decide) 4920
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4921
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7612) (denoteGraph_ringAttn sm initSM 4920) :=
    ringAttn_reduce2_pm_opaque sm initSM 173
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7612, 4920], outs := [4921] }
      7612 4920 4921 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7612 4920 4921)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8215
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14951) (denoteGraph_ringAttn pm initPM 4920) :=
    ringAttn_reduce2_pm_opaque pm initPM 407
      { rank := 0, op := "OpName.FW_rms_norm", ins := [14951, 4920], outs := [8215] }
      14951 4920 8215 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 14951 4920 8215)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8216
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14959) (denoteGraph_ringAttn pm initPM 4920) :=
    ringAttn_reduce2_pm_opaque pm initPM 408
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14959, 4920], outs := [8216] }
      14959 4920 8216 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14959 4920 8216)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4921
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8215, denoteGraph_ringAttn pm initPM 8216] := by
    rw [rSM, hbr08, hw4920, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs14951 hs14959,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8215).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14951
  have hsp1 : (denoteGraph_ringAttn pm initPM 8216).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14959
  have hshape : (denoteGraph_ringAttn sm initSM 4921).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4921 4921 8215 8216 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4922 — 2-tp `FW_float(mref5-first(4921))` (identity, SM node 175,
    PM nodes 411/415; mref5-first via SM node 174, PM 409/410). -/
theorem recon_intermediateGoal_4922_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4922
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8215, hs8216⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7623 : denoteGraph_ringAttn sm initSM 7623 = id (denoteGraph_ringAttn sm initSM 4921) :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921],
        outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7623 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 4921 7623 [7627, 7631, 7635, 7639])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14970 : denoteGraph_ringAttn pm initPM 14970 = id (denoteGraph_ringAttn pm initPM 8215) :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215],
        outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14970 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 8215 14970 [14974, 14978, 14982, 14986])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14993 : denoteGraph_ringAttn pm initPM 14993 = id (denoteGraph_ringAttn pm initPM 8216) :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216],
        outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 14993 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 8216 14993 [14997, 15001, 15005, 15009])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7623 p14970 p14993
  have hbrm : denoteGraph_ringAttn sm initSM 7623
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14970, denoteGraph_ringAttn pm initPM 14993] := by
    rw [s7623, hbr13, ← p14970, ← p14993]
  have rSM : denoteGraph_ringAttn sm initSM 4922 = id (denoteGraph_ringAttn sm initSM 7623) :=
    ringAttn_reduce1_pm_opaque sm initSM 175
      { rank := 0, op := "OpName.FW_float", ins := [7623], outs := [4922] }
      7623 4922 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7623 4922 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8217 = id (denoteGraph_ringAttn pm initPM 14970) :=
    ringAttn_reduce1_pm_opaque pm initPM 411
      { rank := 0, op := "OpName.FW_float", ins := [14970], outs := [8217] }
      14970 8217 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 14970 8217 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8218 = id (denoteGraph_ringAttn pm initPM 14993) :=
    ringAttn_reduce1_pm_opaque pm initPM 415
      { rank := 1, op := "OpName.FW_float", ins := [14993], outs := [8218] }
      14993 8218 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 14993 8218 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs14970 : (denoteGraph_ringAttn pm initPM 14970).shape = [2048, 1024] := by
    rw [p14970]; exact hs8215
  have hs14993 : (denoteGraph_ringAttn pm initPM 14993).shape = [2048, 1024] := by
    rw [p14993]; exact hs8216
  have hval : denoteGraph_ringAttn sm initSM 4922
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8217, denoteGraph_ringAttn pm initPM 8218] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8217).shape = [2048, 1024] := by
    rw [rP0]; exact hs14970
  have hsp1 : (denoteGraph_ringAttn pm initPM 8218).shape = [2048, 1024] := by
    rw [rP1]; exact hs14993
  have hshape : (denoteGraph_ringAttn sm initSM 4922).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4922 4922 8217 8218 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4924 — 2-tp router logits `fw_norm_linear(4922, 4923)` with weight
    `4923 : [64, 1024]` → `[4096, 64]` (SM node 179, PM nodes 419/423). -/
theorem recon_intermediateGoal_4924_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4924
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs8217, hs8218⟩ := twoTp_gather _ _ intermediateGoal_4922 4922 8217 8218
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4922_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4923 : denoteGraph_ringAttn sm initSM 4923 = denoteGraph_ringAttn pm initPM 4923 :=
    veq_weight_ring initSM initPM hInit initGoal_4923 (by native_decide) 4923
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4923 : (denoteGraph_ringAttn sm initSM 4923).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4923 (by native_decide) 4923 [64, 1024]
      rfl rfl (by native_decide)
  have hpw4923 : (denoteGraph_ringAttn pm initPM 4923).shape = [64, 1024] := by
    rw [← hw4923]; exact hsw4923
  have rSM : denoteGraph_ringAttn sm initSM 4924
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 4922) (denoteGraph_ringAttn sm initSM 4923) :=
    ringAttn_reduce2_pm_opaque sm initSM 179
      { rank := 0, op := "OpName.FW_norm_linear", ins := [4922, 4923], outs := [4924] }
      4922 4923 4924 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 4922 4923 4924)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8223
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8217) (denoteGraph_ringAttn pm initPM 4923) :=
    ringAttn_reduce2_pm_opaque pm initPM 419
      { rank := 0, op := "OpName.FW_norm_linear", ins := [8217, 4923], outs := [8223] }
      8217 4923 8223 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 8217 4923 8223)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8224
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 8218) (denoteGraph_ringAttn pm initPM 4923) :=
    ringAttn_reduce2_pm_opaque pm initPM 423
      { rank := 1, op := "OpName.FW_norm_linear", ins := [8218, 4923], outs := [8224] }
      8218 4923 8224 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 8218 4923 8224)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4924
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8223, denoteGraph_ringAttn pm initPM 8224] := by
    rw [rSM, hval14, hw4923, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs8217 hs8218 hpw4923,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8223).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8217 hpw4923
  have hsp1 : (denoteGraph_ringAttn pm initPM 8224).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs8218 hpw4923
  have hshape : (denoteGraph_ringAttn sm initSM 4924).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4924 4924 8223 8224 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L5 top-k routing (`4925`/`4926`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`8223`/`8224`) directly. -/

/-- Shared L5 top-k core: `4924` (full logits) is the dim-0 gather of the two
    per-rank shards `8223`/`8224`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L5 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 4924
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 8223, denoteGraph_ringAttn pm initPM 8224]
      ∧ (denoteGraph_ringAttn sm initSM 4924).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8223).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 8224).shape = [2048, 64]
      ∧ ((sm.nodes.take 183).foldl (applyNodeRingAttn sm) initSM 4924).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 427).foldl (applyNodeRingAttn pm) initPM 8223).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 431).foldl (applyNodeRingAttn pm) initPM 8224).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs8223, hs8224⟩ := twoTp_gather _ _ intermediateGoal_4924 4924 8223 8224
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4924_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs4924sm : (denoteGraph_ringAttn sm initSM 4924).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs8223])]
    simp [List.set, List.getD]
  have hpre4924sm : denoteGraph_ringAttn sm initSM 4924
      = (sm.nodes.take 183).foldl (applyNodeRingAttn sm) initSM 4924 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 4924 183 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 183).foldl (applyNodeRingAttn sm) initSM 4924).shape.reverse.head? = some 64 := by
    rw [← hpre4924sm, hs4924sm]; rfl
  have hpre8223 : denoteGraph_ringAttn pm initPM 8223
      = (pm.nodes.take 427).foldl (applyNodeRingAttn pm) initPM 8223 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8223 427 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 427).foldl (applyNodeRingAttn pm) initPM 8223).shape.reverse.head? = some 64 := by
    rw [← hpre8223, hs8223]; rfl
  have hpre8224 : denoteGraph_ringAttn pm initPM 8224
      = (pm.nodes.take 431).foldl (applyNodeRingAttn pm) initPM 8224 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 8224 431 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 431).foldl (applyNodeRingAttn pm) initPM 8224).shape.reverse.head? = some 64 := by
    rw [← hpre8224, hs8224]; rfl
  exact ⟨hbr16, hs4924sm, hs8223, hs8224, hlastSM, hlast271, hlast275⟩

/-- 4925 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4925_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4925
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4924sm, hs8223, hs8224, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L5 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4925
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4924) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 183
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4924], outs := [4925, 4926, 4927], params := [8, 1] }
      4924 4925 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 183).foldl (applyNodeRingAttn sm) initSM) 0 4924 4925 4926 4927 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8225
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8223) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 427
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8223], outs := [8225, 8227, 8229], params := [8, 1] }
      8223 8225 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 427).foldl (applyNodeRingAttn pm) initPM) 0 8223 8225 8227 8229 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8226
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8224) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 431
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8224], outs := [8226, 8228, 8230], params := [8, 1] }
      8224 8226 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 431).foldl (applyNodeRingAttn pm) initPM) 1 8224 8226 8228 8230 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4925
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8225, denoteGraph_ringAttn pm initPM 8226] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8223 hs8224,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4925).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs4924sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8225).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8223]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8226).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs8224]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4925 4925 8225 8226 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4926 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4926_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4926
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4924sm, hs8223, hs8224, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L5 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4926
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4924) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 183
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4924], outs := [4925, 4926, 4927], params := [8, 1] }
      4924 4926 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 183).foldl (applyNodeRingAttn sm) initSM) 0 4924 4925 4926 4927 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8227
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8223) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 427
      { rank := 0, op := "OpName.FW_topk_routing", ins := [8223], outs := [8225, 8227, 8229], params := [8, 1] }
      8223 8227 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 427).foldl (applyNodeRingAttn pm) initPM) 0 8223 8225 8227 8229 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8228
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 8224) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 431
      { rank := 1, op := "OpName.FW_topk_routing", ins := [8224], outs := [8226, 8228, 8230], params := [8, 1] }
      8224 8228 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 431).foldl (applyNodeRingAttn pm) initPM) 1 8224 8226 8228 8230 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4926
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8227, denoteGraph_ringAttn pm initPM 8228] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs8223 hs8224,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4926).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs4924sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 8227).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8223]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8228).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs8224]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4926 4926 8227 8228 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L5 router expert branches — reshape (`4931`/`4936`/`4940`) of the
    `mref5` copies (positions 2/3/4) of `4921`, all identity 2-tp views. -/

/-- 4931 — 2-tp identity reshape of `mref5-pos2(4921)` (SM node 176, PM 412/416). -/
theorem recon_intermediateGoal_4931_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4931
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8215, hs8216⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4921sm : (denoteGraph_ringAttn sm initSM 4921).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8215])]
    simp [List.set, List.getD]
  have s7631 : denoteGraph_ringAttn sm initSM 7631 = id (denoteGraph_ringAttn sm initSM 4921) :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921],
        outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7631 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14978 : denoteGraph_ringAttn pm initPM 14978 = id (denoteGraph_ringAttn pm initPM 8215) :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215],
        outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14978 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15001 : denoteGraph_ringAttn pm initPM 15001 = id (denoteGraph_ringAttn pm initPM 8216) :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216],
        outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 15001 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7631 p14978 p15001
  have hs7631 : (denoteGraph_ringAttn sm initSM 7631).shape = [4096, 1024] := by rw [s7631]; exact hs4921sm
  have hs14978 : (denoteGraph_ringAttn pm initPM 14978).shape = [2048, 1024] := by rw [p14978]; exact hs8215
  have hs15001 : (denoteGraph_ringAttn pm initPM 15001).shape = [2048, 1024] := by rw [p15001]; exact hs8216
  have hbrm : denoteGraph_ringAttn sm initSM 7631
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14978, denoteGraph_ringAttn pm initPM 15001] := by
    rw [s7631, hbr13, ← p14978, ← p15001]
  have rSM : denoteGraph_ringAttn sm initSM 4931
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7631) :=
    ringAttn_reduce1_pm_opaque sm initSM 176
      { rank := 0, op := "OpName.FW_reshape", ins := [7631], outs := [4931], params := [4096, 1024] }
      7631 4931 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7631 4931)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8237
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14978) :=
    ringAttn_reduce1_pm_opaque pm initPM 412
      { rank := 0, op := "OpName.FW_reshape", ins := [14978], outs := [8237], params := [2048, 1024] }
      14978 8237 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14978 8237)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8238
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15001) :=
    ringAttn_reduce1_pm_opaque pm initPM 416
      { rank := 1, op := "OpName.FW_reshape", ins := [15001], outs := [8238], params := [2048, 1024] }
      15001 8238 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15001 8238)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 8237 = denoteGraph_ringAttn pm initPM 14978 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14978]
  have h66 : denoteGraph_ringAttn pm initPM 8238 = denoteGraph_ringAttn pm initPM 15001 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15001]
  have hval : denoteGraph_ringAttn sm initSM 4931
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8237, denoteGraph_ringAttn pm initPM 8238] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7631, hbrm, hnr, ← h65, ← h66]
  have hs8237 : (denoteGraph_ringAttn pm initPM 8237).shape = [2048, 1024] := by rw [h65]; exact hs14978
  have hs8238 : (denoteGraph_ringAttn pm initPM 8238).shape = [2048, 1024] := by rw [h66]; exact hs15001
  have hs4931 : (denoteGraph_ringAttn sm initSM 4931).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7631]; exact hs7631
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4931 4931 8237 8238 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4931 hs8237 hs8238

/-- 4936 — 2-tp identity reshape of `mref5-pos3(4921)` (SM node 177, PM 413/417). -/
theorem recon_intermediateGoal_4936_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4936
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8215, hs8216⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4921sm : (denoteGraph_ringAttn sm initSM 4921).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8215])]
    simp [List.set, List.getD]
  have s7635 : denoteGraph_ringAttn sm initSM 7635 = id (denoteGraph_ringAttn sm initSM 4921) :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921],
        outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7635 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14982 : denoteGraph_ringAttn pm initPM 14982 = id (denoteGraph_ringAttn pm initPM 8215) :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215],
        outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14982 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15005 : denoteGraph_ringAttn pm initPM 15005 = id (denoteGraph_ringAttn pm initPM 8216) :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216],
        outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 15005 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7635 p14982 p15005
  have hs7635 : (denoteGraph_ringAttn sm initSM 7635).shape = [4096, 1024] := by rw [s7635]; exact hs4921sm
  have hs14982 : (denoteGraph_ringAttn pm initPM 14982).shape = [2048, 1024] := by rw [p14982]; exact hs8215
  have hs15005 : (denoteGraph_ringAttn pm initPM 15005).shape = [2048, 1024] := by rw [p15005]; exact hs8216
  have hbrm : denoteGraph_ringAttn sm initSM 7635
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14982, denoteGraph_ringAttn pm initPM 15005] := by
    rw [s7635, hbr13, ← p14982, ← p15005]
  have rSM : denoteGraph_ringAttn sm initSM 4936
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7635) :=
    ringAttn_reduce1_pm_opaque sm initSM 177
      { rank := 0, op := "OpName.FW_reshape", ins := [7635], outs := [4936], params := [4096, 1024] }
      7635 4936 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7635 4936)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8251
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14982) :=
    ringAttn_reduce1_pm_opaque pm initPM 413
      { rank := 0, op := "OpName.FW_reshape", ins := [14982], outs := [8251], params := [2048, 1024] }
      14982 8251 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14982 8251)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8252
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15005) :=
    ringAttn_reduce1_pm_opaque pm initPM 417
      { rank := 1, op := "OpName.FW_reshape", ins := [15005], outs := [8252], params := [2048, 1024] }
      15005 8252 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15005 8252)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 8251 = denoteGraph_ringAttn pm initPM 14982 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14982]
  have h80 : denoteGraph_ringAttn pm initPM 8252 = denoteGraph_ringAttn pm initPM 15005 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15005]
  have hval : denoteGraph_ringAttn sm initSM 4936
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8251, denoteGraph_ringAttn pm initPM 8252] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7635, hbrm, hnr, ← h79, ← h80]
  have hs8251 : (denoteGraph_ringAttn pm initPM 8251).shape = [2048, 1024] := by rw [h79]; exact hs14982
  have hs8252 : (denoteGraph_ringAttn pm initPM 8252).shape = [2048, 1024] := by rw [h80]; exact hs15005
  have hs4936 : (denoteGraph_ringAttn sm initSM 4936).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7635]; exact hs7635
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4936 4936 8251 8252 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4936 hs8251 hs8252

/-- 4940 — 2-tp identity reshape of `mref5-pos4(4921)` (SM node 178, PM 414/418). -/
theorem recon_intermediateGoal_4940_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4940
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs8215, hs8216⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4921sm : (denoteGraph_ringAttn sm initSM 4921).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8215])]
    simp [List.set, List.getD]
  have s7639 : denoteGraph_ringAttn sm initSM 7639 = id (denoteGraph_ringAttn sm initSM 4921) :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921],
        outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7639 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14986 : denoteGraph_ringAttn pm initPM 14986 = id (denoteGraph_ringAttn pm initPM 8215) :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215],
        outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14986 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15009 : denoteGraph_ringAttn pm initPM 15009 = id (denoteGraph_ringAttn pm initPM 8216) :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216],
        outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 15009 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7639 p14986 p15009
  have hs7639 : (denoteGraph_ringAttn sm initSM 7639).shape = [4096, 1024] := by rw [s7639]; exact hs4921sm
  have hs14986 : (denoteGraph_ringAttn pm initPM 14986).shape = [2048, 1024] := by rw [p14986]; exact hs8215
  have hs15009 : (denoteGraph_ringAttn pm initPM 15009).shape = [2048, 1024] := by rw [p15009]; exact hs8216
  have hbrm : denoteGraph_ringAttn sm initSM 7639
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14986, denoteGraph_ringAttn pm initPM 15009] := by
    rw [s7639, hbr13, ← p14986, ← p15009]
  have rSM : denoteGraph_ringAttn sm initSM 4940
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7639) :=
    ringAttn_reduce1_pm_opaque sm initSM 178
      { rank := 0, op := "OpName.FW_reshape", ins := [7639], outs := [4940], params := [4096, 1024] }
      7639 4940 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7639 4940)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8269
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14986) :=
    ringAttn_reduce1_pm_opaque pm initPM 414
      { rank := 0, op := "OpName.FW_reshape", ins := [14986], outs := [8269], params := [2048, 1024] }
      14986 8269 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14986 8269)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8270
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15009) :=
    ringAttn_reduce1_pm_opaque pm initPM 418
      { rank := 1, op := "OpName.FW_reshape", ins := [15009], outs := [8270], params := [2048, 1024] }
      15009 8270 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15009 8270)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 8269 = denoteGraph_ringAttn pm initPM 14986 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14986]
  have h98 : denoteGraph_ringAttn pm initPM 8270 = denoteGraph_ringAttn pm initPM 15009 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15009]
  have hval : denoteGraph_ringAttn sm initSM 4940
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8269, denoteGraph_ringAttn pm initPM 8270] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7639, hbrm, hnr, ← h97, ← h98]
  have hs8269 : (denoteGraph_ringAttn pm initPM 8269).shape = [2048, 1024] := by rw [h97]; exact hs14986
  have hs8270 : (denoteGraph_ringAttn pm initPM 8270).shape = [2048, 1024] := by rw [h98]; exact hs15009
  have hs4940 : (denoteGraph_ringAttn sm initSM 4940).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7639]; exact hs7639
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4940 4940 8269 8270 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4940 hs8269 hs8270

/-! ### L5 router expert mixlins (`4933`/`4938`/`4942`), 2-tp. -/

/-- 4933 — 2-tp `fw_linear(4931, 4932)`, weight `4932 : [1, 1024]` → `[4096, 1]`
    (SM node 180, PM nodes 420/424). -/
theorem recon_intermediateGoal_4933_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4933
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs8237, hs8238⟩ := twoTp_gather _ _ intermediateGoal_4931 4931 8237 8238
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4931_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4932 : denoteGraph_ringAttn sm initSM 4932 = denoteGraph_ringAttn pm initPM 4932 :=
    veq_weight_ring initSM initPM hInit initGoal_4932 (by native_decide) 4932
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4932 : (denoteGraph_ringAttn pm initPM 4932).shape = [1, 1024] := by
    rw [← hw4932]
    exact shape_weight_ring initSM initPM hInit initGoal_4932 (by native_decide) 4932 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4933
      = fw_linear (denoteGraph_ringAttn sm initSM 4931) (denoteGraph_ringAttn sm initSM 4932) :=
    ringAttn_reduce2_pm_opaque sm initSM 180
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4931, 4932], outs := [4933] }
      4931 4932 4933 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4931 4932 4933)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8241
      = fw_linear (denoteGraph_ringAttn pm initPM 8237) (denoteGraph_ringAttn pm initPM 4932) :=
    ringAttn_reduce2_pm_opaque pm initPM 420
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8237, 4932], outs := [8241] }
      8237 4932 8241 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8237 4932 8241)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8242
      = fw_linear (denoteGraph_ringAttn pm initPM 8238) (denoteGraph_ringAttn pm initPM 4932) :=
    ringAttn_reduce2_pm_opaque pm initPM 424
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8238, 4932], outs := [8242] }
      8238 4932 8242 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8238 4932 8242)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4933
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8241, denoteGraph_ringAttn pm initPM 8242] := by
    rw [rSM, hval23, hw4932, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs8237 hs8238 hpw4932,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8241).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8237 hpw4932
  have hsp1 : (denoteGraph_ringAttn pm initPM 8242).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs8238 hpw4932
  have hshape : (denoteGraph_ringAttn sm initSM 4933).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4933 4933 8241 8242 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4938 — 2-tp `fw_linear(4936, 4937)`, weight `4937 : [512, 1024]` → `[4096, 512]`
    (SM node 181, PM nodes 421/425). -/
theorem recon_intermediateGoal_4938_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4938
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs8251, hs8252⟩ := twoTp_gather _ _ intermediateGoal_4936 4936 8251 8252
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4936_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4937 : denoteGraph_ringAttn sm initSM 4937 = denoteGraph_ringAttn pm initPM 4937 :=
    veq_weight_ring initSM initPM hInit initGoal_4937 (by native_decide) 4937
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4937 : (denoteGraph_ringAttn pm initPM 4937).shape = [512, 1024] := by
    rw [← hw4937]
    exact shape_weight_ring initSM initPM hInit initGoal_4937 (by native_decide) 4937 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4938
      = fw_linear (denoteGraph_ringAttn sm initSM 4936) (denoteGraph_ringAttn sm initSM 4937) :=
    ringAttn_reduce2_pm_opaque sm initSM 181
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4936, 4937], outs := [4938] }
      4936 4937 4938 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4936 4937 4938)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8255
      = fw_linear (denoteGraph_ringAttn pm initPM 8251) (denoteGraph_ringAttn pm initPM 4937) :=
    ringAttn_reduce2_pm_opaque pm initPM 421
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8251, 4937], outs := [8255] }
      8251 4937 8255 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8251 4937 8255)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8256
      = fw_linear (denoteGraph_ringAttn pm initPM 8252) (denoteGraph_ringAttn pm initPM 4937) :=
    ringAttn_reduce2_pm_opaque pm initPM 425
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8252, 4937], outs := [8256] }
      8252 4937 8256 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8252 4937 8256)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4938
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8255, denoteGraph_ringAttn pm initPM 8256] := by
    rw [rSM, hval28, hw4937, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8251 hs8252 hpw4937,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8255).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8251 hpw4937
  have hsp1 : (denoteGraph_ringAttn pm initPM 8256).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8252 hpw4937
  have hshape : (denoteGraph_ringAttn sm initSM 4938).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4938 4938 8255 8256 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4942 — 2-tp `fw_linear(4940, 4941)`, weight `4941 : [512, 1024]` → `[4096, 512]`
    (SM node 182, PM nodes 422/426). -/
theorem recon_intermediateGoal_4942_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4942
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs8269, hs8270⟩ := twoTp_gather _ _ intermediateGoal_4940 4940 8269 8270
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4940_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4941 : denoteGraph_ringAttn sm initSM 4941 = denoteGraph_ringAttn pm initPM 4941 :=
    veq_weight_ring initSM initPM hInit initGoal_4941 (by native_decide) 4941
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4941 : (denoteGraph_ringAttn pm initPM 4941).shape = [512, 1024] := by
    rw [← hw4941]
    exact shape_weight_ring initSM initPM hInit initGoal_4941 (by native_decide) 4941 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4942
      = fw_linear (denoteGraph_ringAttn sm initSM 4940) (denoteGraph_ringAttn sm initSM 4941) :=
    ringAttn_reduce2_pm_opaque sm initSM 182
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4940, 4941], outs := [4942] }
      4940 4941 4942 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4940 4941 4942)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8273
      = fw_linear (denoteGraph_ringAttn pm initPM 8269) (denoteGraph_ringAttn pm initPM 4941) :=
    ringAttn_reduce2_pm_opaque pm initPM 422
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8269, 4941], outs := [8273] }
      8269 4941 8273 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8269 4941 8273)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8274
      = fw_linear (denoteGraph_ringAttn pm initPM 8270) (denoteGraph_ringAttn pm initPM 4941) :=
    ringAttn_reduce2_pm_opaque pm initPM 426
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8270, 4941], outs := [8274] }
      8270 4941 8274 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8270 4941 8274)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4942
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8273, denoteGraph_ringAttn pm initPM 8274] := by
    rw [rSM, hval32, hw4941, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs8269 hs8270 hpw4941,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8273).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8269 hpw4941
  have hsp1 : (denoteGraph_ringAttn pm initPM 8274).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs8270 hpw4941
  have hshape : (denoteGraph_ringAttn sm initSM 4942).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4942 4942 8273 8274 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L5 router expert views (`4934`/`4939`/`4943`), identity 2-tp views. -/

/-- 4934 — 2-tp identity view of `4933` → `[4096, 1]` (SM node 184, PM 428/432). -/
theorem recon_intermediateGoal_4934_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4934
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs8241, hs8242⟩ := twoTp_gather _ _ intermediateGoal_4933 4933 8241 8242
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4933_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4933 : (denoteGraph_ringAttn sm initSM 4933).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8241])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4934
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 4933) :=
    ringAttn_reduce1_pm_opaque sm initSM 184
      { rank := 0, op := "OpName.FW_view", ins := [4933], outs := [4934], params := [4096, 1] }
      4933 4934 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 4933 4934)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8247
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8241) :=
    ringAttn_reduce1_pm_opaque pm initPM 428
      { rank := 0, op := "OpName.FW_view", ins := [8241], outs := [8247], params := [2048, 1] }
      8241 8247 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 8241 8247)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8248
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 8242) :=
    ringAttn_reduce1_pm_opaque pm initPM 432
      { rank := 1, op := "OpName.FW_view", ins := [8242], outs := [8248], params := [2048, 1] }
      8242 8248 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 8242 8248)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 8247 = denoteGraph_ringAttn pm initPM 8241 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs8241]
  have h76 : denoteGraph_ringAttn pm initPM 8248 = denoteGraph_ringAttn pm initPM 8242 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs8242]
  have hval : denoteGraph_ringAttn sm initSM 4934
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8247, denoteGraph_ringAttn pm initPM 8248] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4933, hval25, hnr, ← h75, ← h76]
  have hs8247 : (denoteGraph_ringAttn pm initPM 8247).shape = [2048, 1] := by rw [h75]; exact hs8241
  have hs8248 : (denoteGraph_ringAttn pm initPM 8248).shape = [2048, 1] := by rw [h76]; exact hs8242
  have hs4934 : (denoteGraph_ringAttn sm initSM 4934).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4933]; exact hs4933
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4934 4934 8247 8248 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4934 hs8247 hs8248

/-- 4939 — 2-tp identity view of `4938` → `[4096, 512]` (SM node 185, PM 429/433). -/
theorem recon_intermediateGoal_4939_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4939
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs8255, hs8256⟩ := twoTp_gather _ _ intermediateGoal_4938 4938 8255 8256
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4938_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4938 : (denoteGraph_ringAttn sm initSM 4938).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8255])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4939
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4938) :=
    ringAttn_reduce1_pm_opaque sm initSM 185
      { rank := 0, op := "OpName.FW_view", ins := [4938], outs := [4939], params := [4096, 512] }
      4938 4939 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4938 4939)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8265
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8255) :=
    ringAttn_reduce1_pm_opaque pm initPM 429
      { rank := 0, op := "OpName.FW_view", ins := [8255], outs := [8265], params := [2048, 512] }
      8255 8265 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8255 8265)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8266
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8256) :=
    ringAttn_reduce1_pm_opaque pm initPM 433
      { rank := 1, op := "OpName.FW_view", ins := [8256], outs := [8266], params := [2048, 512] }
      8256 8266 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8256 8266)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 8265 = denoteGraph_ringAttn pm initPM 8255 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8255]
  have h94 : denoteGraph_ringAttn pm initPM 8266 = denoteGraph_ringAttn pm initPM 8256 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8256]
  have hval : denoteGraph_ringAttn sm initSM 4939
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8265, denoteGraph_ringAttn pm initPM 8266] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4938, hval30, hnr, ← h93, ← h94]
  have hs8265 : (denoteGraph_ringAttn pm initPM 8265).shape = [2048, 512] := by rw [h93]; exact hs8255
  have hs8266 : (denoteGraph_ringAttn pm initPM 8266).shape = [2048, 512] := by rw [h94]; exact hs8256
  have hs4939 : (denoteGraph_ringAttn sm initSM 4939).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4938]; exact hs4938
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4939 4939 8265 8266 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4939 hs8265 hs8266

/-- 4943 — 2-tp identity view of `4942` → `[4096, 512]` (SM node 186, PM 430/434). -/
theorem recon_intermediateGoal_4943_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4943
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs8273, hs8274⟩ := twoTp_gather _ _ intermediateGoal_4942 4942 8273 8274
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4942_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4942 : (denoteGraph_ringAttn sm initSM 4942).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8273])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4943
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4942) :=
    ringAttn_reduce1_pm_opaque sm initSM 186
      { rank := 0, op := "OpName.FW_view", ins := [4942], outs := [4943], params := [4096, 512] }
      4942 4943 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4942 4943)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8283
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8273) :=
    ringAttn_reduce1_pm_opaque pm initPM 430
      { rank := 0, op := "OpName.FW_view", ins := [8273], outs := [8283], params := [2048, 512] }
      8273 8283 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8273 8283)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8284
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8274) :=
    ringAttn_reduce1_pm_opaque pm initPM 434
      { rank := 1, op := "OpName.FW_view", ins := [8274], outs := [8284], params := [2048, 512] }
      8274 8284 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8274 8284)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 8283 = denoteGraph_ringAttn pm initPM 8273 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8273]
  have h12 : denoteGraph_ringAttn pm initPM 8284 = denoteGraph_ringAttn pm initPM 8274 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8274]
  have hval : denoteGraph_ringAttn sm initSM 4943
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8283, denoteGraph_ringAttn pm initPM 8284] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4942, hval34, hnr, ← h11, ← h12]
  have hs8283 : (denoteGraph_ringAttn pm initPM 8283).shape = [2048, 512] := by rw [h11]; exact hs8273
  have hs8284 : (denoteGraph_ringAttn pm initPM 8284).shape = [2048, 512] := by rw [h12]; exact hs8274
  have hs4943 : (denoteGraph_ringAttn sm initSM 4943).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4942]; exact hs4942
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4943 4943 8283 8284 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4943 hs8283 hs8284

/-! ### L5 MoE gate/expert branch (`4935` sigmoid, `4944` swiglu, `4945` reshape,
    `4947` mixlin, `4948` view, `4949` broadcast-mul), all 2-tp shard-direct. -/

/-- 4935 — 2-tp `fw_sigmoid(4934)` → `[4096, 1]` (SM node 188, PM 436/439). -/
theorem recon_intermediateGoal_4935_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4935
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs8247, hs8248⟩ := twoTp_gather _ _ intermediateGoal_4934 4934 8247 8248
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4934_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4935 = fw_sigmoid (denoteGraph_ringAttn sm initSM 4934) :=
    ringAttn_reduce1_pm_opaque sm initSM 188
      { rank := 0, op := "OpName.FW_sigmoid", ins := [4934], outs := [4935] }
      4934 4935 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 4934 4935 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8249 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8247) :=
    ringAttn_reduce1_pm_opaque pm initPM 436
      { rank := 0, op := "OpName.FW_sigmoid", ins := [8247], outs := [8249] }
      8247 8249 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 8247 8249 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8250 = fw_sigmoid (denoteGraph_ringAttn pm initPM 8248) :=
    ringAttn_reduce1_pm_opaque pm initPM 439
      { rank := 1, op := "OpName.FW_sigmoid", ins := [8248], outs := [8250] }
      8248 8250 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 8248 8250 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4935
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8249, denoteGraph_ringAttn pm initPM 8250] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs8247 hs8248, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4935).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs8247])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8249).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs8247
  have hsp1 : (denoteGraph_ringAttn pm initPM 8250).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs8248
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4935 4935 8249 8250 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4944 — 2-tp `fw_swiglu(4939, 4943)` → `[4096, 512]` (SM node 189, PM 437/440). -/
theorem recon_intermediateGoal_4944_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4944
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs8265, hs8266⟩ := twoTp_gather _ _ intermediateGoal_4939 4939 8265 8266
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4939_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs8283, hs8284⟩ := twoTp_gather _ _ intermediateGoal_4943 4943 8283 8284
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4943_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4944
      = fw_swiglu (denoteGraph_ringAttn sm initSM 4939) (denoteGraph_ringAttn sm initSM 4943) :=
    ringAttn_reduce2_pm_opaque sm initSM 189
      { rank := 0, op := "OpName.FW_swiglu", ins := [4939, 4943], outs := [4944] }
      4939 4943 4944 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 4939 4943 4944 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8287
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8265) (denoteGraph_ringAttn pm initPM 8283) :=
    ringAttn_reduce2_pm_opaque pm initPM 437
      { rank := 0, op := "OpName.FW_swiglu", ins := [8265, 8283], outs := [8287] }
      8265 8283 8287 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 8265 8283 8287 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8288
      = fw_swiglu (denoteGraph_ringAttn pm initPM 8266) (denoteGraph_ringAttn pm initPM 8284) :=
    ringAttn_reduce2_pm_opaque pm initPM 440
      { rank := 1, op := "OpName.FW_swiglu", ins := [8266, 8284], outs := [8288] }
      8266 8284 8288 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 8266 8284 8288 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4944
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8287, denoteGraph_ringAttn pm initPM 8288] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs8265 hs8266 hs8283 hs8284,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4944).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8283])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8287).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8283
  have hsp1 : (denoteGraph_ringAttn pm initPM 8288).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs8284
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4944 4944 8287 8288 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4945 — 2-tp identity reshape of `4944` → `[4096, 512]` (SM node 190, PM 441/442). -/
theorem recon_intermediateGoal_4945_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4945
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs8287, hs8288⟩ := twoTp_gather _ _ intermediateGoal_4944 4944 8287 8288
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4944_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4944 : (denoteGraph_ringAttn sm initSM 4944).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs8287])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4945
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4944) :=
    ringAttn_reduce1_pm_opaque sm initSM 190
      { rank := 0, op := "OpName.FW_reshape", ins := [4944], outs := [4945], params := [4096, 512] }
      4944 4945 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4944 4945)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8289
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8287) :=
    ringAttn_reduce1_pm_opaque pm initPM 441
      { rank := 0, op := "OpName.FW_reshape", ins := [8287], outs := [8289], params := [2048, 512] }
      8287 8289 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 8287 8289)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8290
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 8288) :=
    ringAttn_reduce1_pm_opaque pm initPM 442
      { rank := 1, op := "OpName.FW_reshape", ins := [8288], outs := [8290], params := [2048, 512] }
      8288 8290 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 8288 8290)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 8289 = denoteGraph_ringAttn pm initPM 8287 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs8287]
  have h18 : denoteGraph_ringAttn pm initPM 8290 = denoteGraph_ringAttn pm initPM 8288 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs8288]
  have hval : denoteGraph_ringAttn sm initSM 4945
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8289, denoteGraph_ringAttn pm initPM 8290] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4944, hval36, hnr, ← h17, ← h18]
  have hs8289 : (denoteGraph_ringAttn pm initPM 8289).shape = [2048, 512] := by rw [h17]; exact hs8287
  have hs8290 : (denoteGraph_ringAttn pm initPM 8290).shape = [2048, 512] := by rw [h18]; exact hs8288
  have hs4945 : (denoteGraph_ringAttn sm initSM 4945).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4944]; exact hs4944
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4945 4945 8289 8290 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4945 hs8289 hs8290

/-- 4947 — 2-tp `fw_linear(4945, 4946)`, weight `4946 : [1024, 512]` → `[4096, 1024]`
    (SM node 191, PM 443/444). -/
theorem recon_intermediateGoal_4947_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4947
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs8289, hs8290⟩ := twoTp_gather _ _ intermediateGoal_4945 4945 8289 8290
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4945_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4946 : denoteGraph_ringAttn sm initSM 4946 = denoteGraph_ringAttn pm initPM 4946 :=
    veq_weight_ring initSM initPM hInit initGoal_4946 (by native_decide) 4946
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4946 : (denoteGraph_ringAttn pm initPM 4946).shape = [1024, 512] := by
    rw [← hw4946]
    exact shape_weight_ring initSM initPM hInit initGoal_4946 (by native_decide) 4946 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4947
      = fw_linear (denoteGraph_ringAttn sm initSM 4945) (denoteGraph_ringAttn sm initSM 4946) :=
    ringAttn_reduce2_pm_opaque sm initSM 191
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4945, 4946], outs := [4947] }
      4945 4946 4947 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4945 4946 4947)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8295
      = fw_linear (denoteGraph_ringAttn pm initPM 8289) (denoteGraph_ringAttn pm initPM 4946) :=
    ringAttn_reduce2_pm_opaque pm initPM 443
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8289, 4946], outs := [8295] }
      8289 4946 8295 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 8289 4946 8295)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8296
      = fw_linear (denoteGraph_ringAttn pm initPM 8290) (denoteGraph_ringAttn pm initPM 4946) :=
    ringAttn_reduce2_pm_opaque pm initPM 444
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8290, 4946], outs := [8296] }
      8290 4946 8296 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 8290 4946 8296)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4947
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8295, denoteGraph_ringAttn pm initPM 8296] := by
    rw [rSM, hval37, hw4946, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs8289 hs8290 hpw4946,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8295).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8289 hpw4946
  have hsp1 : (denoteGraph_ringAttn pm initPM 8296).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs8290 hpw4946
  have hshape : (denoteGraph_ringAttn sm initSM 4947).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4947 4947 8295 8296 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4948 — 2-tp identity view of `4947` → `[4096, 1024]` (SM node 192, PM 445/446). -/
theorem recon_intermediateGoal_4948_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4948
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs8295, hs8296⟩ := twoTp_gather _ _ intermediateGoal_4947 4947 8295 8296
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4947_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4947 : (denoteGraph_ringAttn sm initSM 4947).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs8295])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4948
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4947) :=
    ringAttn_reduce1_pm_opaque sm initSM 192
      { rank := 0, op := "OpName.FW_view", ins := [4947], outs := [4948], params := [4096, 1024] }
      4947 4948 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4947 4948)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8305
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8295) :=
    ringAttn_reduce1_pm_opaque pm initPM 445
      { rank := 0, op := "OpName.FW_view", ins := [8295], outs := [8305], params := [2048, 1024] }
      8295 8305 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 8295 8305)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8306
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 8296) :=
    ringAttn_reduce1_pm_opaque pm initPM 446
      { rank := 1, op := "OpName.FW_view", ins := [8296], outs := [8306], params := [2048, 1024] }
      8296 8306 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 8296 8306)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 8305 = denoteGraph_ringAttn pm initPM 8295 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs8295]
  have h34 : denoteGraph_ringAttn pm initPM 8306 = denoteGraph_ringAttn pm initPM 8296 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs8296]
  have hval : denoteGraph_ringAttn sm initSM 4948
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8305, denoteGraph_ringAttn pm initPM 8306] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4947, hval39, hnr, ← h33, ← h34]
  have hs8305 : (denoteGraph_ringAttn pm initPM 8305).shape = [2048, 1024] := by rw [h33]; exact hs8295
  have hs8306 : (denoteGraph_ringAttn pm initPM 8306).shape = [2048, 1024] := by rw [h34]; exact hs8296
  have hs4948 : (denoteGraph_ringAttn sm initSM 4948).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4947]; exact hs4947
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4948 4948 8305 8306 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4948 hs8305 hs8306

/-- 4949 — 2-tp broadcast `mul(4935, 4948)` → `[4096, 1024]` (SM node 193, PM 447/448). -/
theorem recon_intermediateGoal_4949_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4949
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_4935 4935 8249 8250
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4935_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_4948 4948 8305 8306
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4948_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4949
      = elemwiseMul (denoteGraph_ringAttn sm initSM 4935) (denoteGraph_ringAttn sm initSM 4948) :=
    ringAttn_reduce2_pm_opaque sm initSM 193
      { rank := 0, op := "OpName.FW_mul", ins := [4935, 4948], outs := [4949] }
      4935 4948 4949 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 4935 4948 4949)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8309
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8249) (denoteGraph_ringAttn pm initPM 8305) :=
    ringAttn_reduce2_pm_opaque pm initPM 447
      { rank := 0, op := "OpName.FW_mul", ins := [8249, 8305], outs := [8309] }
      8249 8305 8309 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 8249 8305 8309)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8310
      = elemwiseMul (denoteGraph_ringAttn pm initPM 8250) (denoteGraph_ringAttn pm initPM 8306) :=
    ringAttn_reduce2_pm_opaque pm initPM 448
      { rank := 1, op := "OpName.FW_mul", ins := [8250, 8306], outs := [8310] }
      8250 8306 8310 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 8250 8306 8310)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4949
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8309, denoteGraph_ringAttn pm initPM 8310] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 4949).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 4935).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 4948).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 8309).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 8310).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4949 4949 8309 8310 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 4930 — layer-5 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 4930 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`8235`), rank 1 →
    `[32, 64)` (`8236`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `8227`/`8228` are expert-local (the
    `wf4930_hdisjA/B` fields).  Token input `7627 = mref5-pos1(4921)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 187, PM nodes 435/438). -/
theorem recon_intermediateGoal_4930_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4930
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 7627 = mref5-pos1(4921).
  obtain ⟨hbr13, hs8215, hs8216⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7627 : denoteGraph_ringAttn sm initSM 7627 = id (denoteGraph_ringAttn sm initSM 4921) :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921],
        outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7627 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14974 : denoteGraph_ringAttn pm initPM 14974 = id (denoteGraph_ringAttn pm initPM 8215) :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215],
        outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14974 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14997 : denoteGraph_ringAttn pm initPM 14997 = id (denoteGraph_ringAttn pm initPM 8216) :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216],
        outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 14997 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7627 p14974 p14997
  have hsInA : (denoteGraph_ringAttn pm initPM 14974).shape = [2048, 1024] := by
    rw [p14974]; exact hs8215
  have hsInB : (denoteGraph_ringAttn pm initPM 14997).shape = [2048, 1024] := by
    rw [p14997]; exact hs8216
  have hbrIn : denoteGraph_ringAttn sm initSM 7627
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 14974, denoteGraph_ringAttn pm initPM 14997] := by
    rw [s7627, hbr13, hnr, ← p14974, ← p14997]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_4925 4925 8225 8226
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4925_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_4926 4926 8227 8228
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4926_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 4925
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8225, denoteGraph_ringAttn pm initPM 8226] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 4926
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 8227, denoteGraph_ringAttn pm initPM 8228] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_4928
    (by native_decide) 4928 8231 8232 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_4929
    (by native_decide) 4929 8233 8234 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 8231).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4928 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4928, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8231 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 8232).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4928 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4928, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8232 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 8233).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4929 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4929, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8233 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 8234).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4929 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4929, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 8234 (by native_decide)]; exact hs.2
  -- SM 4930 = full-range all2all (SM node 187).
  have hSMout : denoteGraph_ringAttn sm initSM 4930
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7627)
          (denoteGraph_ringAttn sm initSM 4925) (denoteGraph_ringAttn sm initSM 4926)
          (denoteGraph_ringAttn sm initSM 4928) (denoteGraph_ringAttn sm initSM 4929)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 187
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7627, 4925, 4926, 4928, 4929],
        outs := [4930], params := [64, 0, 64, 8] }
      7627 4925 4926 4928 4929 4930
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7627 4925 4926 4928 4929 4930 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8235 = rank-0 sharded-range all2all (PM node 435).
  have hP0 : denoteGraph_ringAttn pm initPM 8235
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 14974)
          (denoteGraph_ringAttn pm initPM 8225) (denoteGraph_ringAttn pm initPM 8227)
          (denoteGraph_ringAttn pm initPM 8231) (denoteGraph_ringAttn pm initPM 8233)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 435
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14974, 8225, 8227, 8231, 8233],
        outs := [8235], params := [64, 0, 32, 8] }
      14974 8225 8227 8231 8233 8235
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 14974 8225 8227 8231 8233 8235 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 8236 = rank-1 sharded-range all2all (PM node 438).
  have hP1 : denoteGraph_ringAttn pm initPM 8236
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 14997)
          (denoteGraph_ringAttn pm initPM 8226) (denoteGraph_ringAttn pm initPM 8228)
          (denoteGraph_ringAttn pm initPM 8232) (denoteGraph_ringAttn pm initPM 8234)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 438
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14997, 8226, 8228, 8232, 8234],
        outs := [8236], params := [64, 32, 64, 8] }
      14997 8226 8228 8232 8234 8236
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 14997 8226 8228 8232 8234 8236 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 14974) (denoteGraph_ringAttn pm initPM 14997)
      (denoteGraph_ringAttn pm initPM 8225) (denoteGraph_ringAttn pm initPM 8226)
      (denoteGraph_ringAttn pm initPM 8227) (denoteGraph_ringAttn pm initPM 8228)
      (denoteGraph_ringAttn pm initPM 8231) (denoteGraph_ringAttn pm initPM 8232)
      (denoteGraph_ringAttn pm initPM 8233) (denoteGraph_ringAttn pm initPM 8234)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf4930_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf4930_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 4930
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8235, denoteGraph_ringAttn pm initPM 8236] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8235).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 8236).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 4930).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4930 4930 8235 8236 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L5 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7616 — second position of the L5 pre-MoE residual `mref2(4919)` (2-tp, PM
    shards `14955`/`14963`).  Unlike L2's `7564` there is no gather-to-full/chunk
    because `4919` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 172, PM nodes 399/400). -/
theorem recon_intermediateGoal_7616_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7616
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs8211, hs8212⟩ := twoTp_gather _ _ intermediateGoal_4919 4919 8211 8212
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4919_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7616 : denoteGraph_ringAttn sm initSM 7616 = id (denoteGraph_ringAttn sm initSM 4919) :=
    ringAttn_reduce1_pm_opaque sm initSM 172
      { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616], params := [2] }
      4919 7616 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4919 7612 7616 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14955 : denoteGraph_ringAttn pm initPM 14955 = id (denoteGraph_ringAttn pm initPM 8211) :=
    ringAttn_reduce1_pm_opaque pm initPM 405
      { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955], params := [2] }
      8211 14955 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 8211 14951 14955 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14963 : denoteGraph_ringAttn pm initPM 14963 = id (denoteGraph_ringAttn pm initPM 8212) :=
    ringAttn_reduce1_pm_opaque pm initPM 406
      { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963], params := [2] }
      8212 14963 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 8212 14959 14963 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7616 p14955 p14963
  have hsp0 : (denoteGraph_ringAttn pm initPM 14955).shape = [2048, 1024] := by
    rw [p14955]; exact hs8211
  have hsp1 : (denoteGraph_ringAttn pm initPM 14963).shape = [2048, 1024] := by
    rw [p14963]; exact hs8212
  have hval : denoteGraph_ringAttn sm initSM 7616
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14955, denoteGraph_ringAttn pm initPM 14963] := by
    rw [s7616, hbr11, ← p14955, ← p14963]
  have hshape : (denoteGraph_ringAttn sm initSM 7616).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7616 7616 14955 14963 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4950 — post-MoE residual add `4930 + 4949` (2-tp, PM `8313`/`8314`). -/
theorem recon_intermediateGoal_4950_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4950
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs8235, hs8236⟩ := twoTp_gather _ _ intermediateGoal_4930 4930 8235 8236
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4930_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs8309, hs8310⟩ := twoTp_gather _ _ intermediateGoal_4949 4949 8309 8310
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4949_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4950
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 4930) (denoteGraph_ringAttn sm initSM 4949) :=
    ringAttn_reduce2_pm_opaque sm initSM 194
      { rank := 0, op := "OpName.FW_add", ins := [4930, 4949], outs := [4950] }
      4930 4949 4950 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 4930 4949 4950)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8313
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8235) (denoteGraph_ringAttn pm initPM 8309) :=
    ringAttn_reduce2_pm_opaque pm initPM 449
      { rank := 0, op := "OpName.FW_add", ins := [8235, 8309], outs := [8313] }
      8235 8309 8313 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 8235 8309 8313)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8314
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 8236) (denoteGraph_ringAttn pm initPM 8310) :=
    ringAttn_reduce2_pm_opaque pm initPM 450
      { rank := 1, op := "OpName.FW_add", ins := [8236, 8310], outs := [8314] }
      8236 8310 8314 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 8236 8310 8314)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4950
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8313, denoteGraph_ringAttn pm initPM 8314] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs8235 hs8236 hs8309 hs8310,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8313).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8235 hs8309
  have hsp1 : (denoteGraph_ringAttn pm initPM 8314).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs8236 hs8310
  have hshape : (denoteGraph_ringAttn sm initSM 4950).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4950 4950 8313 8314 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4951 — `FW_float(4950)` (identity, 2-tp PM `8319`/`8320`). -/
theorem recon_intermediateGoal_4951_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4951
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs8313, hs8314⟩ := twoTp_gather _ _ intermediateGoal_4950 4950 8313 8314
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4950_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4951 = id (denoteGraph_ringAttn sm initSM 4950) :=
    ringAttn_reduce1_pm_opaque sm initSM 195
      { rank := 0, op := "OpName.FW_float", ins := [4950], outs := [4951] }
      4950 4951 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4950 4951 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8319 = id (denoteGraph_ringAttn pm initPM 8313) :=
    ringAttn_reduce1_pm_opaque pm initPM 451
      { rank := 0, op := "OpName.FW_float", ins := [8313], outs := [8319] }
      8313 8319 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 8313 8319 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8320 = id (denoteGraph_ringAttn pm initPM 8314) :=
    ringAttn_reduce1_pm_opaque pm initPM 452
      { rank := 1, op := "OpName.FW_float", ins := [8314], outs := [8320] }
      8314 8320 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 8314 8320 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 4951
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8319, denoteGraph_ringAttn pm initPM 8320] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8319).shape = [2048, 1024] := by rw [rP0]; exact hs8313
  have hsp1 : (denoteGraph_ringAttn pm initPM 8320).shape = [2048, 1024] := by rw [rP1]; exact hs8314
  have hshape : (denoteGraph_ringAttn sm initSM 4951).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4951 4951 8319 8320 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4952 — cross-block residual add `7616 + 4951` (2-tp, PM `8323`/`8324`). -/
theorem recon_intermediateGoal_4952_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4952
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs14955, hs14963⟩ := twoTp_gather _ _ intermediateGoal_7616 7616 14955 14963
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7616_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs8319, hs8320⟩ := twoTp_gather _ _ intermediateGoal_4951 4951 8319 8320
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4951_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4952
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7616) (denoteGraph_ringAttn sm initSM 4951) :=
    ringAttn_reduce2_pm_opaque sm initSM 196
      { rank := 0, op := "OpName.FW_add", ins := [7616, 4951], outs := [4952] }
      7616 4951 4952 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7616 4951 4952)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8323
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14955) (denoteGraph_ringAttn pm initPM 8319) :=
    ringAttn_reduce2_pm_opaque pm initPM 453
      { rank := 0, op := "OpName.FW_add", ins := [14955, 8319], outs := [8323] }
      14955 8319 8323 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 14955 8319 8323)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8324
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14963) (denoteGraph_ringAttn pm initPM 8320) :=
    ringAttn_reduce2_pm_opaque pm initPM 454
      { rank := 1, op := "OpName.FW_add", ins := [14963, 8320], outs := [8324] }
      14963 8320 8324 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14963 8320 8324)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4952
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8323, denoteGraph_ringAttn pm initPM 8324] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs14955 hs14963 hs8319 hs8320,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8323).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14955 hs8319
  have hsp1 : (denoteGraph_ringAttn pm initPM 8324).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14963 hs8320
  have hshape : (denoteGraph_ringAttn sm initSM 4952).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4952 4952 8323 8324 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4954 — RMSNorm of `mref2-first(4952)` with replicated weight `4953`
    (2-tp, PM `8327`/`8328`). -/
theorem recon_intermediateGoal_4954_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4954
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs8323, hs8324⟩ := twoTp_gather _ _ intermediateGoal_4952 4952 8323 8324
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4952_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7643 : denoteGraph_ringAttn sm initSM 7643 = id (denoteGraph_ringAttn sm initSM 4952) :=
    ringAttn_reduce1_pm_opaque sm initSM 197
      { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647], params := [2] }
      4952 7643 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4952 7643 7647)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15013 : denoteGraph_ringAttn pm initPM 15013 = id (denoteGraph_ringAttn pm initPM 8323) :=
    ringAttn_reduce1_pm_opaque pm initPM 455
      { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017], params := [2] }
      8323 15013 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8323 15013 15017)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15021 : denoteGraph_ringAttn pm initPM 15021 = id (denoteGraph_ringAttn pm initPM 8324) :=
    ringAttn_reduce1_pm_opaque pm initPM 456
      { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025], params := [2] }
      8324 15021 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8324 15021 15025)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7643 p15013 p15021
  have hs15013 : (denoteGraph_ringAttn pm initPM 15013).shape = [2048, 1024] := by
    rw [p15013]; exact hs8323
  have hs15021 : (denoteGraph_ringAttn pm initPM 15021).shape = [2048, 1024] := by
    rw [p15021]; exact hs8324
  have hbr39 : denoteGraph_ringAttn sm initSM 7643
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15013, denoteGraph_ringAttn pm initPM 15021] := by
    rw [s7643, hbr44, ← p15013, ← p15021]
  have hw4953 : denoteGraph_ringAttn sm initSM 4953 = denoteGraph_ringAttn pm initPM 4953 :=
    veq_weight_ring initSM initPM hInit initGoal_4953 (by native_decide) 4953
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4954
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7643) (denoteGraph_ringAttn sm initSM 4953) :=
    ringAttn_reduce2_pm_opaque sm initSM 198
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7643, 4953], outs := [4954] }
      7643 4953 4954 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7643 4953 4954)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8327
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15013) (denoteGraph_ringAttn pm initPM 4953) :=
    ringAttn_reduce2_pm_opaque pm initPM 457
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15013, 4953], outs := [8327] }
      15013 4953 8327 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15013 4953 8327)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8328
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15021) (denoteGraph_ringAttn pm initPM 4953) :=
    ringAttn_reduce2_pm_opaque pm initPM 458
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15021, 4953], outs := [8328] }
      15021 4953 8328 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15021 4953 8328)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4954
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8327, denoteGraph_ringAttn pm initPM 8328] := by
    rw [rSM, hbr39, hw4953, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15013 hs15021,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8327).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15013
  have hsp1 : (denoteGraph_ringAttn pm initPM 8328).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15021
  have hshape : (denoteGraph_ringAttn sm initSM 4954).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4954 4954 8327 8328 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4956 — per-head Q projection `fw_per_head_linear(mref3₀(4954), 4955)`
    (2-tp, PM `8329`/`8330`, weight `4955 : [16,64,1024]`). -/
theorem recon_intermediateGoal_4956_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4956
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8327, hs8328⟩ := twoTp_gather _ _ intermediateGoal_4954 4954 8327 8328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4954_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7652 : denoteGraph_ringAttn sm initSM 7652 = id (denoteGraph_ringAttn sm initSM 4954) :=
    ringAttn_reduce1_pm_opaque sm initSM 199
      { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
      4954 7652 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4954 7652 7656 7660)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15030 : denoteGraph_ringAttn pm initPM 15030 = id (denoteGraph_ringAttn pm initPM 8327) :=
    ringAttn_reduce1_pm_opaque pm initPM 459
      { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
      8327 15030 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8327 15030 15034 15038)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15043 : denoteGraph_ringAttn pm initPM 15043 = id (denoteGraph_ringAttn pm initPM 8328) :=
    ringAttn_reduce1_pm_opaque pm initPM 460
      { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
      8328 15043 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8328 15043 15047 15051)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7652 p15030 p15043
  have hs15030 : (denoteGraph_ringAttn pm initPM 15030).shape = [2048, 1024] := by
    rw [p15030]; exact hs8327
  have hs15043 : (denoteGraph_ringAttn pm initPM 15043).shape = [2048, 1024] := by
    rw [p15043]; exact hs8328
  have hbr48 : denoteGraph_ringAttn sm initSM 7652
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15030, denoteGraph_ringAttn pm initPM 15043] := by
    rw [s7652, hbr46, ← p15030, ← p15043]
  have hw4955 : denoteGraph_ringAttn sm initSM 4955 = denoteGraph_ringAttn pm initPM 4955 :=
    veq_weight_ring initSM initPM hInit initGoal_4955 (by native_decide) 4955
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4955 : (denoteGraph_ringAttn sm initSM 4955).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4955 (by native_decide) 4955 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4955 : (denoteGraph_ringAttn pm initPM 4955).shape = [16, 64, 1024] := by
    rw [← hw4955]; exact hsw4955
  have rSM : denoteGraph_ringAttn sm initSM 4956
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7652) (denoteGraph_ringAttn sm initSM 4955) :=
    ringAttn_reduce2_pm_opaque sm initSM 200
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7652, 4955], outs := [4956] }
      7652 4955 4956 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7652 4955 4956 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8329
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15030) (denoteGraph_ringAttn pm initPM 4955) :=
    ringAttn_reduce2_pm_opaque pm initPM 461
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15030, 4955], outs := [8329] }
      15030 4955 8329 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15030 4955 8329 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8330
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15043) (denoteGraph_ringAttn pm initPM 4955) :=
    ringAttn_reduce2_pm_opaque pm initPM 464
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15043, 4955], outs := [8330] }
      15043 4955 8330 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15043 4955 8330 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4956
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8329, denoteGraph_ringAttn pm initPM 8330] := by
    rw [rSM, hbr48, hw4955, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs15030 hs15043 hpw4955,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8329).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15030 hpw4955
  have hsp1 : (denoteGraph_ringAttn pm initPM 8330).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15043 hpw4955
  have hshape : (denoteGraph_ringAttn sm initSM 4956).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4956 4956 8329 8330 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4958 — per-head K projection `fw_per_head_linear(mref3₁(4954), 4957)`
    (2-tp, PM `8341`/`8342`, weight `4957 : [4,64,1024]`). -/
theorem recon_intermediateGoal_4958_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4958
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8327, hs8328⟩ := twoTp_gather _ _ intermediateGoal_4954 4954 8327 8328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4954_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7656 : denoteGraph_ringAttn sm initSM 7656 = id (denoteGraph_ringAttn sm initSM 4954) :=
    ringAttn_reduce1_pm_opaque sm initSM 199
      { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
      4954 7656 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4954 7652 7656 7660 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15034 : denoteGraph_ringAttn pm initPM 15034 = id (denoteGraph_ringAttn pm initPM 8327) :=
    ringAttn_reduce1_pm_opaque pm initPM 459
      { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
      8327 15034 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8327 15030 15034 15038 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15047 : denoteGraph_ringAttn pm initPM 15047 = id (denoteGraph_ringAttn pm initPM 8328) :=
    ringAttn_reduce1_pm_opaque pm initPM 460
      { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
      8328 15047 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8328 15043 15047 15051 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7656 p15034 p15047
  have hs15034 : (denoteGraph_ringAttn pm initPM 15034).shape = [2048, 1024] := by
    rw [p15034]; exact hs8327
  have hs15047 : (denoteGraph_ringAttn pm initPM 15047).shape = [2048, 1024] := by
    rw [p15047]; exact hs8328
  have hbr52 : denoteGraph_ringAttn sm initSM 7656
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15034, denoteGraph_ringAttn pm initPM 15047] := by
    rw [s7656, hbr46, ← p15034, ← p15047]
  have hw4957 : denoteGraph_ringAttn sm initSM 4957 = denoteGraph_ringAttn pm initPM 4957 :=
    veq_weight_ring initSM initPM hInit initGoal_4957 (by native_decide) 4957
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4957 : (denoteGraph_ringAttn sm initSM 4957).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4957 (by native_decide) 4957 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4957 : (denoteGraph_ringAttn pm initPM 4957).shape = [4, 64, 1024] := by
    rw [← hw4957]; exact hsw4957
  have rSM : denoteGraph_ringAttn sm initSM 4958
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7656) (denoteGraph_ringAttn sm initSM 4957) :=
    ringAttn_reduce2_pm_opaque sm initSM 201
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7656, 4957], outs := [4958] }
      7656 4957 4958 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7656 4957 4958 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8341
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15034) (denoteGraph_ringAttn pm initPM 4957) :=
    ringAttn_reduce2_pm_opaque pm initPM 462
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15034, 4957], outs := [8341] }
      15034 4957 8341 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15034 4957 8341 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8342
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15047) (denoteGraph_ringAttn pm initPM 4957) :=
    ringAttn_reduce2_pm_opaque pm initPM 465
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15047, 4957], outs := [8342] }
      15047 4957 8342 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15047 4957 8342 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4958
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8341, denoteGraph_ringAttn pm initPM 8342] := by
    rw [rSM, hbr52, hw4957, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15034 hs15047 hpw4957,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8341).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15034 hpw4957
  have hsp1 : (denoteGraph_ringAttn pm initPM 8342).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15047 hpw4957
  have hshape : (denoteGraph_ringAttn sm initSM 4958).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4958 4958 8341 8342 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4960 — per-head V projection `fw_per_head_linear(mref3₂(4954), 4959)`
    (2-tp, PM `8351`/`8352`, weight `4959 : [4,64,1024]`). -/
theorem recon_intermediateGoal_4960_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4960
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs8327, hs8328⟩ := twoTp_gather _ _ intermediateGoal_4954 4954 8327 8328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4954_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7660 : denoteGraph_ringAttn sm initSM 7660 = id (denoteGraph_ringAttn sm initSM 4954) :=
    ringAttn_reduce1_pm_opaque sm initSM 199
      { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
      4954 7660 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4954 7652 7656 7660 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15038 : denoteGraph_ringAttn pm initPM 15038 = id (denoteGraph_ringAttn pm initPM 8327) :=
    ringAttn_reduce1_pm_opaque pm initPM 459
      { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
      8327 15038 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8327 15030 15034 15038 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15051 : denoteGraph_ringAttn pm initPM 15051 = id (denoteGraph_ringAttn pm initPM 8328) :=
    ringAttn_reduce1_pm_opaque pm initPM 460
      { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
      8328 15051 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8328 15043 15047 15051 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7660 p15038 p15051
  have hs15038 : (denoteGraph_ringAttn pm initPM 15038).shape = [2048, 1024] := by
    rw [p15038]; exact hs8327
  have hs15051 : (denoteGraph_ringAttn pm initPM 15051).shape = [2048, 1024] := by
    rw [p15051]; exact hs8328
  have hbr56 : denoteGraph_ringAttn sm initSM 7660
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15038, denoteGraph_ringAttn pm initPM 15051] := by
    rw [s7660, hbr46, ← p15038, ← p15051]
  have hw4959 : denoteGraph_ringAttn sm initSM 4959 = denoteGraph_ringAttn pm initPM 4959 :=
    veq_weight_ring initSM initPM hInit initGoal_4959 (by native_decide) 4959
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4959 : (denoteGraph_ringAttn sm initSM 4959).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4959 (by native_decide) 4959 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4959 : (denoteGraph_ringAttn pm initPM 4959).shape = [4, 64, 1024] := by
    rw [← hw4959]; exact hsw4959
  have rSM : denoteGraph_ringAttn sm initSM 4960
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7660) (denoteGraph_ringAttn sm initSM 4959) :=
    ringAttn_reduce2_pm_opaque sm initSM 202
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7660, 4959], outs := [4960] }
      7660 4959 4960 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7660 4959 4960 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 8351
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15038) (denoteGraph_ringAttn pm initPM 4959) :=
    ringAttn_reduce2_pm_opaque pm initPM 463
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15038, 4959], outs := [8351] }
      15038 4959 8351 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15038 4959 8351 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 8352
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15051) (denoteGraph_ringAttn pm initPM 4959) :=
    ringAttn_reduce2_pm_opaque pm initPM 466
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15051, 4959], outs := [8352] }
      15051 4959 8352 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15051 4959 8352 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4960
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8351, denoteGraph_ringAttn pm initPM 8352] := by
    rw [rSM, hbr56, hw4959, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15038 hs15051 hpw4959,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8351).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15038 hpw4959
  have hsp1 : (denoteGraph_ringAttn pm initPM 8352).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15051 hpw4959
  have hshape : (denoteGraph_ringAttn sm initSM 4960).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4960 4960 8351 8352 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L5 rotary cos/sin cache agreement: `sm 4691 = pm 11858` (`= 11853 + 3`). -/
theorem hcache_4691_11858 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11858 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11858 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11858 5 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 4962 — rotary-embedding Q output `rotary(4691, 4961, 4956, 4958).1`
    (2-tp, PM `8363`/`8364`; positions `4961 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_4962_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4962
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs8329, hs8330⟩ := twoTp_gather _ _ intermediateGoal_4956 4956 8329 8330
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4956_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_4958 4958 8341 8342
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4958_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11858 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 4961 = denoteGraph_ringAttn pm initPM 4961 :=
    veq_weight_ring initSM initPM hInit initGoal_4961 (by native_decide) 4961
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp4961 : (denoteGraph_ringAttn sm initSM 4961).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_4961 (by native_decide) 4961 [4096]
      rfl rfl (by native_decide)
  have c8361 : denoteGraph_ringAttn pm initPM 8361
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4961) :=
    ringAttn_reduce1_pm_opaque pm initPM 5
      { rank := 0, op := "OpName.ChunkPrim", ins := [4961], outs := [8361], params := [0] }
      4961 8361 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4961 8361 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8362 : denoteGraph_ringAttn pm initPM 8362
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4961) :=
    ringAttn_reduce1_pm_opaque pm initPM 18
      { rank := 1, op := "OpName.ChunkPrim", ins := [4961], outs := [8362], params := [0] }
      4961 8362 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4961 8362 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4962
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4961)
          (denoteGraph_ringAttn sm initSM 4956) (denoteGraph_ringAttn sm initSM 4958) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 203
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4961, 4956, 4958], outs := [4962, 4963], params := [16, 4] }
          4962 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 203 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 203 4961 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 203 4956 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 203 4958 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8363
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11858) (denoteGraph_ringAttn pm initPM 8361)
          (denoteGraph_ringAttn pm initPM 8329) (denoteGraph_ringAttn pm initPM 8341) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 467
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11858, 8361, 8329, 8341], outs := [8363, 8365], params := [16, 4] }
          8363 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 467 11858 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 467 8361 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 467 8329 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 467 8341 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8364
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11858) (denoteGraph_ringAttn pm initPM 8362)
          (denoteGraph_ringAttn pm initPM 8330) (denoteGraph_ringAttn pm initPM 8342) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 468
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11858, 8362, 8330, 8342], outs := [8364, 8366], params := [16, 4] }
          8364 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 468 11858 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 468 8362 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 468 8330 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 468 8342 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4962
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8363, denoteGraph_ringAttn pm initPM 8364] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 4961) (denoteGraph_ringAttn pm initPM 8329)
          (denoteGraph_ringAttn pm initPM 8330) 2048 16 64 (by omega) (by omega) (by omega)
          hsp4961 hs8329 hs8330,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8361
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 4961) from c8361),
        ← (show denoteGraph_ringAttn pm initPM 8362
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 4961) from c8362),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8363).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8329
  have hsp1 : (denoteGraph_ringAttn pm initPM 8364).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs8330
  have hshape : (denoteGraph_ringAttn sm initSM 4962).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4962 4962 8363 8364 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 4963 — rotary-embedding K output `rotary(4691, 4961, 4956, 4958).2`
    (2-tp, PM `8365`/`8366`). -/
theorem recon_intermediateGoal_4963_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4963
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_4956 4956 8329 8330
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4956_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs8341, hs8342⟩ := twoTp_gather _ _ intermediateGoal_4958 4958 8341 8342
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4958_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11858 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 4961 = denoteGraph_ringAttn pm initPM 4961 :=
    veq_weight_ring initSM initPM hInit initGoal_4961 (by native_decide) 4961
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp4961 : (denoteGraph_ringAttn sm initSM 4961).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_4961 (by native_decide) 4961 [4096]
      rfl rfl (by native_decide)
  have c8361 : denoteGraph_ringAttn pm initPM 8361
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4961) :=
    ringAttn_reduce1_pm_opaque pm initPM 5
      { rank := 0, op := "OpName.ChunkPrim", ins := [4961], outs := [8361], params := [0] }
      4961 8361 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4961 8361 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c8362 : denoteGraph_ringAttn pm initPM 8362
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4961) :=
    ringAttn_reduce1_pm_opaque pm initPM 18
      { rank := 1, op := "OpName.ChunkPrim", ins := [4961], outs := [8362], params := [0] }
      4961 8362 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4961 8362 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4963
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4961)
          (denoteGraph_ringAttn sm initSM 4956) (denoteGraph_ringAttn sm initSM 4958) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 203
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4961, 4956, 4958], outs := [4962, 4963], params := [16, 4] }
          4963 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4961 4956 4958 4962 4963 (by decide),
        ringAttn_prefix_read_pm sm initSM 203 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 203 4961 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 203 4956 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 203 4958 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 8365
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11858) (denoteGraph_ringAttn pm initPM 8361)
          (denoteGraph_ringAttn pm initPM 8329) (denoteGraph_ringAttn pm initPM 8341) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 467
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11858, 8361, 8329, 8341], outs := [8363, 8365], params := [16, 4] }
          8365 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11858 8361 8329 8341 8363 8365 (by decide),
        ringAttn_prefix_read_pm pm initPM 467 11858 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 467 8361 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 467 8329 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 467 8341 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 8366
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11858) (denoteGraph_ringAttn pm initPM 8362)
          (denoteGraph_ringAttn pm initPM 8330) (denoteGraph_ringAttn pm initPM 8342) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 468
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11858, 8362, 8330, 8342], outs := [8364, 8366], params := [16, 4] }
          8366 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11858 8362 8330 8342 8364 8366 (by decide),
        ringAttn_prefix_read_pm pm initPM 468 11858 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 468 8362 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 468 8330 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 468 8342 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4963
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 8365, denoteGraph_ringAttn pm initPM 8366] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 4961) (denoteGraph_ringAttn pm initPM 8341)
          (denoteGraph_ringAttn pm initPM 8342) 2048 4 64 (by omega) (by omega) (by omega)
          hsp4961 hs8341 hs8342,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 8361
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 4961) from c8361),
        ← (show denoteGraph_ringAttn pm initPM 8362
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 4961) from c8362),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 8365).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8341
  have hsp1 : (denoteGraph_ringAttn pm initPM 8366).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs8342
  have hshape : (denoteGraph_ringAttn sm initSM 4963).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4963 4963 8365 8366 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
