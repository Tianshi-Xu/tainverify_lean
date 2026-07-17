/- Worker #23 — Layer-10 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_5182_ringAttn` (the layer-10
   sliding-window attention output, unconditional-given-WF) through the layer-10
   forward block.

   Unlike L2, the L10 block has NO gather-to-full node (L2's PM node 228
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L10
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_5186` targets `[9123, 9124]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L9Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 5183 — 2-tp reshape of the L10 attention output `5182 : [4096,16,64]` to
    `[4096,1024]` (SM node 205, PM nodes 471/472). -/
theorem recon_intermediateGoal_5183_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5183
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs9111, hs9112⟩ := twoTp_gather _ _ intermediateGoal_5182 5182 9111 9112
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5182_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5183
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5182) :=
    ringAttn_reshape_reduce_pm sm initSM 361 0 5182 5183 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9113
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9111) :=
    ringAttn_reshape_reduce_pm pm initPM 783 0 9111 9113 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9114
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9112) :=
    ringAttn_reshape_reduce_pm pm initPM 784 1 9112 9114 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5183
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9113, denoteGraph_ringAttn pm initPM 9114] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs9111 hs9112
  have hs9113 : (denoteGraph_ringAttn pm initPM 9113).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9114 : (denoteGraph_ringAttn pm initPM 9114).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5183 : (denoteGraph_ringAttn sm initSM 5183).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5183 5183 9113 9114 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5183 hs9113 hs9114

/-- 5184 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 206, PM
    nodes 473/474). -/
theorem recon_intermediateGoal_5184_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5184
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs9113, hs9114⟩ := twoTp_gather _ _ intermediateGoal_5183 5183 9113 9114
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5183_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5183 : (denoteGraph_ringAttn sm initSM 5183).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9113])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5184
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5183) :=
    ringAttn_reshape_reduce_pm sm initSM 362 0 5183 5184 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9119
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9113) :=
    ringAttn_reshape_reduce_pm pm initPM 785 0 9113 9119 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9120
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9114) :=
    ringAttn_reshape_reduce_pm pm initPM 786 1 9114 9120 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 9119 = denoteGraph_ringAttn pm initPM 9113 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9113]
  have h18 : denoteGraph_ringAttn pm initPM 9120 = denoteGraph_ringAttn pm initPM 9114 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9114]
  have hval : denoteGraph_ringAttn sm initSM 5184
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9119, denoteGraph_ringAttn pm initPM 9120] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5183, hval05, hnr, ← h17, ← h18]
  have hs9119 : (denoteGraph_ringAttn pm initPM 9119).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9120 : (denoteGraph_ringAttn pm initPM 9120).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5184 : (denoteGraph_ringAttn sm initSM 5184).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5184 5184 9119 9120 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5184 hs9119 hs9120

/-- 5186 — 2-tp down-projection `fw_linear(5184, 5185)` (weight `5185 : [1024,1024]`,
    SM node 207, PM nodes 475/476). -/
theorem recon_intermediateGoal_5186_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5186
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs9119, hs9120⟩ := twoTp_gather _ _ intermediateGoal_5184 5184 9119 9120
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5184_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5185 : denoteGraph_ringAttn sm initSM 5185 = denoteGraph_ringAttn pm initPM 5185 :=
    veq_weight_ring initSM initPM hInit initGoal_5185 (by native_decide) 5185
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5185 : (denoteGraph_ringAttn sm initSM 5185).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5185 (by native_decide) 5185 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw5185 : (denoteGraph_ringAttn pm initPM 5185).shape = [1024, 1024] := by
    rw [← hw5185]; exact hsw5185
  have rSM : denoteGraph_ringAttn sm initSM 5186
      = fw_linear (denoteGraph_ringAttn sm initSM 5184) (denoteGraph_ringAttn sm initSM 5185) :=
    ringAttn_reduce2_pm_opaque sm initSM 363
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5184, 5185], outs := [5186] }
      5184 5185 5186 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5184 5185 5186)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9123
      = fw_linear (denoteGraph_ringAttn pm initPM 9119) (denoteGraph_ringAttn pm initPM 5185) :=
    ringAttn_reduce2_pm_opaque pm initPM 787
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9119, 5185], outs := [9123] }
      9119 5185 9123 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9119 5185 9123)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9124
      = fw_linear (denoteGraph_ringAttn pm initPM 9120) (denoteGraph_ringAttn pm initPM 5185) :=
    ringAttn_reduce2_pm_opaque pm initPM 788
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9120, 5185], outs := [9124] }
      9120 5185 9124 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9120 5185 9124)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5186
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9123, denoteGraph_ringAttn pm initPM 9124] := by
    rw [rSM, hval06, hw5185, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs9119 hs9120 hpw5185,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9123).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9119 hpw5185
  have hsp1 : (denoteGraph_ringAttn pm initPM 9124).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs9120 hpw5185
  have hshape : (denoteGraph_ringAttn sm initSM 5186).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5186 5186 9123 9124 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5187 — 2-tp identity view of `5186` (SM node 208, PM nodes 477/478). -/
theorem recon_intermediateGoal_5187_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5187
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs9123, hs9124⟩ := twoTp_gather _ _ intermediateGoal_5186 5186 9123 9124
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5186_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5186 : (denoteGraph_ringAttn sm initSM 5186).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9123])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5187
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5186) :=
    ringAttn_reduce1_pm_opaque sm initSM 364
      { rank := 0, op := "OpName.FW_view", ins := [5186], outs := [5187], params := [4096, 1024] }
      5186 5187 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5186 5187)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9133
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9123) :=
    ringAttn_reduce1_pm_opaque pm initPM 789
      { rank := 0, op := "OpName.FW_view", ins := [9123], outs := [9133], params := [2048, 1024] }
      9123 9133 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9123 9133)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9134
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9124) :=
    ringAttn_reduce1_pm_opaque pm initPM 790
      { rank := 1, op := "OpName.FW_view", ins := [9124], outs := [9134], params := [2048, 1024] }
      9124 9134 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9124 9134)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 9133 = denoteGraph_ringAttn pm initPM 9123 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9123]
  have h32 : denoteGraph_ringAttn pm initPM 9134 = denoteGraph_ringAttn pm initPM 9124 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9124]
  have hval : denoteGraph_ringAttn sm initSM 5187
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9133, denoteGraph_ringAttn pm initPM 9134] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5186, hval08, hnr, ← h31, ← h32]
  have hs9133 : (denoteGraph_ringAttn pm initPM 9133).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs9134 : (denoteGraph_ringAttn pm initPM 9134).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs5187 : (denoteGraph_ringAttn sm initSM 5187).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5187 5187 9133 9134 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5187 hs9133 hs9134

/-- 5188 — 2-tp `FW_float(5187)` (identity, SM node 209, PM nodes 479/480). -/
theorem recon_intermediateGoal_5188_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5188
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs9133, hs9134⟩ := twoTp_gather _ _ intermediateGoal_5187 5187 9133 9134
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5187_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5188 = id (denoteGraph_ringAttn sm initSM 5187) :=
    ringAttn_reduce1_pm_opaque sm initSM 365
      { rank := 0, op := "OpName.FW_float", ins := [5187], outs := [5188] }
      5187 5188 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5187 5188 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9137 = id (denoteGraph_ringAttn pm initPM 9133) :=
    ringAttn_reduce1_pm_opaque pm initPM 791
      { rank := 0, op := "OpName.FW_float", ins := [9133], outs := [9137] }
      9133 9137 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9133 9137 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9138 = id (denoteGraph_ringAttn pm initPM 9134) :=
    ringAttn_reduce1_pm_opaque pm initPM 792
      { rank := 1, op := "OpName.FW_float", ins := [9134], outs := [9138] }
      9134 9138 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9134 9138 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5188
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9137, denoteGraph_ringAttn pm initPM 9138] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9137).shape = [2048, 1024] := by rw [rP0]; exact hs9133
  have hsp1 : (denoteGraph_ringAttn pm initPM 9138).shape = [2048, 1024] := by rw [rP1]; exact hs9134
  have hshape : (denoteGraph_ringAttn sm initSM 5188).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5188 5188 9137 9138 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7855 — 2-tp `mref2`-second copy of the L2 residual `5168` (SM node 197,
    PM nodes 455/456), carried into the L10 residual add. -/
theorem recon_intermediateGoal_7855_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7855
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs9067, hs9068⟩ := twoTp_gather _ _ intermediateGoal_5168 5168 9067 9068
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5168_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8123 : denoteGraph_ringAttn sm initSM 7855 = id (denoteGraph_ringAttn sm initSM 5168) :=
    ringAttn_reduce1_pm_opaque sm initSM 353
      { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855], params := [2] }
      5168 7855 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5168 7851 7855 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15433 : denoteGraph_ringAttn pm initPM 15433 = id (denoteGraph_ringAttn pm initPM 9067) :=
    ringAttn_reduce1_pm_opaque pm initPM 767
      { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433], params := [2] }
      9067 15433 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9067 15429 15433 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15441 : denoteGraph_ringAttn pm initPM 15441 = id (denoteGraph_ringAttn pm initPM 9068) :=
    ringAttn_reduce1_pm_opaque pm initPM 768
      { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441], params := [2] }
      9068 15441 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9068 15437 15441 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8123 p15433 p15441
  have hsp0 : (denoteGraph_ringAttn pm initPM 15433).shape = [2048, 1024] := by
    rw [p15433]; exact hs9067
  have hsp1 : (denoteGraph_ringAttn pm initPM 15441).shape = [2048, 1024] := by
    rw [p15441]; exact hs9068
  have hval : denoteGraph_ringAttn sm initSM 7855
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15433, denoteGraph_ringAttn pm initPM 15441] := by
    rw [s8123, hbr90, ← p15433, ← p15441]
  have hshape : (denoteGraph_ringAttn sm initSM 7855).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7855 7855 15433 15441 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5189 — 2-tp L10 residual add `7855 + 5188` (SM node 210, PM nodes 481/482). -/
theorem recon_intermediateGoal_5189_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5189
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs15433, hs15441⟩ := twoTp_gather _ _ intermediateGoal_7855 7855 15433 15441
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7855_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs9137, hs9138⟩ := twoTp_gather _ _ intermediateGoal_5188 5188 9137 9138
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5188_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5189
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7855) (denoteGraph_ringAttn sm initSM 5188) :=
    ringAttn_reduce2_pm_opaque sm initSM 366
      { rank := 0, op := "OpName.FW_add", ins := [7855, 5188], outs := [5189] }
      7855 5188 5189 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7855 5188 5189)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9141
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15433) (denoteGraph_ringAttn pm initPM 9137) :=
    ringAttn_reduce2_pm_opaque pm initPM 793
      { rank := 0, op := "OpName.FW_add", ins := [15433, 9137], outs := [9141] }
      15433 9137 9141 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15433 9137 9141)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9142
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15441) (denoteGraph_ringAttn pm initPM 9138) :=
    ringAttn_reduce2_pm_opaque pm initPM 794
      { rank := 1, op := "OpName.FW_add", ins := [15441, 9138], outs := [9142] }
      15441 9138 9142 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15441 9138 9142)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5189
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9141, denoteGraph_ringAttn pm initPM 9142] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15433 hs15441 hs9137 hs9138,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9141).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15433 hs9137
  have hsp1 : (denoteGraph_ringAttn pm initPM 9142).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15441 hs9138
  have hshape : (denoteGraph_ringAttn sm initSM 5189).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5189 5189 9141 9142 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5191 — 2-tp RMSNorm of `mref2-first(5189)` with replicated weight
    `5190 : [1024]` (SM node 212, PM nodes 485/486). -/
theorem recon_intermediateGoal_5191_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5191
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs9141, hs9142⟩ := twoTp_gather _ _ intermediateGoal_5189 5189 9141 9142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5189_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7872 : denoteGraph_ringAttn sm initSM 7872 = id (denoteGraph_ringAttn sm initSM 5189) :=
    ringAttn_reduce1_pm_opaque sm initSM 367
      { rank := 0, op := "OpName.FW_multiref", ins := [5189], outs := [7872, 7876], params := [2] }
      5189 7872 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5189 7872 7876)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15471 : denoteGraph_ringAttn pm initPM 15471 = id (denoteGraph_ringAttn pm initPM 9141) :=
    ringAttn_reduce1_pm_opaque pm initPM 795
      { rank := 0, op := "OpName.FW_multiref", ins := [9141], outs := [15471, 15475], params := [2] }
      9141 15471 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9141 15471 15475)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15479 : denoteGraph_ringAttn pm initPM 15479 = id (denoteGraph_ringAttn pm initPM 9142) :=
    ringAttn_reduce1_pm_opaque pm initPM 796
      { rank := 1, op := "OpName.FW_multiref", ins := [9142], outs := [15479, 15483], params := [2] }
      9142 15479 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9142 15479 15483)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7872 p15471 p15479
  have hs15471 : (denoteGraph_ringAttn pm initPM 15471).shape = [2048, 1024] := by
    rw [p15471]; exact hs9141
  have hs15479 : (denoteGraph_ringAttn pm initPM 15479).shape = [2048, 1024] := by
    rw [p15479]; exact hs9142
  have hbr08 : denoteGraph_ringAttn sm initSM 7872
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15471, denoteGraph_ringAttn pm initPM 15479] := by
    rw [s7872, hbr11, ← p15471, ← p15479]
  have hw5190 : denoteGraph_ringAttn sm initSM 5190 = denoteGraph_ringAttn pm initPM 5190 :=
    veq_weight_ring initSM initPM hInit initGoal_5190 (by native_decide) 5190
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5191
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7872) (denoteGraph_ringAttn sm initSM 5190) :=
    ringAttn_reduce2_pm_opaque sm initSM 368
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7872, 5190], outs := [5191] }
      7872 5190 5191 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7872 5190 5191)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9145
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15471) (denoteGraph_ringAttn pm initPM 5190) :=
    ringAttn_reduce2_pm_opaque pm initPM 797
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15471, 5190], outs := [9145] }
      15471 5190 9145 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15471 5190 9145)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9146
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15479) (denoteGraph_ringAttn pm initPM 5190) :=
    ringAttn_reduce2_pm_opaque pm initPM 798
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15479, 5190], outs := [9146] }
      15479 5190 9146 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15479 5190 9146)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5191
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9145, denoteGraph_ringAttn pm initPM 9146] := by
    rw [rSM, hbr08, hw5190, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15471 hs15479,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9145).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15471
  have hsp1 : (denoteGraph_ringAttn pm initPM 9146).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15479
  have hshape : (denoteGraph_ringAttn sm initSM 5191).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5191 5191 9145 9146 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5192 — 2-tp `FW_float(mref5-first(5191))` (identity, SM node 214,
    PM nodes 489/493; mref5-first via SM node 213, PM 487/488). -/
theorem recon_intermediateGoal_5192_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5192
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9145, hs9146⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7883 : denoteGraph_ringAttn sm initSM 7883 = id (denoteGraph_ringAttn sm initSM 5191) :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191],
        outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7883 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 5191 7883 [7887, 7891, 7895, 7899])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15490 : denoteGraph_ringAttn pm initPM 15490 = id (denoteGraph_ringAttn pm initPM 9145) :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145],
        outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15490 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 9145 15490 [15494, 15498, 15502, 15506])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15513 : denoteGraph_ringAttn pm initPM 15513 = id (denoteGraph_ringAttn pm initPM 9146) :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146],
        outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15513 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 9146 15513 [15517, 15521, 15525, 15529])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7883 p15490 p15513
  have hbrm : denoteGraph_ringAttn sm initSM 7883
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15490, denoteGraph_ringAttn pm initPM 15513] := by
    rw [s7883, hbr13, ← p15490, ← p15513]
  have rSM : denoteGraph_ringAttn sm initSM 5192 = id (denoteGraph_ringAttn sm initSM 7883) :=
    ringAttn_reduce1_pm_opaque sm initSM 370
      { rank := 0, op := "OpName.FW_float", ins := [7883], outs := [5192] }
      7883 5192 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7883 5192 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9147 = id (denoteGraph_ringAttn pm initPM 15490) :=
    ringAttn_reduce1_pm_opaque pm initPM 801
      { rank := 0, op := "OpName.FW_float", ins := [15490], outs := [9147] }
      15490 9147 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 15490 9147 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9148 = id (denoteGraph_ringAttn pm initPM 15513) :=
    ringAttn_reduce1_pm_opaque pm initPM 805
      { rank := 1, op := "OpName.FW_float", ins := [15513], outs := [9148] }
      15513 9148 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 15513 9148 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs15490 : (denoteGraph_ringAttn pm initPM 15490).shape = [2048, 1024] := by
    rw [p15490]; exact hs9145
  have hs15513 : (denoteGraph_ringAttn pm initPM 15513).shape = [2048, 1024] := by
    rw [p15513]; exact hs9146
  have hval : denoteGraph_ringAttn sm initSM 5192
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9147, denoteGraph_ringAttn pm initPM 9148] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9147).shape = [2048, 1024] := by
    rw [rP0]; exact hs15490
  have hsp1 : (denoteGraph_ringAttn pm initPM 9148).shape = [2048, 1024] := by
    rw [rP1]; exact hs15513
  have hshape : (denoteGraph_ringAttn sm initSM 5192).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5192 5192 9147 9148 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5194 — 2-tp router logits `fw_norm_linear(5192, 5193)` with weight
    `5193 : [64, 1024]` → `[4096, 64]` (SM node 218, PM nodes 497/501). -/
theorem recon_intermediateGoal_5194_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5194
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs9147, hs9148⟩ := twoTp_gather _ _ intermediateGoal_5192 5192 9147 9148
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5192_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5193 : denoteGraph_ringAttn sm initSM 5193 = denoteGraph_ringAttn pm initPM 5193 :=
    veq_weight_ring initSM initPM hInit initGoal_5193 (by native_decide) 5193
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5193 : (denoteGraph_ringAttn sm initSM 5193).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5193 (by native_decide) 5193 [64, 1024]
      rfl rfl (by native_decide)
  have hpw5193 : (denoteGraph_ringAttn pm initPM 5193).shape = [64, 1024] := by
    rw [← hw5193]; exact hsw5193
  have rSM : denoteGraph_ringAttn sm initSM 5194
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 5192) (denoteGraph_ringAttn sm initSM 5193) :=
    ringAttn_reduce2_pm_opaque sm initSM 374
      { rank := 0, op := "OpName.FW_norm_linear", ins := [5192, 5193], outs := [5194] }
      5192 5193 5194 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 5192 5193 5194)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9153
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9147) (denoteGraph_ringAttn pm initPM 5193) :=
    ringAttn_reduce2_pm_opaque pm initPM 809
      { rank := 0, op := "OpName.FW_norm_linear", ins := [9147, 5193], outs := [9153] }
      9147 5193 9153 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 9147 5193 9153)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9154
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9148) (denoteGraph_ringAttn pm initPM 5193) :=
    ringAttn_reduce2_pm_opaque pm initPM 813
      { rank := 1, op := "OpName.FW_norm_linear", ins := [9148, 5193], outs := [9154] }
      9148 5193 9154 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 9148 5193 9154)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5194
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9153, denoteGraph_ringAttn pm initPM 9154] := by
    rw [rSM, hval14, hw5193, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs9147 hs9148 hpw5193,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9153).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs9147 hpw5193
  have hsp1 : (denoteGraph_ringAttn pm initPM 9154).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs9148 hpw5193
  have hshape : (denoteGraph_ringAttn sm initSM 5194).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5194 5194 9153 9154 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L10 top-k routing (`5195`/`5196`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`9153`/`9154`) directly. -/

/-- Shared L10 top-k core: `5194` (full logits) is the dim-0 gather of the two
    per-rank shards `9153`/`9154`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L10 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 5194
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 9153, denoteGraph_ringAttn pm initPM 9154]
      ∧ (denoteGraph_ringAttn sm initSM 5194).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 9153).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 9154).shape = [2048, 64]
      ∧ ((sm.nodes.take 378).foldl (applyNodeRingAttn sm) initSM 5194).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 817).foldl (applyNodeRingAttn pm) initPM 9153).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 821).foldl (applyNodeRingAttn pm) initPM 9154).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs9153, hs9154⟩ := twoTp_gather _ _ intermediateGoal_5194 5194 9153 9154
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5194_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs5194sm : (denoteGraph_ringAttn sm initSM 5194).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs9153])]
    simp [List.set, List.getD]
  have hpre5194sm : denoteGraph_ringAttn sm initSM 5194
      = (sm.nodes.take 378).foldl (applyNodeRingAttn sm) initSM 5194 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5194 378 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 378).foldl (applyNodeRingAttn sm) initSM 5194).shape.reverse.head? = some 64 := by
    rw [← hpre5194sm, hs5194sm]; rfl
  have hpre9153 : denoteGraph_ringAttn pm initPM 9153
      = (pm.nodes.take 817).foldl (applyNodeRingAttn pm) initPM 9153 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9153 817 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 817).foldl (applyNodeRingAttn pm) initPM 9153).shape.reverse.head? = some 64 := by
    rw [← hpre9153, hs9153]; rfl
  have hpre9154 : denoteGraph_ringAttn pm initPM 9154
      = (pm.nodes.take 821).foldl (applyNodeRingAttn pm) initPM 9154 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9154 821 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 821).foldl (applyNodeRingAttn pm) initPM 9154).shape.reverse.head? = some 64 := by
    rw [← hpre9154, hs9154]; rfl
  exact ⟨hbr16, hs5194sm, hs9153, hs9154, hlastSM, hlast271, hlast275⟩

/-- 5195 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5195_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5195
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5194sm, hs9153, hs9154, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L10 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5195
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5194) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 378
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5194], outs := [5195, 5196, 5197], params := [8, 1] }
      5194 5195 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 378).foldl (applyNodeRingAttn sm) initSM) 0 5194 5195 5196 5197 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9155
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9153) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 817
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9153], outs := [9155, 9157, 9159], params := [8, 1] }
      9153 9155 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 817).foldl (applyNodeRingAttn pm) initPM) 0 9153 9155 9157 9159 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9156
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9154) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 821
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9154], outs := [9156, 9158, 9160], params := [8, 1] }
      9154 9156 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 821).foldl (applyNodeRingAttn pm) initPM) 1 9154 9156 9158 9160 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5195
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9155, denoteGraph_ringAttn pm initPM 9156] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9153 hs9154,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5195).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs5194sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9155).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9153]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9156).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9154]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5195 5195 9155 9156 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5196 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_5196_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5196
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs5194sm, hs9153, hs9154, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L10 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 5196
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5194) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 378
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5194], outs := [5195, 5196, 5197], params := [8, 1] }
      5194 5196 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 378).foldl (applyNodeRingAttn sm) initSM) 0 5194 5195 5196 5197 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9157
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9153) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 817
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9153], outs := [9155, 9157, 9159], params := [8, 1] }
      9153 9157 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 817).foldl (applyNodeRingAttn pm) initPM) 0 9153 9155 9157 9159 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9158
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9154) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 821
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9154], outs := [9156, 9158, 9160], params := [8, 1] }
      9154 9158 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 821).foldl (applyNodeRingAttn pm) initPM) 1 9154 9156 9158 9160 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5196
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9157, denoteGraph_ringAttn pm initPM 9158] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9153 hs9154,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5196).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs5194sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9157).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9153]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9158).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9154]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5196 5196 9157 9158 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L10 router expert branches — reshape (`5201`/`5206`/`5210`) of the
    `mref5` copies (positions 2/3/4) of `5191`, all identity 2-tp views. -/

/-- 5201 — 2-tp identity reshape of `mref5-pos2(5191)` (SM node 215, PM 490/494). -/
theorem recon_intermediateGoal_5201_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5201
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9145, hs9146⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5191sm : (denoteGraph_ringAttn sm initSM 5191).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9145])]
    simp [List.set, List.getD]
  have s7891 : denoteGraph_ringAttn sm initSM 7891 = id (denoteGraph_ringAttn sm initSM 5191) :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191],
        outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7891 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15498 : denoteGraph_ringAttn pm initPM 15498 = id (denoteGraph_ringAttn pm initPM 9145) :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145],
        outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15498 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15521 : denoteGraph_ringAttn pm initPM 15521 = id (denoteGraph_ringAttn pm initPM 9146) :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146],
        outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15521 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7891 p15498 p15521
  have hs7891 : (denoteGraph_ringAttn sm initSM 7891).shape = [4096, 1024] := by rw [s7891]; exact hs5191sm
  have hs15498 : (denoteGraph_ringAttn pm initPM 15498).shape = [2048, 1024] := by rw [p15498]; exact hs9145
  have hs15521 : (denoteGraph_ringAttn pm initPM 15521).shape = [2048, 1024] := by rw [p15521]; exact hs9146
  have hbrm : denoteGraph_ringAttn sm initSM 7891
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15498, denoteGraph_ringAttn pm initPM 15521] := by
    rw [s7891, hbr13, ← p15498, ← p15521]
  have rSM : denoteGraph_ringAttn sm initSM 5201
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7891) :=
    ringAttn_reduce1_pm_opaque sm initSM 371
      { rank := 0, op := "OpName.FW_reshape", ins := [7891], outs := [5201], params := [4096, 1024] }
      7891 5201 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7891 5201)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9167
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15498) :=
    ringAttn_reduce1_pm_opaque pm initPM 802
      { rank := 0, op := "OpName.FW_reshape", ins := [15498], outs := [9167], params := [2048, 1024] }
      15498 9167 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15498 9167)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9168
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15521) :=
    ringAttn_reduce1_pm_opaque pm initPM 806
      { rank := 1, op := "OpName.FW_reshape", ins := [15521], outs := [9168], params := [2048, 1024] }
      15521 9168 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15521 9168)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 9167 = denoteGraph_ringAttn pm initPM 15498 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15498]
  have h66 : denoteGraph_ringAttn pm initPM 9168 = denoteGraph_ringAttn pm initPM 15521 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15521]
  have hval : denoteGraph_ringAttn sm initSM 5201
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9167, denoteGraph_ringAttn pm initPM 9168] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7891, hbrm, hnr, ← h65, ← h66]
  have hs9167 : (denoteGraph_ringAttn pm initPM 9167).shape = [2048, 1024] := by rw [h65]; exact hs15498
  have hs9168 : (denoteGraph_ringAttn pm initPM 9168).shape = [2048, 1024] := by rw [h66]; exact hs15521
  have hs5201 : (denoteGraph_ringAttn sm initSM 5201).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7891]; exact hs7891
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5201 5201 9167 9168 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5201 hs9167 hs9168

/-- 5206 — 2-tp identity reshape of `mref5-pos3(5191)` (SM node 216, PM 491/495). -/
theorem recon_intermediateGoal_5206_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5206
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9145, hs9146⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5191sm : (denoteGraph_ringAttn sm initSM 5191).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9145])]
    simp [List.set, List.getD]
  have s7895 : denoteGraph_ringAttn sm initSM 7895 = id (denoteGraph_ringAttn sm initSM 5191) :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191],
        outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7895 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15502 : denoteGraph_ringAttn pm initPM 15502 = id (denoteGraph_ringAttn pm initPM 9145) :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145],
        outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15502 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15525 : denoteGraph_ringAttn pm initPM 15525 = id (denoteGraph_ringAttn pm initPM 9146) :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146],
        outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15525 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7895 p15502 p15525
  have hs7895 : (denoteGraph_ringAttn sm initSM 7895).shape = [4096, 1024] := by rw [s7895]; exact hs5191sm
  have hs15502 : (denoteGraph_ringAttn pm initPM 15502).shape = [2048, 1024] := by rw [p15502]; exact hs9145
  have hs15525 : (denoteGraph_ringAttn pm initPM 15525).shape = [2048, 1024] := by rw [p15525]; exact hs9146
  have hbrm : denoteGraph_ringAttn sm initSM 7895
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15502, denoteGraph_ringAttn pm initPM 15525] := by
    rw [s7895, hbr13, ← p15502, ← p15525]
  have rSM : denoteGraph_ringAttn sm initSM 5206
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7895) :=
    ringAttn_reduce1_pm_opaque sm initSM 372
      { rank := 0, op := "OpName.FW_reshape", ins := [7895], outs := [5206], params := [4096, 1024] }
      7895 5206 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7895 5206)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9181
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15502) :=
    ringAttn_reduce1_pm_opaque pm initPM 803
      { rank := 0, op := "OpName.FW_reshape", ins := [15502], outs := [9181], params := [2048, 1024] }
      15502 9181 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15502 9181)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9182
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15525) :=
    ringAttn_reduce1_pm_opaque pm initPM 807
      { rank := 1, op := "OpName.FW_reshape", ins := [15525], outs := [9182], params := [2048, 1024] }
      15525 9182 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15525 9182)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 9181 = denoteGraph_ringAttn pm initPM 15502 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15502]
  have h80 : denoteGraph_ringAttn pm initPM 9182 = denoteGraph_ringAttn pm initPM 15525 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15525]
  have hval : denoteGraph_ringAttn sm initSM 5206
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9181, denoteGraph_ringAttn pm initPM 9182] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7895, hbrm, hnr, ← h79, ← h80]
  have hs9181 : (denoteGraph_ringAttn pm initPM 9181).shape = [2048, 1024] := by rw [h79]; exact hs15502
  have hs9182 : (denoteGraph_ringAttn pm initPM 9182).shape = [2048, 1024] := by rw [h80]; exact hs15525
  have hs5206 : (denoteGraph_ringAttn sm initSM 5206).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7895]; exact hs7895
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5206 5206 9181 9182 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5206 hs9181 hs9182

/-- 5210 — 2-tp identity reshape of `mref5-pos4(5191)` (SM node 217, PM 492/496). -/
theorem recon_intermediateGoal_5210_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5210
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs9145, hs9146⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5191sm : (denoteGraph_ringAttn sm initSM 5191).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9145])]
    simp [List.set, List.getD]
  have s7899 : denoteGraph_ringAttn sm initSM 7899 = id (denoteGraph_ringAttn sm initSM 5191) :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191],
        outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7899 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15506 : denoteGraph_ringAttn pm initPM 15506 = id (denoteGraph_ringAttn pm initPM 9145) :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145],
        outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15506 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15529 : denoteGraph_ringAttn pm initPM 15529 = id (denoteGraph_ringAttn pm initPM 9146) :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146],
        outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15529 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7899 p15506 p15529
  have hs7899 : (denoteGraph_ringAttn sm initSM 7899).shape = [4096, 1024] := by rw [s7899]; exact hs5191sm
  have hs15506 : (denoteGraph_ringAttn pm initPM 15506).shape = [2048, 1024] := by rw [p15506]; exact hs9145
  have hs15529 : (denoteGraph_ringAttn pm initPM 15529).shape = [2048, 1024] := by rw [p15529]; exact hs9146
  have hbrm : denoteGraph_ringAttn sm initSM 7899
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15506, denoteGraph_ringAttn pm initPM 15529] := by
    rw [s7899, hbr13, ← p15506, ← p15529]
  have rSM : denoteGraph_ringAttn sm initSM 5210
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7899) :=
    ringAttn_reduce1_pm_opaque sm initSM 373
      { rank := 0, op := "OpName.FW_reshape", ins := [7899], outs := [5210], params := [4096, 1024] }
      7899 5210 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7899 5210)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9199
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15506) :=
    ringAttn_reduce1_pm_opaque pm initPM 804
      { rank := 0, op := "OpName.FW_reshape", ins := [15506], outs := [9199], params := [2048, 1024] }
      15506 9199 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 15506 9199)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9200
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 15529) :=
    ringAttn_reduce1_pm_opaque pm initPM 808
      { rank := 1, op := "OpName.FW_reshape", ins := [15529], outs := [9200], params := [2048, 1024] }
      15529 9200 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 15529 9200)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 9199 = denoteGraph_ringAttn pm initPM 15506 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs15506]
  have h98 : denoteGraph_ringAttn pm initPM 9200 = denoteGraph_ringAttn pm initPM 15529 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs15529]
  have hval : denoteGraph_ringAttn sm initSM 5210
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9199, denoteGraph_ringAttn pm initPM 9200] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7899, hbrm, hnr, ← h97, ← h98]
  have hs9199 : (denoteGraph_ringAttn pm initPM 9199).shape = [2048, 1024] := by rw [h97]; exact hs15506
  have hs9200 : (denoteGraph_ringAttn pm initPM 9200).shape = [2048, 1024] := by rw [h98]; exact hs15529
  have hs5210 : (denoteGraph_ringAttn sm initSM 5210).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7899]; exact hs7899
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5210 5210 9199 9200 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5210 hs9199 hs9200

/-! ### L10 router expert mixlins (`5203`/`5208`/`5212`), 2-tp. -/

/-- 5203 — 2-tp `fw_linear(5201, 5202)`, weight `5202 : [1, 1024]` → `[4096, 1]`
    (SM node 219, PM nodes 498/502). -/
theorem recon_intermediateGoal_5203_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5203
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs9167, hs9168⟩ := twoTp_gather _ _ intermediateGoal_5201 5201 9167 9168
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5201_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5202 : denoteGraph_ringAttn sm initSM 5202 = denoteGraph_ringAttn pm initPM 5202 :=
    veq_weight_ring initSM initPM hInit initGoal_5202 (by native_decide) 5202
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5202 : (denoteGraph_ringAttn pm initPM 5202).shape = [1, 1024] := by
    rw [← hw5202]
    exact shape_weight_ring initSM initPM hInit initGoal_5202 (by native_decide) 5202 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5203
      = fw_linear (denoteGraph_ringAttn sm initSM 5201) (denoteGraph_ringAttn sm initSM 5202) :=
    ringAttn_reduce2_pm_opaque sm initSM 375
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5201, 5202], outs := [5203] }
      5201 5202 5203 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5201 5202 5203)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9171
      = fw_linear (denoteGraph_ringAttn pm initPM 9167) (denoteGraph_ringAttn pm initPM 5202) :=
    ringAttn_reduce2_pm_opaque pm initPM 810
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9167, 5202], outs := [9171] }
      9167 5202 9171 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9167 5202 9171)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9172
      = fw_linear (denoteGraph_ringAttn pm initPM 9168) (denoteGraph_ringAttn pm initPM 5202) :=
    ringAttn_reduce2_pm_opaque pm initPM 814
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9168, 5202], outs := [9172] }
      9168 5202 9172 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9168 5202 9172)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5203
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9171, denoteGraph_ringAttn pm initPM 9172] := by
    rw [rSM, hval23, hw5202, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs9167 hs9168 hpw5202,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9171).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9167 hpw5202
  have hsp1 : (denoteGraph_ringAttn pm initPM 9172).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9168 hpw5202
  have hshape : (denoteGraph_ringAttn sm initSM 5203).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5203 5203 9171 9172 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5208 — 2-tp `fw_linear(5206, 5207)`, weight `5207 : [512, 1024]` → `[4096, 512]`
    (SM node 220, PM nodes 499/503). -/
theorem recon_intermediateGoal_5208_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5208
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs9181, hs9182⟩ := twoTp_gather _ _ intermediateGoal_5206 5206 9181 9182
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5206_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5207 : denoteGraph_ringAttn sm initSM 5207 = denoteGraph_ringAttn pm initPM 5207 :=
    veq_weight_ring initSM initPM hInit initGoal_5207 (by native_decide) 5207
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5207 : (denoteGraph_ringAttn pm initPM 5207).shape = [512, 1024] := by
    rw [← hw5207]
    exact shape_weight_ring initSM initPM hInit initGoal_5207 (by native_decide) 5207 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5208
      = fw_linear (denoteGraph_ringAttn sm initSM 5206) (denoteGraph_ringAttn sm initSM 5207) :=
    ringAttn_reduce2_pm_opaque sm initSM 376
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5206, 5207], outs := [5208] }
      5206 5207 5208 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5206 5207 5208)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9185
      = fw_linear (denoteGraph_ringAttn pm initPM 9181) (denoteGraph_ringAttn pm initPM 5207) :=
    ringAttn_reduce2_pm_opaque pm initPM 811
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9181, 5207], outs := [9185] }
      9181 5207 9185 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9181 5207 9185)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9186
      = fw_linear (denoteGraph_ringAttn pm initPM 9182) (denoteGraph_ringAttn pm initPM 5207) :=
    ringAttn_reduce2_pm_opaque pm initPM 815
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9182, 5207], outs := [9186] }
      9182 5207 9186 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9182 5207 9186)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5208
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9185, denoteGraph_ringAttn pm initPM 9186] := by
    rw [rSM, hval28, hw5207, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs9181 hs9182 hpw5207,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9185).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9181 hpw5207
  have hsp1 : (denoteGraph_ringAttn pm initPM 9186).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9182 hpw5207
  have hshape : (denoteGraph_ringAttn sm initSM 5208).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5208 5208 9185 9186 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5212 — 2-tp `fw_linear(5210, 5211)`, weight `5211 : [512, 1024]` → `[4096, 512]`
    (SM node 221, PM nodes 500/504). -/
theorem recon_intermediateGoal_5212_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5212
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs9199, hs9200⟩ := twoTp_gather _ _ intermediateGoal_5210 5210 9199 9200
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5210_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5211 : denoteGraph_ringAttn sm initSM 5211 = denoteGraph_ringAttn pm initPM 5211 :=
    veq_weight_ring initSM initPM hInit initGoal_5211 (by native_decide) 5211
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5211 : (denoteGraph_ringAttn pm initPM 5211).shape = [512, 1024] := by
    rw [← hw5211]
    exact shape_weight_ring initSM initPM hInit initGoal_5211 (by native_decide) 5211 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5212
      = fw_linear (denoteGraph_ringAttn sm initSM 5210) (denoteGraph_ringAttn sm initSM 5211) :=
    ringAttn_reduce2_pm_opaque sm initSM 377
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5210, 5211], outs := [5212] }
      5210 5211 5212 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5210 5211 5212)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9203
      = fw_linear (denoteGraph_ringAttn pm initPM 9199) (denoteGraph_ringAttn pm initPM 5211) :=
    ringAttn_reduce2_pm_opaque pm initPM 812
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9199, 5211], outs := [9203] }
      9199 5211 9203 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9199 5211 9203)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9204
      = fw_linear (denoteGraph_ringAttn pm initPM 9200) (denoteGraph_ringAttn pm initPM 5211) :=
    ringAttn_reduce2_pm_opaque pm initPM 816
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9200, 5211], outs := [9204] }
      9200 5211 9204 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9200 5211 9204)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5212
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9203, denoteGraph_ringAttn pm initPM 9204] := by
    rw [rSM, hval32, hw5211, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs9199 hs9200 hpw5211,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9203).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9199 hpw5211
  have hsp1 : (denoteGraph_ringAttn pm initPM 9204).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9200 hpw5211
  have hshape : (denoteGraph_ringAttn sm initSM 5212).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5212 5212 9203 9204 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L10 router expert views (`5204`/`5209`/`5213`), identity 2-tp views. -/

/-- 5204 — 2-tp identity view of `5203` → `[4096, 1]` (SM node 223, PM 506/510). -/
theorem recon_intermediateGoal_5204_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5204
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs9171, hs9172⟩ := twoTp_gather _ _ intermediateGoal_5203 5203 9171 9172
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5203_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5203 : (denoteGraph_ringAttn sm initSM 5203).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs9171])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5204
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 5203) :=
    ringAttn_reduce1_pm_opaque sm initSM 379
      { rank := 0, op := "OpName.FW_view", ins := [5203], outs := [5204], params := [4096, 1] }
      5203 5204 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 5203 5204)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9177
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9171) :=
    ringAttn_reduce1_pm_opaque pm initPM 818
      { rank := 0, op := "OpName.FW_view", ins := [9171], outs := [9177], params := [2048, 1] }
      9171 9177 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 9171 9177)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9178
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9172) :=
    ringAttn_reduce1_pm_opaque pm initPM 822
      { rank := 1, op := "OpName.FW_view", ins := [9172], outs := [9178], params := [2048, 1] }
      9172 9178 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 9172 9178)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 9177 = denoteGraph_ringAttn pm initPM 9171 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs9171]
  have h76 : denoteGraph_ringAttn pm initPM 9178 = denoteGraph_ringAttn pm initPM 9172 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs9172]
  have hval : denoteGraph_ringAttn sm initSM 5204
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9177, denoteGraph_ringAttn pm initPM 9178] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5203, hval25, hnr, ← h75, ← h76]
  have hs9177 : (denoteGraph_ringAttn pm initPM 9177).shape = [2048, 1] := by rw [h75]; exact hs9171
  have hs9178 : (denoteGraph_ringAttn pm initPM 9178).shape = [2048, 1] := by rw [h76]; exact hs9172
  have hs5204 : (denoteGraph_ringAttn sm initSM 5204).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs5203]; exact hs5203
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5204 5204 9177 9178 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5204 hs9177 hs9178

/-- 5209 — 2-tp identity view of `5208` → `[4096, 512]` (SM node 224, PM 507/511). -/
theorem recon_intermediateGoal_5209_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5209
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs9185, hs9186⟩ := twoTp_gather _ _ intermediateGoal_5208 5208 9185 9186
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5208_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5208 : (denoteGraph_ringAttn sm initSM 5208).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9185])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5209
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5208) :=
    ringAttn_reduce1_pm_opaque sm initSM 380
      { rank := 0, op := "OpName.FW_view", ins := [5208], outs := [5209], params := [4096, 512] }
      5208 5209 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5208 5209)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9195
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9185) :=
    ringAttn_reduce1_pm_opaque pm initPM 819
      { rank := 0, op := "OpName.FW_view", ins := [9185], outs := [9195], params := [2048, 512] }
      9185 9195 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9185 9195)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9196
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9186) :=
    ringAttn_reduce1_pm_opaque pm initPM 823
      { rank := 1, op := "OpName.FW_view", ins := [9186], outs := [9196], params := [2048, 512] }
      9186 9196 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9186 9196)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 9195 = denoteGraph_ringAttn pm initPM 9185 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9185]
  have h94 : denoteGraph_ringAttn pm initPM 9196 = denoteGraph_ringAttn pm initPM 9186 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9186]
  have hval : denoteGraph_ringAttn sm initSM 5209
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9195, denoteGraph_ringAttn pm initPM 9196] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5208, hval30, hnr, ← h93, ← h94]
  have hs9195 : (denoteGraph_ringAttn pm initPM 9195).shape = [2048, 512] := by rw [h93]; exact hs9185
  have hs9196 : (denoteGraph_ringAttn pm initPM 9196).shape = [2048, 512] := by rw [h94]; exact hs9186
  have hs5209 : (denoteGraph_ringAttn sm initSM 5209).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5208]; exact hs5208
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5209 5209 9195 9196 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5209 hs9195 hs9196

/-- 5213 — 2-tp identity view of `5212` → `[4096, 512]` (SM node 225, PM 508/512). -/
theorem recon_intermediateGoal_5213_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5213
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs9203, hs9204⟩ := twoTp_gather _ _ intermediateGoal_5212 5212 9203 9204
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5212_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5212 : (denoteGraph_ringAttn sm initSM 5212).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9203])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5213
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5212) :=
    ringAttn_reduce1_pm_opaque sm initSM 381
      { rank := 0, op := "OpName.FW_view", ins := [5212], outs := [5213], params := [4096, 512] }
      5212 5213 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5212 5213)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9213
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9203) :=
    ringAttn_reduce1_pm_opaque pm initPM 820
      { rank := 0, op := "OpName.FW_view", ins := [9203], outs := [9213], params := [2048, 512] }
      9203 9213 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9203 9213)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9214
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9204) :=
    ringAttn_reduce1_pm_opaque pm initPM 824
      { rank := 1, op := "OpName.FW_view", ins := [9204], outs := [9214], params := [2048, 512] }
      9204 9214 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9204 9214)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 9213 = denoteGraph_ringAttn pm initPM 9203 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9203]
  have h12 : denoteGraph_ringAttn pm initPM 9214 = denoteGraph_ringAttn pm initPM 9204 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9204]
  have hval : denoteGraph_ringAttn sm initSM 5213
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9213, denoteGraph_ringAttn pm initPM 9214] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5212, hval34, hnr, ← h11, ← h12]
  have hs9213 : (denoteGraph_ringAttn pm initPM 9213).shape = [2048, 512] := by rw [h11]; exact hs9203
  have hs9214 : (denoteGraph_ringAttn pm initPM 9214).shape = [2048, 512] := by rw [h12]; exact hs9204
  have hs5213 : (denoteGraph_ringAttn sm initSM 5213).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5212]; exact hs5212
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5213 5213 9213 9214 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5213 hs9213 hs9214

/-! ### L10 MoE gate/expert branch (`5205` sigmoid, `5214` swiglu, `5215` reshape,
    `5217` mixlin, `5218` view, `5219` broadcast-mul), all 2-tp shard-direct. -/

/-- 5205 — 2-tp `fw_sigmoid(5204)` → `[4096, 1]` (SM node 227, PM 514/517). -/
theorem recon_intermediateGoal_5205_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5205
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs9177, hs9178⟩ := twoTp_gather _ _ intermediateGoal_5204 5204 9177 9178
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5204_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5205 = fw_sigmoid (denoteGraph_ringAttn sm initSM 5204) :=
    ringAttn_reduce1_pm_opaque sm initSM 383
      { rank := 0, op := "OpName.FW_sigmoid", ins := [5204], outs := [5205] }
      5204 5205 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 5204 5205 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9179 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9177) :=
    ringAttn_reduce1_pm_opaque pm initPM 826
      { rank := 0, op := "OpName.FW_sigmoid", ins := [9177], outs := [9179] }
      9177 9179 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 9177 9179 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9180 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9178) :=
    ringAttn_reduce1_pm_opaque pm initPM 829
      { rank := 1, op := "OpName.FW_sigmoid", ins := [9178], outs := [9180] }
      9178 9180 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 9178 9180 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5205
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9179, denoteGraph_ringAttn pm initPM 9180] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs9177 hs9178, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5205).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs9177])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9179).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs9177
  have hsp1 : (denoteGraph_ringAttn pm initPM 9180).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs9178
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5205 5205 9179 9180 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5214 — 2-tp `fw_swiglu(5209, 5213)` → `[4096, 512]` (SM node 228, PM 515/518). -/
theorem recon_intermediateGoal_5214_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5214
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs9195, hs9196⟩ := twoTp_gather _ _ intermediateGoal_5209 5209 9195 9196
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5209_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs9213, hs9214⟩ := twoTp_gather _ _ intermediateGoal_5213 5213 9213 9214
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5213_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5214
      = fw_swiglu (denoteGraph_ringAttn sm initSM 5209) (denoteGraph_ringAttn sm initSM 5213) :=
    ringAttn_reduce2_pm_opaque sm initSM 384
      { rank := 0, op := "OpName.FW_swiglu", ins := [5209, 5213], outs := [5214] }
      5209 5213 5214 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 5209 5213 5214 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9217
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9195) (denoteGraph_ringAttn pm initPM 9213) :=
    ringAttn_reduce2_pm_opaque pm initPM 827
      { rank := 0, op := "OpName.FW_swiglu", ins := [9195, 9213], outs := [9217] }
      9195 9213 9217 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 9195 9213 9217 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9218
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9196) (denoteGraph_ringAttn pm initPM 9214) :=
    ringAttn_reduce2_pm_opaque pm initPM 830
      { rank := 1, op := "OpName.FW_swiglu", ins := [9196, 9214], outs := [9218] }
      9196 9214 9218 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 9196 9214 9218 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5214
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9217, denoteGraph_ringAttn pm initPM 9218] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs9195 hs9196 hs9213 hs9214,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5214).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9213])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9217).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9213
  have hsp1 : (denoteGraph_ringAttn pm initPM 9218).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs9214
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5214 5214 9217 9218 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5215 — 2-tp identity reshape of `5214` → `[4096, 512]` (SM node 229, PM 519/520). -/
theorem recon_intermediateGoal_5215_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5215
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs9217, hs9218⟩ := twoTp_gather _ _ intermediateGoal_5214 5214 9217 9218
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5214_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5214 : (denoteGraph_ringAttn sm initSM 5214).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs9217])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5215
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5214) :=
    ringAttn_reduce1_pm_opaque sm initSM 385
      { rank := 0, op := "OpName.FW_reshape", ins := [5214], outs := [5215], params := [4096, 512] }
      5214 5215 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5214 5215)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9219
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9217) :=
    ringAttn_reduce1_pm_opaque pm initPM 831
      { rank := 0, op := "OpName.FW_reshape", ins := [9217], outs := [9219], params := [2048, 512] }
      9217 9219 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9217 9219)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9220
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9218) :=
    ringAttn_reduce1_pm_opaque pm initPM 832
      { rank := 1, op := "OpName.FW_reshape", ins := [9218], outs := [9220], params := [2048, 512] }
      9218 9220 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9218 9220)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 9219 = denoteGraph_ringAttn pm initPM 9217 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs9217]
  have h18 : denoteGraph_ringAttn pm initPM 9220 = denoteGraph_ringAttn pm initPM 9218 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs9218]
  have hval : denoteGraph_ringAttn sm initSM 5215
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9219, denoteGraph_ringAttn pm initPM 9220] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5214, hval36, hnr, ← h17, ← h18]
  have hs9219 : (denoteGraph_ringAttn pm initPM 9219).shape = [2048, 512] := by rw [h17]; exact hs9217
  have hs9220 : (denoteGraph_ringAttn pm initPM 9220).shape = [2048, 512] := by rw [h18]; exact hs9218
  have hs5215 : (denoteGraph_ringAttn sm initSM 5215).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs5214]; exact hs5214
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5215 5215 9219 9220 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5215 hs9219 hs9220

/-- 5217 — 2-tp `fw_linear(5215, 5216)`, weight `5216 : [1024, 512]` → `[4096, 1024]`
    (SM node 230, PM 521/522). -/
theorem recon_intermediateGoal_5217_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5217
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs9219, hs9220⟩ := twoTp_gather _ _ intermediateGoal_5215 5215 9219 9220
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5215_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5216 : denoteGraph_ringAttn sm initSM 5216 = denoteGraph_ringAttn pm initPM 5216 :=
    veq_weight_ring initSM initPM hInit initGoal_5216 (by native_decide) 5216
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw5216 : (denoteGraph_ringAttn pm initPM 5216).shape = [1024, 512] := by
    rw [← hw5216]
    exact shape_weight_ring initSM initPM hInit initGoal_5216 (by native_decide) 5216 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5217
      = fw_linear (denoteGraph_ringAttn sm initSM 5215) (denoteGraph_ringAttn sm initSM 5216) :=
    ringAttn_reduce2_pm_opaque sm initSM 386
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5215, 5216], outs := [5217] }
      5215 5216 5217 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5215 5216 5217)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9225
      = fw_linear (denoteGraph_ringAttn pm initPM 9219) (denoteGraph_ringAttn pm initPM 5216) :=
    ringAttn_reduce2_pm_opaque pm initPM 833
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9219, 5216], outs := [9225] }
      9219 5216 9225 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9219 5216 9225)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9226
      = fw_linear (denoteGraph_ringAttn pm initPM 9220) (denoteGraph_ringAttn pm initPM 5216) :=
    ringAttn_reduce2_pm_opaque pm initPM 834
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9220, 5216], outs := [9226] }
      9220 5216 9226 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9220 5216 9226)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5217
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9225, denoteGraph_ringAttn pm initPM 9226] := by
    rw [rSM, hval37, hw5216, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs9219 hs9220 hpw5216,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9225).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9219 hpw5216
  have hsp1 : (denoteGraph_ringAttn pm initPM 9226).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9220 hpw5216
  have hshape : (denoteGraph_ringAttn sm initSM 5217).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5217 5217 9225 9226 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5218 — 2-tp identity view of `5217` → `[4096, 1024]` (SM node 231, PM 523/524). -/
theorem recon_intermediateGoal_5218_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5218
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs9225, hs9226⟩ := twoTp_gather _ _ intermediateGoal_5217 5217 9225 9226
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5217_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5217 : (denoteGraph_ringAttn sm initSM 5217).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs9225])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 5218
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5217) :=
    ringAttn_reduce1_pm_opaque sm initSM 387
      { rank := 0, op := "OpName.FW_view", ins := [5217], outs := [5218], params := [4096, 1024] }
      5217 5218 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5217 5218)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9235
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9225) :=
    ringAttn_reduce1_pm_opaque pm initPM 835
      { rank := 0, op := "OpName.FW_view", ins := [9225], outs := [9235], params := [2048, 1024] }
      9225 9235 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9225 9235)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9236
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9226) :=
    ringAttn_reduce1_pm_opaque pm initPM 836
      { rank := 1, op := "OpName.FW_view", ins := [9226], outs := [9236], params := [2048, 1024] }
      9226 9236 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9226 9236)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 9235 = denoteGraph_ringAttn pm initPM 9225 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs9225]
  have h34 : denoteGraph_ringAttn pm initPM 9236 = denoteGraph_ringAttn pm initPM 9226 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs9226]
  have hval : denoteGraph_ringAttn sm initSM 5218
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9235, denoteGraph_ringAttn pm initPM 9236] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5217, hval39, hnr, ← h33, ← h34]
  have hs9235 : (denoteGraph_ringAttn pm initPM 9235).shape = [2048, 1024] := by rw [h33]; exact hs9225
  have hs9236 : (denoteGraph_ringAttn pm initPM 9236).shape = [2048, 1024] := by rw [h34]; exact hs9226
  have hs5218 : (denoteGraph_ringAttn sm initSM 5218).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs5217]; exact hs5217
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5218 5218 9235 9236 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs5218 hs9235 hs9236

/-- 5219 — 2-tp broadcast `mul(5205, 5218)` → `[4096, 1024]` (SM node 232, PM 525/526). -/
theorem recon_intermediateGoal_5219_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5219
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_5205 5205 9179 9180
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5205_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_5218 5218 9235 9236
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5218_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5219
      = elemwiseMul (denoteGraph_ringAttn sm initSM 5205) (denoteGraph_ringAttn sm initSM 5218) :=
    ringAttn_reduce2_pm_opaque sm initSM 388
      { rank := 0, op := "OpName.FW_mul", ins := [5205, 5218], outs := [5219] }
      5205 5218 5219 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 5205 5218 5219)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9239
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9179) (denoteGraph_ringAttn pm initPM 9235) :=
    ringAttn_reduce2_pm_opaque pm initPM 837
      { rank := 0, op := "OpName.FW_mul", ins := [9179, 9235], outs := [9239] }
      9179 9235 9239 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 9179 9235 9239)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9240
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9180) (denoteGraph_ringAttn pm initPM 9236) :=
    ringAttn_reduce2_pm_opaque pm initPM 838
      { rank := 1, op := "OpName.FW_mul", ins := [9180, 9236], outs := [9240] }
      9180 9236 9240 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 9180 9236 9240)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5219
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9239, denoteGraph_ringAttn pm initPM 9240] := by
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
  have hshape : (denoteGraph_ringAttn sm initSM 5219).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 5205).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 5218).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 9239).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 9240).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5219 5219 9239 9240 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 5200 — layer-10 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 5200 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`9165`), rank 1 →
    `[32, 64)` (`9166`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `9157`/`9158` are expert-local (the
    `wf5200_hdisjA/B` fields).  Token input `7887 = mref5-pos1(5191)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 226, PM nodes 513/516). -/
theorem recon_intermediateGoal_5200_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5200
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 8289 = mref5-pos1(5191).
  obtain ⟨hbr13, hs9145, hs9146⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8289 : denoteGraph_ringAttn sm initSM 7887 = id (denoteGraph_ringAttn sm initSM 5191) :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191],
        outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7887 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15494 : denoteGraph_ringAttn pm initPM 15494 = id (denoteGraph_ringAttn pm initPM 9145) :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145],
        outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15494 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15517 : denoteGraph_ringAttn pm initPM 15517 = id (denoteGraph_ringAttn pm initPM 9146) :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146],
        outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15517 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8289 p15494 p15517
  have hsInA : (denoteGraph_ringAttn pm initPM 15494).shape = [2048, 1024] := by
    rw [p15494]; exact hs9145
  have hsInB : (denoteGraph_ringAttn pm initPM 15517).shape = [2048, 1024] := by
    rw [p15517]; exact hs9146
  have hbrIn : denoteGraph_ringAttn sm initSM 7887
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 15494, denoteGraph_ringAttn pm initPM 15517] := by
    rw [s8289, hbr13, hnr, ← p15494, ← p15517]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_5195 5195 9155 9156
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5195_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_5196 5196 9157 9158
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5196_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 5195
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9155, denoteGraph_ringAttn pm initPM 9156] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 5196
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9157, denoteGraph_ringAttn pm initPM 9158] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_5198
    (by native_decide) 5198 9161 9162 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_5199
    (by native_decide) 5199 9163 9164 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 9161).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5198 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5198, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9161 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 9162).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5198 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5198, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9162 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 9163).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5199 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5199, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9163 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 9164).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5199 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5199, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9164 (by native_decide)]; exact hs.2
  -- SM 5200 = full-range all2all (SM node 226).
  have hSMout : denoteGraph_ringAttn sm initSM 5200
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7887)
          (denoteGraph_ringAttn sm initSM 5195) (denoteGraph_ringAttn sm initSM 5196)
          (denoteGraph_ringAttn sm initSM 5198) (denoteGraph_ringAttn sm initSM 5199)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 382
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7887, 5195, 5196, 5198, 5199],
        outs := [5200], params := [64, 0, 64, 8] }
      7887 5195 5196 5198 5199 5200
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7887 5195 5196 5198 5199 5200 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9165 = rank-0 sharded-range all2all (PM node 513).
  have hP0 : denoteGraph_ringAttn pm initPM 9165
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15494)
          (denoteGraph_ringAttn pm initPM 9155) (denoteGraph_ringAttn pm initPM 9157)
          (denoteGraph_ringAttn pm initPM 9161) (denoteGraph_ringAttn pm initPM 9163)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 825
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15494, 9155, 9157, 9161, 9163],
        outs := [9165], params := [64, 0, 32, 8] }
      15494 9155 9157 9161 9163 9165
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 15494 9155 9157 9161 9163 9165 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9166 = rank-1 sharded-range all2all (PM node 516).
  have hP1 : denoteGraph_ringAttn pm initPM 9166
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 15517)
          (denoteGraph_ringAttn pm initPM 9156) (denoteGraph_ringAttn pm initPM 9158)
          (denoteGraph_ringAttn pm initPM 9162) (denoteGraph_ringAttn pm initPM 9164)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 828
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15517, 9156, 9158, 9162, 9164],
        outs := [9166], params := [64, 32, 64, 8] }
      15517 9156 9158 9162 9164 9166
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 15517 9156 9158 9162 9164 9166 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 15494) (denoteGraph_ringAttn pm initPM 15517)
      (denoteGraph_ringAttn pm initPM 9155) (denoteGraph_ringAttn pm initPM 9156)
      (denoteGraph_ringAttn pm initPM 9157) (denoteGraph_ringAttn pm initPM 9158)
      (denoteGraph_ringAttn pm initPM 9161) (denoteGraph_ringAttn pm initPM 9162)
      (denoteGraph_ringAttn pm initPM 9163) (denoteGraph_ringAttn pm initPM 9164)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf5200_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf5200_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 5200
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9165, denoteGraph_ringAttn pm initPM 9166] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9165).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9166).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 5200).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5200 5200 9165 9166 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L10 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7876 — second position of the L10 pre-MoE residual `mref2(5189)` (2-tp, PM
    shards `15475`/`15483`).  Unlike L2's `7824` there is no gather-to-full/chunk
    because `5189` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 211, PM nodes 477/478). -/
theorem recon_intermediateGoal_7876_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7876
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs9141, hs9142⟩ := twoTp_gather _ _ intermediateGoal_5189 5189 9141 9142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5189_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8144 : denoteGraph_ringAttn sm initSM 7876 = id (denoteGraph_ringAttn sm initSM 5189) :=
    ringAttn_reduce1_pm_opaque sm initSM 367
      { rank := 0, op := "OpName.FW_multiref", ins := [5189], outs := [7872, 7876], params := [2] }
      5189 7876 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5189 7872 7876 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15475 : denoteGraph_ringAttn pm initPM 15475 = id (denoteGraph_ringAttn pm initPM 9141) :=
    ringAttn_reduce1_pm_opaque pm initPM 795
      { rank := 0, op := "OpName.FW_multiref", ins := [9141], outs := [15471, 15475], params := [2] }
      9141 15475 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9141 15471 15475 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15483 : denoteGraph_ringAttn pm initPM 15483 = id (denoteGraph_ringAttn pm initPM 9142) :=
    ringAttn_reduce1_pm_opaque pm initPM 796
      { rank := 1, op := "OpName.FW_multiref", ins := [9142], outs := [15479, 15483], params := [2] }
      9142 15483 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9142 15479 15483 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8144 p15475 p15483
  have hsp0 : (denoteGraph_ringAttn pm initPM 15475).shape = [2048, 1024] := by
    rw [p15475]; exact hs9141
  have hsp1 : (denoteGraph_ringAttn pm initPM 15483).shape = [2048, 1024] := by
    rw [p15483]; exact hs9142
  have hval : denoteGraph_ringAttn sm initSM 7876
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15475, denoteGraph_ringAttn pm initPM 15483] := by
    rw [s8144, hbr11, ← p15475, ← p15483]
  have hshape : (denoteGraph_ringAttn sm initSM 7876).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7876 7876 15475 15483 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5220 — post-MoE residual add `5200 + 5219` (2-tp, PM `9243`/`9244`). -/
theorem recon_intermediateGoal_5220_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5220
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs9165, hs9166⟩ := twoTp_gather _ _ intermediateGoal_5200 5200 9165 9166
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5200_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs9239, hs9240⟩ := twoTp_gather _ _ intermediateGoal_5219 5219 9239 9240
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5219_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5220
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 5200) (denoteGraph_ringAttn sm initSM 5219) :=
    ringAttn_reduce2_pm_opaque sm initSM 389
      { rank := 0, op := "OpName.FW_add", ins := [5200, 5219], outs := [5220] }
      5200 5219 5220 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 5200 5219 5220)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9243
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9165) (denoteGraph_ringAttn pm initPM 9239) :=
    ringAttn_reduce2_pm_opaque pm initPM 839
      { rank := 0, op := "OpName.FW_add", ins := [9165, 9239], outs := [9243] }
      9165 9239 9243 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 9165 9239 9243)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9244
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9166) (denoteGraph_ringAttn pm initPM 9240) :=
    ringAttn_reduce2_pm_opaque pm initPM 840
      { rank := 1, op := "OpName.FW_add", ins := [9166, 9240], outs := [9244] }
      9166 9240 9244 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 9166 9240 9244)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5220
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9243, denoteGraph_ringAttn pm initPM 9244] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs9165 hs9166 hs9239 hs9240,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9243).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9165 hs9239
  have hsp1 : (denoteGraph_ringAttn pm initPM 9244).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9166 hs9240
  have hshape : (denoteGraph_ringAttn sm initSM 5220).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5220 5220 9243 9244 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5221 — `FW_float(5220)` (identity, 2-tp PM `9249`/`9250`). -/
theorem recon_intermediateGoal_5221_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5221
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs9243, hs9244⟩ := twoTp_gather _ _ intermediateGoal_5220 5220 9243 9244
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5220_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5221 = id (denoteGraph_ringAttn sm initSM 5220) :=
    ringAttn_reduce1_pm_opaque sm initSM 390
      { rank := 0, op := "OpName.FW_float", ins := [5220], outs := [5221] }
      5220 5221 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5220 5221 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9249 = id (denoteGraph_ringAttn pm initPM 9243) :=
    ringAttn_reduce1_pm_opaque pm initPM 841
      { rank := 0, op := "OpName.FW_float", ins := [9243], outs := [9249] }
      9243 9249 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9243 9249 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9250 = id (denoteGraph_ringAttn pm initPM 9244) :=
    ringAttn_reduce1_pm_opaque pm initPM 842
      { rank := 1, op := "OpName.FW_float", ins := [9244], outs := [9250] }
      9244 9250 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9244 9250 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5221
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9249, denoteGraph_ringAttn pm initPM 9250] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9249).shape = [2048, 1024] := by rw [rP0]; exact hs9243
  have hsp1 : (denoteGraph_ringAttn pm initPM 9250).shape = [2048, 1024] := by rw [rP1]; exact hs9244
  have hshape : (denoteGraph_ringAttn sm initSM 5221).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5221 5221 9249 9250 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5222 — cross-block residual add `7876 + 5221` (2-tp, PM `9253`/`9254`). -/
theorem recon_intermediateGoal_5222_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5222
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs15475, hs15483⟩ := twoTp_gather _ _ intermediateGoal_7876 7876 15475 15483
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7876_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs9249, hs9250⟩ := twoTp_gather _ _ intermediateGoal_5221 5221 9249 9250
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5221_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5222
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7876) (denoteGraph_ringAttn sm initSM 5221) :=
    ringAttn_reduce2_pm_opaque sm initSM 391
      { rank := 0, op := "OpName.FW_add", ins := [7876, 5221], outs := [5222] }
      7876 5221 5222 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7876 5221 5222)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9253
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15475) (denoteGraph_ringAttn pm initPM 9249) :=
    ringAttn_reduce2_pm_opaque pm initPM 843
      { rank := 0, op := "OpName.FW_add", ins := [15475, 9249], outs := [9253] }
      15475 9249 9253 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15475 9249 9253)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9254
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15483) (denoteGraph_ringAttn pm initPM 9250) :=
    ringAttn_reduce2_pm_opaque pm initPM 844
      { rank := 1, op := "OpName.FW_add", ins := [15483, 9250], outs := [9254] }
      15483 9250 9254 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15483 9250 9254)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5222
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9253, denoteGraph_ringAttn pm initPM 9254] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15475 hs15483 hs9249 hs9250,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9253).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15475 hs9249
  have hsp1 : (denoteGraph_ringAttn pm initPM 9254).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15483 hs9250
  have hshape : (denoteGraph_ringAttn sm initSM 5222).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5222 5222 9253 9254 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5224 — RMSNorm of `mref2-first(5222)` with replicated weight `5223`
    (2-tp, PM `9257`/`9258`). -/
theorem recon_intermediateGoal_5224_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5224
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs9253, hs9254⟩ := twoTp_gather _ _ intermediateGoal_5222 5222 9253 9254
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5222_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8305 : denoteGraph_ringAttn sm initSM 7903 = id (denoteGraph_ringAttn sm initSM 5222) :=
    ringAttn_reduce1_pm_opaque sm initSM 392
      { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907], params := [2] }
      5222 7903 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5222 7903 7907)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15533 : denoteGraph_ringAttn pm initPM 15533 = id (denoteGraph_ringAttn pm initPM 9253) :=
    ringAttn_reduce1_pm_opaque pm initPM 845
      { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537], params := [2] }
      9253 15533 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9253 15533 15537)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15541 : denoteGraph_ringAttn pm initPM 15541 = id (denoteGraph_ringAttn pm initPM 9254) :=
    ringAttn_reduce1_pm_opaque pm initPM 846
      { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545], params := [2] }
      9254 15541 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9254 15541 15545)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8305 p15533 p15541
  have hs15533 : (denoteGraph_ringAttn pm initPM 15533).shape = [2048, 1024] := by
    rw [p15533]; exact hs9253
  have hs15541 : (denoteGraph_ringAttn pm initPM 15541).shape = [2048, 1024] := by
    rw [p15541]; exact hs9254
  have hbr39 : denoteGraph_ringAttn sm initSM 7903
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15533, denoteGraph_ringAttn pm initPM 15541] := by
    rw [s8305, hbr44, ← p15533, ← p15541]
  have hw5223 : denoteGraph_ringAttn sm initSM 5223 = denoteGraph_ringAttn pm initPM 5223 :=
    veq_weight_ring initSM initPM hInit initGoal_5223 (by native_decide) 5223
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5224
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7903) (denoteGraph_ringAttn sm initSM 5223) :=
    ringAttn_reduce2_pm_opaque sm initSM 393
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7903, 5223], outs := [5224] }
      7903 5223 5224 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7903 5223 5224)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9257
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15533) (denoteGraph_ringAttn pm initPM 5223) :=
    ringAttn_reduce2_pm_opaque pm initPM 847
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15533, 5223], outs := [9257] }
      15533 5223 9257 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15533 5223 9257)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9258
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15541) (denoteGraph_ringAttn pm initPM 5223) :=
    ringAttn_reduce2_pm_opaque pm initPM 848
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15541, 5223], outs := [9258] }
      15541 5223 9258 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15541 5223 9258)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5224
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9257, denoteGraph_ringAttn pm initPM 9258] := by
    rw [rSM, hbr39, hw5223, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15533 hs15541,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9257).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15533
  have hsp1 : (denoteGraph_ringAttn pm initPM 9258).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15541
  have hshape : (denoteGraph_ringAttn sm initSM 5224).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5224 5224 9257 9258 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5226 — per-head Q projection `fw_per_head_linear(mref3₀(5224), 5225)`
    (2-tp, PM `9259`/`9260`, weight `5225 : [16,64,1024]`). -/
theorem recon_intermediateGoal_5226_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5226
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9257, hs9258⟩ := twoTp_gather _ _ intermediateGoal_5224 5224 9257 9258
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5224_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8314 : denoteGraph_ringAttn sm initSM 7912 = id (denoteGraph_ringAttn sm initSM 5224) :=
    ringAttn_reduce1_pm_opaque sm initSM 394
      { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
      5224 7912 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5224 7912 7916 7920)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15550 : denoteGraph_ringAttn pm initPM 15550 = id (denoteGraph_ringAttn pm initPM 9257) :=
    ringAttn_reduce1_pm_opaque pm initPM 849
      { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
      9257 15550 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 9257 15550 15554 15558)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15563 : denoteGraph_ringAttn pm initPM 15563 = id (denoteGraph_ringAttn pm initPM 9258) :=
    ringAttn_reduce1_pm_opaque pm initPM 850
      { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
      9258 15563 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 9258 15563 15567 15571)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8314 p15550 p15563
  have hs15550 : (denoteGraph_ringAttn pm initPM 15550).shape = [2048, 1024] := by
    rw [p15550]; exact hs9257
  have hs15563 : (denoteGraph_ringAttn pm initPM 15563).shape = [2048, 1024] := by
    rw [p15563]; exact hs9258
  have hbr48 : denoteGraph_ringAttn sm initSM 7912
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15550, denoteGraph_ringAttn pm initPM 15563] := by
    rw [s8314, hbr46, ← p15550, ← p15563]
  have hw5225 : denoteGraph_ringAttn sm initSM 5225 = denoteGraph_ringAttn pm initPM 5225 :=
    veq_weight_ring initSM initPM hInit initGoal_5225 (by native_decide) 5225
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5225 : (denoteGraph_ringAttn sm initSM 5225).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5225 (by native_decide) 5225 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5225 : (denoteGraph_ringAttn pm initPM 5225).shape = [16, 64, 1024] := by
    rw [← hw5225]; exact hsw5225
  have rSM : denoteGraph_ringAttn sm initSM 5226
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7912) (denoteGraph_ringAttn sm initSM 5225) :=
    ringAttn_reduce2_pm_opaque sm initSM 395
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7912, 5225], outs := [5226] }
      7912 5225 5226 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7912 5225 5226 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9259
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15550) (denoteGraph_ringAttn pm initPM 5225) :=
    ringAttn_reduce2_pm_opaque pm initPM 851
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15550, 5225], outs := [9259] }
      15550 5225 9259 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15550 5225 9259 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9260
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15563) (denoteGraph_ringAttn pm initPM 5225) :=
    ringAttn_reduce2_pm_opaque pm initPM 854
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15563, 5225], outs := [9260] }
      15563 5225 9260 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15563 5225 9260 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5226
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9259, denoteGraph_ringAttn pm initPM 9260] := by
    rw [rSM, hbr48, hw5225, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs15550 hs15563 hpw5225,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9259).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15550 hpw5225
  have hsp1 : (denoteGraph_ringAttn pm initPM 9260).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs15563 hpw5225
  have hshape : (denoteGraph_ringAttn sm initSM 5226).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5226 5226 9259 9260 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5228 — per-head K projection `fw_per_head_linear(mref3₁(5224), 5227)`
    (2-tp, PM `9271`/`9272`, weight `5227 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5228_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5228
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9257, hs9258⟩ := twoTp_gather _ _ intermediateGoal_5224 5224 9257 9258
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5224_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8184 : denoteGraph_ringAttn sm initSM 7916 = id (denoteGraph_ringAttn sm initSM 5224) :=
    ringAttn_reduce1_pm_opaque sm initSM 394
      { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
      5224 7916 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5224 7912 7916 7920 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15554 : denoteGraph_ringAttn pm initPM 15554 = id (denoteGraph_ringAttn pm initPM 9257) :=
    ringAttn_reduce1_pm_opaque pm initPM 849
      { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
      9257 15554 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 9257 15550 15554 15558 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15567 : denoteGraph_ringAttn pm initPM 15567 = id (denoteGraph_ringAttn pm initPM 9258) :=
    ringAttn_reduce1_pm_opaque pm initPM 850
      { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
      9258 15567 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 9258 15563 15567 15571 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8184 p15554 p15567
  have hs15554 : (denoteGraph_ringAttn pm initPM 15554).shape = [2048, 1024] := by
    rw [p15554]; exact hs9257
  have hs15567 : (denoteGraph_ringAttn pm initPM 15567).shape = [2048, 1024] := by
    rw [p15567]; exact hs9258
  have hbr52 : denoteGraph_ringAttn sm initSM 7916
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15554, denoteGraph_ringAttn pm initPM 15567] := by
    rw [s8184, hbr46, ← p15554, ← p15567]
  have hw5227 : denoteGraph_ringAttn sm initSM 5227 = denoteGraph_ringAttn pm initPM 5227 :=
    veq_weight_ring initSM initPM hInit initGoal_5227 (by native_decide) 5227
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5227 : (denoteGraph_ringAttn sm initSM 5227).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5227 (by native_decide) 5227 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5227 : (denoteGraph_ringAttn pm initPM 5227).shape = [4, 64, 1024] := by
    rw [← hw5227]; exact hsw5227
  have rSM : denoteGraph_ringAttn sm initSM 5228
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7916) (denoteGraph_ringAttn sm initSM 5227) :=
    ringAttn_reduce2_pm_opaque sm initSM 396
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7916, 5227], outs := [5228] }
      7916 5227 5228 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7916 5227 5228 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9271
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15554) (denoteGraph_ringAttn pm initPM 5227) :=
    ringAttn_reduce2_pm_opaque pm initPM 852
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15554, 5227], outs := [9271] }
      15554 5227 9271 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15554 5227 9271 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9272
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15567) (denoteGraph_ringAttn pm initPM 5227) :=
    ringAttn_reduce2_pm_opaque pm initPM 855
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15567, 5227], outs := [9272] }
      15567 5227 9272 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15567 5227 9272 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5228
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9271, denoteGraph_ringAttn pm initPM 9272] := by
    rw [rSM, hbr52, hw5227, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15554 hs15567 hpw5227,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9271).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15554 hpw5227
  have hsp1 : (denoteGraph_ringAttn pm initPM 9272).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15567 hpw5227
  have hshape : (denoteGraph_ringAttn sm initSM 5228).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5228 5228 9271 9272 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5230 — per-head V projection `fw_per_head_linear(mref3₂(5224), 5229)`
    (2-tp, PM `9281`/`9282`, weight `5229 : [4,64,1024]`). -/
theorem recon_intermediateGoal_5230_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5230
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs9257, hs9258⟩ := twoTp_gather _ _ intermediateGoal_5224 5224 9257 9258
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5224_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7920 : denoteGraph_ringAttn sm initSM 7920 = id (denoteGraph_ringAttn sm initSM 5224) :=
    ringAttn_reduce1_pm_opaque sm initSM 394
      { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
      5224 7920 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5224 7912 7916 7920 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15558 : denoteGraph_ringAttn pm initPM 15558 = id (denoteGraph_ringAttn pm initPM 9257) :=
    ringAttn_reduce1_pm_opaque pm initPM 849
      { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
      9257 15558 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 9257 15550 15554 15558 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15571 : denoteGraph_ringAttn pm initPM 15571 = id (denoteGraph_ringAttn pm initPM 9258) :=
    ringAttn_reduce1_pm_opaque pm initPM 850
      { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
      9258 15571 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 9258 15563 15567 15571 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7920 p15558 p15571
  have hs15558 : (denoteGraph_ringAttn pm initPM 15558).shape = [2048, 1024] := by
    rw [p15558]; exact hs9257
  have hs15571 : (denoteGraph_ringAttn pm initPM 15571).shape = [2048, 1024] := by
    rw [p15571]; exact hs9258
  have hbr56 : denoteGraph_ringAttn sm initSM 7920
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15558, denoteGraph_ringAttn pm initPM 15571] := by
    rw [s7920, hbr46, ← p15558, ← p15571]
  have hw5229 : denoteGraph_ringAttn sm initSM 5229 = denoteGraph_ringAttn pm initPM 5229 :=
    veq_weight_ring initSM initPM hInit initGoal_5229 (by native_decide) 5229
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5229 : (denoteGraph_ringAttn sm initSM 5229).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5229 (by native_decide) 5229 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5229 : (denoteGraph_ringAttn pm initPM 5229).shape = [4, 64, 1024] := by
    rw [← hw5229]; exact hsw5229
  have rSM : denoteGraph_ringAttn sm initSM 5230
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7920) (denoteGraph_ringAttn sm initSM 5229) :=
    ringAttn_reduce2_pm_opaque sm initSM 397
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7920, 5229], outs := [5230] }
      7920 5229 5230 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7920 5229 5230 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9281
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15558) (denoteGraph_ringAttn pm initPM 5229) :=
    ringAttn_reduce2_pm_opaque pm initPM 853
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15558, 5229], outs := [9281] }
      15558 5229 9281 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 15558 5229 9281 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9282
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 15571) (denoteGraph_ringAttn pm initPM 5229) :=
    ringAttn_reduce2_pm_opaque pm initPM 856
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15571, 5229], outs := [9282] }
      15571 5229 9282 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 15571 5229 9282 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5230
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9281, denoteGraph_ringAttn pm initPM 9282] := by
    rw [rSM, hbr56, hw5229, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs15558 hs15571 hpw5229,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9281).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15558 hpw5229
  have hsp1 : (denoteGraph_ringAttn pm initPM 9282).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs15571 hpw5229
  have hshape : (denoteGraph_ringAttn sm initSM 5230).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5230 5230 9281 9282 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L10 rotary cos/sin cache agreement: `sm 4691 = pm 11863` (`= 11853 + 3`). -/
theorem hcache_4691_11863 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11863 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11863 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11863 10 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 5232 — rotary-embedding Q output `rotary(4691, 5231, 5226, 5228).1`
    (2-tp, PM `9293`/`9294`; positions `5231 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_5232_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5232
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs9259, hs9260⟩ := twoTp_gather _ _ intermediateGoal_5226 5226 9259 9260
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5226_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_5228 5228 9271 9272
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5228_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11863 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5231 = denoteGraph_ringAttn pm initPM 5231 :=
    veq_weight_ring initSM initPM hInit initGoal_5231 (by native_decide) 5231
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5231 : (denoteGraph_ringAttn sm initSM 5231).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5231 (by native_decide) 5231 [4096]
      rfl rfl (by native_decide)
  have c9291 : denoteGraph_ringAttn pm initPM 9291
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5231) :=
    ringAttn_reduce1_pm_opaque pm initPM 10
      { rank := 0, op := "OpName.ChunkPrim", ins := [5231], outs := [9291], params := [0] }
      5231 9291 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5231 9291 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c9292 : denoteGraph_ringAttn pm initPM 9292
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5231) :=
    ringAttn_reduce1_pm_opaque pm initPM 23
      { rank := 1, op := "OpName.ChunkPrim", ins := [5231], outs := [9292], params := [0] }
      5231 9292 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5231 9292 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5232
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5231)
          (denoteGraph_ringAttn sm initSM 5226) (denoteGraph_ringAttn sm initSM 5228) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 398
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5231, 5226, 5228], outs := [5232, 5233], params := [16, 4] }
          5232 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 398 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 398 5231 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 398 5226 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 398 5228 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 9293
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11863) (denoteGraph_ringAttn pm initPM 9291)
          (denoteGraph_ringAttn pm initPM 9259) (denoteGraph_ringAttn pm initPM 9271) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 857
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11863, 9291, 9259, 9271], outs := [9293, 9295], params := [16, 4] }
          9293 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 857 11863 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 857 9291 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 857 9259 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 857 9271 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 9294
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11863) (denoteGraph_ringAttn pm initPM 9292)
          (denoteGraph_ringAttn pm initPM 9260) (denoteGraph_ringAttn pm initPM 9272) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 858
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11863, 9292, 9260, 9272], outs := [9294, 9296], params := [16, 4] }
          9294 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 858 11863 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 858 9292 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 858 9260 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 858 9272 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5232
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9293, denoteGraph_ringAttn pm initPM 9294] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5231) (denoteGraph_ringAttn pm initPM 9259)
          (denoteGraph_ringAttn pm initPM 9260) 2048 16 64 (by omega) (by omega) (by omega)
          hsp5231 hs9259 hs9260,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 9291
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5231) from c9291),
        ← (show denoteGraph_ringAttn pm initPM 9292
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5231) from c9292),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9293).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs9259
  have hsp1 : (denoteGraph_ringAttn pm initPM 9294).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs9260
  have hshape : (denoteGraph_ringAttn sm initSM 5232).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5232 5232 9293 9294 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 5233 — rotary-embedding K output `rotary(4691, 5231, 5226, 5228).2`
    (2-tp, PM `9295`/`9296`). -/
theorem recon_intermediateGoal_5233_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5233
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_5226 5226 9259 9260
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5226_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs9271, hs9272⟩ := twoTp_gather _ _ intermediateGoal_5228 5228 9271 9272
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5228_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11863 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 5231 = denoteGraph_ringAttn pm initPM 5231 :=
    veq_weight_ring initSM initPM hInit initGoal_5231 (by native_decide) 5231
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp5231 : (denoteGraph_ringAttn sm initSM 5231).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_5231 (by native_decide) 5231 [4096]
      rfl rfl (by native_decide)
  have c9291 : denoteGraph_ringAttn pm initPM 9291
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 5231) :=
    ringAttn_reduce1_pm_opaque pm initPM 10
      { rank := 0, op := "OpName.ChunkPrim", ins := [5231], outs := [9291], params := [0] }
      5231 9291 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 5231 9291 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c9292 : denoteGraph_ringAttn pm initPM 9292
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 5231) :=
    ringAttn_reduce1_pm_opaque pm initPM 23
      { rank := 1, op := "OpName.ChunkPrim", ins := [5231], outs := [9292], params := [0] }
      5231 9292 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 5231 9292 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5233
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 5231)
          (denoteGraph_ringAttn sm initSM 5226) (denoteGraph_ringAttn sm initSM 5228) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 398
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5231, 5226, 5228], outs := [5232, 5233], params := [16, 4] }
          5233 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5231 5226 5228 5232 5233 (by decide),
        ringAttn_prefix_read_pm sm initSM 398 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 398 5231 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 398 5226 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 398 5228 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 9295
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11863) (denoteGraph_ringAttn pm initPM 9291)
          (denoteGraph_ringAttn pm initPM 9259) (denoteGraph_ringAttn pm initPM 9271) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 857
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11863, 9291, 9259, 9271], outs := [9293, 9295], params := [16, 4] }
          9295 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11863 9291 9259 9271 9293 9295 (by decide),
        ringAttn_prefix_read_pm pm initPM 857 11863 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 857 9291 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 857 9259 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 857 9271 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 9296
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11863) (denoteGraph_ringAttn pm initPM 9292)
          (denoteGraph_ringAttn pm initPM 9260) (denoteGraph_ringAttn pm initPM 9272) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 858
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11863, 9292, 9260, 9272], outs := [9294, 9296], params := [16, 4] }
          9296 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11863 9292 9260 9272 9294 9296 (by decide),
        ringAttn_prefix_read_pm pm initPM 858 11863 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 858 9292 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 858 9260 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 858 9272 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 5233
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9295, denoteGraph_ringAttn pm initPM 9296] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 5231) (denoteGraph_ringAttn pm initPM 9271)
          (denoteGraph_ringAttn pm initPM 9272) 2048 4 64 (by omega) (by omega) (by omega)
          hsp5231 hs9271 hs9272,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 9291
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 5231) from c9291),
        ← (show denoteGraph_ringAttn pm initPM 9292
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 5231) from c9292),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9295).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs9271
  have hsp1 : (denoteGraph_ringAttn pm initPM 9296).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs9272
  have hshape : (denoteGraph_ringAttn sm initSM 5233).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5233 5233 9295 9296 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
