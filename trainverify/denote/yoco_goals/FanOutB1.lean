import denote.yoco_goals.ZigzagL11Body
import denote.yoco_goals.RingAttnLineageGoals

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 7487 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4790`.
    Identity alias: `7487` reconstructs exactly as `4790` (allGather of its shards). -/
theorem recon_intermediateGoal_7487_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7487
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4790 4790 7765 7766
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4790_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7487 = denoteGraph_ringAttn sm initSM 4790 :=
    ringAttn_reduce1_pm_opaque sm initSM 80
      { rank := 0, op := "OpName.FW_multiref", ins := [4790], outs := [7487, 7491], params := [2] }
      4790 7487 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4790 7487 7491)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14701 = denoteGraph_ringAttn pm initPM 7765 :=
    ringAttn_reduce1_pm_opaque pm initPM 221
      { rank := 0, op := "OpName.FW_multiref", ins := [7765], outs := [14701, 14705], params := [2] }
      7765 14701 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 7765 14701 14705)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14709 = denoteGraph_ringAttn pm initPM 7766 :=
    ringAttn_reduce1_pm_opaque pm initPM 222
      { rank := 1, op := "OpName.FW_multiref", ins := [7766], outs := [14709, 14713], params := [2] }
      7766 14709 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 7766 14709 14713)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7487
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14701, denoteGraph_ringAttn pm initPM 14709] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14701).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14709).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7487).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7487 7487 14701 14709 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7519 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4813`.
    Identity alias: `7519` reconstructs exactly as `4813` (allGather of its shards). -/
theorem recon_intermediateGoal_7519_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7519
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7519 = denoteGraph_ringAttn sm initSM 4813 :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7519 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 4813 7519 7523 7527 7531 7535)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14762 = denoteGraph_ringAttn pm initPM 7843 :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14762 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 7843 14762 14766 14770 14774 14778)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14785 = denoteGraph_ringAttn pm initPM 7844 :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14785 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 7844 14785 14789 14793 14797 14801)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7519
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14762, denoteGraph_ringAttn pm initPM 14785] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14762).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14785).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7519).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7519 7519 14762 14785 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7539 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4844`.
    Identity alias: `7539` reconstructs exactly as `4844` (allGather of its shards). -/
theorem recon_intermediateGoal_7539_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7539
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4844 4844 7951 7952
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4844_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7539 = denoteGraph_ringAttn sm initSM 4844 :=
    ringAttn_reduce1_pm_opaque sm initSM 119
      { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543], params := [2] }
      4844 7539 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4844 7539 7543)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14805 = denoteGraph_ringAttn pm initPM 7951 :=
    ringAttn_reduce1_pm_opaque pm initPM 299
      { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809], params := [2] }
      7951 14805 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 7951 14805 14809)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14813 = denoteGraph_ringAttn pm initPM 7952 :=
    ringAttn_reduce1_pm_opaque pm initPM 300
      { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817], params := [2] }
      7952 14813 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 7952 14813 14817)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7539
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14805, denoteGraph_ringAttn pm initPM 14813] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14805).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14813).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7539).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7539 7539 14805 14813 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7571 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4867`.
    Identity alias: `7571` reconstructs exactly as `4867` (allGather of its shards). -/
theorem recon_intermediateGoal_7571_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7571
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7571 = denoteGraph_ringAttn sm initSM 4867 :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7571 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 4867 7571 7575 7579 7583 7587)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14866 = denoteGraph_ringAttn pm initPM 8029 :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14866 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 8029 14866 14870 14874 14878 14882)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14889 = denoteGraph_ringAttn pm initPM 8030 :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14889 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 8030 14889 14893 14897 14901 14905)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7571
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14866, denoteGraph_ringAttn pm initPM 14889] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14866).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14889).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7571).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7571 7571 14866 14889 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7591 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4898`.
    Identity alias: `7591` reconstructs exactly as `4898` (allGather of its shards). -/
theorem recon_intermediateGoal_7591_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7591
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4898 4898 8137 8138
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4898_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7591 = denoteGraph_ringAttn sm initSM 4898 :=
    ringAttn_reduce1_pm_opaque sm initSM 158
      { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595], params := [2] }
      4898 7591 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4898 7591 7595)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14909 = denoteGraph_ringAttn pm initPM 8137 :=
    ringAttn_reduce1_pm_opaque pm initPM 377
      { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913], params := [2] }
      8137 14909 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8137 14909 14913)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14917 = denoteGraph_ringAttn pm initPM 8138 :=
    ringAttn_reduce1_pm_opaque pm initPM 378
      { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921], params := [2] }
      8138 14917 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8138 14917 14921)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7591
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14909, denoteGraph_ringAttn pm initPM 14917] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14909).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14917).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7591).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7591 7591 14909 14917 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7623 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4921`.
    Identity alias: `7623` reconstructs exactly as `4921` (allGather of its shards). -/
theorem recon_intermediateGoal_7623_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7623
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7623 = denoteGraph_ringAttn sm initSM 4921 :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7623 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 4921 7623 7627 7631 7635 7639)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14970 = denoteGraph_ringAttn pm initPM 8215 :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14970 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 8215 14970 14974 14978 14982 14986)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14993 = denoteGraph_ringAttn pm initPM 8216 :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 14993 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 8216 14993 14997 15001 15005 15009)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7623
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14970, denoteGraph_ringAttn pm initPM 14993] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14970).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14993).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7623).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7623 7623 14970 14993 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7643 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4952`.
    Identity alias: `7643` reconstructs exactly as `4952` (allGather of its shards). -/
theorem recon_intermediateGoal_7643_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7643
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4952 4952 8323 8324
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4952_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7643 = denoteGraph_ringAttn sm initSM 4952 :=
    ringAttn_reduce1_pm_opaque sm initSM 197
      { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647], params := [2] }
      4952 7643 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4952 7643 7647)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15013 = denoteGraph_ringAttn pm initPM 8323 :=
    ringAttn_reduce1_pm_opaque pm initPM 455
      { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017], params := [2] }
      8323 15013 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8323 15013 15017)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15021 = denoteGraph_ringAttn pm initPM 8324 :=
    ringAttn_reduce1_pm_opaque pm initPM 456
      { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025], params := [2] }
      8324 15021 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8324 15021 15025)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7643
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15013, denoteGraph_ringAttn pm initPM 15021] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15013).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15021).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7643).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7643 7643 15013 15021 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7675 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4975`.
    Identity alias: `7675` reconstructs exactly as `4975` (allGather of its shards). -/
theorem recon_intermediateGoal_7675_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7675
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7675 = denoteGraph_ringAttn sm initSM 4975 :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7675 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 4975 7675 7679 7683 7687 7691)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15074 = denoteGraph_ringAttn pm initPM 8401 :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15074 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 8401 15074 15078 15082 15086 15090)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15097 = denoteGraph_ringAttn pm initPM 8402 :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15097 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 8402 15097 15101 15105 15109 15113)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7675
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15074, denoteGraph_ringAttn pm initPM 15097] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15074).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15097).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7675).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7675 7675 15074 15097 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7695 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5006`.
    Identity alias: `7695` reconstructs exactly as `5006` (allGather of its shards). -/
theorem recon_intermediateGoal_7695_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7695
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5006 5006 8509 8510
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5006_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7695 = denoteGraph_ringAttn sm initSM 5006 :=
    ringAttn_reduce1_pm_opaque sm initSM 236
      { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699], params := [2] }
      5006 7695 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5006 7695 7699)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15117 = denoteGraph_ringAttn pm initPM 8509 :=
    ringAttn_reduce1_pm_opaque pm initPM 533
      { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121], params := [2] }
      8509 15117 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8509 15117 15121)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15125 = denoteGraph_ringAttn pm initPM 8510 :=
    ringAttn_reduce1_pm_opaque pm initPM 534
      { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129], params := [2] }
      8510 15125 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8510 15125 15129)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7695
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15117, denoteGraph_ringAttn pm initPM 15125] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15117).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15125).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7695).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7695 7695 15117 15125 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7727 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5029`.
    Identity alias: `7727` reconstructs exactly as `5029` (allGather of its shards). -/
theorem recon_intermediateGoal_7727_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7727
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7727 = denoteGraph_ringAttn sm initSM 5029 :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7727 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5029 7727 7731 7735 7739 7743)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15178 = denoteGraph_ringAttn pm initPM 8587 :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15178 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 8587 15178 15182 15186 15190 15194)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15201 = denoteGraph_ringAttn pm initPM 8588 :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15201 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 8588 15201 15205 15209 15213 15217)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7727
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15178, denoteGraph_ringAttn pm initPM 15201] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15178).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15201).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7727).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7727 7727 15178 15201 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7747 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5060`.
    Identity alias: `7747` reconstructs exactly as `5060` (allGather of its shards). -/
theorem recon_intermediateGoal_7747_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7747
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5060 5060 8695 8696
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5060_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7747 = denoteGraph_ringAttn sm initSM 5060 :=
    ringAttn_reduce1_pm_opaque sm initSM 275
      { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751], params := [2] }
      5060 7747 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5060 7747 7751)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15221 = denoteGraph_ringAttn pm initPM 8695 :=
    ringAttn_reduce1_pm_opaque pm initPM 611
      { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225], params := [2] }
      8695 15221 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8695 15221 15225)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15229 = denoteGraph_ringAttn pm initPM 8696 :=
    ringAttn_reduce1_pm_opaque pm initPM 612
      { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233], params := [2] }
      8696 15229 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8696 15229 15233)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7747
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15221, denoteGraph_ringAttn pm initPM 15229] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15221).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15229).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7747).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7747 7747 15221 15229 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7779 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5083`.
    Identity alias: `7779` reconstructs exactly as `5083` (allGather of its shards). -/
theorem recon_intermediateGoal_7779_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7779
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7779 = denoteGraph_ringAttn sm initSM 5083 :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7779 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5083 7779 7783 7787 7791 7795)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15282 = denoteGraph_ringAttn pm initPM 8773 :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15282 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 8773 15282 15286 15290 15294 15298)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15305 = denoteGraph_ringAttn pm initPM 8774 :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15305 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 8774 15305 15309 15313 15317 15321)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7779
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15282, denoteGraph_ringAttn pm initPM 15305] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15282).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15305).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7779).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7779 7779 15282 15305 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7799 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5114`.
    Identity alias: `7799` reconstructs exactly as `5114` (allGather of its shards). -/
theorem recon_intermediateGoal_7799_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7799
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5114 5114 8881 8882
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5114_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7799 = denoteGraph_ringAttn sm initSM 5114 :=
    ringAttn_reduce1_pm_opaque sm initSM 314
      { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803], params := [2] }
      5114 7799 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5114 7799 7803)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15325 = denoteGraph_ringAttn pm initPM 8881 :=
    ringAttn_reduce1_pm_opaque pm initPM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329], params := [2] }
      8881 15325 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8881 15325 15329)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15333 = denoteGraph_ringAttn pm initPM 8882 :=
    ringAttn_reduce1_pm_opaque pm initPM 690
      { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337], params := [2] }
      8882 15333 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8882 15333 15337)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7799
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15325, denoteGraph_ringAttn pm initPM 15333] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15325).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15333).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7799).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7799 7799 15325 15333 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7831 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5137`.
    Identity alias: `7831` reconstructs exactly as `5137` (allGather of its shards). -/
theorem recon_intermediateGoal_7831_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7831
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7831 = denoteGraph_ringAttn sm initSM 5137 :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7831 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5137 7831 7835 7839 7843 7847)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15386 = denoteGraph_ringAttn pm initPM 8959 :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15386 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 8959 15386 15390 15394 15398 15402)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15409 = denoteGraph_ringAttn pm initPM 8960 :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15409 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 8960 15409 15413 15417 15421 15425)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7831
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15386, denoteGraph_ringAttn pm initPM 15409] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15386).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15409).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7831).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7831 7831 15386 15409 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7851 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5168`.
    Identity alias: `7851` reconstructs exactly as `5168` (allGather of its shards). -/
theorem recon_intermediateGoal_7851_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7851
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5168 5168 9067 9068
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5168_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7851 = denoteGraph_ringAttn sm initSM 5168 :=
    ringAttn_reduce1_pm_opaque sm initSM 353
      { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855], params := [2] }
      5168 7851 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5168 7851 7855)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15429 = denoteGraph_ringAttn pm initPM 9067 :=
    ringAttn_reduce1_pm_opaque pm initPM 767
      { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433], params := [2] }
      9067 15429 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9067 15429 15433)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15437 = denoteGraph_ringAttn pm initPM 9068 :=
    ringAttn_reduce1_pm_opaque pm initPM 768
      { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441], params := [2] }
      9068 15437 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9068 15437 15441)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7851
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15429, denoteGraph_ringAttn pm initPM 15437] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15429).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15437).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7851).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7851 7851 15429 15437 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7883 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5191`.
    Identity alias: `7883` reconstructs exactly as `5191` (allGather of its shards). -/
theorem recon_intermediateGoal_7883_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7883
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7883 = denoteGraph_ringAttn sm initSM 5191 :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7883 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5191 7883 7887 7891 7895 7899)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15490 = denoteGraph_ringAttn pm initPM 9145 :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15490 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 9145 15490 15494 15498 15502 15506)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15513 = denoteGraph_ringAttn pm initPM 9146 :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15513 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 9146 15513 15517 15521 15525 15529)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7883
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15490, denoteGraph_ringAttn pm initPM 15513] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15490).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15513).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7883).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7883 7883 15490 15513 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7903 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5222`.
    Identity alias: `7903` reconstructs exactly as `5222` (allGather of its shards). -/
theorem recon_intermediateGoal_7903_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7903
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5222 5222 9253 9254
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5222_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7903 = denoteGraph_ringAttn sm initSM 5222 :=
    ringAttn_reduce1_pm_opaque sm initSM 392
      { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907], params := [2] }
      5222 7903 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5222 7903 7907)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15533 = denoteGraph_ringAttn pm initPM 9253 :=
    ringAttn_reduce1_pm_opaque pm initPM 845
      { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537], params := [2] }
      9253 15533 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9253 15533 15537)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15541 = denoteGraph_ringAttn pm initPM 9254 :=
    ringAttn_reduce1_pm_opaque pm initPM 846
      { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545], params := [2] }
      9254 15541 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9254 15541 15545)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7903
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15533, denoteGraph_ringAttn pm initPM 15541] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15533).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15541).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7903).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7903 7903 15533 15541 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7935 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5245`.
    Identity alias: `7935` reconstructs exactly as `5245` (allGather of its shards). -/
theorem recon_intermediateGoal_7935_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7935
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7935 = denoteGraph_ringAttn sm initSM 5245 :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7935 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5245 7935 7939 7943 7947 7951)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15594 = denoteGraph_ringAttn pm initPM 9331 :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15594 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 9331 15594 15598 15602 15606 15610)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15617 = denoteGraph_ringAttn pm initPM 9332 :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15617 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 9332 15617 15621 15625 15629 15633)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7935
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15594, denoteGraph_ringAttn pm initPM 15617] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15594).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15617).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7935).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7935 7935 15594 15617 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7955 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5276`.
    Identity alias: `7955` reconstructs exactly as `5276` (allGather of its shards). -/
theorem recon_intermediateGoal_7955_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7955
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5276 5276 9439 9440
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5276_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7955 = denoteGraph_ringAttn sm initSM 5276 :=
    ringAttn_reduce1_pm_opaque sm initSM 431
      { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959], params := [2] }
      5276 7955 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5276 7955 7959)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15637 = denoteGraph_ringAttn pm initPM 9439 :=
    ringAttn_reduce1_pm_opaque pm initPM 923
      { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641], params := [2] }
      9439 15637 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9439 15637 15641)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15645 = denoteGraph_ringAttn pm initPM 9440 :=
    ringAttn_reduce1_pm_opaque pm initPM 924
      { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649], params := [2] }
      9440 15645 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9440 15645 15649)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7955
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15637, denoteGraph_ringAttn pm initPM 15645] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15637).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15645).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7955).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7955 7955 15637 15645 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7987 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5299`.
    Identity alias: `7987` reconstructs exactly as `5299` (allGather of its shards). -/
theorem recon_intermediateGoal_7987_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7987
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7987 = denoteGraph_ringAttn sm initSM 5299 :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7987 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5299 7987 7991 7995 7999 8003)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15698 = denoteGraph_ringAttn pm initPM 9517 :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15698 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 9517 15698 15702 15706 15710 15714)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15721 = denoteGraph_ringAttn pm initPM 9518 :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15721 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 9518 15721 15725 15729 15733 15737)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7987
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15698, denoteGraph_ringAttn pm initPM 15721] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15698).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15721).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7987).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7987 7987 15698 15721 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8011 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5330`.
    Identity alias: `8011` reconstructs exactly as `5330` (allGather of its shards). -/
theorem recon_intermediateGoal_8011_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8011
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5330 5330 9625 9626
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5330_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8011 = denoteGraph_ringAttn sm initSM 5330 :=
    ringAttn_reduce1_pm_opaque sm initSM 470
      { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] }
      5330 8011 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5330 8007 8011 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 13257 = denoteGraph_ringAttn pm initPM 9625 :=
    ringAttn_reduce1_pm_opaque pm initPM 1001
      { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] }
      9625 13257 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9625 14597 13257 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 13258 = denoteGraph_ringAttn pm initPM 9626 :=
    ringAttn_reduce1_pm_opaque pm initPM 1002
      { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] }
      9626 13258 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9626 14599 13258 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8011
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 13257, denoteGraph_ringAttn pm initPM 13258] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 13257).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 13258).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8011).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8011 8011 13257 13258 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8166 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5356`.
    Identity alias: `8166` reconstructs exactly as `5356` (allGather of its shards). -/
theorem recon_intermediateGoal_8166_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8166
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8166 = denoteGraph_ringAttn sm initSM 5356 :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8166 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16012 = denoteGraph_ringAttn pm initPM 9721 :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16012 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16035 = denoteGraph_ringAttn pm initPM 9722 :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16035 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8166
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16012, denoteGraph_ringAttn pm initPM 16035] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16012).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16035).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8166).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8166 8166 16012 16035 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8197 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5405`.
    Identity alias: `8197` reconstructs exactly as `5405` (allGather of its shards). -/
theorem recon_intermediateGoal_8197_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8197
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5405 5405 9893 9894
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5405_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8197 = denoteGraph_ringAttn sm initSM 5405 :=
    ringAttn_reduce1_pm_opaque sm initSM 549
      { rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] }
      5405 8197 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5405 8197 8201 8205 8209 8213)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16082 = denoteGraph_ringAttn pm initPM 9893 :=
    ringAttn_reduce1_pm_opaque pm initPM 1160
      { rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] }
      9893 16082 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 9893 16082 16086 16090 16094 16098)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16105 = denoteGraph_ringAttn pm initPM 9894 :=
    ringAttn_reduce1_pm_opaque pm initPM 1161
      { rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] }
      9894 16105 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 9894 16105 16109 16113 16117 16121)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8197
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16082, denoteGraph_ringAttn pm initPM 16105] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16082).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16105).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8197).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8197 8197 16082 16105 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8217 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5436`.
    Identity alias: `8217` reconstructs exactly as `5436` (allGather of its shards). -/
theorem recon_intermediateGoal_8217_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8217
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5436 5436 10001 10002
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5436_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8217 = denoteGraph_ringAttn sm initSM 5436 :=
    ringAttn_reduce1_pm_opaque sm initSM 572
      { rank := 0, op := "OpName.FW_multiref", ins := [5436], outs := [8217, 8221], params := [2] }
      5436 8217 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5436 8217 8221)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16125 = denoteGraph_ringAttn pm initPM 10001 :=
    ringAttn_reduce1_pm_opaque pm initPM 1206
      { rank := 0, op := "OpName.FW_multiref", ins := [10001], outs := [16125, 16129], params := [2] }
      10001 16125 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10001 16125 16129)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16133 = denoteGraph_ringAttn pm initPM 10002 :=
    ringAttn_reduce1_pm_opaque pm initPM 1207
      { rank := 1, op := "OpName.FW_multiref", ins := [10002], outs := [16133, 16137], params := [2] }
      10002 16133 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10002 16133 16137)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8217
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16125, denoteGraph_ringAttn pm initPM 16133] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16125).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16133).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8217).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8217 8217 16125 16133 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8248 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5454`.
    Identity alias: `8248` reconstructs exactly as `5454` (allGather of its shards). -/
theorem recon_intermediateGoal_8248_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8248
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5454 5454 10065 10066
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5454_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8248 = denoteGraph_ringAttn sm initSM 5454 :=
    ringAttn_reduce1_pm_opaque sm initSM 584
      { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] }
      5454 8248 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5454 8236 8240 8244 8248 8252 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16172 = denoteGraph_ringAttn pm initPM 10065 :=
    ringAttn_reduce1_pm_opaque pm initPM 1230
      { rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] }
      10065 16172 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 10065 16160 16164 16168 16172 16176 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16195 = denoteGraph_ringAttn pm initPM 10066 :=
    ringAttn_reduce1_pm_opaque pm initPM 1231
      { rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] }
      10066 16195 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 10066 16183 16187 16191 16195 16199 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8248
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16172, denoteGraph_ringAttn pm initPM 16195] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16172).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16195).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8248).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8248 8248 16172 16195 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8279 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5503`.
    Identity alias: `8279` reconstructs exactly as `5503` (allGather of its shards). -/
theorem recon_intermediateGoal_8279_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8279
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5503 5503 10237 10238
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5503_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8279 = denoteGraph_ringAttn sm initSM 5503 :=
    ringAttn_reduce1_pm_opaque sm initSM 619
      { rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] }
      5503 8279 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5503 8275 8279 8283 8287 8291 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16242 = denoteGraph_ringAttn pm initPM 10237 :=
    ringAttn_reduce1_pm_opaque pm initPM 1300
      { rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] }
      10237 16242 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 10237 16238 16242 16246 16250 16254 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16265 = denoteGraph_ringAttn pm initPM 10238 :=
    ringAttn_reduce1_pm_opaque pm initPM 1301
      { rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] }
      10238 16265 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 10238 16261 16265 16269 16273 16277 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8279
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16242, denoteGraph_ringAttn pm initPM 16265] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16242).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16265).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8279).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8279 8279 16242 16265 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8303 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5550`.
    Identity alias: `8303` reconstructs exactly as `5550` (allGather of its shards). -/
theorem recon_intermediateGoal_8303_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8303
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5550 5550 10405 10406
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5550_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8303 = denoteGraph_ringAttn sm initSM 5550 :=
    ringAttn_reduce1_pm_opaque sm initSM 652
      { rank := 0, op := "OpName.FW_multiref", ins := [5550], outs := [8303, 8307], params := [2] }
      5550 8303 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5550 8303 8307)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16297 = denoteGraph_ringAttn pm initPM 10405 :=
    ringAttn_reduce1_pm_opaque pm initPM 1366
      { rank := 0, op := "OpName.FW_multiref", ins := [10405], outs := [16297, 16301], params := [2] }
      10405 16297 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10405 16297 16301)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16305 = denoteGraph_ringAttn pm initPM 10406 :=
    ringAttn_reduce1_pm_opaque pm initPM 1367
      { rank := 1, op := "OpName.FW_multiref", ins := [10406], outs := [16305, 16309], params := [2] }
      10406 16305 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10406 16305 16309)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8303
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16297, denoteGraph_ringAttn pm initPM 16305] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16297).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16305).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8303).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8303 8303 16297 16305 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8330 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5552`.
    Identity alias: `8330` reconstructs exactly as `5552` (allGather of its shards). -/
theorem recon_intermediateGoal_8330_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8330
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5552 5552 10409 10410
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5552_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8330 = denoteGraph_ringAttn sm initSM 5552 :=
    ringAttn_reduce1_pm_opaque sm initSM 654
      { rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] }
      5552 8330 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5552 8314 8318 8322 8326 8330 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16332 = denoteGraph_ringAttn pm initPM 10409 :=
    ringAttn_reduce1_pm_opaque pm initPM 1370
      { rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] }
      10409 16332 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 10409 16316 16320 16324 16328 16332 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16355 = denoteGraph_ringAttn pm initPM 10410 :=
    ringAttn_reduce1_pm_opaque pm initPM 1371
      { rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] }
      10410 16355 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 10410 16339 16343 16347 16351 16355 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8330
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16332, denoteGraph_ringAttn pm initPM 16355] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16332).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16355).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8330).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8330 8330 16332 16355 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8361 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5601`.
    Identity alias: `8361` reconstructs exactly as `5601` (allGather of its shards). -/
theorem recon_intermediateGoal_8361_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8361
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5601 5601 10581 10582
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5601_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8361 = denoteGraph_ringAttn sm initSM 5601 :=
    ringAttn_reduce1_pm_opaque sm initSM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] }
      5601 8361 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5601 8353 8357 8361 8365 8369 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16402 = denoteGraph_ringAttn pm initPM 10581 :=
    ringAttn_reduce1_pm_opaque pm initPM 1440
      { rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] }
      10581 16402 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 10581 16394 16398 16402 16406 16410 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16425 = denoteGraph_ringAttn pm initPM 10582 :=
    ringAttn_reduce1_pm_opaque pm initPM 1441
      { rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] }
      10582 16425 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 10582 16417 16421 16425 16429 16433 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8361
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16402, denoteGraph_ringAttn pm initPM 16425] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16402).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16425).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8361).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8361 8361 16402 16425 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8392 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5650`.
    Identity alias: `8392` reconstructs exactly as `5650` (allGather of its shards). -/
theorem recon_intermediateGoal_8392_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8392
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5650 5650 10753 10754
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5650_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8392 = denoteGraph_ringAttn sm initSM 5650 :=
    ringAttn_reduce1_pm_opaque sm initSM 724
      { rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] }
      5650 8392 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5650 8392 8396 8400 8404 8408)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16472 = denoteGraph_ringAttn pm initPM 10753 :=
    ringAttn_reduce1_pm_opaque pm initPM 1510
      { rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] }
      10753 16472 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 10753 16472 16476 16480 16484 16488)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16495 = denoteGraph_ringAttn pm initPM 10754 :=
    ringAttn_reduce1_pm_opaque pm initPM 1511
      { rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] }
      10754 16495 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 10754 16495 16499 16503 16507 16511)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8392
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16472, denoteGraph_ringAttn pm initPM 16495] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16472).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16495).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8392).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8392 8392 16472 16495 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8412 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5681`.
    Identity alias: `8412` reconstructs exactly as `5681` (allGather of its shards). -/
theorem recon_intermediateGoal_8412_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8412
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5681 5681 10861 10862
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5681_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8412 = denoteGraph_ringAttn sm initSM 5681 :=
    ringAttn_reduce1_pm_opaque sm initSM 747
      { rank := 0, op := "OpName.FW_multiref", ins := [5681], outs := [8412, 8416], params := [2] }
      5681 8412 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5681 8412 8416)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16515 = denoteGraph_ringAttn pm initPM 10861 :=
    ringAttn_reduce1_pm_opaque pm initPM 1556
      { rank := 0, op := "OpName.FW_multiref", ins := [10861], outs := [16515, 16519], params := [2] }
      10861 16515 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10861 16515 16519)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16523 = denoteGraph_ringAttn pm initPM 10862 :=
    ringAttn_reduce1_pm_opaque pm initPM 1557
      { rank := 1, op := "OpName.FW_multiref", ins := [10862], outs := [16523, 16527], params := [2] }
      10862 16523 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10862 16523 16527)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8412
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16515, denoteGraph_ringAttn pm initPM 16523] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16515).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16523).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8412).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8412 8412 16515 16523 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8443 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5699`.
    Identity alias: `8443` reconstructs exactly as `5699` (allGather of its shards). -/
theorem recon_intermediateGoal_8443_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8443
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5699 5699 10925 10926
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5699_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8443 = denoteGraph_ringAttn sm initSM 5699 :=
    ringAttn_reduce1_pm_opaque sm initSM 759
      { rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] }
      5699 8443 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5699 8431 8435 8439 8443 8447 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16562 = denoteGraph_ringAttn pm initPM 10925 :=
    ringAttn_reduce1_pm_opaque pm initPM 1580
      { rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] }
      10925 16562 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 10925 16550 16554 16558 16562 16566 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16585 = denoteGraph_ringAttn pm initPM 10926 :=
    ringAttn_reduce1_pm_opaque pm initPM 1581
      { rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] }
      10926 16585 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 10926 16573 16577 16581 16585 16589 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8443
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16562, denoteGraph_ringAttn pm initPM 16585] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16562).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16585).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8443).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8443 8443 16562 16585 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8474 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5748`.
    Identity alias: `8474` reconstructs exactly as `5748` (allGather of its shards). -/
theorem recon_intermediateGoal_8474_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8474
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5748 5748 11097 11098
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5748_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8474 = denoteGraph_ringAttn sm initSM 5748 :=
    ringAttn_reduce1_pm_opaque sm initSM 794
      { rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] }
      5748 8474 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5748 8470 8474 8478 8482 8486 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16632 = denoteGraph_ringAttn pm initPM 11097 :=
    ringAttn_reduce1_pm_opaque pm initPM 1650
      { rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] }
      11097 16632 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 11097 16628 16632 16636 16640 16644 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16655 = denoteGraph_ringAttn pm initPM 11098 :=
    ringAttn_reduce1_pm_opaque pm initPM 1651
      { rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] }
      11098 16655 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 11098 16651 16655 16659 16663 16667 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8474
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16632, denoteGraph_ringAttn pm initPM 16655] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16632).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16655).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8474).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8474 8474 16632 16655 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8498 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5795`.
    Identity alias: `8498` reconstructs exactly as `5795` (allGather of its shards). -/
theorem recon_intermediateGoal_8498_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8498
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5795 5795 11265 11266
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5795_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8498 = denoteGraph_ringAttn sm initSM 5795 :=
    ringAttn_reduce1_pm_opaque sm initSM 827
      { rank := 0, op := "OpName.FW_multiref", ins := [5795], outs := [8498, 8502], params := [2] }
      5795 8498 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5795 8498 8502)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16687 = denoteGraph_ringAttn pm initPM 11265 :=
    ringAttn_reduce1_pm_opaque pm initPM 1716
      { rank := 0, op := "OpName.FW_multiref", ins := [11265], outs := [16687, 16691], params := [2] }
      11265 16687 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11265 16687 16691)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16695 = denoteGraph_ringAttn pm initPM 11266 :=
    ringAttn_reduce1_pm_opaque pm initPM 1717
      { rank := 1, op := "OpName.FW_multiref", ins := [11266], outs := [16695, 16699], params := [2] }
      11266 16695 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11266 16695 16699)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8498
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16687, denoteGraph_ringAttn pm initPM 16695] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16687).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16695).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8498).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8498 8498 16687 16695 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8525 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5797`.
    Identity alias: `8525` reconstructs exactly as `5797` (allGather of its shards). -/
theorem recon_intermediateGoal_8525_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8525
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5797 5797 11269 11270
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5797_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8525 = denoteGraph_ringAttn sm initSM 5797 :=
    ringAttn_reduce1_pm_opaque sm initSM 829
      { rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] }
      5797 8525 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5797 8509 8513 8517 8521 8525 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16722 = denoteGraph_ringAttn pm initPM 11269 :=
    ringAttn_reduce1_pm_opaque pm initPM 1720
      { rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] }
      11269 16722 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 11269 16706 16710 16714 16718 16722 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16745 = denoteGraph_ringAttn pm initPM 11270 :=
    ringAttn_reduce1_pm_opaque pm initPM 1721
      { rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] }
      11270 16745 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 11270 16729 16733 16737 16741 16745 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8525
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16722, denoteGraph_ringAttn pm initPM 16745] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16722).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16745).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8525).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8525 8525 16722 16745 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8556 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5846`.
    Identity alias: `8556` reconstructs exactly as `5846` (allGather of its shards). -/
theorem recon_intermediateGoal_8556_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8556
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5846 5846 11441 11442
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8556 = denoteGraph_ringAttn sm initSM 5846 :=
    ringAttn_reduce1_pm_opaque sm initSM 864
      { rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] }
      5846 8556 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5846 8548 8552 8556 8560 8564 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16792 = denoteGraph_ringAttn pm initPM 11441 :=
    ringAttn_reduce1_pm_opaque pm initPM 1790
      { rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] }
      11441 16792 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 11441 16784 16788 16792 16796 16800 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16815 = denoteGraph_ringAttn pm initPM 11442 :=
    ringAttn_reduce1_pm_opaque pm initPM 1791
      { rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] }
      11442 16815 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 11442 16807 16811 16815 16819 16823 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8556
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16792, denoteGraph_ringAttn pm initPM 16815] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16792).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16815).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8556).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8556 8556 16792 16815 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8587 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5895`.
    Identity alias: `8587` reconstructs exactly as `5895` (allGather of its shards). -/
theorem recon_intermediateGoal_8587_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8587
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5895 5895 11613 11614
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5895_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8587 = denoteGraph_ringAttn sm initSM 5895 :=
    ringAttn_reduce1_pm_opaque sm initSM 899
      { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }
      5895 8587 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5895 8587 8591 8595 8599 8603)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16862 = denoteGraph_ringAttn pm initPM 11613 :=
    ringAttn_reduce1_pm_opaque pm initPM 1860
      { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }
      11613 16862 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 11613 16862 16866 16870 16874 16878)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16885 = denoteGraph_ringAttn pm initPM 11614 :=
    ringAttn_reduce1_pm_opaque pm initPM 1861
      { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }
      11614 16885 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 11614 16885 16889 16893 16897 16901)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8587
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16862, denoteGraph_ringAttn pm initPM 16885] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16862).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16885).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8587).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8587 8587 16862 16885 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
