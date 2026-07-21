import denote.yoco_goals.ZigzagL11Body

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 7500 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4792`.
    Identity alias: `7500` reconstructs exactly as `4792` (allGather of its shards). -/
theorem recon_intermediateGoal_7500_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7500
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4792 4792 7769 7770
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4792_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7500 = denoteGraph_ringAttn sm initSM 4792 :=
    ringAttn_reduce1_pm_opaque sm initSM 82
      { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
      4792 7500 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4792 7496 7500 7504 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14722 = denoteGraph_ringAttn pm initPM 7769 :=
    ringAttn_reduce1_pm_opaque pm initPM 225
      { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
      7769 14722 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 7769 14718 14722 14726 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14735 = denoteGraph_ringAttn pm initPM 7770 :=
    ringAttn_reduce1_pm_opaque pm initPM 226
      { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
      7770 14735 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 7770 14731 14735 14739 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7500
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14722, denoteGraph_ringAttn pm initPM 14735] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14722).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14735).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7500).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7500 7500 14722 14735 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7527 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4813`.
    Identity alias: `7527` reconstructs exactly as `4813` (allGather of its shards). -/
theorem recon_intermediateGoal_7527_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7527
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7527 = denoteGraph_ringAttn sm initSM 4813 :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7527 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14770 = denoteGraph_ringAttn pm initPM 7843 :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14770 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14793 = denoteGraph_ringAttn pm initPM 7844 :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14793 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7527
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14770, denoteGraph_ringAttn pm initPM 14793] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14770).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14793).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7527).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7527 7527 14770 14793 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7552 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4846`.
    Identity alias: `7552` reconstructs exactly as `4846` (allGather of its shards). -/
theorem recon_intermediateGoal_7552_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7552
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4846 4846 7955 7956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7552 = denoteGraph_ringAttn sm initSM 4846 :=
    ringAttn_reduce1_pm_opaque sm initSM 121
      { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
      4846 7552 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4846 7548 7552 7556 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14826 = denoteGraph_ringAttn pm initPM 7955 :=
    ringAttn_reduce1_pm_opaque pm initPM 303
      { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
      7955 14826 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 7955 14822 14826 14830 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14839 = denoteGraph_ringAttn pm initPM 7956 :=
    ringAttn_reduce1_pm_opaque pm initPM 304
      { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
      7956 14839 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 7956 14835 14839 14843 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7552
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14826, denoteGraph_ringAttn pm initPM 14839] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14826).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14839).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7552).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7552 7552 14826 14839 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7579 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4867`.
    Identity alias: `7579` reconstructs exactly as `4867` (allGather of its shards). -/
theorem recon_intermediateGoal_7579_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7579
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7579 = denoteGraph_ringAttn sm initSM 4867 :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7579 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14874 = denoteGraph_ringAttn pm initPM 8029 :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14874 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14897 = denoteGraph_ringAttn pm initPM 8030 :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14897 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7579
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14874, denoteGraph_ringAttn pm initPM 14897] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14874).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14897).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7579).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7579 7579 14874 14897 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7604 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4900`.
    Identity alias: `7604` reconstructs exactly as `4900` (allGather of its shards). -/
theorem recon_intermediateGoal_7604_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7604
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4900 4900 8141 8142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4900_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7604 = denoteGraph_ringAttn sm initSM 4900 :=
    ringAttn_reduce1_pm_opaque sm initSM 160
      { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
      4900 7604 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4900 7600 7604 7608 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14930 = denoteGraph_ringAttn pm initPM 8141 :=
    ringAttn_reduce1_pm_opaque pm initPM 381
      { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
      8141 14930 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8141 14926 14930 14934 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14943 = denoteGraph_ringAttn pm initPM 8142 :=
    ringAttn_reduce1_pm_opaque pm initPM 382
      { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
      8142 14943 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8142 14939 14943 14947 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7604
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14930, denoteGraph_ringAttn pm initPM 14943] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14930).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14943).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7604).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7604 7604 14930 14943 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7631 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4921`.
    Identity alias: `7631` reconstructs exactly as `4921` (allGather of its shards). -/
theorem recon_intermediateGoal_7631_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7631
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7631 = denoteGraph_ringAttn sm initSM 4921 :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7631 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14978 = denoteGraph_ringAttn pm initPM 8215 :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14978 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15001 = denoteGraph_ringAttn pm initPM 8216 :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 15001 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7631
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14978, denoteGraph_ringAttn pm initPM 15001] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14978).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15001).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7631).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7631 7631 14978 15001 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7656 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4954`.
    Identity alias: `7656` reconstructs exactly as `4954` (allGather of its shards). -/
theorem recon_intermediateGoal_7656_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7656
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4954 4954 8327 8328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4954_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7656 = denoteGraph_ringAttn sm initSM 4954 :=
    ringAttn_reduce1_pm_opaque sm initSM 199
      { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
      4954 7656 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4954 7652 7656 7660 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15034 = denoteGraph_ringAttn pm initPM 8327 :=
    ringAttn_reduce1_pm_opaque pm initPM 459
      { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
      8327 15034 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8327 15030 15034 15038 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15047 = denoteGraph_ringAttn pm initPM 8328 :=
    ringAttn_reduce1_pm_opaque pm initPM 460
      { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
      8328 15047 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8328 15043 15047 15051 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7656
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15034, denoteGraph_ringAttn pm initPM 15047] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15034).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15047).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7656).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7656 7656 15034 15047 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7683 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4975`.
    Identity alias: `7683` reconstructs exactly as `4975` (allGather of its shards). -/
theorem recon_intermediateGoal_7683_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7683
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7683 = denoteGraph_ringAttn sm initSM 4975 :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7683 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15082 = denoteGraph_ringAttn pm initPM 8401 :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15082 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15105 = denoteGraph_ringAttn pm initPM 8402 :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15105 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7683
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15082, denoteGraph_ringAttn pm initPM 15105] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15082).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15105).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7683).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7683 7683 15082 15105 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7708 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5008`.
    Identity alias: `7708` reconstructs exactly as `5008` (allGather of its shards). -/
theorem recon_intermediateGoal_7708_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7708
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5008 5008 8513 8514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5008_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7708 = denoteGraph_ringAttn sm initSM 5008 :=
    ringAttn_reduce1_pm_opaque sm initSM 238
      { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
      5008 7708 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5008 7704 7708 7712 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15138 = denoteGraph_ringAttn pm initPM 8513 :=
    ringAttn_reduce1_pm_opaque pm initPM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
      8513 15138 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8513 15134 15138 15142 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15151 = denoteGraph_ringAttn pm initPM 8514 :=
    ringAttn_reduce1_pm_opaque pm initPM 538
      { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
      8514 15151 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8514 15147 15151 15155 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7708
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15138, denoteGraph_ringAttn pm initPM 15151] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15138).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15151).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7708).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7708 7708 15138 15151 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7735 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5029`.
    Identity alias: `7735` reconstructs exactly as `5029` (allGather of its shards). -/
theorem recon_intermediateGoal_7735_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7735
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7735 = denoteGraph_ringAttn sm initSM 5029 :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7735 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15186 = denoteGraph_ringAttn pm initPM 8587 :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15186 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15209 = denoteGraph_ringAttn pm initPM 8588 :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15209 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7735
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15186, denoteGraph_ringAttn pm initPM 15209] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15186).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15209).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7735).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7735 7735 15186 15209 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7760 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5062`.
    Identity alias: `7760` reconstructs exactly as `5062` (allGather of its shards). -/
theorem recon_intermediateGoal_7760_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7760
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5062 5062 8699 8700
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5062_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7760 = denoteGraph_ringAttn sm initSM 5062 :=
    ringAttn_reduce1_pm_opaque sm initSM 277
      { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
      5062 7760 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5062 7756 7760 7764 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15242 = denoteGraph_ringAttn pm initPM 8699 :=
    ringAttn_reduce1_pm_opaque pm initPM 615
      { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
      8699 15242 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8699 15238 15242 15246 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15255 = denoteGraph_ringAttn pm initPM 8700 :=
    ringAttn_reduce1_pm_opaque pm initPM 616
      { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
      8700 15255 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8700 15251 15255 15259 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7760
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15242, denoteGraph_ringAttn pm initPM 15255] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15242).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15255).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7760).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7760 7760 15242 15255 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7787 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5083`.
    Identity alias: `7787` reconstructs exactly as `5083` (allGather of its shards). -/
theorem recon_intermediateGoal_7787_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7787
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7787 = denoteGraph_ringAttn sm initSM 5083 :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7787 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15290 = denoteGraph_ringAttn pm initPM 8773 :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15290 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15313 = denoteGraph_ringAttn pm initPM 8774 :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15313 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7787
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15290, denoteGraph_ringAttn pm initPM 15313] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15290).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15313).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7787).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7787 7787 15290 15313 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7812 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5116`.
    Identity alias: `7812` reconstructs exactly as `5116` (allGather of its shards). -/
theorem recon_intermediateGoal_7812_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7812
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5116 5116 8885 8886
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5116_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7812 = denoteGraph_ringAttn sm initSM 5116 :=
    ringAttn_reduce1_pm_opaque sm initSM 316
      { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
      5116 7812 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5116 7808 7812 7816 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15346 = denoteGraph_ringAttn pm initPM 8885 :=
    ringAttn_reduce1_pm_opaque pm initPM 693
      { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
      8885 15346 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 8885 15342 15346 15350 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15359 = denoteGraph_ringAttn pm initPM 8886 :=
    ringAttn_reduce1_pm_opaque pm initPM 694
      { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
      8886 15359 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 8886 15355 15359 15363 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7812
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15346, denoteGraph_ringAttn pm initPM 15359] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15346).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15359).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7812).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7812 7812 15346 15359 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7839 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5137`.
    Identity alias: `7839` reconstructs exactly as `5137` (allGather of its shards). -/
theorem recon_intermediateGoal_7839_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7839
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7839 = denoteGraph_ringAttn sm initSM 5137 :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7839 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15394 = denoteGraph_ringAttn pm initPM 8959 :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15394 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15417 = denoteGraph_ringAttn pm initPM 8960 :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15417 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7839
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15394, denoteGraph_ringAttn pm initPM 15417] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15394).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15417).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7839).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7839 7839 15394 15417 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7864 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5170`.
    Identity alias: `7864` reconstructs exactly as `5170` (allGather of its shards). -/
theorem recon_intermediateGoal_7864_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7864
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5170 5170 9071 9072
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5170_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7864 = denoteGraph_ringAttn sm initSM 5170 :=
    ringAttn_reduce1_pm_opaque sm initSM 355
      { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
      5170 7864 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5170 7860 7864 7868 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15450 = denoteGraph_ringAttn pm initPM 9071 :=
    ringAttn_reduce1_pm_opaque pm initPM 771
      { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
      9071 15450 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 9071 15446 15450 15454 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15463 = denoteGraph_ringAttn pm initPM 9072 :=
    ringAttn_reduce1_pm_opaque pm initPM 772
      { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
      9072 15463 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 9072 15459 15463 15467 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7864
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15450, denoteGraph_ringAttn pm initPM 15463] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15450).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15463).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7864).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7864 7864 15450 15463 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7891 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5191`.
    Identity alias: `7891` reconstructs exactly as `5191` (allGather of its shards). -/
theorem recon_intermediateGoal_7891_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7891
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7891 = denoteGraph_ringAttn sm initSM 5191 :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7891 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15498 = denoteGraph_ringAttn pm initPM 9145 :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15498 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15521 = denoteGraph_ringAttn pm initPM 9146 :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15521 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7891
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15498, denoteGraph_ringAttn pm initPM 15521] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15498).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15521).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7891).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7891 7891 15498 15521 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7916 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5224`.
    Identity alias: `7916` reconstructs exactly as `5224` (allGather of its shards). -/
theorem recon_intermediateGoal_7916_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7916
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5224 5224 9257 9258
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5224_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7916 = denoteGraph_ringAttn sm initSM 5224 :=
    ringAttn_reduce1_pm_opaque sm initSM 394
      { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
      5224 7916 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5224 7912 7916 7920 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15554 = denoteGraph_ringAttn pm initPM 9257 :=
    ringAttn_reduce1_pm_opaque pm initPM 849
      { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
      9257 15554 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 9257 15550 15554 15558 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15567 = denoteGraph_ringAttn pm initPM 9258 :=
    ringAttn_reduce1_pm_opaque pm initPM 850
      { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
      9258 15567 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 9258 15563 15567 15571 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7916
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15554, denoteGraph_ringAttn pm initPM 15567] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15554).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15567).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7916).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7916 7916 15554 15567 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7943 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5245`.
    Identity alias: `7943` reconstructs exactly as `5245` (allGather of its shards). -/
theorem recon_intermediateGoal_7943_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7943
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7943 = denoteGraph_ringAttn sm initSM 5245 :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7943 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15602 = denoteGraph_ringAttn pm initPM 9331 :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15602 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15625 = denoteGraph_ringAttn pm initPM 9332 :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15625 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7943
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15602, denoteGraph_ringAttn pm initPM 15625] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15602).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15625).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7943).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7943 7943 15602 15625 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7968 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5278`.
    Identity alias: `7968` reconstructs exactly as `5278` (allGather of its shards). -/
theorem recon_intermediateGoal_7968_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7968
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5278 5278 9443 9444
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5278_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7968 = denoteGraph_ringAttn sm initSM 5278 :=
    ringAttn_reduce1_pm_opaque sm initSM 433
      { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
      5278 7968 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 5278 7964 7968 7972 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15658 = denoteGraph_ringAttn pm initPM 9443 :=
    ringAttn_reduce1_pm_opaque pm initPM 927
      { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
      9443 15658 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 9443 15654 15658 15662 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15671 = denoteGraph_ringAttn pm initPM 9444 :=
    ringAttn_reduce1_pm_opaque pm initPM 928
      { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
      9444 15671 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 9444 15667 15671 15675 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7968
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15658, denoteGraph_ringAttn pm initPM 15671] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15658).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15671).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7968).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7968 7968 15658 15671 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7995 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5299`.
    Identity alias: `7995` reconstructs exactly as `5299` (allGather of its shards). -/
theorem recon_intermediateGoal_7995_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7995
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7995 = denoteGraph_ringAttn sm initSM 5299 :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7995 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15706 = denoteGraph_ringAttn pm initPM 9517 :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15706 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15729 = denoteGraph_ringAttn pm initPM 9518 :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15729 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7995
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15706, denoteGraph_ringAttn pm initPM 15729] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15706).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15729).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7995).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7995 7995 15706 15729 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8147 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5354`.
    Identity alias: `8147` reconstructs exactly as `5354` (allGather of its shards). -/
theorem recon_intermediateGoal_8147_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8147
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5354 5354 9717 9718
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5354_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8147 = denoteGraph_ringAttn sm initSM 5354 :=
    ringAttn_reduce1_pm_opaque sm initSM 512
      { rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151], params := [2] }
      5354 8147 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5354 8147 8151)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15985 = denoteGraph_ringAttn pm initPM 9717 :=
    ringAttn_reduce1_pm_opaque pm initPM 1086
      { rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989], params := [2] }
      9717 15985 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9717 15985 15989)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15993 = denoteGraph_ringAttn pm initPM 9718 :=
    ringAttn_reduce1_pm_opaque pm initPM 1087
      { rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997], params := [2] }
      9718 15993 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9718 15993 15997)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8147
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15985, denoteGraph_ringAttn pm initPM 15993] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15985).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15993).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8147).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8147 8147 15985 15993 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8174 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5356`.
    Identity alias: `8174` reconstructs exactly as `5356` (allGather of its shards). -/
theorem recon_intermediateGoal_8174_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8174
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8174 = denoteGraph_ringAttn sm initSM 5356 :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8174 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16020 = denoteGraph_ringAttn pm initPM 9721 :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16020 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16043 = denoteGraph_ringAttn pm initPM 9722 :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16043 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8174
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16020, denoteGraph_ringAttn pm initPM 16043] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16020).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16043).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8174).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8174 8174 16020 16043 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8205 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5405`.
    Identity alias: `8205` reconstructs exactly as `5405` (allGather of its shards). -/
theorem recon_intermediateGoal_8205_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8205
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5405 5405 9893 9894
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5405_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8205 = denoteGraph_ringAttn sm initSM 5405 :=
    ringAttn_reduce1_pm_opaque sm initSM 549
      { rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] }
      5405 8205 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5405 8197 8201 8205 8209 8213 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16090 = denoteGraph_ringAttn pm initPM 9893 :=
    ringAttn_reduce1_pm_opaque pm initPM 1160
      { rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] }
      9893 16090 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9893 16082 16086 16090 16094 16098 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16113 = denoteGraph_ringAttn pm initPM 9894 :=
    ringAttn_reduce1_pm_opaque pm initPM 1161
      { rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] }
      9894 16113 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9894 16105 16109 16113 16117 16121 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8205
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16090, denoteGraph_ringAttn pm initPM 16113] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16090).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16113).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8205).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8205 8205 16090 16113 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8236 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5454`.
    Identity alias: `8236` reconstructs exactly as `5454` (allGather of its shards). -/
theorem recon_intermediateGoal_8236_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8236
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5454 5454 10065 10066
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5454_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8236 = denoteGraph_ringAttn sm initSM 5454 :=
    ringAttn_reduce1_pm_opaque sm initSM 584
      { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] }
      5454 8236 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5454 8236 8240 8244 8248 8252)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16160 = denoteGraph_ringAttn pm initPM 10065 :=
    ringAttn_reduce1_pm_opaque pm initPM 1230
      { rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] }
      10065 16160 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 10065 16160 16164 16168 16172 16176)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16183 = denoteGraph_ringAttn pm initPM 10066 :=
    ringAttn_reduce1_pm_opaque pm initPM 1231
      { rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] }
      10066 16183 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 10066 16183 16187 16191 16195 16199)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8236
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16160, denoteGraph_ringAttn pm initPM 16183] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16160).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16183).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8236).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8236 8236 16160 16183 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8256 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5485`.
    Identity alias: `8256` reconstructs exactly as `5485` (allGather of its shards). -/
theorem recon_intermediateGoal_8256_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8256
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5485 5485 10173 10174
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5485_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8256 = denoteGraph_ringAttn sm initSM 5485 :=
    ringAttn_reduce1_pm_opaque sm initSM 607
      { rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8256, 8260], params := [2] }
      5485 8256 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5485 8256 8260)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16203 = denoteGraph_ringAttn pm initPM 10173 :=
    ringAttn_reduce1_pm_opaque pm initPM 1276
      { rank := 0, op := "OpName.FW_multiref", ins := [10173], outs := [16203, 16207], params := [2] }
      10173 16203 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10173 16203 16207)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16211 = denoteGraph_ringAttn pm initPM 10174 :=
    ringAttn_reduce1_pm_opaque pm initPM 1277
      { rank := 1, op := "OpName.FW_multiref", ins := [10174], outs := [16211, 16215], params := [2] }
      10174 16211 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10174 16211 16215)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8256
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16203, denoteGraph_ringAttn pm initPM 16211] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16203).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16211).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8256).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8256 8256 16203 16211 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8287 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5503`.
    Identity alias: `8287` reconstructs exactly as `5503` (allGather of its shards). -/
theorem recon_intermediateGoal_8287_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8287
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5503 5503 10237 10238
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5503_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8287 = denoteGraph_ringAttn sm initSM 5503 :=
    ringAttn_reduce1_pm_opaque sm initSM 619
      { rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] }
      5503 8287 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5503 8275 8279 8283 8287 8291 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16250 = denoteGraph_ringAttn pm initPM 10237 :=
    ringAttn_reduce1_pm_opaque pm initPM 1300
      { rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] }
      10237 16250 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 10237 16238 16242 16246 16250 16254 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16273 = denoteGraph_ringAttn pm initPM 10238 :=
    ringAttn_reduce1_pm_opaque pm initPM 1301
      { rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] }
      10238 16273 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 10238 16261 16265 16269 16273 16277 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8287
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16250, denoteGraph_ringAttn pm initPM 16273] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16250).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16273).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8287).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8287 8287 16250 16273 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8318 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5552`.
    Identity alias: `8318` reconstructs exactly as `5552` (allGather of its shards). -/
theorem recon_intermediateGoal_8318_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8318
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5552 5552 10409 10410
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5552_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8318 = denoteGraph_ringAttn sm initSM 5552 :=
    ringAttn_reduce1_pm_opaque sm initSM 654
      { rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] }
      5552 8318 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5552 8314 8318 8322 8326 8330 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16320 = denoteGraph_ringAttn pm initPM 10409 :=
    ringAttn_reduce1_pm_opaque pm initPM 1370
      { rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] }
      10409 16320 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 10409 16316 16320 16324 16328 16332 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16343 = denoteGraph_ringAttn pm initPM 10410 :=
    ringAttn_reduce1_pm_opaque pm initPM 1371
      { rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] }
      10410 16343 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 10410 16339 16343 16347 16351 16355 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8318
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16320, denoteGraph_ringAttn pm initPM 16343] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16320).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16343).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8318).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8318 8318 16320 16343 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8342 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5599`.
    Identity alias: `8342` reconstructs exactly as `5599` (allGather of its shards). -/
theorem recon_intermediateGoal_8342_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8342
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5599 5599 10577 10578
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5599_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8342 = denoteGraph_ringAttn sm initSM 5599 :=
    ringAttn_reduce1_pm_opaque sm initSM 687
      { rank := 0, op := "OpName.FW_multiref", ins := [5599], outs := [8342, 8346], params := [2] }
      5599 8342 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5599 8342 8346)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16375 = denoteGraph_ringAttn pm initPM 10577 :=
    ringAttn_reduce1_pm_opaque pm initPM 1436
      { rank := 0, op := "OpName.FW_multiref", ins := [10577], outs := [16375, 16379], params := [2] }
      10577 16375 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10577 16375 16379)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16383 = denoteGraph_ringAttn pm initPM 10578 :=
    ringAttn_reduce1_pm_opaque pm initPM 1437
      { rank := 1, op := "OpName.FW_multiref", ins := [10578], outs := [16383, 16387], params := [2] }
      10578 16383 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10578 16383 16387)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8342
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16375, denoteGraph_ringAttn pm initPM 16383] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16375).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16383).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8342).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8342 8342 16375 16383 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8369 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5601`.
    Identity alias: `8369` reconstructs exactly as `5601` (allGather of its shards). -/
theorem recon_intermediateGoal_8369_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8369
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5601 5601 10581 10582
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5601_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8369 = denoteGraph_ringAttn sm initSM 5601 :=
    ringAttn_reduce1_pm_opaque sm initSM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] }
      5601 8369 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5601 8353 8357 8361 8365 8369 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16410 = denoteGraph_ringAttn pm initPM 10581 :=
    ringAttn_reduce1_pm_opaque pm initPM 1440
      { rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] }
      10581 16410 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 10581 16394 16398 16402 16406 16410 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16433 = denoteGraph_ringAttn pm initPM 10582 :=
    ringAttn_reduce1_pm_opaque pm initPM 1441
      { rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] }
      10582 16433 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 10582 16417 16421 16425 16429 16433 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8369
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16410, denoteGraph_ringAttn pm initPM 16433] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16410).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16433).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8369).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8369 8369 16410 16433 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8400 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5650`.
    Identity alias: `8400` reconstructs exactly as `5650` (allGather of its shards). -/
theorem recon_intermediateGoal_8400_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8400
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5650 5650 10753 10754
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5650_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8400 = denoteGraph_ringAttn sm initSM 5650 :=
    ringAttn_reduce1_pm_opaque sm initSM 724
      { rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] }
      5650 8400 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5650 8392 8396 8400 8404 8408 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16480 = denoteGraph_ringAttn pm initPM 10753 :=
    ringAttn_reduce1_pm_opaque pm initPM 1510
      { rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] }
      10753 16480 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 10753 16472 16476 16480 16484 16488 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16503 = denoteGraph_ringAttn pm initPM 10754 :=
    ringAttn_reduce1_pm_opaque pm initPM 1511
      { rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] }
      10754 16503 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 10754 16495 16499 16503 16507 16511 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8400
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16480, denoteGraph_ringAttn pm initPM 16503] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16480).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16503).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8400).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8400 8400 16480 16503 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8431 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5699`.
    Identity alias: `8431` reconstructs exactly as `5699` (allGather of its shards). -/
theorem recon_intermediateGoal_8431_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8431
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5699 5699 10925 10926
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5699_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8431 = denoteGraph_ringAttn sm initSM 5699 :=
    ringAttn_reduce1_pm_opaque sm initSM 759
      { rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] }
      5699 8431 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5699 8431 8435 8439 8443 8447)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16550 = denoteGraph_ringAttn pm initPM 10925 :=
    ringAttn_reduce1_pm_opaque pm initPM 1580
      { rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] }
      10925 16550 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 10925 16550 16554 16558 16562 16566)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16573 = denoteGraph_ringAttn pm initPM 10926 :=
    ringAttn_reduce1_pm_opaque pm initPM 1581
      { rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] }
      10926 16573 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 10926 16573 16577 16581 16585 16589)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8431
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16550, denoteGraph_ringAttn pm initPM 16573] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16550).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16573).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8431).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8431 8431 16550 16573 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8451 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5730`.
    Identity alias: `8451` reconstructs exactly as `5730` (allGather of its shards). -/
theorem recon_intermediateGoal_8451_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8451
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5730 5730 11033 11034
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5730_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8451 = denoteGraph_ringAttn sm initSM 5730 :=
    ringAttn_reduce1_pm_opaque sm initSM 782
      { rank := 0, op := "OpName.FW_multiref", ins := [5730], outs := [8451, 8455], params := [2] }
      5730 8451 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5730 8451 8455)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16593 = denoteGraph_ringAttn pm initPM 11033 :=
    ringAttn_reduce1_pm_opaque pm initPM 1626
      { rank := 0, op := "OpName.FW_multiref", ins := [11033], outs := [16593, 16597], params := [2] }
      11033 16593 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11033 16593 16597)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16601 = denoteGraph_ringAttn pm initPM 11034 :=
    ringAttn_reduce1_pm_opaque pm initPM 1627
      { rank := 1, op := "OpName.FW_multiref", ins := [11034], outs := [16601, 16605], params := [2] }
      11034 16601 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11034 16601 16605)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8451
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16593, denoteGraph_ringAttn pm initPM 16601] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16593).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16601).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8451).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8451 8451 16593 16601 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8482 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5748`.
    Identity alias: `8482` reconstructs exactly as `5748` (allGather of its shards). -/
theorem recon_intermediateGoal_8482_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8482
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5748 5748 11097 11098
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5748_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8482 = denoteGraph_ringAttn sm initSM 5748 :=
    ringAttn_reduce1_pm_opaque sm initSM 794
      { rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] }
      5748 8482 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5748 8470 8474 8478 8482 8486 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16640 = denoteGraph_ringAttn pm initPM 11097 :=
    ringAttn_reduce1_pm_opaque pm initPM 1650
      { rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] }
      11097 16640 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 11097 16628 16632 16636 16640 16644 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16663 = denoteGraph_ringAttn pm initPM 11098 :=
    ringAttn_reduce1_pm_opaque pm initPM 1651
      { rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] }
      11098 16663 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 11098 16651 16655 16659 16663 16667 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8482
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16640, denoteGraph_ringAttn pm initPM 16663] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16640).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16663).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8482).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8482 8482 16640 16663 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8513 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5797`.
    Identity alias: `8513` reconstructs exactly as `5797` (allGather of its shards). -/
theorem recon_intermediateGoal_8513_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8513
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5797 5797 11269 11270
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5797_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8513 = denoteGraph_ringAttn sm initSM 5797 :=
    ringAttn_reduce1_pm_opaque sm initSM 829
      { rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] }
      5797 8513 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5797 8509 8513 8517 8521 8525 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16710 = denoteGraph_ringAttn pm initPM 11269 :=
    ringAttn_reduce1_pm_opaque pm initPM 1720
      { rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] }
      11269 16710 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 11269 16706 16710 16714 16718 16722 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16733 = denoteGraph_ringAttn pm initPM 11270 :=
    ringAttn_reduce1_pm_opaque pm initPM 1721
      { rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] }
      11270 16733 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 11270 16729 16733 16737 16741 16745 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8513
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16710, denoteGraph_ringAttn pm initPM 16733] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16710).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16733).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8513).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8513 8513 16710 16733 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8537 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5844`.
    Identity alias: `8537` reconstructs exactly as `5844` (allGather of its shards). -/
theorem recon_intermediateGoal_8537_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8537
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5844 5844 11437 11438
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5844_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8537 = denoteGraph_ringAttn sm initSM 5844 :=
    ringAttn_reduce1_pm_opaque sm initSM 862
      { rank := 0, op := "OpName.FW_multiref", ins := [5844], outs := [8537, 8541], params := [2] }
      5844 8537 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5844 8537 8541)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16765 = denoteGraph_ringAttn pm initPM 11437 :=
    ringAttn_reduce1_pm_opaque pm initPM 1786
      { rank := 0, op := "OpName.FW_multiref", ins := [11437], outs := [16765, 16769], params := [2] }
      11437 16765 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11437 16765 16769)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16773 = denoteGraph_ringAttn pm initPM 11438 :=
    ringAttn_reduce1_pm_opaque pm initPM 1787
      { rank := 1, op := "OpName.FW_multiref", ins := [11438], outs := [16773, 16777], params := [2] }
      11438 16773 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11438 16773 16777)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8537
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16765, denoteGraph_ringAttn pm initPM 16773] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16765).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16773).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8537).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8537 8537 16765 16773 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8564 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5846`.
    Identity alias: `8564` reconstructs exactly as `5846` (allGather of its shards). -/
theorem recon_intermediateGoal_8564_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8564
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5846 5846 11441 11442
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8564 = denoteGraph_ringAttn sm initSM 5846 :=
    ringAttn_reduce1_pm_opaque sm initSM 864
      { rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] }
      5846 8564 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5846 8548 8552 8556 8560 8564 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16800 = denoteGraph_ringAttn pm initPM 11441 :=
    ringAttn_reduce1_pm_opaque pm initPM 1790
      { rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] }
      11441 16800 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 11441 16784 16788 16792 16796 16800 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16823 = denoteGraph_ringAttn pm initPM 11442 :=
    ringAttn_reduce1_pm_opaque pm initPM 1791
      { rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] }
      11442 16823 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 11442 16807 16811 16815 16819 16823 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8564
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16800, denoteGraph_ringAttn pm initPM 16823] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16800).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16823).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8564).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8564 8564 16800 16823 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8595 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5895`.
    Identity alias: `8595` reconstructs exactly as `5895` (allGather of its shards). -/
theorem recon_intermediateGoal_8595_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8595
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5895 5895 11613 11614
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5895_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8595 = denoteGraph_ringAttn sm initSM 5895 :=
    ringAttn_reduce1_pm_opaque sm initSM 899
      { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }
      5895 8595 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5895 8587 8591 8595 8599 8603 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16870 = denoteGraph_ringAttn pm initPM 11613 :=
    ringAttn_reduce1_pm_opaque pm initPM 1860
      { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }
      11613 16870 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 11613 16862 16866 16870 16874 16878 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16893 = denoteGraph_ringAttn pm initPM 11614 :=
    ringAttn_reduce1_pm_opaque pm initPM 1861
      { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }
      11614 16893 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 11614 16885 16889 16893 16897 16901 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8595
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16870, denoteGraph_ringAttn pm initPM 16893] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16870).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16893).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8595).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8595 8595 16870 16893 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
