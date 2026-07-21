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

/-- 7496 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4792`.
    Identity alias: `7496` reconstructs exactly as `4792` (allGather of its shards). -/
theorem recon_intermediateGoal_7496_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7496
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4792 4792 7769 7770
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4792_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7496 = denoteGraph_ringAttn sm initSM 4792 :=
    ringAttn_reduce1_pm_opaque sm initSM 82
      { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
      4792 7496 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4792 7496 7500 7504)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14718 = denoteGraph_ringAttn pm initPM 7769 :=
    ringAttn_reduce1_pm_opaque pm initPM 225
      { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
      7769 14718 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 7769 14718 14722 14726)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14731 = denoteGraph_ringAttn pm initPM 7770 :=
    ringAttn_reduce1_pm_opaque pm initPM 226
      { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
      7770 14731 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 7770 14731 14735 14739)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7496
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14718, denoteGraph_ringAttn pm initPM 14731] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14718).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14731).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7496).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7496 7496 14718 14731 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7523 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4813`.
    Identity alias: `7523` reconstructs exactly as `4813` (allGather of its shards). -/
theorem recon_intermediateGoal_7523_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7523
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7523 = denoteGraph_ringAttn sm initSM 4813 :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7523 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14766 = denoteGraph_ringAttn pm initPM 7843 :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14766 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14789 = denoteGraph_ringAttn pm initPM 7844 :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14789 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7523
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14766, denoteGraph_ringAttn pm initPM 14789] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14766).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14789).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7523).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7523 7523 14766 14789 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7548 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4846`.
    Identity alias: `7548` reconstructs exactly as `4846` (allGather of its shards). -/
theorem recon_intermediateGoal_7548_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7548
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4846 4846 7955 7956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7548 = denoteGraph_ringAttn sm initSM 4846 :=
    ringAttn_reduce1_pm_opaque sm initSM 121
      { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
      4846 7548 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4846 7548 7552 7556)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14822 = denoteGraph_ringAttn pm initPM 7955 :=
    ringAttn_reduce1_pm_opaque pm initPM 303
      { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
      7955 14822 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 7955 14822 14826 14830)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14835 = denoteGraph_ringAttn pm initPM 7956 :=
    ringAttn_reduce1_pm_opaque pm initPM 304
      { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
      7956 14835 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 7956 14835 14839 14843)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7548
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14822, denoteGraph_ringAttn pm initPM 14835] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14822).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14835).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7548).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7548 7548 14822 14835 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7575 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4867`.
    Identity alias: `7575` reconstructs exactly as `4867` (allGather of its shards). -/
theorem recon_intermediateGoal_7575_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7575
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7575 = denoteGraph_ringAttn sm initSM 4867 :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7575 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14870 = denoteGraph_ringAttn pm initPM 8029 :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14870 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14893 = denoteGraph_ringAttn pm initPM 8030 :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14893 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7575
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14870, denoteGraph_ringAttn pm initPM 14893] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14870).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14893).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7575).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7575 7575 14870 14893 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7600 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4900`.
    Identity alias: `7600` reconstructs exactly as `4900` (allGather of its shards). -/
theorem recon_intermediateGoal_7600_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7600
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4900 4900 8141 8142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4900_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7600 = denoteGraph_ringAttn sm initSM 4900 :=
    ringAttn_reduce1_pm_opaque sm initSM 160
      { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
      4900 7600 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4900 7600 7604 7608)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14926 = denoteGraph_ringAttn pm initPM 8141 :=
    ringAttn_reduce1_pm_opaque pm initPM 381
      { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
      8141 14926 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8141 14926 14930 14934)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14939 = denoteGraph_ringAttn pm initPM 8142 :=
    ringAttn_reduce1_pm_opaque pm initPM 382
      { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
      8142 14939 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8142 14939 14943 14947)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7600
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14926, denoteGraph_ringAttn pm initPM 14939] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14926).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14939).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7600).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7600 7600 14926 14939 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7627 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4921`.
    Identity alias: `7627` reconstructs exactly as `4921` (allGather of its shards). -/
theorem recon_intermediateGoal_7627_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7627
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7627 = denoteGraph_ringAttn sm initSM 4921 :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7627 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14974 = denoteGraph_ringAttn pm initPM 8215 :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14974 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14997 = denoteGraph_ringAttn pm initPM 8216 :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 14997 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7627
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14974, denoteGraph_ringAttn pm initPM 14997] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14974).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14997).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7627).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7627 7627 14974 14997 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7652 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4954`.
    Identity alias: `7652` reconstructs exactly as `4954` (allGather of its shards). -/
theorem recon_intermediateGoal_7652_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7652
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4954 4954 8327 8328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4954_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7652 = denoteGraph_ringAttn sm initSM 4954 :=
    ringAttn_reduce1_pm_opaque sm initSM 199
      { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
      4954 7652 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4954 7652 7656 7660)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15030 = denoteGraph_ringAttn pm initPM 8327 :=
    ringAttn_reduce1_pm_opaque pm initPM 459
      { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
      8327 15030 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8327 15030 15034 15038)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15043 = denoteGraph_ringAttn pm initPM 8328 :=
    ringAttn_reduce1_pm_opaque pm initPM 460
      { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
      8328 15043 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8328 15043 15047 15051)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7652
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15030, denoteGraph_ringAttn pm initPM 15043] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15030).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15043).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7652).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7652 7652 15030 15043 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7679 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `4975`.
    Identity alias: `7679` reconstructs exactly as `4975` (allGather of its shards). -/
theorem recon_intermediateGoal_7679_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7679
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7679 = denoteGraph_ringAttn sm initSM 4975 :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7679 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15078 = denoteGraph_ringAttn pm initPM 8401 :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15078 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15101 = denoteGraph_ringAttn pm initPM 8402 :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15101 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7679
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15078, denoteGraph_ringAttn pm initPM 15101] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15078).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15101).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7679).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7679 7679 15078 15101 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7704 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5008`.
    Identity alias: `7704` reconstructs exactly as `5008` (allGather of its shards). -/
theorem recon_intermediateGoal_7704_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7704
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5008 5008 8513 8514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5008_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7704 = denoteGraph_ringAttn sm initSM 5008 :=
    ringAttn_reduce1_pm_opaque sm initSM 238
      { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
      5008 7704 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5008 7704 7708 7712)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15134 = denoteGraph_ringAttn pm initPM 8513 :=
    ringAttn_reduce1_pm_opaque pm initPM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
      8513 15134 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8513 15134 15138 15142)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15147 = denoteGraph_ringAttn pm initPM 8514 :=
    ringAttn_reduce1_pm_opaque pm initPM 538
      { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
      8514 15147 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8514 15147 15151 15155)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7704
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15134, denoteGraph_ringAttn pm initPM 15147] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15134).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15147).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7704).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7704 7704 15134 15147 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7731 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5029`.
    Identity alias: `7731` reconstructs exactly as `5029` (allGather of its shards). -/
theorem recon_intermediateGoal_7731_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7731
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7731 = denoteGraph_ringAttn sm initSM 5029 :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7731 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15182 = denoteGraph_ringAttn pm initPM 8587 :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15182 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15205 = denoteGraph_ringAttn pm initPM 8588 :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15205 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7731
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15182, denoteGraph_ringAttn pm initPM 15205] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15182).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15205).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7731).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7731 7731 15182 15205 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7756 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5062`.
    Identity alias: `7756` reconstructs exactly as `5062` (allGather of its shards). -/
theorem recon_intermediateGoal_7756_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7756
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5062 5062 8699 8700
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5062_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7756 = denoteGraph_ringAttn sm initSM 5062 :=
    ringAttn_reduce1_pm_opaque sm initSM 277
      { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
      5062 7756 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5062 7756 7760 7764)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15238 = denoteGraph_ringAttn pm initPM 8699 :=
    ringAttn_reduce1_pm_opaque pm initPM 615
      { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
      8699 15238 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8699 15238 15242 15246)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15251 = denoteGraph_ringAttn pm initPM 8700 :=
    ringAttn_reduce1_pm_opaque pm initPM 616
      { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
      8700 15251 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8700 15251 15255 15259)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7756
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15238, denoteGraph_ringAttn pm initPM 15251] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15238).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15251).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7756).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7756 7756 15238 15251 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7783 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5083`.
    Identity alias: `7783` reconstructs exactly as `5083` (allGather of its shards). -/
theorem recon_intermediateGoal_7783_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7783
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7783 = denoteGraph_ringAttn sm initSM 5083 :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7783 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15286 = denoteGraph_ringAttn pm initPM 8773 :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15286 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15309 = denoteGraph_ringAttn pm initPM 8774 :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15309 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7783
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15286, denoteGraph_ringAttn pm initPM 15309] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15286).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15309).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7783).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7783 7783 15286 15309 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7808 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5116`.
    Identity alias: `7808` reconstructs exactly as `5116` (allGather of its shards). -/
theorem recon_intermediateGoal_7808_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7808
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5116 5116 8885 8886
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5116_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7808 = denoteGraph_ringAttn sm initSM 5116 :=
    ringAttn_reduce1_pm_opaque sm initSM 316
      { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
      5116 7808 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5116 7808 7812 7816)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15342 = denoteGraph_ringAttn pm initPM 8885 :=
    ringAttn_reduce1_pm_opaque pm initPM 693
      { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
      8885 15342 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 8885 15342 15346 15350)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15355 = denoteGraph_ringAttn pm initPM 8886 :=
    ringAttn_reduce1_pm_opaque pm initPM 694
      { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
      8886 15355 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 8886 15355 15359 15363)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7808
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15342, denoteGraph_ringAttn pm initPM 15355] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15342).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15355).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7808).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7808 7808 15342 15355 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7835 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5137`.
    Identity alias: `7835` reconstructs exactly as `5137` (allGather of its shards). -/
theorem recon_intermediateGoal_7835_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7835
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7835 = denoteGraph_ringAttn sm initSM 5137 :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7835 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15390 = denoteGraph_ringAttn pm initPM 8959 :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15390 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15413 = denoteGraph_ringAttn pm initPM 8960 :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15413 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7835
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15390, denoteGraph_ringAttn pm initPM 15413] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15390).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15413).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7835).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7835 7835 15390 15413 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7860 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5170`.
    Identity alias: `7860` reconstructs exactly as `5170` (allGather of its shards). -/
theorem recon_intermediateGoal_7860_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7860
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5170 5170 9071 9072
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5170_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7860 = denoteGraph_ringAttn sm initSM 5170 :=
    ringAttn_reduce1_pm_opaque sm initSM 355
      { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
      5170 7860 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5170 7860 7864 7868)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15446 = denoteGraph_ringAttn pm initPM 9071 :=
    ringAttn_reduce1_pm_opaque pm initPM 771
      { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
      9071 15446 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 9071 15446 15450 15454)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15459 = denoteGraph_ringAttn pm initPM 9072 :=
    ringAttn_reduce1_pm_opaque pm initPM 772
      { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
      9072 15459 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 9072 15459 15463 15467)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7860
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15446, denoteGraph_ringAttn pm initPM 15459] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15446).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15459).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7860).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7860 7860 15446 15459 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7887 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5191`.
    Identity alias: `7887` reconstructs exactly as `5191` (allGather of its shards). -/
theorem recon_intermediateGoal_7887_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7887
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7887 = denoteGraph_ringAttn sm initSM 5191 :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7887 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15494 = denoteGraph_ringAttn pm initPM 9145 :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15494 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15517 = denoteGraph_ringAttn pm initPM 9146 :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15517 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7887
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15494, denoteGraph_ringAttn pm initPM 15517] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15494).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15517).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7887).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7887 7887 15494 15517 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7912 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5224`.
    Identity alias: `7912` reconstructs exactly as `5224` (allGather of its shards). -/
theorem recon_intermediateGoal_7912_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7912
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5224 5224 9257 9258
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5224_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7912 = denoteGraph_ringAttn sm initSM 5224 :=
    ringAttn_reduce1_pm_opaque sm initSM 394
      { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
      5224 7912 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5224 7912 7916 7920)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15550 = denoteGraph_ringAttn pm initPM 9257 :=
    ringAttn_reduce1_pm_opaque pm initPM 849
      { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
      9257 15550 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 9257 15550 15554 15558)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15563 = denoteGraph_ringAttn pm initPM 9258 :=
    ringAttn_reduce1_pm_opaque pm initPM 850
      { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
      9258 15563 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 9258 15563 15567 15571)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7912
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15550, denoteGraph_ringAttn pm initPM 15563] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15550).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15563).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7912).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7912 7912 15550 15563 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7939 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5245`.
    Identity alias: `7939` reconstructs exactly as `5245` (allGather of its shards). -/
theorem recon_intermediateGoal_7939_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7939
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7939 = denoteGraph_ringAttn sm initSM 5245 :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7939 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15598 = denoteGraph_ringAttn pm initPM 9331 :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15598 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15621 = denoteGraph_ringAttn pm initPM 9332 :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15621 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7939
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15598, denoteGraph_ringAttn pm initPM 15621] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15598).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15621).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7939).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7939 7939 15598 15621 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7964 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5278`.
    Identity alias: `7964` reconstructs exactly as `5278` (allGather of its shards). -/
theorem recon_intermediateGoal_7964_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7964
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5278 5278 9443 9444
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5278_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7964 = denoteGraph_ringAttn sm initSM 5278 :=
    ringAttn_reduce1_pm_opaque sm initSM 433
      { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
      5278 7964 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 5278 7964 7968 7972)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15654 = denoteGraph_ringAttn pm initPM 9443 :=
    ringAttn_reduce1_pm_opaque pm initPM 927
      { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
      9443 15654 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 9443 15654 15658 15662)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15667 = denoteGraph_ringAttn pm initPM 9444 :=
    ringAttn_reduce1_pm_opaque pm initPM 928
      { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
      9444 15667 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 9444 15667 15671 15675)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7964
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15654, denoteGraph_ringAttn pm initPM 15667] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15654).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15667).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7964).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7964 7964 15654 15667 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7991 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5299`.
    Identity alias: `7991` reconstructs exactly as `5299` (allGather of its shards). -/
theorem recon_intermediateGoal_7991_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7991
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7991 = denoteGraph_ringAttn sm initSM 5299 :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7991 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15702 = denoteGraph_ringAttn pm initPM 9517 :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15702 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15725 = denoteGraph_ringAttn pm initPM 9518 :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15725 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7991
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15702, denoteGraph_ringAttn pm initPM 15725] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15702).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15725).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7991).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7991 7991 15702 15725 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8139 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5338`.
    Identity alias: `8139` reconstructs exactly as `5338` (allGather of its shards). -/
theorem recon_intermediateGoal_8139_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8139
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5338 5338 9655 9656
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5338_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8139 = denoteGraph_ringAttn sm initSM 5338 :=
    ringAttn_reduce1_pm_opaque sm initSM 474
      { rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] }
      5338 8139 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5338 8139 8143)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15969 = denoteGraph_ringAttn pm initPM 9655 :=
    ringAttn_reduce1_pm_opaque pm initPM 1006
      { rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] }
      9655 15969 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9655 15969 15973)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15977 = denoteGraph_ringAttn pm initPM 9656 :=
    ringAttn_reduce1_pm_opaque pm initPM 1009
      { rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] }
      9656 15977 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9656 15977 15981)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8139
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15969, denoteGraph_ringAttn pm initPM 15977] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15969).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15977).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8139).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8139 8139 15969 15977 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8170 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5356`.
    Identity alias: `8170` reconstructs exactly as `5356` (allGather of its shards). -/
theorem recon_intermediateGoal_8170_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8170
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8170 = denoteGraph_ringAttn sm initSM 5356 :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8170 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16016 = denoteGraph_ringAttn pm initPM 9721 :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16016 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16039 = denoteGraph_ringAttn pm initPM 9722 :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16039 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8170
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16016, denoteGraph_ringAttn pm initPM 16039] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16016).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16039).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8170).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8170 8170 16016 16039 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8201 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5405`.
    Identity alias: `8201` reconstructs exactly as `5405` (allGather of its shards). -/
theorem recon_intermediateGoal_8201_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8201
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5405 5405 9893 9894
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5405_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8201 = denoteGraph_ringAttn sm initSM 5405 :=
    ringAttn_reduce1_pm_opaque sm initSM 549
      { rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] }
      5405 8201 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5405 8197 8201 8205 8209 8213 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16086 = denoteGraph_ringAttn pm initPM 9893 :=
    ringAttn_reduce1_pm_opaque pm initPM 1160
      { rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] }
      9893 16086 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9893 16082 16086 16090 16094 16098 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16109 = denoteGraph_ringAttn pm initPM 9894 :=
    ringAttn_reduce1_pm_opaque pm initPM 1161
      { rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] }
      9894 16109 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9894 16105 16109 16113 16117 16121 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8201
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16086, denoteGraph_ringAttn pm initPM 16109] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16086).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16109).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8201).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8201 8201 16086 16109 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8225 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5452`.
    Identity alias: `8225` reconstructs exactly as `5452` (allGather of its shards). -/
theorem recon_intermediateGoal_8225_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8225
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5452 5452 10061 10062
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5452_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8225 = denoteGraph_ringAttn sm initSM 5452 :=
    ringAttn_reduce1_pm_opaque sm initSM 582
      { rank := 0, op := "OpName.FW_multiref", ins := [5452], outs := [8225, 8229], params := [2] }
      5452 8225 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5452 8225 8229)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16141 = denoteGraph_ringAttn pm initPM 10061 :=
    ringAttn_reduce1_pm_opaque pm initPM 1226
      { rank := 0, op := "OpName.FW_multiref", ins := [10061], outs := [16141, 16145], params := [2] }
      10061 16141 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10061 16141 16145)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16149 = denoteGraph_ringAttn pm initPM 10062 :=
    ringAttn_reduce1_pm_opaque pm initPM 1227
      { rank := 1, op := "OpName.FW_multiref", ins := [10062], outs := [16149, 16153], params := [2] }
      10062 16149 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10062 16149 16153)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8225
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16141, denoteGraph_ringAttn pm initPM 16149] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16141).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16149).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8225).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8225 8225 16141 16149 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8252 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5454`.
    Identity alias: `8252` reconstructs exactly as `5454` (allGather of its shards). -/
theorem recon_intermediateGoal_8252_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8252
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5454 5454 10065 10066
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5454_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8252 = denoteGraph_ringAttn sm initSM 5454 :=
    ringAttn_reduce1_pm_opaque sm initSM 584
      { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] }
      5454 8252 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5454 8236 8240 8244 8248 8252 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16176 = denoteGraph_ringAttn pm initPM 10065 :=
    ringAttn_reduce1_pm_opaque pm initPM 1230
      { rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] }
      10065 16176 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 10065 16160 16164 16168 16172 16176 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16199 = denoteGraph_ringAttn pm initPM 10066 :=
    ringAttn_reduce1_pm_opaque pm initPM 1231
      { rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] }
      10066 16199 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 10066 16183 16187 16191 16195 16199 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8252
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16176, denoteGraph_ringAttn pm initPM 16199] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16176).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16199).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8252).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8252 8252 16176 16199 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8283 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5503`.
    Identity alias: `8283` reconstructs exactly as `5503` (allGather of its shards). -/
theorem recon_intermediateGoal_8283_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8283
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5503 5503 10237 10238
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5503_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8283 = denoteGraph_ringAttn sm initSM 5503 :=
    ringAttn_reduce1_pm_opaque sm initSM 619
      { rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] }
      5503 8283 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5503 8275 8279 8283 8287 8291 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16246 = denoteGraph_ringAttn pm initPM 10237 :=
    ringAttn_reduce1_pm_opaque pm initPM 1300
      { rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] }
      10237 16246 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 10237 16238 16242 16246 16250 16254 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16269 = denoteGraph_ringAttn pm initPM 10238 :=
    ringAttn_reduce1_pm_opaque pm initPM 1301
      { rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] }
      10238 16269 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 10238 16261 16265 16269 16273 16277 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8283
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16246, denoteGraph_ringAttn pm initPM 16269] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16246).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16269).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8283).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8283 8283 16246 16269 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8314 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5552`.
    Identity alias: `8314` reconstructs exactly as `5552` (allGather of its shards). -/
theorem recon_intermediateGoal_8314_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8314
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5552 5552 10409 10410
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5552_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8314 = denoteGraph_ringAttn sm initSM 5552 :=
    ringAttn_reduce1_pm_opaque sm initSM 654
      { rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] }
      5552 8314 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5552 8314 8318 8322 8326 8330)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16316 = denoteGraph_ringAttn pm initPM 10409 :=
    ringAttn_reduce1_pm_opaque pm initPM 1370
      { rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] }
      10409 16316 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 10409 16316 16320 16324 16328 16332)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16339 = denoteGraph_ringAttn pm initPM 10410 :=
    ringAttn_reduce1_pm_opaque pm initPM 1371
      { rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] }
      10410 16339 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 10410 16339 16343 16347 16351 16355)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8314
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16316, denoteGraph_ringAttn pm initPM 16339] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16316).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16339).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8314).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8314 8314 16316 16339 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8334 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5583`.
    Identity alias: `8334` reconstructs exactly as `5583` (allGather of its shards). -/
theorem recon_intermediateGoal_8334_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8334
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5583 5583 10517 10518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5583_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8334 = denoteGraph_ringAttn sm initSM 5583 :=
    ringAttn_reduce1_pm_opaque sm initSM 677
      { rank := 0, op := "OpName.FW_multiref", ins := [5583], outs := [8334, 8338], params := [2] }
      5583 8334 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5583 8334 8338)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16359 = denoteGraph_ringAttn pm initPM 10517 :=
    ringAttn_reduce1_pm_opaque pm initPM 1416
      { rank := 0, op := "OpName.FW_multiref", ins := [10517], outs := [16359, 16363], params := [2] }
      10517 16359 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10517 16359 16363)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16367 = denoteGraph_ringAttn pm initPM 10518 :=
    ringAttn_reduce1_pm_opaque pm initPM 1417
      { rank := 1, op := "OpName.FW_multiref", ins := [10518], outs := [16367, 16371], params := [2] }
      10518 16367 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10518 16367 16371)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8334
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16359, denoteGraph_ringAttn pm initPM 16367] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16359).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16367).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8334).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8334 8334 16359 16367 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8365 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5601`.
    Identity alias: `8365` reconstructs exactly as `5601` (allGather of its shards). -/
theorem recon_intermediateGoal_8365_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8365
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5601 5601 10581 10582
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5601_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8365 = denoteGraph_ringAttn sm initSM 5601 :=
    ringAttn_reduce1_pm_opaque sm initSM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] }
      5601 8365 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5601 8353 8357 8361 8365 8369 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16406 = denoteGraph_ringAttn pm initPM 10581 :=
    ringAttn_reduce1_pm_opaque pm initPM 1440
      { rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] }
      10581 16406 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 10581 16394 16398 16402 16406 16410 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16429 = denoteGraph_ringAttn pm initPM 10582 :=
    ringAttn_reduce1_pm_opaque pm initPM 1441
      { rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] }
      10582 16429 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 10582 16417 16421 16425 16429 16433 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8365
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16406, denoteGraph_ringAttn pm initPM 16429] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16406).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16429).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8365).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8365 8365 16406 16429 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8396 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5650`.
    Identity alias: `8396` reconstructs exactly as `5650` (allGather of its shards). -/
theorem recon_intermediateGoal_8396_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8396
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5650 5650 10753 10754
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5650_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8396 = denoteGraph_ringAttn sm initSM 5650 :=
    ringAttn_reduce1_pm_opaque sm initSM 724
      { rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] }
      5650 8396 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5650 8392 8396 8400 8404 8408 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16476 = denoteGraph_ringAttn pm initPM 10753 :=
    ringAttn_reduce1_pm_opaque pm initPM 1510
      { rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] }
      10753 16476 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 10753 16472 16476 16480 16484 16488 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16499 = denoteGraph_ringAttn pm initPM 10754 :=
    ringAttn_reduce1_pm_opaque pm initPM 1511
      { rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] }
      10754 16499 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 10754 16495 16499 16503 16507 16511 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8396
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16476, denoteGraph_ringAttn pm initPM 16499] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16476).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16499).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8396).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8396 8396 16476 16499 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8420 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5697`.
    Identity alias: `8420` reconstructs exactly as `5697` (allGather of its shards). -/
theorem recon_intermediateGoal_8420_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8420
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5697 5697 10921 10922
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5697_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8420 = denoteGraph_ringAttn sm initSM 5697 :=
    ringAttn_reduce1_pm_opaque sm initSM 757
      { rank := 0, op := "OpName.FW_multiref", ins := [5697], outs := [8420, 8424], params := [2] }
      5697 8420 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5697 8420 8424)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16531 = denoteGraph_ringAttn pm initPM 10921 :=
    ringAttn_reduce1_pm_opaque pm initPM 1576
      { rank := 0, op := "OpName.FW_multiref", ins := [10921], outs := [16531, 16535], params := [2] }
      10921 16531 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10921 16531 16535)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16539 = denoteGraph_ringAttn pm initPM 10922 :=
    ringAttn_reduce1_pm_opaque pm initPM 1577
      { rank := 1, op := "OpName.FW_multiref", ins := [10922], outs := [16539, 16543], params := [2] }
      10922 16539 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10922 16539 16543)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8420
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16531, denoteGraph_ringAttn pm initPM 16539] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16531).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16539).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8420).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8420 8420 16531 16539 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8447 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5699`.
    Identity alias: `8447` reconstructs exactly as `5699` (allGather of its shards). -/
theorem recon_intermediateGoal_8447_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8447
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5699 5699 10925 10926
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5699_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8447 = denoteGraph_ringAttn sm initSM 5699 :=
    ringAttn_reduce1_pm_opaque sm initSM 759
      { rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] }
      5699 8447 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5699 8431 8435 8439 8443 8447 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16566 = denoteGraph_ringAttn pm initPM 10925 :=
    ringAttn_reduce1_pm_opaque pm initPM 1580
      { rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] }
      10925 16566 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 10925 16550 16554 16558 16562 16566 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16589 = denoteGraph_ringAttn pm initPM 10926 :=
    ringAttn_reduce1_pm_opaque pm initPM 1581
      { rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] }
      10926 16589 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 10926 16573 16577 16581 16585 16589 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8447
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16566, denoteGraph_ringAttn pm initPM 16589] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16566).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16589).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8447).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8447 8447 16566 16589 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8478 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5748`.
    Identity alias: `8478` reconstructs exactly as `5748` (allGather of its shards). -/
theorem recon_intermediateGoal_8478_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8478
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5748 5748 11097 11098
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5748_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8478 = denoteGraph_ringAttn sm initSM 5748 :=
    ringAttn_reduce1_pm_opaque sm initSM 794
      { rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] }
      5748 8478 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5748 8470 8474 8478 8482 8486 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16636 = denoteGraph_ringAttn pm initPM 11097 :=
    ringAttn_reduce1_pm_opaque pm initPM 1650
      { rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] }
      11097 16636 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 11097 16628 16632 16636 16640 16644 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16659 = denoteGraph_ringAttn pm initPM 11098 :=
    ringAttn_reduce1_pm_opaque pm initPM 1651
      { rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] }
      11098 16659 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 11098 16651 16655 16659 16663 16667 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8478
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16636, denoteGraph_ringAttn pm initPM 16659] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16636).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16659).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8478).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8478 8478 16636 16659 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8509 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5797`.
    Identity alias: `8509` reconstructs exactly as `5797` (allGather of its shards). -/
theorem recon_intermediateGoal_8509_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8509
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5797 5797 11269 11270
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5797_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8509 = denoteGraph_ringAttn sm initSM 5797 :=
    ringAttn_reduce1_pm_opaque sm initSM 829
      { rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] }
      5797 8509 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5797 8509 8513 8517 8521 8525)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16706 = denoteGraph_ringAttn pm initPM 11269 :=
    ringAttn_reduce1_pm_opaque pm initPM 1720
      { rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] }
      11269 16706 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 11269 16706 16710 16714 16718 16722)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16729 = denoteGraph_ringAttn pm initPM 11270 :=
    ringAttn_reduce1_pm_opaque pm initPM 1721
      { rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] }
      11270 16729 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 11270 16729 16733 16737 16741 16745)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8509
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16706, denoteGraph_ringAttn pm initPM 16729] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16706).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16729).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8509).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8509 8509 16706 16729 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8529 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5828`.
    Identity alias: `8529` reconstructs exactly as `5828` (allGather of its shards). -/
theorem recon_intermediateGoal_8529_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8529
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5828 5828 11377 11378
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5828_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8529 = denoteGraph_ringAttn sm initSM 5828 :=
    ringAttn_reduce1_pm_opaque sm initSM 852
      { rank := 0, op := "OpName.FW_multiref", ins := [5828], outs := [8529, 8533], params := [2] }
      5828 8529 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5828 8529 8533)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16749 = denoteGraph_ringAttn pm initPM 11377 :=
    ringAttn_reduce1_pm_opaque pm initPM 1766
      { rank := 0, op := "OpName.FW_multiref", ins := [11377], outs := [16749, 16753], params := [2] }
      11377 16749 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11377 16749 16753)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16757 = denoteGraph_ringAttn pm initPM 11378 :=
    ringAttn_reduce1_pm_opaque pm initPM 1767
      { rank := 1, op := "OpName.FW_multiref", ins := [11378], outs := [16757, 16761], params := [2] }
      11378 16757 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11378 16757 16761)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8529
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16749, denoteGraph_ringAttn pm initPM 16757] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16749).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16757).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8529).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8529 8529 16749 16757 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8560 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5846`.
    Identity alias: `8560` reconstructs exactly as `5846` (allGather of its shards). -/
theorem recon_intermediateGoal_8560_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8560
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5846 5846 11441 11442
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8560 = denoteGraph_ringAttn sm initSM 5846 :=
    ringAttn_reduce1_pm_opaque sm initSM 864
      { rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] }
      5846 8560 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5846 8548 8552 8556 8560 8564 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16796 = denoteGraph_ringAttn pm initPM 11441 :=
    ringAttn_reduce1_pm_opaque pm initPM 1790
      { rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] }
      11441 16796 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 11441 16784 16788 16792 16796 16800 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16819 = denoteGraph_ringAttn pm initPM 11442 :=
    ringAttn_reduce1_pm_opaque pm initPM 1791
      { rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] }
      11442 16819 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 11442 16807 16811 16815 16819 16823 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8560
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16796, denoteGraph_ringAttn pm initPM 16819] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16796).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16819).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8560).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8560 8560 16796 16819 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8591 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5895`.
    Identity alias: `8591` reconstructs exactly as `5895` (allGather of its shards). -/
theorem recon_intermediateGoal_8591_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8591
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5895 5895 11613 11614
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5895_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8591 = denoteGraph_ringAttn sm initSM 5895 :=
    ringAttn_reduce1_pm_opaque sm initSM 899
      { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }
      5895 8591 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5895 8587 8591 8595 8599 8603 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16866 = denoteGraph_ringAttn pm initPM 11613 :=
    ringAttn_reduce1_pm_opaque pm initPM 1860
      { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }
      11613 16866 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 11613 16862 16866 16870 16874 16878 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16889 = denoteGraph_ringAttn pm initPM 11614 :=
    ringAttn_reduce1_pm_opaque pm initPM 1861
      { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }
      11614 16889 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 11614 16885 16889 16893 16897 16901 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8591
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16866, denoteGraph_ringAttn pm initPM 16889] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16866).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16889).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8591).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8591 8591 16866 16889 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
