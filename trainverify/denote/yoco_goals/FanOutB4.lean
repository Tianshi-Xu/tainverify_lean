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

/-- 7504 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4792`.
    Identity alias: `7504` reconstructs exactly as `4792` (allGather of its shards). -/
theorem recon_intermediateGoal_7504_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7504
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4792 4792 7769 7770
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4792_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7504 = denoteGraph_ringAttn sm initSM 4792 :=
    ringAttn_reduce1_pm_opaque sm initSM 82
      { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
      4792 7504 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4792 7496 7500 7504 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14726 = denoteGraph_ringAttn pm initPM 7769 :=
    ringAttn_reduce1_pm_opaque pm initPM 225
      { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
      7769 14726 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 7769 14718 14722 14726 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14739 = denoteGraph_ringAttn pm initPM 7770 :=
    ringAttn_reduce1_pm_opaque pm initPM 226
      { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
      7770 14739 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 7770 14731 14735 14739 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7504
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14726, denoteGraph_ringAttn pm initPM 14739] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14726).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14739).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7504).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7504 7504 14726 14739 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7531 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `4813`.
    Identity alias: `7531` reconstructs exactly as `4813` (allGather of its shards). -/
theorem recon_intermediateGoal_7531_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7531
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7531 = denoteGraph_ringAttn sm initSM 4813 :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7531 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14774 = denoteGraph_ringAttn pm initPM 7843 :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14774 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14797 = denoteGraph_ringAttn pm initPM 7844 :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14797 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7531
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14774, denoteGraph_ringAttn pm initPM 14797] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14774).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14797).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7531).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7531 7531 14774 14797 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7556 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4846`.
    Identity alias: `7556` reconstructs exactly as `4846` (allGather of its shards). -/
theorem recon_intermediateGoal_7556_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7556
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4846 4846 7955 7956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7556 = denoteGraph_ringAttn sm initSM 4846 :=
    ringAttn_reduce1_pm_opaque sm initSM 121
      { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
      4846 7556 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4846 7548 7552 7556 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14830 = denoteGraph_ringAttn pm initPM 7955 :=
    ringAttn_reduce1_pm_opaque pm initPM 303
      { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
      7955 14830 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 7955 14822 14826 14830 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14843 = denoteGraph_ringAttn pm initPM 7956 :=
    ringAttn_reduce1_pm_opaque pm initPM 304
      { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
      7956 14843 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 7956 14835 14839 14843 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7556
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14830, denoteGraph_ringAttn pm initPM 14843] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14830).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14843).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7556).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7556 7556 14830 14843 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7583 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `4867`.
    Identity alias: `7583` reconstructs exactly as `4867` (allGather of its shards). -/
theorem recon_intermediateGoal_7583_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7583
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7583 = denoteGraph_ringAttn sm initSM 4867 :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7583 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14878 = denoteGraph_ringAttn pm initPM 8029 :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14878 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14901 = denoteGraph_ringAttn pm initPM 8030 :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14901 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7583
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14878, denoteGraph_ringAttn pm initPM 14901] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14878).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14901).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7583).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7583 7583 14878 14901 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7608 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4900`.
    Identity alias: `7608` reconstructs exactly as `4900` (allGather of its shards). -/
theorem recon_intermediateGoal_7608_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7608
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4900 4900 8141 8142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4900_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7608 = denoteGraph_ringAttn sm initSM 4900 :=
    ringAttn_reduce1_pm_opaque sm initSM 160
      { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
      4900 7608 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4900 7600 7604 7608 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14934 = denoteGraph_ringAttn pm initPM 8141 :=
    ringAttn_reduce1_pm_opaque pm initPM 381
      { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
      8141 14934 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8141 14926 14930 14934 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14947 = denoteGraph_ringAttn pm initPM 8142 :=
    ringAttn_reduce1_pm_opaque pm initPM 382
      { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
      8142 14947 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8142 14939 14943 14947 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7608
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14934, denoteGraph_ringAttn pm initPM 14947] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14934).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14947).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7608).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7608 7608 14934 14947 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7635 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `4921`.
    Identity alias: `7635` reconstructs exactly as `4921` (allGather of its shards). -/
theorem recon_intermediateGoal_7635_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7635
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7635 = denoteGraph_ringAttn sm initSM 4921 :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7635 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14982 = denoteGraph_ringAttn pm initPM 8215 :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14982 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15005 = denoteGraph_ringAttn pm initPM 8216 :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 15005 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7635
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14982, denoteGraph_ringAttn pm initPM 15005] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14982).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15005).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7635).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7635 7635 14982 15005 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7660 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `4954`.
    Identity alias: `7660` reconstructs exactly as `4954` (allGather of its shards). -/
theorem recon_intermediateGoal_7660_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7660
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4954 4954 8327 8328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4954_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7660 = denoteGraph_ringAttn sm initSM 4954 :=
    ringAttn_reduce1_pm_opaque sm initSM 199
      { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
      4954 7660 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4954 7652 7656 7660 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15038 = denoteGraph_ringAttn pm initPM 8327 :=
    ringAttn_reduce1_pm_opaque pm initPM 459
      { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
      8327 15038 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8327 15030 15034 15038 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15051 = denoteGraph_ringAttn pm initPM 8328 :=
    ringAttn_reduce1_pm_opaque pm initPM 460
      { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
      8328 15051 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8328 15043 15047 15051 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7660
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15038, denoteGraph_ringAttn pm initPM 15051] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15038).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15051).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7660).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7660 7660 15038 15051 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7687 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `4975`.
    Identity alias: `7687` reconstructs exactly as `4975` (allGather of its shards). -/
theorem recon_intermediateGoal_7687_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7687
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7687 = denoteGraph_ringAttn sm initSM 4975 :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7687 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15086 = denoteGraph_ringAttn pm initPM 8401 :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15086 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15109 = denoteGraph_ringAttn pm initPM 8402 :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15109 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7687
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15086, denoteGraph_ringAttn pm initPM 15109] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15086).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15109).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7687).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7687 7687 15086 15109 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7712 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5008`.
    Identity alias: `7712` reconstructs exactly as `5008` (allGather of its shards). -/
theorem recon_intermediateGoal_7712_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7712
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5008 5008 8513 8514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5008_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7712 = denoteGraph_ringAttn sm initSM 5008 :=
    ringAttn_reduce1_pm_opaque sm initSM 238
      { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
      5008 7712 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5008 7704 7708 7712 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15142 = denoteGraph_ringAttn pm initPM 8513 :=
    ringAttn_reduce1_pm_opaque pm initPM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
      8513 15142 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8513 15134 15138 15142 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15155 = denoteGraph_ringAttn pm initPM 8514 :=
    ringAttn_reduce1_pm_opaque pm initPM 538
      { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
      8514 15155 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8514 15147 15151 15155 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7712
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15142, denoteGraph_ringAttn pm initPM 15155] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15142).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15155).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7712).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7712 7712 15142 15155 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7739 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5029`.
    Identity alias: `7739` reconstructs exactly as `5029` (allGather of its shards). -/
theorem recon_intermediateGoal_7739_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7739
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7739 = denoteGraph_ringAttn sm initSM 5029 :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7739 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15190 = denoteGraph_ringAttn pm initPM 8587 :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15190 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15213 = denoteGraph_ringAttn pm initPM 8588 :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15213 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7739
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15190, denoteGraph_ringAttn pm initPM 15213] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15190).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15213).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7739).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7739 7739 15190 15213 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7764 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5062`.
    Identity alias: `7764` reconstructs exactly as `5062` (allGather of its shards). -/
theorem recon_intermediateGoal_7764_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7764
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5062 5062 8699 8700
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5062_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7764 = denoteGraph_ringAttn sm initSM 5062 :=
    ringAttn_reduce1_pm_opaque sm initSM 277
      { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
      5062 7764 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5062 7756 7760 7764 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15246 = denoteGraph_ringAttn pm initPM 8699 :=
    ringAttn_reduce1_pm_opaque pm initPM 615
      { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
      8699 15246 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8699 15238 15242 15246 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15259 = denoteGraph_ringAttn pm initPM 8700 :=
    ringAttn_reduce1_pm_opaque pm initPM 616
      { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
      8700 15259 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8700 15251 15255 15259 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7764
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15246, denoteGraph_ringAttn pm initPM 15259] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15246).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15259).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7764).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7764 7764 15246 15259 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7791 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5083`.
    Identity alias: `7791` reconstructs exactly as `5083` (allGather of its shards). -/
theorem recon_intermediateGoal_7791_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7791
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7791 = denoteGraph_ringAttn sm initSM 5083 :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7791 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15294 = denoteGraph_ringAttn pm initPM 8773 :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15294 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15317 = denoteGraph_ringAttn pm initPM 8774 :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15317 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7791
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15294, denoteGraph_ringAttn pm initPM 15317] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15294).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15317).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7791).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7791 7791 15294 15317 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7816 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5116`.
    Identity alias: `7816` reconstructs exactly as `5116` (allGather of its shards). -/
theorem recon_intermediateGoal_7816_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7816
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5116 5116 8885 8886
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5116_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7816 = denoteGraph_ringAttn sm initSM 5116 :=
    ringAttn_reduce1_pm_opaque sm initSM 316
      { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
      5116 7816 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5116 7808 7812 7816 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15350 = denoteGraph_ringAttn pm initPM 8885 :=
    ringAttn_reduce1_pm_opaque pm initPM 693
      { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
      8885 15350 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 8885 15342 15346 15350 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15363 = denoteGraph_ringAttn pm initPM 8886 :=
    ringAttn_reduce1_pm_opaque pm initPM 694
      { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
      8886 15363 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 8886 15355 15359 15363 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7816
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15350, denoteGraph_ringAttn pm initPM 15363] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15350).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15363).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7816).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7816 7816 15350 15363 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7843 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5137`.
    Identity alias: `7843` reconstructs exactly as `5137` (allGather of its shards). -/
theorem recon_intermediateGoal_7843_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7843
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7843 = denoteGraph_ringAttn sm initSM 5137 :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7843 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15398 = denoteGraph_ringAttn pm initPM 8959 :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15398 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15421 = denoteGraph_ringAttn pm initPM 8960 :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15421 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7843
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15398, denoteGraph_ringAttn pm initPM 15421] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15398).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15421).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7843).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7843 7843 15398 15421 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7868 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5170`.
    Identity alias: `7868` reconstructs exactly as `5170` (allGather of its shards). -/
theorem recon_intermediateGoal_7868_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7868
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5170 5170 9071 9072
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5170_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7868 = denoteGraph_ringAttn sm initSM 5170 :=
    ringAttn_reduce1_pm_opaque sm initSM 355
      { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
      5170 7868 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5170 7860 7864 7868 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15454 = denoteGraph_ringAttn pm initPM 9071 :=
    ringAttn_reduce1_pm_opaque pm initPM 771
      { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
      9071 15454 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 9071 15446 15450 15454 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15467 = denoteGraph_ringAttn pm initPM 9072 :=
    ringAttn_reduce1_pm_opaque pm initPM 772
      { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
      9072 15467 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 9072 15459 15463 15467 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7868
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15454, denoteGraph_ringAttn pm initPM 15467] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15454).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15467).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7868).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7868 7868 15454 15467 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7895 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5191`.
    Identity alias: `7895` reconstructs exactly as `5191` (allGather of its shards). -/
theorem recon_intermediateGoal_7895_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7895
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7895 = denoteGraph_ringAttn sm initSM 5191 :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7895 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15502 = denoteGraph_ringAttn pm initPM 9145 :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15502 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15525 = denoteGraph_ringAttn pm initPM 9146 :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15525 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7895
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15502, denoteGraph_ringAttn pm initPM 15525] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15502).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15525).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7895).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7895 7895 15502 15525 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7920 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5224`.
    Identity alias: `7920` reconstructs exactly as `5224` (allGather of its shards). -/
theorem recon_intermediateGoal_7920_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7920
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5224 5224 9257 9258
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5224_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7920 = denoteGraph_ringAttn sm initSM 5224 :=
    ringAttn_reduce1_pm_opaque sm initSM 394
      { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
      5224 7920 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5224 7912 7916 7920 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15558 = denoteGraph_ringAttn pm initPM 9257 :=
    ringAttn_reduce1_pm_opaque pm initPM 849
      { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
      9257 15558 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 9257 15550 15554 15558 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15571 = denoteGraph_ringAttn pm initPM 9258 :=
    ringAttn_reduce1_pm_opaque pm initPM 850
      { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
      9258 15571 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 9258 15563 15567 15571 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7920
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15558, denoteGraph_ringAttn pm initPM 15571] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15558).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15571).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7920).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7920 7920 15558 15571 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7947 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5245`.
    Identity alias: `7947` reconstructs exactly as `5245` (allGather of its shards). -/
theorem recon_intermediateGoal_7947_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7947
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7947 = denoteGraph_ringAttn sm initSM 5245 :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7947 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15606 = denoteGraph_ringAttn pm initPM 9331 :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15606 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15629 = denoteGraph_ringAttn pm initPM 9332 :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15629 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7947
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15606, denoteGraph_ringAttn pm initPM 15629] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15606).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15629).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7947).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7947 7947 15606 15629 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7972 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5278`.
    Identity alias: `7972` reconstructs exactly as `5278` (allGather of its shards). -/
theorem recon_intermediateGoal_7972_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7972
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5278 5278 9443 9444
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5278_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7972 = denoteGraph_ringAttn sm initSM 5278 :=
    ringAttn_reduce1_pm_opaque sm initSM 433
      { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
      5278 7972 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 5278 7964 7968 7972 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15662 = denoteGraph_ringAttn pm initPM 9443 :=
    ringAttn_reduce1_pm_opaque pm initPM 927
      { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
      9443 15662 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 9443 15654 15658 15662 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15675 = denoteGraph_ringAttn pm initPM 9444 :=
    ringAttn_reduce1_pm_opaque pm initPM 928
      { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
      9444 15675 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 9444 15667 15671 15675 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7972
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15662, denoteGraph_ringAttn pm initPM 15675] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15662).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15675).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7972).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7972 7972 15662 15675 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7999 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5299`.
    Identity alias: `7999` reconstructs exactly as `5299` (allGather of its shards). -/
theorem recon_intermediateGoal_7999_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7999
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7999 = denoteGraph_ringAttn sm initSM 5299 :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 7999 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15710 = denoteGraph_ringAttn pm initPM 9517 :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15710 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15733 = denoteGraph_ringAttn pm initPM 9518 :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15733 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7999
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15710, denoteGraph_ringAttn pm initPM 15733] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15710).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15733).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7999).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7999 7999 15710 15733 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8158 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5356`.
    Identity alias: `8158` reconstructs exactly as `5356` (allGather of its shards). -/
theorem recon_intermediateGoal_8158_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8158
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8158 = denoteGraph_ringAttn sm initSM 5356 :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8158 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5356 8158 8162 8166 8170 8174)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16004 = denoteGraph_ringAttn pm initPM 9721 :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16004 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 9721 16004 16008 16012 16016 16020)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16027 = denoteGraph_ringAttn pm initPM 9722 :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16027 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 9722 16027 16031 16035 16039 16043)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8158
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16004, denoteGraph_ringAttn pm initPM 16027] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16004).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16027).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8158).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8158 8158 16004 16027 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8178 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5387`.
    Identity alias: `8178` reconstructs exactly as `5387` (allGather of its shards). -/
theorem recon_intermediateGoal_8178_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8178
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5387 5387 9829 9830
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5387_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8178 = denoteGraph_ringAttn sm initSM 5387 :=
    ringAttn_reduce1_pm_opaque sm initSM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [5387], outs := [8178, 8182], params := [2] }
      5387 8178 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5387 8178 8182)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16047 = denoteGraph_ringAttn pm initPM 9829 :=
    ringAttn_reduce1_pm_opaque pm initPM 1136
      { rank := 0, op := "OpName.FW_multiref", ins := [9829], outs := [16047, 16051], params := [2] }
      9829 16047 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9829 16047 16051)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16055 = denoteGraph_ringAttn pm initPM 9830 :=
    ringAttn_reduce1_pm_opaque pm initPM 1137
      { rank := 1, op := "OpName.FW_multiref", ins := [9830], outs := [16055, 16059], params := [2] }
      9830 16055 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9830 16055 16059)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8178
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16047, denoteGraph_ringAttn pm initPM 16055] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16047).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16055).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8178).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8178 8178 16047 16055 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8209 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5405`.
    Identity alias: `8209` reconstructs exactly as `5405` (allGather of its shards). -/
theorem recon_intermediateGoal_8209_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8209
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5405 5405 9893 9894
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5405_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8209 = denoteGraph_ringAttn sm initSM 5405 :=
    ringAttn_reduce1_pm_opaque sm initSM 549
      { rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] }
      5405 8209 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5405 8197 8201 8205 8209 8213 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16094 = denoteGraph_ringAttn pm initPM 9893 :=
    ringAttn_reduce1_pm_opaque pm initPM 1160
      { rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] }
      9893 16094 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9893 16082 16086 16090 16094 16098 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16117 = denoteGraph_ringAttn pm initPM 9894 :=
    ringAttn_reduce1_pm_opaque pm initPM 1161
      { rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] }
      9894 16117 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9894 16105 16109 16113 16117 16121 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8209
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16094, denoteGraph_ringAttn pm initPM 16117] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16094).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16117).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8209).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8209 8209 16094 16117 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8240 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5454`.
    Identity alias: `8240` reconstructs exactly as `5454` (allGather of its shards). -/
theorem recon_intermediateGoal_8240_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8240
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5454 5454 10065 10066
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5454_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8240 = denoteGraph_ringAttn sm initSM 5454 :=
    ringAttn_reduce1_pm_opaque sm initSM 584
      { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] }
      5454 8240 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5454 8236 8240 8244 8248 8252 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16164 = denoteGraph_ringAttn pm initPM 10065 :=
    ringAttn_reduce1_pm_opaque pm initPM 1230
      { rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] }
      10065 16164 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 10065 16160 16164 16168 16172 16176 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16187 = denoteGraph_ringAttn pm initPM 10066 :=
    ringAttn_reduce1_pm_opaque pm initPM 1231
      { rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] }
      10066 16187 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 10066 16183 16187 16191 16195 16199 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8240
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16164, denoteGraph_ringAttn pm initPM 16187] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16164).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16187).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8240).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8240 8240 16164 16187 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8264 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5501`.
    Identity alias: `8264` reconstructs exactly as `5501` (allGather of its shards). -/
theorem recon_intermediateGoal_8264_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8264
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5501 5501 10233 10234
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5501_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8264 = denoteGraph_ringAttn sm initSM 5501 :=
    ringAttn_reduce1_pm_opaque sm initSM 617
      { rank := 0, op := "OpName.FW_multiref", ins := [5501], outs := [8264, 8268], params := [2] }
      5501 8264 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5501 8264 8268)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16219 = denoteGraph_ringAttn pm initPM 10233 :=
    ringAttn_reduce1_pm_opaque pm initPM 1296
      { rank := 0, op := "OpName.FW_multiref", ins := [10233], outs := [16219, 16223], params := [2] }
      10233 16219 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10233 16219 16223)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16227 = denoteGraph_ringAttn pm initPM 10234 :=
    ringAttn_reduce1_pm_opaque pm initPM 1297
      { rank := 1, op := "OpName.FW_multiref", ins := [10234], outs := [16227, 16231], params := [2] }
      10234 16227 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10234 16227 16231)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8264
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16219, denoteGraph_ringAttn pm initPM 16227] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16219).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16227).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8264).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8264 8264 16219 16227 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8291 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5503`.
    Identity alias: `8291` reconstructs exactly as `5503` (allGather of its shards). -/
theorem recon_intermediateGoal_8291_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8291
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5503 5503 10237 10238
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5503_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8291 = denoteGraph_ringAttn sm initSM 5503 :=
    ringAttn_reduce1_pm_opaque sm initSM 619
      { rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] }
      5503 8291 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5503 8275 8279 8283 8287 8291 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16254 = denoteGraph_ringAttn pm initPM 10237 :=
    ringAttn_reduce1_pm_opaque pm initPM 1300
      { rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] }
      10237 16254 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 10237 16238 16242 16246 16250 16254 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16277 = denoteGraph_ringAttn pm initPM 10238 :=
    ringAttn_reduce1_pm_opaque pm initPM 1301
      { rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] }
      10238 16277 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 10238 16261 16265 16269 16273 16277 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8291
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16254, denoteGraph_ringAttn pm initPM 16277] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16254).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16277).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8291).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8291 8291 16254 16277 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8322 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5552`.
    Identity alias: `8322` reconstructs exactly as `5552` (allGather of its shards). -/
theorem recon_intermediateGoal_8322_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8322
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5552 5552 10409 10410
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5552_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8322 = denoteGraph_ringAttn sm initSM 5552 :=
    ringAttn_reduce1_pm_opaque sm initSM 654
      { rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] }
      5552 8322 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5552 8314 8318 8322 8326 8330 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16324 = denoteGraph_ringAttn pm initPM 10409 :=
    ringAttn_reduce1_pm_opaque pm initPM 1370
      { rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] }
      10409 16324 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 10409 16316 16320 16324 16328 16332 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16347 = denoteGraph_ringAttn pm initPM 10410 :=
    ringAttn_reduce1_pm_opaque pm initPM 1371
      { rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] }
      10410 16347 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 10410 16339 16343 16347 16351 16355 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8322
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16324, denoteGraph_ringAttn pm initPM 16347] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16324).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16347).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8322).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8322 8322 16324 16347 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8353 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5601`.
    Identity alias: `8353` reconstructs exactly as `5601` (allGather of its shards). -/
theorem recon_intermediateGoal_8353_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8353
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5601 5601 10581 10582
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5601_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8353 = denoteGraph_ringAttn sm initSM 5601 :=
    ringAttn_reduce1_pm_opaque sm initSM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] }
      5601 8353 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5601 8353 8357 8361 8365 8369)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16394 = denoteGraph_ringAttn pm initPM 10581 :=
    ringAttn_reduce1_pm_opaque pm initPM 1440
      { rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] }
      10581 16394 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 10581 16394 16398 16402 16406 16410)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16417 = denoteGraph_ringAttn pm initPM 10582 :=
    ringAttn_reduce1_pm_opaque pm initPM 1441
      { rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] }
      10582 16417 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 10582 16417 16421 16425 16429 16433)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8353
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16394, denoteGraph_ringAttn pm initPM 16417] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16394).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16417).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8353).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8353 8353 16394 16417 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8373 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5632`.
    Identity alias: `8373` reconstructs exactly as `5632` (allGather of its shards). -/
theorem recon_intermediateGoal_8373_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8373
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5632 5632 10689 10690
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5632_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8373 = denoteGraph_ringAttn sm initSM 5632 :=
    ringAttn_reduce1_pm_opaque sm initSM 712
      { rank := 0, op := "OpName.FW_multiref", ins := [5632], outs := [8373, 8377], params := [2] }
      5632 8373 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5632 8373 8377)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16437 = denoteGraph_ringAttn pm initPM 10689 :=
    ringAttn_reduce1_pm_opaque pm initPM 1486
      { rank := 0, op := "OpName.FW_multiref", ins := [10689], outs := [16437, 16441], params := [2] }
      10689 16437 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10689 16437 16441)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16445 = denoteGraph_ringAttn pm initPM 10690 :=
    ringAttn_reduce1_pm_opaque pm initPM 1487
      { rank := 1, op := "OpName.FW_multiref", ins := [10690], outs := [16445, 16449], params := [2] }
      10690 16445 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10690 16445 16449)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8373
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16437, denoteGraph_ringAttn pm initPM 16445] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16437).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16445).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8373).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8373 8373 16437 16445 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8404 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5650`.
    Identity alias: `8404` reconstructs exactly as `5650` (allGather of its shards). -/
theorem recon_intermediateGoal_8404_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8404
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5650 5650 10753 10754
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5650_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8404 = denoteGraph_ringAttn sm initSM 5650 :=
    ringAttn_reduce1_pm_opaque sm initSM 724
      { rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] }
      5650 8404 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5650 8392 8396 8400 8404 8408 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16484 = denoteGraph_ringAttn pm initPM 10753 :=
    ringAttn_reduce1_pm_opaque pm initPM 1510
      { rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] }
      10753 16484 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 10753 16472 16476 16480 16484 16488 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16507 = denoteGraph_ringAttn pm initPM 10754 :=
    ringAttn_reduce1_pm_opaque pm initPM 1511
      { rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] }
      10754 16507 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 10754 16495 16499 16503 16507 16511 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8404
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16484, denoteGraph_ringAttn pm initPM 16507] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16484).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16507).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8404).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8404 8404 16484 16507 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8435 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5699`.
    Identity alias: `8435` reconstructs exactly as `5699` (allGather of its shards). -/
theorem recon_intermediateGoal_8435_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8435
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5699 5699 10925 10926
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5699_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8435 = denoteGraph_ringAttn sm initSM 5699 :=
    ringAttn_reduce1_pm_opaque sm initSM 759
      { rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] }
      5699 8435 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5699 8431 8435 8439 8443 8447 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16554 = denoteGraph_ringAttn pm initPM 10925 :=
    ringAttn_reduce1_pm_opaque pm initPM 1580
      { rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] }
      10925 16554 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 10925 16550 16554 16558 16562 16566 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16577 = denoteGraph_ringAttn pm initPM 10926 :=
    ringAttn_reduce1_pm_opaque pm initPM 1581
      { rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] }
      10926 16577 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 10926 16573 16577 16581 16585 16589 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8435
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16554, denoteGraph_ringAttn pm initPM 16577] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16554).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16577).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8435).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8435 8435 16554 16577 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8459 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5746`.
    Identity alias: `8459` reconstructs exactly as `5746` (allGather of its shards). -/
theorem recon_intermediateGoal_8459_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8459
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5746 5746 11093 11094
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5746_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8459 = denoteGraph_ringAttn sm initSM 5746 :=
    ringAttn_reduce1_pm_opaque sm initSM 792
      { rank := 0, op := "OpName.FW_multiref", ins := [5746], outs := [8459, 8463], params := [2] }
      5746 8459 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5746 8459 8463)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16609 = denoteGraph_ringAttn pm initPM 11093 :=
    ringAttn_reduce1_pm_opaque pm initPM 1646
      { rank := 0, op := "OpName.FW_multiref", ins := [11093], outs := [16609, 16613], params := [2] }
      11093 16609 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11093 16609 16613)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16617 = denoteGraph_ringAttn pm initPM 11094 :=
    ringAttn_reduce1_pm_opaque pm initPM 1647
      { rank := 1, op := "OpName.FW_multiref", ins := [11094], outs := [16617, 16621], params := [2] }
      11094 16617 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11094 16617 16621)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8459
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16609, denoteGraph_ringAttn pm initPM 16617] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16609).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16617).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8459).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8459 8459 16609 16617 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8486 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5748`.
    Identity alias: `8486` reconstructs exactly as `5748` (allGather of its shards). -/
theorem recon_intermediateGoal_8486_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8486
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5748 5748 11097 11098
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5748_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8486 = denoteGraph_ringAttn sm initSM 5748 :=
    ringAttn_reduce1_pm_opaque sm initSM 794
      { rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] }
      5748 8486 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5748 8470 8474 8478 8482 8486 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16644 = denoteGraph_ringAttn pm initPM 11097 :=
    ringAttn_reduce1_pm_opaque pm initPM 1650
      { rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] }
      11097 16644 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 11097 16628 16632 16636 16640 16644 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16667 = denoteGraph_ringAttn pm initPM 11098 :=
    ringAttn_reduce1_pm_opaque pm initPM 1651
      { rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] }
      11098 16667 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 11098 16651 16655 16659 16663 16667 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8486
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16644, denoteGraph_ringAttn pm initPM 16667] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16644).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16667).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8486).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8486 8486 16644 16667 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8517 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5797`.
    Identity alias: `8517` reconstructs exactly as `5797` (allGather of its shards). -/
theorem recon_intermediateGoal_8517_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8517
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5797 5797 11269 11270
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5797_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8517 = denoteGraph_ringAttn sm initSM 5797 :=
    ringAttn_reduce1_pm_opaque sm initSM 829
      { rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] }
      5797 8517 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5797 8509 8513 8517 8521 8525 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16714 = denoteGraph_ringAttn pm initPM 11269 :=
    ringAttn_reduce1_pm_opaque pm initPM 1720
      { rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] }
      11269 16714 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 11269 16706 16710 16714 16718 16722 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16737 = denoteGraph_ringAttn pm initPM 11270 :=
    ringAttn_reduce1_pm_opaque pm initPM 1721
      { rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] }
      11270 16737 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 11270 16729 16733 16737 16741 16745 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8517
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16714, denoteGraph_ringAttn pm initPM 16737] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16714).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16737).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8517).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8517 8517 16714 16737 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8548 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5846`.
    Identity alias: `8548` reconstructs exactly as `5846` (allGather of its shards). -/
theorem recon_intermediateGoal_8548_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8548
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5846 5846 11441 11442
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8548 = denoteGraph_ringAttn sm initSM 5846 :=
    ringAttn_reduce1_pm_opaque sm initSM 864
      { rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] }
      5846 8548 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5846 8548 8552 8556 8560 8564)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16784 = denoteGraph_ringAttn pm initPM 11441 :=
    ringAttn_reduce1_pm_opaque pm initPM 1790
      { rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] }
      11441 16784 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 11441 16784 16788 16792 16796 16800)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16807 = denoteGraph_ringAttn pm initPM 11442 :=
    ringAttn_reduce1_pm_opaque pm initPM 1791
      { rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] }
      11442 16807 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 11442 16807 16811 16815 16819 16823)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8548
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16784, denoteGraph_ringAttn pm initPM 16807] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16784).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16807).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8548).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8548 8548 16784 16807 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8568 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5877`.
    Identity alias: `8568` reconstructs exactly as `5877` (allGather of its shards). -/
theorem recon_intermediateGoal_8568_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8568
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5877 5877 11549 11550
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5877_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8568 = denoteGraph_ringAttn sm initSM 5877 :=
    ringAttn_reduce1_pm_opaque sm initSM 887
      { rank := 0, op := "OpName.FW_multiref", ins := [5877], outs := [8568, 8572], params := [2] }
      5877 8568 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5877 8568 8572)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16827 = denoteGraph_ringAttn pm initPM 11549 :=
    ringAttn_reduce1_pm_opaque pm initPM 1836
      { rank := 0, op := "OpName.FW_multiref", ins := [11549], outs := [16827, 16831], params := [2] }
      11549 16827 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11549 16827 16831)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16835 = denoteGraph_ringAttn pm initPM 11550 :=
    ringAttn_reduce1_pm_opaque pm initPM 1837
      { rank := 1, op := "OpName.FW_multiref", ins := [11550], outs := [16835, 16839], params := [2] }
      11550 16835 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11550 16835 16839)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8568
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16827, denoteGraph_ringAttn pm initPM 16835] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16827).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16835).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8568).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8568 8568 16827 16835 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8599 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5895`.
    Identity alias: `8599` reconstructs exactly as `5895` (allGather of its shards). -/
theorem recon_intermediateGoal_8599_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_8599
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5895 5895 11613 11614
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5895_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8599 = denoteGraph_ringAttn sm initSM 5895 :=
    ringAttn_reduce1_pm_opaque sm initSM 899
      { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }
      5895 8599 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5895 8587 8591 8595 8599 8603 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16874 = denoteGraph_ringAttn pm initPM 11613 :=
    ringAttn_reduce1_pm_opaque pm initPM 1860
      { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }
      11613 16874 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 11613 16862 16866 16870 16874 16878 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16897 = denoteGraph_ringAttn pm initPM 11614 :=
    ringAttn_reduce1_pm_opaque pm initPM 1861
      { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }
      11614 16897 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 11614 16885 16889 16893 16897 16901 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8599
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16874, denoteGraph_ringAttn pm initPM 16897] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16874).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16897).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8599).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_8599 8599 16874 16897 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
