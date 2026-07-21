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

/-- 7508 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4811`.
    Identity alias: `7508` reconstructs exactly as `4811` (allGather of its shards). -/
theorem recon_intermediateGoal_7508_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7508
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4811 4811 7839 7840
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4811_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7508 = denoteGraph_ringAttn sm initSM 4811 :=
    ringAttn_reduce1_pm_opaque sm initSM 94
      { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512], params := [2] }
      4811 7508 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4811 7508 7512)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14743 = denoteGraph_ringAttn pm initPM 7839 :=
    ringAttn_reduce1_pm_opaque pm initPM 249
      { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747], params := [2] }
      7839 14743 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 7839 14743 14747)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14751 = denoteGraph_ringAttn pm initPM 7840 :=
    ringAttn_reduce1_pm_opaque pm initPM 250
      { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755], params := [2] }
      7840 14751 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 7840 14751 14755)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7508
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14743, denoteGraph_ringAttn pm initPM 14751] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14743).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14751).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7508).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7508 7508 14743 14751 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7535 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `4813`.
    Identity alias: `7535` reconstructs exactly as `4813` (allGather of its shards). -/
theorem recon_intermediateGoal_7535_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7535
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7535 = denoteGraph_ringAttn sm initSM 4813 :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7535 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14778 = denoteGraph_ringAttn pm initPM 7843 :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14778 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14801 = denoteGraph_ringAttn pm initPM 7844 :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14801 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7535
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14778, denoteGraph_ringAttn pm initPM 14801] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14778).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14801).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7535).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7535 7535 14778 14801 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7560 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4865`.
    Identity alias: `7560` reconstructs exactly as `4865` (allGather of its shards). -/
theorem recon_intermediateGoal_7560_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7560
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4865 4865 8025 8026
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4865_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7560 = denoteGraph_ringAttn sm initSM 4865 :=
    ringAttn_reduce1_pm_opaque sm initSM 133
      { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564], params := [2] }
      4865 7560 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4865 7560 7564)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14847 = denoteGraph_ringAttn pm initPM 8025 :=
    ringAttn_reduce1_pm_opaque pm initPM 327
      { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851], params := [2] }
      8025 14847 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8025 14847 14851)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14855 = denoteGraph_ringAttn pm initPM 8026 :=
    ringAttn_reduce1_pm_opaque pm initPM 328
      { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859], params := [2] }
      8026 14855 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8026 14855 14859)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7560
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14847, denoteGraph_ringAttn pm initPM 14855] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14847).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14855).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7560).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7560 7560 14847 14855 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7587 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `4867`.
    Identity alias: `7587` reconstructs exactly as `4867` (allGather of its shards). -/
theorem recon_intermediateGoal_7587_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7587
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4867 4867 8029 8030
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4867_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7587 = denoteGraph_ringAttn sm initSM 4867 :=
    ringAttn_reduce1_pm_opaque sm initSM 135
      { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
      4867 7587 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4867 7571 7575 7579 7583 7587 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14882 = denoteGraph_ringAttn pm initPM 8029 :=
    ringAttn_reduce1_pm_opaque pm initPM 331
      { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
      8029 14882 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8029 14866 14870 14874 14878 14882 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14905 = denoteGraph_ringAttn pm initPM 8030 :=
    ringAttn_reduce1_pm_opaque pm initPM 332
      { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
      8030 14905 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8030 14889 14893 14897 14901 14905 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7587
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14882, denoteGraph_ringAttn pm initPM 14905] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14882).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14905).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7587).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7587 7587 14882 14905 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7612 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4919`.
    Identity alias: `7612` reconstructs exactly as `4919` (allGather of its shards). -/
theorem recon_intermediateGoal_7612_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7612
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4919 4919 8211 8212
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4919_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7612 = denoteGraph_ringAttn sm initSM 4919 :=
    ringAttn_reduce1_pm_opaque sm initSM 172
      { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616], params := [2] }
      4919 7612 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4919 7612 7616)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14951 = denoteGraph_ringAttn pm initPM 8211 :=
    ringAttn_reduce1_pm_opaque pm initPM 405
      { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955], params := [2] }
      8211 14951 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8211 14951 14955)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 14959 = denoteGraph_ringAttn pm initPM 8212 :=
    ringAttn_reduce1_pm_opaque pm initPM 406
      { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963], params := [2] }
      8212 14959 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8212 14959 14963)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7612
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14951, denoteGraph_ringAttn pm initPM 14959] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14951).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 14959).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7612).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7612 7612 14951 14959 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7639 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `4921`.
    Identity alias: `7639` reconstructs exactly as `4921` (allGather of its shards). -/
theorem recon_intermediateGoal_7639_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7639
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4921 4921 8215 8216
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4921_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7639 = denoteGraph_ringAttn sm initSM 4921 :=
    ringAttn_reduce1_pm_opaque sm initSM 174
      { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
      4921 7639 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 14986 = denoteGraph_ringAttn pm initPM 8215 :=
    ringAttn_reduce1_pm_opaque pm initPM 409
      { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
      8215 14986 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15009 = denoteGraph_ringAttn pm initPM 8216 :=
    ringAttn_reduce1_pm_opaque pm initPM 410
      { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
      8216 15009 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7639
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14986, denoteGraph_ringAttn pm initPM 15009] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 14986).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15009).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7639).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7639 7639 14986 15009 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7664 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `4973`.
    Identity alias: `7664` reconstructs exactly as `4973` (allGather of its shards). -/
theorem recon_intermediateGoal_7664_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7664
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4973 4973 8397 8398
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4973_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7664 = denoteGraph_ringAttn sm initSM 4973 :=
    ringAttn_reduce1_pm_opaque sm initSM 211
      { rank := 0, op := "OpName.FW_multiref", ins := [4973], outs := [7664, 7668], params := [2] }
      4973 7664 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4973 7664 7668)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15055 = denoteGraph_ringAttn pm initPM 8397 :=
    ringAttn_reduce1_pm_opaque pm initPM 483
      { rank := 0, op := "OpName.FW_multiref", ins := [8397], outs := [15055, 15059], params := [2] }
      8397 15055 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8397 15055 15059)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15063 = denoteGraph_ringAttn pm initPM 8398 :=
    ringAttn_reduce1_pm_opaque pm initPM 484
      { rank := 1, op := "OpName.FW_multiref", ins := [8398], outs := [15063, 15067], params := [2] }
      8398 15063 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8398 15063 15067)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7664
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15055, denoteGraph_ringAttn pm initPM 15063] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15055).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15063).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7664).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7664 7664 15055 15063 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7691 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `4975`.
    Identity alias: `7691` reconstructs exactly as `4975` (allGather of its shards). -/
theorem recon_intermediateGoal_7691_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7691
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_4975 4975 8401 8402
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7691 = denoteGraph_ringAttn sm initSM 4975 :=
    ringAttn_reduce1_pm_opaque sm initSM 213
      { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
      4975 7691 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4975 7675 7679 7683 7687 7691 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15090 = denoteGraph_ringAttn pm initPM 8401 :=
    ringAttn_reduce1_pm_opaque pm initPM 487
      { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
      8401 15090 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8401 15074 15078 15082 15086 15090 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15113 = denoteGraph_ringAttn pm initPM 8402 :=
    ringAttn_reduce1_pm_opaque pm initPM 488
      { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
      8402 15113 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8402 15097 15101 15105 15109 15113 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7691
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15090, denoteGraph_ringAttn pm initPM 15113] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15090).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15113).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7691).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7691 7691 15090 15113 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7716 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5027`.
    Identity alias: `7716` reconstructs exactly as `5027` (allGather of its shards). -/
theorem recon_intermediateGoal_7716_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7716
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5027 5027 8583 8584
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5027_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7716 = denoteGraph_ringAttn sm initSM 5027 :=
    ringAttn_reduce1_pm_opaque sm initSM 250
      { rank := 0, op := "OpName.FW_multiref", ins := [5027], outs := [7716, 7720], params := [2] }
      5027 7716 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5027 7716 7720)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15159 = denoteGraph_ringAttn pm initPM 8583 :=
    ringAttn_reduce1_pm_opaque pm initPM 561
      { rank := 0, op := "OpName.FW_multiref", ins := [8583], outs := [15159, 15163], params := [2] }
      8583 15159 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8583 15159 15163)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15167 = denoteGraph_ringAttn pm initPM 8584 :=
    ringAttn_reduce1_pm_opaque pm initPM 562
      { rank := 1, op := "OpName.FW_multiref", ins := [8584], outs := [15167, 15171], params := [2] }
      8584 15167 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8584 15167 15171)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7716
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15159, denoteGraph_ringAttn pm initPM 15167] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15159).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15167).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7716).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7716 7716 15159 15167 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7743 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5029`.
    Identity alias: `7743` reconstructs exactly as `5029` (allGather of its shards). -/
theorem recon_intermediateGoal_7743_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7743
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5029 5029 8587 8588
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5029_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7743 = denoteGraph_ringAttn sm initSM 5029 :=
    ringAttn_reduce1_pm_opaque sm initSM 252
      { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
      5029 7743 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5029 7727 7731 7735 7739 7743 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15194 = denoteGraph_ringAttn pm initPM 8587 :=
    ringAttn_reduce1_pm_opaque pm initPM 565
      { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
      8587 15194 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8587 15178 15182 15186 15190 15194 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15217 = denoteGraph_ringAttn pm initPM 8588 :=
    ringAttn_reduce1_pm_opaque pm initPM 566
      { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
      8588 15217 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8588 15201 15205 15209 15213 15217 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7743
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15194, denoteGraph_ringAttn pm initPM 15217] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15194).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15217).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7743).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7743 7743 15194 15217 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7768 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5081`.
    Identity alias: `7768` reconstructs exactly as `5081` (allGather of its shards). -/
theorem recon_intermediateGoal_7768_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7768
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5081 5081 8769 8770
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5081_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7768 = denoteGraph_ringAttn sm initSM 5081 :=
    ringAttn_reduce1_pm_opaque sm initSM 289
      { rank := 0, op := "OpName.FW_multiref", ins := [5081], outs := [7768, 7772], params := [2] }
      5081 7768 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5081 7768 7772)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15263 = denoteGraph_ringAttn pm initPM 8769 :=
    ringAttn_reduce1_pm_opaque pm initPM 639
      { rank := 0, op := "OpName.FW_multiref", ins := [8769], outs := [15263, 15267], params := [2] }
      8769 15263 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8769 15263 15267)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15271 = denoteGraph_ringAttn pm initPM 8770 :=
    ringAttn_reduce1_pm_opaque pm initPM 640
      { rank := 1, op := "OpName.FW_multiref", ins := [8770], outs := [15271, 15275], params := [2] }
      8770 15271 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8770 15271 15275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7768
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15263, denoteGraph_ringAttn pm initPM 15271] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15263).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15271).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7768).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7768 7768 15263 15271 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7795 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5083`.
    Identity alias: `7795` reconstructs exactly as `5083` (allGather of its shards). -/
theorem recon_intermediateGoal_7795_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7795
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5083 5083 8773 8774
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5083_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7795 = denoteGraph_ringAttn sm initSM 5083 :=
    ringAttn_reduce1_pm_opaque sm initSM 291
      { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795], params := [5] }
      5083 7795 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5083 7779 7783 7787 7791 7795 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15298 = denoteGraph_ringAttn pm initPM 8773 :=
    ringAttn_reduce1_pm_opaque pm initPM 643
      { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298], params := [5] }
      8773 15298 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8773 15282 15286 15290 15294 15298 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15321 = denoteGraph_ringAttn pm initPM 8774 :=
    ringAttn_reduce1_pm_opaque pm initPM 644
      { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321], params := [5] }
      8774 15321 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8774 15305 15309 15313 15317 15321 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7795
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15298, denoteGraph_ringAttn pm initPM 15321] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15298).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15321).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7795).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7795 7795 15298 15321 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7820 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5135`.
    Identity alias: `7820` reconstructs exactly as `5135` (allGather of its shards). -/
theorem recon_intermediateGoal_7820_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7820
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5135 5135 8955 8956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5135_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7820 = denoteGraph_ringAttn sm initSM 5135 :=
    ringAttn_reduce1_pm_opaque sm initSM 328
      { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824], params := [2] }
      5135 7820 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5135 7820 7824)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15367 = denoteGraph_ringAttn pm initPM 8955 :=
    ringAttn_reduce1_pm_opaque pm initPM 717
      { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371], params := [2] }
      8955 15367 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 8955 15367 15371)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15375 = denoteGraph_ringAttn pm initPM 8956 :=
    ringAttn_reduce1_pm_opaque pm initPM 718
      { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379], params := [2] }
      8956 15375 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 8956 15375 15379)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7820
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15367, denoteGraph_ringAttn pm initPM 15375] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15367).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15375).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7820).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7820 7820 15367 15375 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7847 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5137`.
    Identity alias: `7847` reconstructs exactly as `5137` (allGather of its shards). -/
theorem recon_intermediateGoal_7847_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7847
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5137 5137 8959 8960
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7847 = denoteGraph_ringAttn sm initSM 5137 :=
    ringAttn_reduce1_pm_opaque sm initSM 330
      { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
      5137 7847 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5137 7831 7835 7839 7843 7847 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15402 = denoteGraph_ringAttn pm initPM 8959 :=
    ringAttn_reduce1_pm_opaque pm initPM 721
      { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
      8959 15402 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 8959 15386 15390 15394 15398 15402 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15425 = denoteGraph_ringAttn pm initPM 8960 :=
    ringAttn_reduce1_pm_opaque pm initPM 722
      { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
      8960 15425 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 8960 15409 15413 15417 15421 15425 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7847
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15402, denoteGraph_ringAttn pm initPM 15425] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15402).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15425).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7847).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7847 7847 15402 15425 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7872 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5189`.
    Identity alias: `7872` reconstructs exactly as `5189` (allGather of its shards). -/
theorem recon_intermediateGoal_7872_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7872
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5189 5189 9141 9142
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5189_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7872 = denoteGraph_ringAttn sm initSM 5189 :=
    ringAttn_reduce1_pm_opaque sm initSM 367
      { rank := 0, op := "OpName.FW_multiref", ins := [5189], outs := [7872, 7876], params := [2] }
      5189 7872 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5189 7872 7876)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15471 = denoteGraph_ringAttn pm initPM 9141 :=
    ringAttn_reduce1_pm_opaque pm initPM 795
      { rank := 0, op := "OpName.FW_multiref", ins := [9141], outs := [15471, 15475], params := [2] }
      9141 15471 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9141 15471 15475)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15479 = denoteGraph_ringAttn pm initPM 9142 :=
    ringAttn_reduce1_pm_opaque pm initPM 796
      { rank := 1, op := "OpName.FW_multiref", ins := [9142], outs := [15479, 15483], params := [2] }
      9142 15479 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9142 15479 15483)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7872
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15471, denoteGraph_ringAttn pm initPM 15479] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15471).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15479).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7872).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7872 7872 15471 15479 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7899 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5191`.
    Identity alias: `7899` reconstructs exactly as `5191` (allGather of its shards). -/
theorem recon_intermediateGoal_7899_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7899
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5191 5191 9145 9146
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7899 = denoteGraph_ringAttn sm initSM 5191 :=
    ringAttn_reduce1_pm_opaque sm initSM 369
      { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
      5191 7899 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5191 7883 7887 7891 7895 7899 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15506 = denoteGraph_ringAttn pm initPM 9145 :=
    ringAttn_reduce1_pm_opaque pm initPM 799
      { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
      9145 15506 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9145 15490 15494 15498 15502 15506 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15529 = denoteGraph_ringAttn pm initPM 9146 :=
    ringAttn_reduce1_pm_opaque pm initPM 800
      { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
      9146 15529 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9146 15513 15517 15521 15525 15529 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7899
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15506, denoteGraph_ringAttn pm initPM 15529] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15506).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15529).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7899).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7899 7899 15506 15529 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7924 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5243`.
    Identity alias: `7924` reconstructs exactly as `5243` (allGather of its shards). -/
theorem recon_intermediateGoal_7924_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7924
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5243 5243 9327 9328
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5243_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7924 = denoteGraph_ringAttn sm initSM 5243 :=
    ringAttn_reduce1_pm_opaque sm initSM 406
      { rank := 0, op := "OpName.FW_multiref", ins := [5243], outs := [7924, 7928], params := [2] }
      5243 7924 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5243 7924 7928)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15575 = denoteGraph_ringAttn pm initPM 9327 :=
    ringAttn_reduce1_pm_opaque pm initPM 873
      { rank := 0, op := "OpName.FW_multiref", ins := [9327], outs := [15575, 15579], params := [2] }
      9327 15575 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9327 15575 15579)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15583 = denoteGraph_ringAttn pm initPM 9328 :=
    ringAttn_reduce1_pm_opaque pm initPM 874
      { rank := 1, op := "OpName.FW_multiref", ins := [9328], outs := [15583, 15587], params := [2] }
      9328 15583 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9328 15583 15587)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7924
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15575, denoteGraph_ringAttn pm initPM 15583] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15575).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15583).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7924).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7924 7924 15575 15583 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7951 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5245`.
    Identity alias: `7951` reconstructs exactly as `5245` (allGather of its shards). -/
theorem recon_intermediateGoal_7951_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7951
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5245 5245 9331 9332
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5245_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7951 = denoteGraph_ringAttn sm initSM 5245 :=
    ringAttn_reduce1_pm_opaque sm initSM 408
      { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
      5245 7951 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5245 7935 7939 7943 7947 7951 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15610 = denoteGraph_ringAttn pm initPM 9331 :=
    ringAttn_reduce1_pm_opaque pm initPM 877
      { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
      9331 15610 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9331 15594 15598 15602 15606 15610 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15633 = denoteGraph_ringAttn pm initPM 9332 :=
    ringAttn_reduce1_pm_opaque pm initPM 878
      { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
      9332 15633 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9332 15617 15621 15625 15629 15633 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7951
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15610, denoteGraph_ringAttn pm initPM 15633] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15610).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15633).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7951).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7951 7951 15610 15633 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7976 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5297`.
    Identity alias: `7976` reconstructs exactly as `5297` (allGather of its shards). -/
theorem recon_intermediateGoal_7976_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7976
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5297 5297 9513 9514
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5297_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 7976 = denoteGraph_ringAttn sm initSM 5297 :=
    ringAttn_reduce1_pm_opaque sm initSM 445
      { rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] }
      5297 7976 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5297 7976 7980)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15679 = denoteGraph_ringAttn pm initPM 9513 :=
    ringAttn_reduce1_pm_opaque pm initPM 951
      { rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683], params := [2] }
      9513 15679 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9513 15679 15683)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15687 = denoteGraph_ringAttn pm initPM 9514 :=
    ringAttn_reduce1_pm_opaque pm initPM 952
      { rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691], params := [2] }
      9514 15687 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9514 15687 15691)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 7976
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15679, denoteGraph_ringAttn pm initPM 15687] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15679).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15687).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 7976).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7976 7976 15679 15687 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8003 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5299`.
    Identity alias: `8003` reconstructs exactly as `5299` (allGather of its shards). -/
theorem recon_intermediateGoal_8003_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8003
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5299 5299 9517 9518
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8003 = denoteGraph_ringAttn sm initSM 5299 :=
    ringAttn_reduce1_pm_opaque sm initSM 447
      { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
      5299 8003 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 15714 = denoteGraph_ringAttn pm initPM 9517 :=
    ringAttn_reduce1_pm_opaque pm initPM 955
      { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
      9517 15714 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 15737 = denoteGraph_ringAttn pm initPM 9518 :=
    ringAttn_reduce1_pm_opaque pm initPM 956
      { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
      9518 15737 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8003
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15714, denoteGraph_ringAttn pm initPM 15737] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15714).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 15737).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8003).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8003 8003 15714 15737 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8162 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5356`.
    Identity alias: `8162` reconstructs exactly as `5356` (allGather of its shards). -/
theorem recon_intermediateGoal_8162_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8162
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8162 = denoteGraph_ringAttn sm initSM 5356 :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8162 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16008 = denoteGraph_ringAttn pm initPM 9721 :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16008 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16031 = denoteGraph_ringAttn pm initPM 9722 :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16031 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8162
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16008, denoteGraph_ringAttn pm initPM 16031] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16008).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16031).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8162).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8162 8162 16008 16031 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8186 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5403`.
    Identity alias: `8186` reconstructs exactly as `5403` (allGather of its shards). -/
theorem recon_intermediateGoal_8186_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8186
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5403 5403 9889 9890
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5403_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8186 = denoteGraph_ringAttn sm initSM 5403 :=
    ringAttn_reduce1_pm_opaque sm initSM 547
      { rank := 0, op := "OpName.FW_multiref", ins := [5403], outs := [8186, 8190], params := [2] }
      5403 8186 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5403 8186 8190)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16063 = denoteGraph_ringAttn pm initPM 9889 :=
    ringAttn_reduce1_pm_opaque pm initPM 1156
      { rank := 0, op := "OpName.FW_multiref", ins := [9889], outs := [16063, 16067], params := [2] }
      9889 16063 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9889 16063 16067)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16071 = denoteGraph_ringAttn pm initPM 9890 :=
    ringAttn_reduce1_pm_opaque pm initPM 1157
      { rank := 1, op := "OpName.FW_multiref", ins := [9890], outs := [16071, 16075], params := [2] }
      9890 16071 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9890 16071 16075)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8186
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16063, denoteGraph_ringAttn pm initPM 16071] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16063).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16071).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8186).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8186 8186 16063 16071 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8213 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5405`.
    Identity alias: `8213` reconstructs exactly as `5405` (allGather of its shards). -/
theorem recon_intermediateGoal_8213_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8213
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5405 5405 9893 9894
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5405_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8213 = denoteGraph_ringAttn sm initSM 5405 :=
    ringAttn_reduce1_pm_opaque sm initSM 549
      { rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] }
      5405 8213 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5405 8197 8201 8205 8209 8213 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16098 = denoteGraph_ringAttn pm initPM 9893 :=
    ringAttn_reduce1_pm_opaque pm initPM 1160
      { rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] }
      9893 16098 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9893 16082 16086 16090 16094 16098 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16121 = denoteGraph_ringAttn pm initPM 9894 :=
    ringAttn_reduce1_pm_opaque pm initPM 1161
      { rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] }
      9894 16121 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9894 16105 16109 16113 16117 16121 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8213
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16098, denoteGraph_ringAttn pm initPM 16121] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16098).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16121).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8213).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8213 8213 16098 16121 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8244 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5454`.
    Identity alias: `8244` reconstructs exactly as `5454` (allGather of its shards). -/
theorem recon_intermediateGoal_8244_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8244
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5454 5454 10065 10066
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5454_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8244 = denoteGraph_ringAttn sm initSM 5454 :=
    ringAttn_reduce1_pm_opaque sm initSM 584
      { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] }
      5454 8244 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5454 8236 8240 8244 8248 8252 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16168 = denoteGraph_ringAttn pm initPM 10065 :=
    ringAttn_reduce1_pm_opaque pm initPM 1230
      { rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] }
      10065 16168 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 10065 16160 16164 16168 16172 16176 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16191 = denoteGraph_ringAttn pm initPM 10066 :=
    ringAttn_reduce1_pm_opaque pm initPM 1231
      { rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] }
      10066 16191 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 10066 16183 16187 16191 16195 16199 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8244
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16168, denoteGraph_ringAttn pm initPM 16191] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16168).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16191).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8244).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8244 8244 16168 16191 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8275 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5503`.
    Identity alias: `8275` reconstructs exactly as `5503` (allGather of its shards). -/
theorem recon_intermediateGoal_8275_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8275
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5503 5503 10237 10238
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5503_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8275 = denoteGraph_ringAttn sm initSM 5503 :=
    ringAttn_reduce1_pm_opaque sm initSM 619
      { rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] }
      5503 8275 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5503 8275 8279 8283 8287 8291)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16238 = denoteGraph_ringAttn pm initPM 10237 :=
    ringAttn_reduce1_pm_opaque pm initPM 1300
      { rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] }
      10237 16238 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 10237 16238 16242 16246 16250 16254)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16261 = denoteGraph_ringAttn pm initPM 10238 :=
    ringAttn_reduce1_pm_opaque pm initPM 1301
      { rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] }
      10238 16261 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 10238 16261 16265 16269 16273 16277)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8275
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16238, denoteGraph_ringAttn pm initPM 16261] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16238).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16261).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8275).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8275 8275 16238 16261 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8295 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5534`.
    Identity alias: `8295` reconstructs exactly as `5534` (allGather of its shards). -/
theorem recon_intermediateGoal_8295_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8295
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5534 5534 10345 10346
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5534_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8295 = denoteGraph_ringAttn sm initSM 5534 :=
    ringAttn_reduce1_pm_opaque sm initSM 642
      { rank := 0, op := "OpName.FW_multiref", ins := [5534], outs := [8295, 8299], params := [2] }
      5534 8295 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5534 8295 8299)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16281 = denoteGraph_ringAttn pm initPM 10345 :=
    ringAttn_reduce1_pm_opaque pm initPM 1346
      { rank := 0, op := "OpName.FW_multiref", ins := [10345], outs := [16281, 16285], params := [2] }
      10345 16281 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10345 16281 16285)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16289 = denoteGraph_ringAttn pm initPM 10346 :=
    ringAttn_reduce1_pm_opaque pm initPM 1347
      { rank := 1, op := "OpName.FW_multiref", ins := [10346], outs := [16289, 16293], params := [2] }
      10346 16289 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10346 16289 16293)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8295
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16281, denoteGraph_ringAttn pm initPM 16289] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16281).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16289).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8295).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8295 8295 16281 16289 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8326 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5552`.
    Identity alias: `8326` reconstructs exactly as `5552` (allGather of its shards). -/
theorem recon_intermediateGoal_8326_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8326
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5552 5552 10409 10410
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5552_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8326 = denoteGraph_ringAttn sm initSM 5552 :=
    ringAttn_reduce1_pm_opaque sm initSM 654
      { rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] }
      5552 8326 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5552 8314 8318 8322 8326 8330 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16328 = denoteGraph_ringAttn pm initPM 10409 :=
    ringAttn_reduce1_pm_opaque pm initPM 1370
      { rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] }
      10409 16328 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 10409 16316 16320 16324 16328 16332 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16351 = denoteGraph_ringAttn pm initPM 10410 :=
    ringAttn_reduce1_pm_opaque pm initPM 1371
      { rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] }
      10410 16351 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 10410 16339 16343 16347 16351 16355 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8326
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16328, denoteGraph_ringAttn pm initPM 16351] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16328).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16351).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8326).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8326 8326 16328 16351 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8357 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5601`.
    Identity alias: `8357` reconstructs exactly as `5601` (allGather of its shards). -/
theorem recon_intermediateGoal_8357_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8357
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5601 5601 10581 10582
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5601_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8357 = denoteGraph_ringAttn sm initSM 5601 :=
    ringAttn_reduce1_pm_opaque sm initSM 689
      { rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] }
      5601 8357 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5601 8353 8357 8361 8365 8369 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16398 = denoteGraph_ringAttn pm initPM 10581 :=
    ringAttn_reduce1_pm_opaque pm initPM 1440
      { rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] }
      10581 16398 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 10581 16394 16398 16402 16406 16410 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16421 = denoteGraph_ringAttn pm initPM 10582 :=
    ringAttn_reduce1_pm_opaque pm initPM 1441
      { rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] }
      10582 16421 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 10582 16417 16421 16425 16429 16433 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8357
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16398, denoteGraph_ringAttn pm initPM 16421] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16398).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16421).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8357).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8357 8357 16398 16421 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8381 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5648`.
    Identity alias: `8381` reconstructs exactly as `5648` (allGather of its shards). -/
theorem recon_intermediateGoal_8381_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8381
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5648 5648 10749 10750
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5648_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8381 = denoteGraph_ringAttn sm initSM 5648 :=
    ringAttn_reduce1_pm_opaque sm initSM 722
      { rank := 0, op := "OpName.FW_multiref", ins := [5648], outs := [8381, 8385], params := [2] }
      5648 8381 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5648 8381 8385)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16453 = denoteGraph_ringAttn pm initPM 10749 :=
    ringAttn_reduce1_pm_opaque pm initPM 1506
      { rank := 0, op := "OpName.FW_multiref", ins := [10749], outs := [16453, 16457], params := [2] }
      10749 16453 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 10749 16453 16457)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16461 = denoteGraph_ringAttn pm initPM 10750 :=
    ringAttn_reduce1_pm_opaque pm initPM 1507
      { rank := 1, op := "OpName.FW_multiref", ins := [10750], outs := [16461, 16465], params := [2] }
      10750 16461 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 10750 16461 16465)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8381
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16453, denoteGraph_ringAttn pm initPM 16461] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16453).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16461).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8381).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8381 8381 16453 16461 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8408 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5650`.
    Identity alias: `8408` reconstructs exactly as `5650` (allGather of its shards). -/
theorem recon_intermediateGoal_8408_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8408
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5650 5650 10753 10754
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5650_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8408 = denoteGraph_ringAttn sm initSM 5650 :=
    ringAttn_reduce1_pm_opaque sm initSM 724
      { rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] }
      5650 8408 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5650 8392 8396 8400 8404 8408 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16488 = denoteGraph_ringAttn pm initPM 10753 :=
    ringAttn_reduce1_pm_opaque pm initPM 1510
      { rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] }
      10753 16488 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 10753 16472 16476 16480 16484 16488 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16511 = denoteGraph_ringAttn pm initPM 10754 :=
    ringAttn_reduce1_pm_opaque pm initPM 1511
      { rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] }
      10754 16511 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 10754 16495 16499 16503 16507 16511 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8408
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16488, denoteGraph_ringAttn pm initPM 16511] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16488).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16511).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8408).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8408 8408 16488 16511 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8439 — 2-tp `FW_multiref` fan-out (pos 2) of proven base `5699`.
    Identity alias: `8439` reconstructs exactly as `5699` (allGather of its shards). -/
theorem recon_intermediateGoal_8439_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8439
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5699 5699 10925 10926
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5699_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8439 = denoteGraph_ringAttn sm initSM 5699 :=
    ringAttn_reduce1_pm_opaque sm initSM 759
      { rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] }
      5699 8439 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5699 8431 8435 8439 8443 8447 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16558 = denoteGraph_ringAttn pm initPM 10925 :=
    ringAttn_reduce1_pm_opaque pm initPM 1580
      { rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] }
      10925 16558 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 10925 16550 16554 16558 16562 16566 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16581 = denoteGraph_ringAttn pm initPM 10926 :=
    ringAttn_reduce1_pm_opaque pm initPM 1581
      { rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] }
      10926 16581 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 10926 16573 16577 16581 16585 16589 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8439
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16558, denoteGraph_ringAttn pm initPM 16581] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16558).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16581).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8439).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8439 8439 16558 16581 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8470 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5748`.
    Identity alias: `8470` reconstructs exactly as `5748` (allGather of its shards). -/
theorem recon_intermediateGoal_8470_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8470
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5748 5748 11097 11098
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5748_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8470 = denoteGraph_ringAttn sm initSM 5748 :=
    ringAttn_reduce1_pm_opaque sm initSM 794
      { rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] }
      5748 8470 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5748 8470 8474 8478 8482 8486)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16628 = denoteGraph_ringAttn pm initPM 11097 :=
    ringAttn_reduce1_pm_opaque pm initPM 1650
      { rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] }
      11097 16628 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 11097 16628 16632 16636 16640 16644)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16651 = denoteGraph_ringAttn pm initPM 11098 :=
    ringAttn_reduce1_pm_opaque pm initPM 1651
      { rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] }
      11098 16651 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 11098 16651 16655 16659 16663 16667)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8470
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16628, denoteGraph_ringAttn pm initPM 16651] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16628).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16651).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8470).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8470 8470 16628 16651 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8490 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5779`.
    Identity alias: `8490` reconstructs exactly as `5779` (allGather of its shards). -/
theorem recon_intermediateGoal_8490_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8490
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5779 5779 11205 11206
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5779_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8490 = denoteGraph_ringAttn sm initSM 5779 :=
    ringAttn_reduce1_pm_opaque sm initSM 817
      { rank := 0, op := "OpName.FW_multiref", ins := [5779], outs := [8490, 8494], params := [2] }
      5779 8490 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5779 8490 8494)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16671 = denoteGraph_ringAttn pm initPM 11205 :=
    ringAttn_reduce1_pm_opaque pm initPM 1696
      { rank := 0, op := "OpName.FW_multiref", ins := [11205], outs := [16671, 16675], params := [2] }
      11205 16671 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11205 16671 16675)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16679 = denoteGraph_ringAttn pm initPM 11206 :=
    ringAttn_reduce1_pm_opaque pm initPM 1697
      { rank := 1, op := "OpName.FW_multiref", ins := [11206], outs := [16679, 16683], params := [2] }
      11206 16679 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11206 16679 16683)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8490
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16671, denoteGraph_ringAttn pm initPM 16679] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16671).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16679).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8490).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8490 8490 16671 16679 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8521 — 2-tp `FW_multiref` fan-out (pos 3) of proven base `5797`.
    Identity alias: `8521` reconstructs exactly as `5797` (allGather of its shards). -/
theorem recon_intermediateGoal_8521_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8521
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5797 5797 11269 11270
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5797_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8521 = denoteGraph_ringAttn sm initSM 5797 :=
    ringAttn_reduce1_pm_opaque sm initSM 829
      { rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] }
      5797 8521 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5797 8509 8513 8517 8521 8525 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16718 = denoteGraph_ringAttn pm initPM 11269 :=
    ringAttn_reduce1_pm_opaque pm initPM 1720
      { rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] }
      11269 16718 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 11269 16706 16710 16714 16718 16722 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16741 = denoteGraph_ringAttn pm initPM 11270 :=
    ringAttn_reduce1_pm_opaque pm initPM 1721
      { rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] }
      11270 16741 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 11270 16729 16733 16737 16741 16745 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8521
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16718, denoteGraph_ringAttn pm initPM 16741] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16718).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16741).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8521).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8521 8521 16718 16741 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8552 — 2-tp `FW_multiref` fan-out (pos 1) of proven base `5846`.
    Identity alias: `8552` reconstructs exactly as `5846` (allGather of its shards). -/
theorem recon_intermediateGoal_8552_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8552
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5846 5846 11441 11442
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5846_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8552 = denoteGraph_ringAttn sm initSM 5846 :=
    ringAttn_reduce1_pm_opaque sm initSM 864
      { rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] }
      5846 8552 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5846 8548 8552 8556 8560 8564 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16788 = denoteGraph_ringAttn pm initPM 11441 :=
    ringAttn_reduce1_pm_opaque pm initPM 1790
      { rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] }
      11441 16788 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 11441 16784 16788 16792 16796 16800 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16811 = denoteGraph_ringAttn pm initPM 11442 :=
    ringAttn_reduce1_pm_opaque pm initPM 1791
      { rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] }
      11442 16811 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 11442 16807 16811 16815 16819 16823 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8552
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16788, denoteGraph_ringAttn pm initPM 16811] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16788).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16811).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8552).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8552 8552 16788 16811 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8576 — 2-tp `FW_multiref` fan-out (pos 0) of proven base `5893`.
    Identity alias: `8576` reconstructs exactly as `5893` (allGather of its shards). -/
theorem recon_intermediateGoal_8576_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8576
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5893 5893 11609 11610
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5893_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8576 = denoteGraph_ringAttn sm initSM 5893 :=
    ringAttn_reduce1_pm_opaque sm initSM 897
      { rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580], params := [2] }
      5893 8576 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5893 8576 8580)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16843 = denoteGraph_ringAttn pm initPM 11609 :=
    ringAttn_reduce1_pm_opaque pm initPM 1856
      { rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847], params := [2] }
      11609 16843 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 11609 16843 16847)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16851 = denoteGraph_ringAttn pm initPM 11610 :=
    ringAttn_reduce1_pm_opaque pm initPM 1857
      { rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855], params := [2] }
      11610 16851 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 11610 16851 16855)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8576
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16843, denoteGraph_ringAttn pm initPM 16851] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16843).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16851).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8576).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8576 8576 16843 16851 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8603 — 2-tp `FW_multiref` fan-out (pos 4) of proven base `5895`.
    Identity alias: `8603` reconstructs exactly as `5895` (allGather of its shards). -/
theorem recon_intermediateGoal_8603_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8603
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5895 5895 11613 11614
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5895_ringAttn initSM initPM hSM hPM hInit hWF)
  have sG : denoteGraph_ringAttn sm initSM 8603 = denoteGraph_ringAttn sm initSM 5895 :=
    ringAttn_reduce1_pm_opaque sm initSM 899
      { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }
      5895 8603 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5895 8587 8591 8595 8599 8603 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP0 : denoteGraph_ringAttn pm initPM 16878 = denoteGraph_ringAttn pm initPM 11613 :=
    ringAttn_reduce1_pm_opaque pm initPM 1860
      { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }
      11613 16878 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 11613 16862 16866 16870 16874 16878 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pP1 : denoteGraph_ringAttn pm initPM 16901 = denoteGraph_ringAttn pm initPM 11614 :=
    ringAttn_reduce1_pm_opaque pm initPM 1861
      { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }
      11614 16901 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 11614 16885 16889 16893 16897 16901 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8603
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16878, denoteGraph_ringAttn pm initPM 16901] := by
    rw [sG, hgB, ← pP0, ← pP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 16878).shape = [2048, 1024] := by
    rw [pP0]; exact hsPA
  have hsp1 : (denoteGraph_ringAttn pm initPM 16901).shape = [2048, 1024] := by
    rw [pP1]; exact hsPB
  have hshape : (denoteGraph_ringAttn sm initSM 8603).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8603 8603 16878 16901 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
