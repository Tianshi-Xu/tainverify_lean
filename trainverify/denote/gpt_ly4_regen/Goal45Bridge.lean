/- goal_45 桥 (prereqs 54 个: goal_2..goal_44 + 257,259,261,263,265,267,269,271,275,277,279)。
   SM=FW_transpose(622,p=[1,2])→623 (sm node 48);
   PM=4×ChunkPrim(622,dim=3)→1973-1976 (pm node 309-312), 然后 4×FW_transpose(1973..,p=[1,2])→1977-1980 (pm node 313-316). tps=4个, gatherDim=3.
   622=goal_44 输出 (single-tp [1,4,8,8])。结构同 goal_39/goal_37: ChunkPrim dim=3 + FW_transpose,
   multi-tps, gather distributes over transpose。套 Goal39Bridge 模板 (完全同构,
   仅 tid/node 不同: 617→623, 616→622, 1825-1832→1973-1980, sm 42→48, pm 252-255→309-312 & 264-267→313-316, 输入 goal_38→goal_44)。 -/
import denote.gpt_ly4_regen.Goal44Bridge
import denote.gpt_ly4_regen.Goal_45

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_45 算 623 ==========
theorem denote_sm_goal_45_623 (s : Store) :
    denoteGraph sm_goal_45 s 623 = transposeAxes 1 2 (s 622) := by
  simp only [sm_goal_45, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_45 算 1977-1980 ==========
theorem denote_pm_goal_45_1977 (s : Store) :
    denoteGraph pm_goal_45 s 1977 = transposeAxes 1 2 (chunkPrimDimN 3 4 0 (s 622)) := by
  simp only [pm_goal_45, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_45_1978 (s : Store) :
    denoteGraph pm_goal_45 s 1978 = transposeAxes 1 2 (chunkPrimDimN 3 4 1 (s 622)) := by
  simp only [pm_goal_45, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_45_1979 (s : Store) :
    denoteGraph pm_goal_45 s 1979 = transposeAxes 1 2 (chunkPrimDimN 3 4 2 (s 622)) := by
  simp only [pm_goal_45, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_45_1980 (s : Store) :
    denoteGraph pm_goal_45 s 1980 = transposeAxes 1 2 (chunkPrimDimN 3 4 3 (s 622)) := by
  simp only [pm_goal_45, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 623 (node 48) ==========
theorem sm_frame_623_self (initSM : Store) :
    denoteGraph sm initSM 623 = denoteGraph sm_goal_45 (denoteGraph sm initSM) 623 := by
  rw [denote_sm_goal_45_623]
  rw [sm_val initSM 48 623 (by native_decide) (by native_decide)]
  rw [show sm.nodes[48]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [622], outs := [623], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 48 622 (by native_decide)]

-- ========== PM full: 1973-1976 (4 ChunkPrim dim=3, node 309-312) ==========
theorem pm_full_1973 (initPM : Store) :
    denoteGraph pm initPM 1973 = chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 622) := by
  rw [pm_val initPM 309 1973 (by native_decide) (by native_decide)]
  rw [show pm.nodes[309]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [622], outs := [1973], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 309 622 (by native_decide)]

theorem pm_full_1974 (initPM : Store) :
    denoteGraph pm initPM 1974 = chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 622) := by
  rw [pm_val initPM 310 1974 (by native_decide) (by native_decide)]
  rw [show pm.nodes[310]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [622], outs := [1974], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 310 622 (by native_decide)]

theorem pm_full_1975 (initPM : Store) :
    denoteGraph pm initPM 1975 = chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 622) := by
  rw [pm_val initPM 311 1975 (by native_decide) (by native_decide)]
  rw [show pm.nodes[311]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [622], outs := [1975], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 311 622 (by native_decide)]

theorem pm_full_1976 (initPM : Store) :
    denoteGraph pm initPM 1976 = chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 622) := by
  rw [pm_val initPM 312 1976 (by native_decide) (by native_decide)]
  rw [show pm.nodes[312]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [622], outs := [1976], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 312 622 (by native_decide)]

-- ========== PM full: 1977-1980 (4 FW_transpose, node 313-316) ==========
theorem pm_frame_1977_self (initPM : Store) :
    denoteGraph pm initPM 1977 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 622)) := by
  rw [pm_val initPM 313 1977 (by native_decide) (by native_decide)]
  rw [show pm.nodes[313]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1973], outs := [1977], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 313 1973 (by native_decide)]
  rw [pm_full_1973]

theorem pm_frame_1978_self (initPM : Store) :
    denoteGraph pm initPM 1978 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 622)) := by
  rw [pm_val initPM 314 1978 (by native_decide) (by native_decide)]
  rw [show pm.nodes[314]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1974], outs := [1978], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 314 1974 (by native_decide)]
  rw [pm_full_1974]

theorem pm_frame_1979_self (initPM : Store) :
    denoteGraph pm initPM 1979 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 622)) := by
  rw [pm_val initPM 315 1979 (by native_decide) (by native_decide)]
  rw [show pm.nodes[315]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1975], outs := [1979], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 315 1975 (by native_decide)]
  rw [pm_full_1975]

theorem pm_frame_1980_self (initPM : Store) :
    denoteGraph pm initPM 1980 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 622)) := by
  rw [pm_val initPM 316 1980 (by native_decide) (by native_decide)]
  rw [show pm.nodes[316]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1976], outs := [1980], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 316 1976 (by native_decide)]
  rw [pm_full_1976]

-- ========== 总装 ==========
theorem goal_45_cut_to_full (h : goal_45_stmt_cut) : goal_45_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg6 := goal_6_intermediate initSM initPM hSM hPM hInit
  have hg7 := goal_7_intermediate initSM initPM hSM hPM hInit
  have hg8 := goal_8_intermediate initSM initPM hSM hPM hInit
  have hg9 := goal_9_intermediate initSM initPM hSM hPM hInit
  have hg10 := goal_10_intermediate initSM initPM hSM hPM hInit
  have hg11 := goal_11_intermediate initSM initPM hSM hPM hInit
  have hg12 := goal_12_intermediate initSM initPM hSM hPM hInit
  have hg13 := goal_13_intermediate initSM initPM hSM hPM hInit
  have hg14 := goal_14_intermediate initSM initPM hSM hPM hInit
  have hg15 := goal_15_intermediate initSM initPM hSM hPM hInit
  have hg16 := goal_16_intermediate initSM initPM hSM hPM hInit
  have hg17 := goal_17_intermediate initSM initPM hSM hPM hInit
  have hg18 := goal_18_intermediate initSM initPM hSM hPM hInit
  have hg19 := goal_19_intermediate initSM initPM hSM hPM hInit
  have hg20 := goal_20_intermediate initSM initPM hSM hPM hInit
  have hg21 := goal_21_intermediate initSM initPM hSM hPM hInit
  have hg22 := goal_22_intermediate initSM initPM hSM hPM hInit
  have hg23 := goal_23_intermediate initSM initPM hSM hPM hInit
  have hg24 := goal_24_intermediate initSM initPM hSM hPM hInit
  have hg25 := goal_25_intermediate initSM initPM hSM hPM hInit
  have hg26 := goal_26_intermediate initSM initPM hSM hPM hInit
  have hg27 := goal_27_intermediate initSM initPM hSM hPM hInit
  have hg28 := goal_28_intermediate initSM initPM hSM hPM hInit
  have hg29 := goal_29_intermediate initSM initPM hSM hPM hInit
  have hg30 := goal_30_intermediate initSM initPM hSM hPM hInit
  have hg31 := goal_31_intermediate initSM initPM hSM hPM hInit
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg33 := goal_33_intermediate initSM initPM hSM hPM hInit
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg38 := goal_38_intermediate initSM initPM hSM hPM hInit
  have hg39 := goal_39_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg41 := goal_41_intermediate initSM initPM hSM hPM hInit
  have hg42 := goal_42_intermediate initSM initPM hSM hPM hInit
  have hg43 := goal_43_intermediate initSM initPM hSM hPM hInit
  have hg44 := goal_44_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_45.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_45.numRanks goal_45_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_45_cut_initGoals, goal_45_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg6
      · exact hg7
      · exact hg8
      · exact hg9
      · exact hg10
      · exact hg11
      · exact hg12
      · exact hg13
      · exact hg14
      · exact hg15
      · exact hg16
      · exact hg17
      · exact hg18
      · exact hg19
      · exact hg20
      · exact hg21
      · exact hg22
      · exact hg23
      · exact hg24
      · exact hg25
      · exact hg26
      · exact hg27
      · exact hg28
      · exact hg29
      · exact hg30
      · exact hg31
      · exact hg32
      · exact hg33
      · exact hg34
      · exact hg35
      · exact hg36
      · exact hg37
      · exact hg38
      · exact hg39
      · exact hg40
      · exact hg41
      · exact hg42
      · exact hg43
      · exact hg44
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg275
      · exact hg277
      · exact hg279
  -- shape: 622 = goal_44.ts/tps (single), shape [1,4,8,8]
  have h622_smsh : (Ssm 622).shape = [1, 4, 8, 8] := by
    have h := hg44.1; simp only [goal_44] at h; exact h
  have h622_pmsh : (Spm 622).shape = [1, 4, 8, 8] := by
    have h := hg44.2.1; simp only [goal_44, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM45 : StoreShapesHold Ssm sm_goal_45InitEnv := by
    intro tid sh hsh
    rw [sm_goal_45InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_45InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h622_smsh
  have hPM45 : StoreShapesHold Spm pm_goal_45InitEnv := by
    intro tid sh hsh
    rw [pm_goal_45InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_45InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h622_pmsh
  have hcut := h Ssm Spm hSM45 hPM45 hInitCut
  -- Frame: 623 (sm), 1977-1980 (pm)
  have hsmf : Ssm 623 = denoteGraph sm_goal_45 Ssm 623 := by
    rw [hSsm]; exact sm_frame_623_self initSM
  have hpm1977 : Spm 1977 = denoteGraph pm_goal_45 Spm 1977 := by
    rw [denote_pm_goal_45_1977]
    rw [hSpm]
    have := pm_frame_1977_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1978 : Spm 1978 = denoteGraph pm_goal_45 Spm 1978 := by
    rw [denote_pm_goal_45_1978]
    rw [hSpm]
    have := pm_frame_1978_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1979 : Spm 1979 = denoteGraph pm_goal_45 Spm 1979 := by
    rw [denote_pm_goal_45_1979]
    rw [hSpm]
    have := pm_frame_1979_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1980 : Spm 1980 = denoteGraph pm_goal_45 Spm 1980 := by
    rw [denote_pm_goal_45_1980]
    rw [hSpm]
    have := pm_frame_1980_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_45, List.map] at hcut ⊢
  rw [hsmf, hpm1977, hpm1978, hpm1979, hpm1980]
  exact hcut

theorem goal_45_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_45 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_45_stmt := goal_45_cut_to_full prove_goal_45_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_45] using this

end TrainVerify.Denote.GeneratedGoals
