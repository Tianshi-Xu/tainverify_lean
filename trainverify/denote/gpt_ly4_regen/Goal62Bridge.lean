/- goal_62 桥 (prereqs 72 个)。
   SM=FW_transpose(649,p=[1,2])→650 (sm node 69);
   PM=4×ChunkPrim(649,dim=2)→2365-2368 (pm node 437-440), 然后 4×FW_transpose(chunk,p=[1,2])→2369-2372 (pm node 449-452). tps=4个, gatherDim=2.
   649=goal_61 输出 (single-tp [1,8,4,8])。结构同 goal_45/goal_39: ChunkPrim + FW_transpose, multi-tps,
   gather distributes over transpose。套 Goal45Bridge 模板 (完全同构, 仅 dim 3→2, tid/node 不同, 输入 goal_44→goal_61)。 -/
import denote.gpt_ly4_regen.Goal61Bridge
import denote.gpt_ly4_regen.Goal_62

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

-- ========== 迷你图 sm_goal_62 算 650 ==========
theorem denote_sm_goal_62_650 (s : Store) :
    denoteGraph sm_goal_62 s 650 = transposeAxes 1 2 (s 649) := by
  simp only [sm_goal_62, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

theorem denote_pm_goal_62_2369 (s : Store) :
    denoteGraph pm_goal_62 s 2369 = transposeAxes 1 2 (chunkPrimDimN 3 4 0 (s 649)) := by
  simp only [pm_goal_62, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_62_2370 (s : Store) :
    denoteGraph pm_goal_62 s 2370 = transposeAxes 1 2 (chunkPrimDimN 3 4 1 (s 649)) := by
  simp only [pm_goal_62, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_62_2371 (s : Store) :
    denoteGraph pm_goal_62 s 2371 = transposeAxes 1 2 (chunkPrimDimN 3 4 2 (s 649)) := by
  simp only [pm_goal_62, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_62_2372 (s : Store) :
    denoteGraph pm_goal_62 s 2372 = transposeAxes 1 2 (chunkPrimDimN 3 4 3 (s 649)) := by
  simp only [pm_goal_62, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 650 (node 69) ==========
theorem sm_frame_650_self (initSM : Store) :
    denoteGraph sm initSM 650 = denoteGraph sm_goal_62 (denoteGraph sm initSM) 650 := by
  rw [denote_sm_goal_62_650]
  rw [sm_val initSM 69 650 (by native_decide) (by native_decide)]
  rw [show sm.nodes[69]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [649], outs := [650], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 69 649 (by native_decide)]

-- ========== PM full: 2365-2368 (4 ChunkPrim dim=2, node 437-440) ==========
theorem pm_full_2365 (initPM : Store) :
    denoteGraph pm initPM 2365 = chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 649) := by
  rw [pm_val initPM 437 2365 (by native_decide) (by native_decide)]
  rw [show pm.nodes[437]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [649], outs := [2365], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 437 649 (by native_decide)]

theorem pm_full_2366 (initPM : Store) :
    denoteGraph pm initPM 2366 = chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 649) := by
  rw [pm_val initPM 438 2366 (by native_decide) (by native_decide)]
  rw [show pm.nodes[438]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [649], outs := [2366], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 438 649 (by native_decide)]

theorem pm_full_2367 (initPM : Store) :
    denoteGraph pm initPM 2367 = chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 649) := by
  rw [pm_val initPM 439 2367 (by native_decide) (by native_decide)]
  rw [show pm.nodes[439]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [649], outs := [2367], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 439 649 (by native_decide)]

theorem pm_full_2368 (initPM : Store) :
    denoteGraph pm initPM 2368 = chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 649) := by
  rw [pm_val initPM 440 2368 (by native_decide) (by native_decide)]
  rw [show pm.nodes[440]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [649], outs := [2368], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 440 649 (by native_decide)]

-- ========== PM full: 2369-2372 (4 FW_transpose, node 449-452) ==========
theorem pm_frame_2369_self (initPM : Store) :
    denoteGraph pm initPM 2369 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 649)) := by
  rw [pm_val initPM 449 2369 (by native_decide) (by native_decide)]
  rw [show pm.nodes[449]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [2365], outs := [2369], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 449 2365 (by native_decide)]
  rw [pm_full_2365]

theorem pm_frame_2370_self (initPM : Store) :
    denoteGraph pm initPM 2370 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 649)) := by
  rw [pm_val initPM 450 2370 (by native_decide) (by native_decide)]
  rw [show pm.nodes[450]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [2366], outs := [2370], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 450 2366 (by native_decide)]
  rw [pm_full_2366]

theorem pm_frame_2371_self (initPM : Store) :
    denoteGraph pm initPM 2371 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 649)) := by
  rw [pm_val initPM 451 2371 (by native_decide) (by native_decide)]
  rw [show pm.nodes[451]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [2367], outs := [2371], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 451 2367 (by native_decide)]
  rw [pm_full_2367]

theorem pm_frame_2372_self (initPM : Store) :
    denoteGraph pm initPM 2372 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 649)) := by
  rw [pm_val initPM 452 2372 (by native_decide) (by native_decide)]
  rw [show pm.nodes[452]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [2368], outs := [2372], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 452 2368 (by native_decide)]
  rw [pm_full_2368]

-- ========== 总装 ==========
theorem goal_62_cut_to_full (h : goal_62_stmt_cut) : goal_62_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
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
  have hg45 := goal_45_intermediate initSM initPM hSM hPM hInit
  have hg46 := goal_46_intermediate initSM initPM hSM hPM hInit
  have hg47 := goal_47_intermediate initSM initPM hSM hPM hInit
  have hg48 := goal_48_intermediate initSM initPM hSM hPM hInit
  have hg49 := goal_49_intermediate initSM initPM hSM hPM hInit
  have hg50 := goal_50_intermediate initSM initPM hSM hPM hInit
  have hg51 := goal_51_intermediate initSM initPM hSM hPM hInit
  have hg52 := goal_52_intermediate initSM initPM hSM hPM hInit
  have hg53 := goal_53_intermediate initSM initPM hSM hPM hInit
  have hg54 := goal_54_intermediate initSM initPM hSM hPM hInit
  have hg55 := goal_55_intermediate initSM initPM hSM hPM hInit
  have hg56 := goal_57_intermediate initSM initPM hSM hPM hInit
  have hg59 := goal_61_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg273 := goal_273_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hg281 := goal_281_intermediate initSM initPM hSM hPM hInit
  have hg283 := goal_283_intermediate initSM initPM hSM hPM hInit
  have hg285 := goal_285_intermediate initSM initPM hSM hPM hInit
  have hg289 := goal_291_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg55 hg56 hg59 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hg289 hinitC
  have hnr : pm_goal_62.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_62.numRanks goal_62_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_62_cut_initGoals, goal_62_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg50, hg51, hg52, hg53, hg54, hg55, hg56, hg59, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, hg281, hg283, hg285, hg289, List.forall_mem_nil _⟩
  have h649_smsh : (Ssm 649).shape = [1, 8, 4, 8] := by
    have h := hg59.1; simp only [goal_61] at h; exact h
  have h649_pmsh : (Spm 649).shape = [1, 8, 4, 8] := by
    have h := hg59.2.1; simp only [goal_61, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM60 : StoreShapesHold Ssm sm_goal_62InitEnv := by
    intro tid sh hsh
    rw [sm_goal_62InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_62InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h649_smsh
  have hPM60 : StoreShapesHold Spm pm_goal_62InitEnv := by
    intro tid sh hsh
    rw [pm_goal_62InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_62InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h649_pmsh
  have hcut := h Ssm Spm hSM60 hPM60 hInitCut
  have hsmf : Ssm 650 = denoteGraph sm_goal_62 Ssm 650 := by
    rw [hSsm]; exact sm_frame_650_self initSM
  have hpm2369 : Spm 2369 = denoteGraph pm_goal_62 Spm 2369 := by
    rw [denote_pm_goal_62_2369]
    rw [hSpm]
    have := pm_frame_2369_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2370 : Spm 2370 = denoteGraph pm_goal_62 Spm 2370 := by
    rw [denote_pm_goal_62_2370]
    rw [hSpm]
    have := pm_frame_2370_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2371 : Spm 2371 = denoteGraph pm_goal_62 Spm 2371 := by
    rw [denote_pm_goal_62_2371]
    rw [hSpm]
    have := pm_frame_2371_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2372 : Spm 2372 = denoteGraph pm_goal_62 Spm 2372 := by
    rw [denote_pm_goal_62_2372]
    rw [hSpm]
    have := pm_frame_2372_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_62, List.map] at hcut ⊢
  rw [hsmf, hpm2369, hpm2370, hpm2371, hpm2372]
  exact hcut

theorem goal_62_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_62 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_62_stmt := goal_62_cut_to_full prove_goal_62_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
