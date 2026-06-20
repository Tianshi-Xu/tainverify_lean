/- goal_60 桥 (prereqs 72 个)。
   SM=FW_transpose(647,p=[1,2])→648 (sm node 68);
   PM=4×ChunkPrim(647,dim=2)→2341-2344 (pm node 433-436), 然后 4×FW_transpose(chunk,p=[1,2])→2345-2348 (pm node 445-448). tps=4个, gatherDim=2.
   647=goal_59 输出 (single-tp [1,8,4,8])。结构同 goal_45/goal_39: ChunkPrim + FW_transpose, multi-tps,
   gather distributes over transpose。套 Goal45Bridge 模板 (完全同构, 仅 dim 3→2, tid/node 不同, 输入 goal_44→goal_59)。 -/
import denote.gpt_ly4_regen.Goal59Bridge
import denote.gpt_ly4_regen.Goal_60

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

-- ========== 迷你图 sm_goal_60 算 648 ==========
theorem denote_sm_goal_60_648 (s : Store) :
    denoteGraph sm_goal_60 s 648 = transposeAxes 1 2 (s 647) := by
  simp only [sm_goal_60, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

theorem denote_pm_goal_60_2345 (s : Store) :
    denoteGraph pm_goal_60 s 2345 = transposeAxes 1 2 (chunkPrimDimN 2 4 0 (s 647)) := by
  simp only [pm_goal_60, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_60_2346 (s : Store) :
    denoteGraph pm_goal_60 s 2346 = transposeAxes 1 2 (chunkPrimDimN 2 4 1 (s 647)) := by
  simp only [pm_goal_60, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_60_2347 (s : Store) :
    denoteGraph pm_goal_60 s 2347 = transposeAxes 1 2 (chunkPrimDimN 2 4 2 (s 647)) := by
  simp only [pm_goal_60, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_60_2348 (s : Store) :
    denoteGraph pm_goal_60 s 2348 = transposeAxes 1 2 (chunkPrimDimN 2 4 3 (s 647)) := by
  simp only [pm_goal_60, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 648 (node 68) ==========
theorem sm_frame_648_self (initSM : Store) :
    denoteGraph sm initSM 648 = denoteGraph sm_goal_60 (denoteGraph sm initSM) 648 := by
  rw [denote_sm_goal_60_648]
  rw [sm_val initSM 68 648 (by native_decide) (by native_decide)]
  rw [show sm.nodes[68]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [647], outs := [648], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 68 647 (by native_decide)]

-- ========== PM full: 2341-2344 (4 ChunkPrim dim=2, node 433-436) ==========
theorem pm_full_2341 (initPM : Store) :
    denoteGraph pm initPM 2341 = chunkPrimDimN 2 pm.numRanks 0 (denoteGraph pm initPM 647) := by
  rw [pm_val initPM 433 2341 (by native_decide) (by native_decide)]
  rw [show pm.nodes[433]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [647], outs := [2341], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 433 647 (by native_decide)]

theorem pm_full_2342 (initPM : Store) :
    denoteGraph pm initPM 2342 = chunkPrimDimN 2 pm.numRanks 1 (denoteGraph pm initPM 647) := by
  rw [pm_val initPM 434 2342 (by native_decide) (by native_decide)]
  rw [show pm.nodes[434]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [647], outs := [2342], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 434 647 (by native_decide)]

theorem pm_full_2343 (initPM : Store) :
    denoteGraph pm initPM 2343 = chunkPrimDimN 2 pm.numRanks 2 (denoteGraph pm initPM 647) := by
  rw [pm_val initPM 435 2343 (by native_decide) (by native_decide)]
  rw [show pm.nodes[435]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [647], outs := [2343], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 435 647 (by native_decide)]

theorem pm_full_2344 (initPM : Store) :
    denoteGraph pm initPM 2344 = chunkPrimDimN 2 pm.numRanks 3 (denoteGraph pm initPM 647) := by
  rw [pm_val initPM 436 2344 (by native_decide) (by native_decide)]
  rw [show pm.nodes[436]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [647], outs := [2344], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 436 647 (by native_decide)]

-- ========== PM full: 2345-2348 (4 FW_transpose, node 445-448) ==========
theorem pm_frame_2345_self (initPM : Store) :
    denoteGraph pm initPM 2345 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 0 (denoteGraph pm initPM 647)) := by
  rw [pm_val initPM 445 2345 (by native_decide) (by native_decide)]
  rw [show pm.nodes[445]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [2341], outs := [2345], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 445 2341 (by native_decide)]
  rw [pm_full_2341]

theorem pm_frame_2346_self (initPM : Store) :
    denoteGraph pm initPM 2346 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 1 (denoteGraph pm initPM 647)) := by
  rw [pm_val initPM 446 2346 (by native_decide) (by native_decide)]
  rw [show pm.nodes[446]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [2342], outs := [2346], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 446 2342 (by native_decide)]
  rw [pm_full_2342]

theorem pm_frame_2347_self (initPM : Store) :
    denoteGraph pm initPM 2347 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 2 (denoteGraph pm initPM 647)) := by
  rw [pm_val initPM 447 2347 (by native_decide) (by native_decide)]
  rw [show pm.nodes[447]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [2343], outs := [2347], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 447 2343 (by native_decide)]
  rw [pm_full_2343]

theorem pm_frame_2348_self (initPM : Store) :
    denoteGraph pm initPM 2348 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 3 (denoteGraph pm initPM 647)) := by
  rw [pm_val initPM 448 2348 (by native_decide) (by native_decide)]
  rw [show pm.nodes[448]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [2344], outs := [2348], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 448 2344 (by native_decide)]
  rw [pm_full_2344]

-- ========== 总装 ==========
theorem goal_60_cut_to_full (h : goal_60_stmt_cut) : goal_60_stmt := by
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
  have hg56 := goal_56_intermediate initSM initPM hSM hPM hInit
  have hg59 := goal_59_intermediate initSM initPM hSM hPM hInit
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
  have hg289 := goal_289_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg55 hg56 hg59 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hg289 hinitC
  have hnr : pm_goal_60.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_60.numRanks goal_60_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_60_cut_initGoals, goal_60_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg45
      · exact hg46
      · exact hg47
      · exact hg48
      · exact hg49
      · exact hg50
      · exact hg51
      · exact hg52
      · exact hg53
      · exact hg54
      · exact hg55
      · exact hg56
      · exact hg59
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg273
      · exact hg275
      · exact hg277
      · exact hg279
      · exact hg281
      · exact hg283
      · exact hg285
      · exact hg289
  have h647_smsh : (Ssm 647).shape = [1, 8, 4, 8] := by
    have h := hg59.1; simp only [goal_59] at h; exact h
  have h647_pmsh : (Spm 647).shape = [1, 8, 4, 8] := by
    have h := hg59.2.1; simp only [goal_59, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM60 : StoreShapesHold Ssm sm_goal_60InitEnv := by
    intro tid sh hsh
    rw [sm_goal_60InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_60InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h647_smsh
  have hPM60 : StoreShapesHold Spm pm_goal_60InitEnv := by
    intro tid sh hsh
    rw [pm_goal_60InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_60InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h647_pmsh
  have hcut := h Ssm Spm hSM60 hPM60 hInitCut
  have hsmf : Ssm 648 = denoteGraph sm_goal_60 Ssm 648 := by
    rw [hSsm]; exact sm_frame_648_self initSM
  have hpm2345 : Spm 2345 = denoteGraph pm_goal_60 Spm 2345 := by
    rw [denote_pm_goal_60_2345]
    rw [hSpm]
    have := pm_frame_2345_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2346 : Spm 2346 = denoteGraph pm_goal_60 Spm 2346 := by
    rw [denote_pm_goal_60_2346]
    rw [hSpm]
    have := pm_frame_2346_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2347 : Spm 2347 = denoteGraph pm_goal_60 Spm 2347 := by
    rw [denote_pm_goal_60_2347]
    rw [hSpm]
    have := pm_frame_2347_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2348 : Spm 2348 = denoteGraph pm_goal_60 Spm 2348 := by
    rw [denote_pm_goal_60_2348]
    rw [hSpm]
    have := pm_frame_2348_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_60, List.map] at hcut ⊢
  rw [hsmf, hpm2345, hpm2346, hpm2347, hpm2348]
  exact hcut

theorem goal_60_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_60 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_60_stmt := goal_60_cut_to_full prove_goal_60_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
