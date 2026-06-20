/- goal_20 桥 (prereqs=[2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,257,261,263,265])。
   第15种结构: 纯 per-rank FW_transpose, multi-tps, 无 collective。
   SM=FW_transpose(587,p=[1,2])→588 (node 20)。
   PM=4×FW_transpose(1413-1416,p=[1,2])→1433-1436 (node 127-130)。输入 587/1413-1416 来自 goal_19。
   套 Goal19Bridge (multi-tps 总装) + Goal15Bridge (transpose frame) 模板, 但去掉 AllToAll 包装 (PM 直接 transpose 上游 tps)。
   注: transpose-distrib 语义已在 cut 证明里处理; bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal14Bridge
import denote.gpt_ly4_regen.Goal18Bridge
import denote.gpt_ly4_regen.Goal19Bridge
import denote.gpt_ly4_regen.Goal_20

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_20 算 588 (FW_transpose) ==========
theorem denote_sm_goal_20_588 (s : Store) :
    denoteGraph sm_goal_20 s 588 = transposeAxes 1 2 (s 587) := by
  simp only [sm_goal_20, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_20 算 1433-1436 (4×FW_transpose) ==========
theorem denote_pm_goal_20_1433 (s : Store) :
    denoteGraph pm_goal_20 s 1433 = transposeAxes 1 2 (s 1413) := by
  simp only [pm_goal_20, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]

theorem denote_pm_goal_20_1434 (s : Store) :
    denoteGraph pm_goal_20 s 1434 = transposeAxes 1 2 (s 1414) := by
  simp only [pm_goal_20, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_20_1435 (s : Store) :
    denoteGraph pm_goal_20 s 1435 = transposeAxes 1 2 (s 1415) := by
  simp only [pm_goal_20, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_20_1436 (s : Store) :
    denoteGraph pm_goal_20 s 1436 = transposeAxes 1 2 (s 1416) := by
  simp only [pm_goal_20, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 588 (node 20 FW_transpose) ==========
theorem sm_frame_588_self (initSM : Store) :
    denoteGraph sm initSM 588 = denoteGraph sm_goal_20 (denoteGraph sm initSM) 588 := by
  rw [denote_sm_goal_20_588]
  rw [sm_val initSM 20 588 (by native_decide) (by native_decide)]
  rw [show sm.nodes[20]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [587], outs := [588], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 20 587 (by native_decide)]

-- ========== PM self-frame: 1433-1436 (4×FW_transpose, node 127-130) ==========
theorem pm_frame_1433_self (initPM : Store) :
    denoteGraph pm initPM 1433 = transposeAxes 1 2 (denoteGraph pm initPM 1413) := by
  rw [pm_val initPM 127 1433 (by native_decide) (by native_decide)]
  rw [show pm.nodes[127]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1413], outs := [1433], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 127 1413 (by native_decide)]

theorem pm_frame_1434_self (initPM : Store) :
    denoteGraph pm initPM 1434 = transposeAxes 1 2 (denoteGraph pm initPM 1414) := by
  rw [pm_val initPM 128 1434 (by native_decide) (by native_decide)]
  rw [show pm.nodes[128]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1414], outs := [1434], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 128 1414 (by native_decide)]

theorem pm_frame_1435_self (initPM : Store) :
    denoteGraph pm initPM 1435 = transposeAxes 1 2 (denoteGraph pm initPM 1415) := by
  rw [pm_val initPM 129 1435 (by native_decide) (by native_decide)]
  rw [show pm.nodes[129]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1415], outs := [1435], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 129 1415 (by native_decide)]

theorem pm_frame_1436_self (initPM : Store) :
    denoteGraph pm initPM 1436 = transposeAxes 1 2 (denoteGraph pm initPM 1416) := by
  rw [pm_val initPM 130 1436 (by native_decide) (by native_decide)]
  rw [show pm.nodes[130]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1416], outs := [1436], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 130 1416 (by native_decide)]

-- ========== 总装 ==========
theorem goal_20_cut_to_full (h : goal_20_stmt_cut) : goal_20_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg257 hg261 hg263 hg265 hinitC
  have hnr : pm_goal_20.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 587=goal_19.ts [1,4,8,8]; 1413-1416=goal_19.tps [1,4,8,2]
  have h587_smsh : (Ssm 587).shape = [1, 4, 8, 8] := by
    have h := hg19.1; simp only [goal_19] at h; exact h
  have h1413_pmsh : (Spm 1413).shape = [1, 4, 8, 2] := by
    have h := hg19.2.1; simp only [goal_19, List.map, List.cons.injEq, and_true] at h; exact h.1
  have h1414_pmsh : (Spm 1414).shape = [1, 4, 8, 2] := by
    have h := hg19.2.1; simp only [goal_19, List.map, List.cons.injEq, and_true] at h; exact h.2.1
  have h1415_pmsh : (Spm 1415).shape = [1, 4, 8, 2] := by
    have h := hg19.2.1; simp only [goal_19, List.map, List.cons.injEq, and_true] at h; exact h.2.2.1
  have h1416_pmsh : (Spm 1416).shape = [1, 4, 8, 2] := by
    have h := hg19.2.1; simp only [goal_19, List.map, List.cons.injEq, and_true] at h; exact h.2.2.2
  have hSM20 : StoreShapesHold Ssm sm_goal_20InitEnv := by
    intro tid sh hsh
    rw [sm_goal_20InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_20InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h587_smsh
  have hPM20 : StoreShapesHold Spm pm_goal_20InitEnv := by
    intro tid sh hsh
    rw [pm_goal_20InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_20InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1413_pmsh
    · exact h1414_pmsh
    · exact h1415_pmsh
    · exact h1416_pmsh
  have hInitCut : InitGoalsHold pm_goal_20.numRanks goal_20_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_20_cut_initGoals, goal_20_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg261
      · exact hg263
      · exact hg265
  have hcut := h Ssm Spm hSM20 hPM20 hInitCut
  -- Frame: 588 (sm), 1433-1436 (pm)
  have hsmf : Ssm 588 = denoteGraph sm_goal_20 Ssm 588 := by
    rw [hSsm]; exact sm_frame_588_self initSM
  have hpm1433 : Spm 1433 = denoteGraph pm_goal_20 Spm 1433 := by
    rw [denote_pm_goal_20_1433]; rw [hSpm]; exact pm_frame_1433_self initPM
  have hpm1434 : Spm 1434 = denoteGraph pm_goal_20 Spm 1434 := by
    rw [denote_pm_goal_20_1434]; rw [hSpm]; exact pm_frame_1434_self initPM
  have hpm1435 : Spm 1435 = denoteGraph pm_goal_20 Spm 1435 := by
    rw [denote_pm_goal_20_1435]; rw [hSpm]; exact pm_frame_1435_self initPM
  have hpm1436 : Spm 1436 = denoteGraph pm_goal_20 Spm 1436 := by
    rw [denote_pm_goal_20_1436]; rw [hSpm]; exact pm_frame_1436_self initPM
  rw [hnr] at hcut
  simp only [goal_20, List.map] at hcut ⊢
  rw [hsmf, hpm1433, hpm1434, hpm1435, hpm1436]
  exact hcut

theorem goal_20_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_20 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_20_stmt := goal_20_cut_to_full prove_goal_20_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
