/- goal_7 桥 (prereqs=[2,3,4,5,257,263])。SM=FW_linear(922,573)→574; PM=4×FW_linear(1201-1204,573)→1205-1208 →AllGather→574(单tp)。
   输入 922/1201-1204 = goal_263 输出; 573 = weight init。套 AllGather-in-PM 模板 + FW_linear。 -/
import denote.gpt_ly4_regen.Goal263Bridge
import denote.gpt_ly4_regen.Goal_7

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- goal_263_intermediate 已移至 Goal263Bridge (import 获得)

-- ========== 迷你图 sm_goal_7 算 574 (FW_linear) ==========
theorem denote_sm_goal_7_574 (s : Store) :
    denoteGraph sm_goal_7 s 574 = fw_linear (s 922) (s 573) := by
  simp only [sm_goal_7, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_7 算 574 (4×FW_linear → AllGather) ==========
theorem denote_pm_goal_7_574 (s : Store) :
    denoteGraph pm_goal_7 s 574 = allGatherPrimDimN 1 4 0
      [fw_linear (s 1201) (s 573), fw_linear (s 1202) (s 573),
       fw_linear (s 1203) (s 573), fw_linear (s 1204) (s 573)] := by
  simp only [pm_goal_7, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out]
  simp only [List.map]
  set_option maxHeartbeats 800000 in congr 1

-- ========== SM self-frame: full 算 574 (node 7 FW_linear) ==========
theorem sm_frame_574_self (initSM : Store) :
    denoteGraph sm initSM 574 = denoteGraph sm_goal_7 (denoteGraph sm initSM) 574 := by
  rw [denote_sm_goal_7_574]
  rw [sm_val initSM 7 574 (by native_decide) (by native_decide)]
  rw [show sm.nodes[7]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [922, 573], outs := [574] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 7 922 (by native_decide),
      sm_prefix_eq initSM 7 573 (by native_decide)]

-- ========== full pm 算 FW_linear 输出 1205-1208 (node 42/44/46/49) = fw_linear(Spm 1201.., Spm 573) ==========
theorem pm_full_1205 (initPM : Store) :
    denoteGraph pm initPM 1205 = fw_linear (denoteGraph pm initPM 1201) (denoteGraph pm initPM 573) := by
  rw [pm_val initPM 42 1205 (by native_decide) (by native_decide)]
  rw [show pm.nodes[42]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1201, 573], outs := [1205] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 42 1201 (by native_decide),
      pm_prefix_eq initPM 42 573 (by native_decide)]

theorem pm_full_1206 (initPM : Store) :
    denoteGraph pm initPM 1206 = fw_linear (denoteGraph pm initPM 1202) (denoteGraph pm initPM 573) := by
  rw [pm_val initPM 44 1206 (by native_decide) (by native_decide)]
  rw [show pm.nodes[44]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [1202, 573], outs := [1206] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 44 1202 (by native_decide),
      pm_prefix_eq initPM 44 573 (by native_decide)]

theorem pm_full_1207 (initPM : Store) :
    denoteGraph pm initPM 1207 = fw_linear (denoteGraph pm initPM 1203) (denoteGraph pm initPM 573) := by
  rw [pm_val initPM 46 1207 (by native_decide) (by native_decide)]
  rw [show pm.nodes[46]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [1203, 573], outs := [1207] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 46 1203 (by native_decide),
      pm_prefix_eq initPM 46 573 (by native_decide)]

theorem pm_full_1208 (initPM : Store) :
    denoteGraph pm initPM 1208 = fw_linear (denoteGraph pm initPM 1204) (denoteGraph pm initPM 573) := by
  rw [pm_val initPM 49 1208 (by native_decide) (by native_decide)]
  rw [show pm.nodes[49]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [1204, 573], outs := [1208] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 49 1204 (by native_decide),
      pm_prefix_eq initPM 49 573 (by native_decide)]

-- ========== PM self-frame: 574 (AllGather node 55, ins=computed range) ==========
theorem pm_frame_574_self (initPM : Store) :
    denoteGraph pm initPM 574
      = allGatherPrimDimN 1 4 0
          [fw_linear (denoteGraph pm initPM 1201) (denoteGraph pm initPM 573),
           fw_linear (denoteGraph pm initPM 1202) (denoteGraph pm initPM 573),
           fw_linear (denoteGraph pm initPM 1203) (denoteGraph pm initPM 573),
           fw_linear (denoteGraph pm initPM 1204) (denoteGraph pm initPM 573)] := by
  rw [pm_val initPM 55 574 (by native_decide) (by native_decide)]
  rw [show pm.nodes[55]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 1205 + r)), outs := [574], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 55 1205 (by native_decide),
      pm_prefix_eq initPM 55 1206 (by native_decide),
      pm_prefix_eq initPM 55 1207 (by native_decide),
      pm_prefix_eq initPM 55 1208 (by native_decide)]
  rw [pm_full_1205, pm_full_1206, pm_full_1207, pm_full_1208]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_7_cut_to_full (h : goal_7_stmt_cut) : goal_7_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg257 hg263 hinitC
  have hnr : pm_goal_7.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_7.numRanks goal_7_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_7_cut_initGoals, goal_7_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg257
      · exact hg263
  -- 922 = goal_263.ts; 1201-1204 = goal_263.tps; 573 = weight init
  have h922_smsh : (Ssm 922).shape = [1, 8, 32] := by
    have h := hg263.1; simp only [goal_263] at h; exact h
  have h4 : (Spm 1201).shape = [1,2,32] ∧ (Spm 1202).shape = [1,2,32] ∧
           (Spm 1203).shape = [1,2,32] ∧ (Spm 1204).shape = [1,2,32] := by
    have h := hg263.2.1
    simp only [goal_263, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1201sh, h1202sh, h1203sh, h1204sh⟩ := h4
  have h573_sm : (Ssm 573).shape = [32, 32] := by
    have hg := hinitC initGoal_573 (by simp only [initGoals]; decide)
    have h := hg.1; simp only [initGoal_573] at h; exact h
  have h573_pm : (Spm 573).shape = [32, 32] := by
    have hg := hinitC initGoal_573 (by simp only [initGoals]; decide)
    have h := hg.2.1; simp only [initGoal_573, List.map, List.cons.injEq] at h; exact h.1
  have hSM7 : StoreShapesHold Ssm sm_goal_7InitEnv := by
    intro tid sh hsh
    rw [sm_goal_7InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_7InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h573_sm
    · exact h922_smsh
  have hPM7 : StoreShapesHold Spm pm_goal_7InitEnv := by
    intro tid sh hsh
    rw [pm_goal_7InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_7InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h573_pm
    · exact h1201sh
    · exact h1202sh
    · exact h1203sh
    · exact h1204sh
  have hcut := h Ssm Spm hSM7 hPM7 hInitCut
  have hsmf : Ssm 574 = denoteGraph sm_goal_7 Ssm 574 := by
    rw [hSsm]; exact sm_frame_574_self initSM
  have hpm574 : Spm 574 = denoteGraph pm_goal_7 Spm 574 := by
    rw [denote_pm_goal_7_574]
    rw [hSpm]; exact pm_frame_574_self initPM
  rw [hnr] at hcut
  simp only [goal_7, List.map] at hcut ⊢
  rw [hsmf, hpm574]
  exact hcut

theorem goal_7_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_7 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_7_stmt := goal_7_cut_to_full prove_goal_7_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals


#print axioms TrainVerify.Denote.GeneratedGoals.goal_7_cut_to_full
