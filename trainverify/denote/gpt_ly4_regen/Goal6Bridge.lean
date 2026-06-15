/- goal_6 桥 (prereqs=[2,3,4,5,257,261])。SM=FW_linear(918,571)→572; PM=4×FW_linear(1173-1176,571)→1177-1180 →AllGather→572(单tp)。
   输入 918/1173-1176 = goal_261 输出; 571 = weight init。套 265 AllGather-in-PM 模板 + FW_linear。 -/
import denote.gpt_ly4_regen.Goal261Bridge
import denote.gpt_ly4_regen.Goal_6

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_6 算 572 (FW_linear) ==========
theorem denote_sm_goal_6_572 (s : Store) :
    denoteGraph sm_goal_6 s 572 = fw_linear (s 918) (s 571) := by
  simp only [sm_goal_6, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_6 算 572 (4×FW_linear → AllGather) ==========
theorem denote_pm_goal_6_572 (s : Store) :
    denoteGraph pm_goal_6 s 572 = allGatherPrimDimN 1 4 0
      [fw_linear (s 1173) (s 571), fw_linear (s 1174) (s 571),
       fw_linear (s 1175) (s 571), fw_linear (s 1176) (s 571)] := by
  simp only [pm_goal_6, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out]
  simp only [List.map]
  set_option maxHeartbeats 800000 in congr 1

-- ========== SM self-frame: full 算 572 (node 6 FW_linear) ==========
theorem sm_frame_572_self (initSM : Store) :
    denoteGraph sm initSM 572 = denoteGraph sm_goal_6 (denoteGraph sm initSM) 572 := by
  rw [denote_sm_goal_6_572]
  rw [sm_val initSM 6 572 (by native_decide) (by native_decide)]
  rw [show sm.nodes[6]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 6 918 (by native_decide),
      sm_prefix_eq initSM 6 571 (by native_decide)]

-- ========== full pm 算 FW_linear 输出 1177-1180 (node 41/43/45/48) = fw_linear(Spm 1173.., Spm 571) ==========
theorem pm_full_1177 (initPM : Store) :
    denoteGraph pm initPM 1177 = fw_linear (denoteGraph pm initPM 1173) (denoteGraph pm initPM 571) := by
  rw [pm_val initPM 41 1177 (by native_decide) (by native_decide)]
  rw [show pm.nodes[41]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 41 1173 (by native_decide),
      pm_prefix_eq initPM 41 571 (by native_decide)]

theorem pm_full_1178 (initPM : Store) :
    denoteGraph pm initPM 1178 = fw_linear (denoteGraph pm initPM 1174) (denoteGraph pm initPM 571) := by
  rw [pm_val initPM 43 1178 (by native_decide) (by native_decide)]
  rw [show pm.nodes[43]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 43 1174 (by native_decide),
      pm_prefix_eq initPM 43 571 (by native_decide)]

theorem pm_full_1179 (initPM : Store) :
    denoteGraph pm initPM 1179 = fw_linear (denoteGraph pm initPM 1175) (denoteGraph pm initPM 571) := by
  rw [pm_val initPM 45 1179 (by native_decide) (by native_decide)]
  rw [show pm.nodes[45]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 45 1175 (by native_decide),
      pm_prefix_eq initPM 45 571 (by native_decide)]

theorem pm_full_1180 (initPM : Store) :
    denoteGraph pm initPM 1180 = fw_linear (denoteGraph pm initPM 1176) (denoteGraph pm initPM 571) := by
  rw [pm_val initPM 48 1180 (by native_decide) (by native_decide)]
  rw [show pm.nodes[48]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 48 1176 (by native_decide),
      pm_prefix_eq initPM 48 571 (by native_decide)]

-- ========== PM self-frame: 572 (AllGather node 54, ins=computed range) ==========
theorem pm_frame_572_self (initPM : Store) :
    denoteGraph pm initPM 572
      = allGatherPrimDimN 1 4 0
          [fw_linear (denoteGraph pm initPM 1173) (denoteGraph pm initPM 571),
           fw_linear (denoteGraph pm initPM 1174) (denoteGraph pm initPM 571),
           fw_linear (denoteGraph pm initPM 1175) (denoteGraph pm initPM 571),
           fw_linear (denoteGraph pm initPM 1176) (denoteGraph pm initPM 571)] := by
  rw [pm_val initPM 54 572 (by native_decide) (by native_decide)]
  rw [show pm.nodes[54]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 1177 + r)), outs := [572], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  -- take54 store 上 1177-1180 = 全图 (pm_prefix_eq 54) = fw_linear(...)
  rw [pm_prefix_eq initPM 54 1177 (by native_decide),
      pm_prefix_eq initPM 54 1178 (by native_decide),
      pm_prefix_eq initPM 54 1179 (by native_decide),
      pm_prefix_eq initPM 54 1180 (by native_decide)]
  rw [pm_full_1177, pm_full_1178, pm_full_1179, pm_full_1180]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_6_cut_to_full (h : goal_6_stmt_cut) : goal_6_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_6.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_6.numRanks goal_6_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_6_cut_initGoals, goal_6_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg257
      · exact hg261
  -- 918 = goal_261.ts; 1173-1176 = goal_261.tps; 571 = weight init
  have h918_smsh : (Ssm 918).shape = [1, 8, 32] := by
    have h := hg261.1; simp only [goal_261] at h; exact h
  have h4 : (Spm 1173).shape = [1,2,32] ∧ (Spm 1174).shape = [1,2,32] ∧
           (Spm 1175).shape = [1,2,32] ∧ (Spm 1176).shape = [1,2,32] := by
    have h := hg261.2.1
    simp only [goal_261, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1173sh, h1174sh, h1175sh, h1176sh⟩ := h4
  have h571_sm : (Ssm 571).shape = [32, 32] := by
    have hg := hinitC initGoal_571 (by simp only [initGoals]; decide)
    have h := hg.1; simp only [initGoal_571] at h; exact h
  have h571_pm : (Spm 571).shape = [32, 32] := by
    have hg := hinitC initGoal_571 (by simp only [initGoals]; decide)
    have h := hg.2.1; simp only [initGoal_571, List.map, List.cons.injEq] at h; exact h.1
  have hSM6 : StoreShapesHold Ssm sm_goal_6InitEnv := by
    intro tid sh hsh
    rw [sm_goal_6InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_6InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h571_sm
    · exact h918_smsh
  have hPM6 : StoreShapesHold Spm pm_goal_6InitEnv := by
    intro tid sh hsh
    rw [pm_goal_6InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_6InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h571_pm
    · exact h1173sh
    · exact h1174sh
    · exact h1175sh
    · exact h1176sh
  have hcut := h Ssm Spm hSM6 hPM6 hInitCut
  have hsmf : Ssm 572 = denoteGraph sm_goal_6 Ssm 572 := by
    rw [hSsm]; exact sm_frame_572_self initSM
  have hpm572 : Spm 572 = denoteGraph pm_goal_6 Spm 572 := by
    rw [denote_pm_goal_6_572]
    rw [hSpm]; exact pm_frame_572_self initPM
  rw [hnr] at hcut
  simp only [goal_6, List.map] at hcut ⊢
  rw [hsmf, hpm572]
  exact hcut

theorem goal_6_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_6 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_6_stmt := goal_6_cut_to_full prove_goal_6_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_6] using this

end TrainVerify.Denote.GeneratedGoals
