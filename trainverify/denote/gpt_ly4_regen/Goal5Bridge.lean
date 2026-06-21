/- goal_5 桥 (非 base case, prereqs=[goal_2,goal_3,goal_4,goal_257])。
   算子: FW_layernorm。输入 1141-1144 = goal_257 输出; 568/569 = init weight。
   复用 Goal4Bridge 齿轮 + goal_2/3/4/257_intermediate。 -/
import denote.gpt_ly4_regen.Goal4Bridge
import denote.gpt_ly4_regen.Goal257Bridge
import denote.gpt_ly4_regen.Goal_5

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 pm_goal_5 算 1145-1148 (各 rank 独立 layernorm) ==========
theorem denote_pm_goal_5_1145 (s : Store) :
    denoteGraph pm_goal_5 s 1145 = fw_layernorm (s 1141) (s 568) (s 569) := by
  simp only [pm_goal_5, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]

theorem denote_pm_goal_5_1146 (s : Store) :
    denoteGraph pm_goal_5 s 1146 = fw_layernorm (s 1142) (s 568) (s 569) := by
  simp only [pm_goal_5, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]; congr 1

theorem denote_pm_goal_5_1147 (s : Store) :
    denoteGraph pm_goal_5 s 1147 = fw_layernorm (s 1143) (s 568) (s 569) := by
  simp only [pm_goal_5, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]; congr 1

theorem denote_pm_goal_5_1148 (s : Store) :
    denoteGraph pm_goal_5 s 1148 = fw_layernorm (s 1144) (s 568) (s 569) := by
  simp only [pm_goal_5, denoteGraph, List.foldl]
  rw [applyNode_fw_layernorm_out]; congr 1

-- ========== 迷你图 sm_goal_5 算 570 ==========
theorem denote_sm_goal_5_570 (s : Store) :
    denoteGraph sm_goal_5 s 570 = fw_layernorm (s 903) (s 568) (s 569) := by
  simp only [sm_goal_5, denoteGraph, List.foldl]
  rw [applyNode_fw_layernorm_out]

-- ========== SM self-frame: full 算 570 (node 4 layernorm, ins=[903,568,569]) ==========
theorem sm_frame_570_self (initSM : Store) :
    denoteGraph sm initSM 570 = denoteGraph sm_goal_5 (denoteGraph sm initSM) 570 := by
  rw [denote_sm_goal_5_570]
  rw [sm_val initSM 4 570 (by native_decide) (by native_decide)]
  rw [show sm.nodes[4]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [903, 568, 569], outs := [570] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [sm_prefix_eq initSM 4 903 (by native_decide),
      sm_prefix_eq initSM 4 568 (by native_decide),
      sm_prefix_eq initSM 4 569 (by native_decide)]

-- ========== PM self-frame: 1145-1148 (node 33-36 layernorm) ==========
theorem pm_frame_1145_self (initPM : Store) :
    denoteGraph pm initPM 1145 = denoteGraph pm_goal_5 (denoteGraph pm initPM) 1145 := by
  rw [denote_pm_goal_5_1145]
  rw [pm_val initPM 33 1145 (by native_decide) (by native_decide)]
  rw [show pm.nodes[33]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [1141, 568, 569], outs := [1145] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 33 1141 (by native_decide),
      pm_prefix_eq initPM 33 568 (by native_decide),
      pm_prefix_eq initPM 33 569 (by native_decide)]

theorem pm_frame_1146_self (initPM : Store) :
    denoteGraph pm initPM 1146 = denoteGraph pm_goal_5 (denoteGraph pm initPM) 1146 := by
  rw [denote_pm_goal_5_1146]
  rw [pm_val initPM 34 1146 (by native_decide) (by native_decide)]
  rw [show pm.nodes[34]'(by native_decide)
      = { rank := 1, op := "OpName.FW_layernorm", ins := [1142, 568, 569], outs := [1146] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 34 1142 (by native_decide),
      pm_prefix_eq initPM 34 568 (by native_decide),
      pm_prefix_eq initPM 34 569 (by native_decide)]

theorem pm_frame_1147_self (initPM : Store) :
    denoteGraph pm initPM 1147 = denoteGraph pm_goal_5 (denoteGraph pm initPM) 1147 := by
  rw [denote_pm_goal_5_1147]
  rw [pm_val initPM 35 1147 (by native_decide) (by native_decide)]
  rw [show pm.nodes[35]'(by native_decide)
      = { rank := 2, op := "OpName.FW_layernorm", ins := [1143, 568, 569], outs := [1147] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 35 1143 (by native_decide),
      pm_prefix_eq initPM 35 568 (by native_decide),
      pm_prefix_eq initPM 35 569 (by native_decide)]

theorem pm_frame_1148_self (initPM : Store) :
    denoteGraph pm initPM 1148 = denoteGraph pm_goal_5 (denoteGraph pm initPM) 1148 := by
  rw [denote_pm_goal_5_1148]
  rw [pm_val initPM 36 1148 (by native_decide) (by native_decide)]
  rw [show pm.nodes[36]'(by native_decide)
      = { rank := 3, op := "OpName.FW_layernorm", ins := [1144, 568, 569], outs := [1148] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 36 1144 (by native_decide),
      pm_prefix_eq initPM 36 568 (by native_decide),
      pm_prefix_eq initPM 36 569 (by native_decide)]

-- ========== 总装: goal_5_cut_to_full ==========
theorem goal_5_cut_to_full (h : goal_5_stmt_cut) : goal_5_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg257 hinitC
  have hnr : pm_goal_5.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_5.numRanks goal_5_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_5_cut_initGoals, goal_5_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg257, List.forall_mem_nil _⟩
  -- 903 + 1141-1144 shape 从 hg257; 568/569 shape 从 initGoals (initGoal_568/569)
  have h903_smsh : (Ssm 903).shape = [1, 8, 32] := by
    have h := hg257.1; simp only [goal_257] at h; exact h
  have h4 : (Spm 1141).shape = [1,2,32] ∧ (Spm 1142).shape = [1,2,32] ∧
           (Spm 1143).shape = [1,2,32] ∧ (Spm 1144).shape = [1,2,32] := by
    have h := hg257.2.1
    simp only [goal_257, List.map, List.cons.injEq, and_true, and_assoc] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1141sh, h1142sh, h1143sh, h1144sh⟩ := h4
  -- 568/569: 从 initGoals_preserved 抽 (initGoal_568/569 在 computed store hold)
  have h568_sm : (Ssm 568).shape = [32] := by
    have hg := hinitC initGoal_568 (by simp only [initGoals]; decide)
    have h := hg.1; simp only [initGoal_568] at h; exact h
  have h569_sm : (Ssm 569).shape = [32] := by
    have hg := hinitC initGoal_569 (by simp only [initGoals]; decide)
    have h := hg.1; simp only [initGoal_569] at h; exact h
  have h568_pm : (Spm 568).shape = [32] := by
    have hg := hinitC initGoal_568 (by simp only [initGoals]; decide)
    have h := hg.2.1; simp only [initGoal_568, List.map, List.cons.injEq] at h; exact h.1
  have h569_pm : (Spm 569).shape = [32] := by
    have hg := hinitC initGoal_569 (by simp only [initGoals]; decide)
    have h := hg.2.1; simp only [initGoal_569, List.map, List.cons.injEq] at h; exact h.1
  have hSM5 : StoreShapesHold Ssm sm_goal_5InitEnv := by
    intro tid sh hsh
    rw [sm_goal_5InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_5InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h568_sm
    · exact h569_sm
    · exact h903_smsh
  have hPM5 : StoreShapesHold Spm pm_goal_5InitEnv := by
    intro tid sh hsh
    rw [pm_goal_5InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_5InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h568_pm
    · exact h569_pm
    · exact h1141sh
    · exact h1142sh
    · exact h1143sh
    · exact h1144sh
  have hcut := h Ssm Spm hSM5 hPM5 hInitCut
  have hsmf : Ssm 570 = denoteGraph sm_goal_5 Ssm 570 := by
    rw [hSsm]; exact sm_frame_570_self initSM
  have hpm1145 : Spm 1145 = denoteGraph pm_goal_5 Spm 1145 := by
    rw [hSpm]; exact pm_frame_1145_self initPM
  have hpm1146 : Spm 1146 = denoteGraph pm_goal_5 Spm 1146 := by
    rw [hSpm]; exact pm_frame_1146_self initPM
  have hpm1147 : Spm 1147 = denoteGraph pm_goal_5 Spm 1147 := by
    rw [hSpm]; exact pm_frame_1147_self initPM
  have hpm1148 : Spm 1148 = denoteGraph pm_goal_5 Spm 1148 := by
    rw [hSpm]; exact pm_frame_1148_self initPM
  rw [hnr] at hcut
  simp only [goal_5, List.map] at hcut ⊢
  rw [hsmf, hpm1145, hpm1146, hpm1147, hpm1148]
  exact hcut

-- ========== 导出 goal_5_intermediate ==========
theorem goal_5_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_5 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_5_stmt := goal_5_cut_to_full prove_goal_5_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
