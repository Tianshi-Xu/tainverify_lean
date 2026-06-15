/- goal_11 桥 (prereqs=[2,3,4,5,7,257,263])。SM=FW_view(574)→579; PM=4×FW_view(574)→579 (4 rank 都写同 tid, replicated 输出).
   574=goal_7 输出。无 weight, 无 collective。 -/
import denote.gpt_ly4_regen.Goal7Bridge
import denote.gpt_ly4_regen.Goal_11

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_11 算 579 ==========
theorem denote_sm_goal_11_579 (s : Store) :
    denoteGraph sm_goal_11 s 579 = fw_view [1, 8, 4, 8] (s 574) := by
  simp only [sm_goal_11, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_11 算 579 ==========
theorem denote_pm_goal_11_579 (s : Store) :
    denoteGraph pm_goal_11 s 579 = fw_view [1, 8, 4, 8] (s 574) := by
  simp only [pm_goal_11, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 574 (by decide),
      applyNode_skip _ _ _ 574 (by decide),
      applyNode_skip _ _ _ 574 (by decide)]

-- ========== SM self-frame: full sm 算 579 (node 10, FW_view) ==========
theorem sm_frame_579_self (initSM : Store) :
    denoteGraph sm initSM 579 = denoteGraph sm_goal_11 (denoteGraph sm initSM) 579 := by
  rw [denote_sm_goal_11_579]
  rw [sm_val initSM 10 579 (by native_decide) (by native_decide)]
  rw [show sm.nodes[10]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [574], outs := [579], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 10 574 (by native_decide)]

-- ========== PM self-frame: full pm 算 579 (4 rank 都写, 取最后 = node 64) ==========
theorem pm_frame_579_self (initPM : Store) :
    denoteGraph pm initPM 579 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 574) := by
  rw [pm_val initPM 64 579 (by native_decide) (by native_decide)]
  rw [show pm.nodes[64]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [574], outs := [579], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 64 574 (by native_decide)]

-- ========== 总装 ==========
theorem goal_11_cut_to_full (h : goal_11_stmt_cut) : goal_11_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg7 := goal_7_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_11.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_11.numRanks goal_11_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_11_cut_initGoals, goal_11_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg7
      · exact hg257
      · exact hg263
  -- 574 = goal_7.ts; (Ssm 574).shape = [1,8,32] (from hg7)
  have h574_smsh : (Ssm 574).shape = [1, 8, 32] := by
    have h := hg7.1; simp only [goal_7] at h; exact h
  have hSM11 : StoreShapesHold Ssm sm_goal_11InitEnv := by
    intro tid sh hsh
    rw [sm_goal_11InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_11InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h574_smsh
  have hPM11 : StoreShapesHold Spm pm_goal_11InitEnv := by
    intro tid sh hsh
    rw [pm_goal_11InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_11InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    -- pm 上 574 = goal_7.tps[0] = goal_7 单 tp, shape [1,8,32]
    have h := hg7.2.1; simp only [goal_7, List.map, List.cons.injEq, and_true] at h
    exact h
  have hcut := h Ssm Spm hSM11 hPM11 hInitCut
  have hsmf : Ssm 579 = denoteGraph sm_goal_11 Ssm 579 := by
    rw [hSsm]; exact sm_frame_579_self initSM
  have hpm579 : Spm 579 = denoteGraph pm_goal_11 Spm 579 := by
    rw [denote_pm_goal_11_579]
    rw [hSpm]; exact pm_frame_579_self initPM
  rw [hnr] at hcut
  simp only [goal_11, List.map] at hcut ⊢
  rw [hsmf, hpm579]
  exact hcut

end TrainVerify.Denote.GeneratedGoals

