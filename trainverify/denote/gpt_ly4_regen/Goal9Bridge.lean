/- goal_9 桥 (prereqs=[2,3,4,5,6,257,261])。SM=FW_view(572)→577; PM=4×FW_view(572)→577 (4 rank 都写同 tid, replicated 输出).
   572=goal_6 输出。无 weight, 无 collective。 -/
import denote.gpt_ly4_regen.Goal6Bridge
import denote.gpt_ly4_regen.Goal_9

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_9 算 577 ==========
theorem denote_sm_goal_9_577 (s : Store) :
    denoteGraph sm_goal_9 s 577 = fw_view [1, 8, 4, 8] (s 572) := by
  simp only [sm_goal_9, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_9 算 577 ==========
theorem denote_pm_goal_9_577 (s : Store) :
    denoteGraph pm_goal_9 s 577 = fw_view [1, 8, 4, 8] (s 572) := by
  simp only [pm_goal_9, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 572 (by decide),
      applyNode_skip _ _ _ 572 (by decide),
      applyNode_skip _ _ _ 572 (by decide)]

-- ========== goal_6 中间产物: 提供 (initSM 572).shape + reconstruct 等式 ==========
-- 直接复用 goal_6_intermediate

-- ========== SM self-frame: full sm 算 577 (node 9, FW_view) ==========
theorem sm_frame_577_self (initSM : Store) :
    denoteGraph sm initSM 577 = denoteGraph sm_goal_9 (denoteGraph sm initSM) 577 := by
  rw [denote_sm_goal_9_577]
  rw [sm_val initSM 9 577 (by native_decide) (by native_decide)]
  rw [show sm.nodes[9]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [572], outs := [577], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 9 572 (by native_decide)]

-- ========== PM self-frame: full pm 算 577 (4 rank 都写, 取最后 = node 60) ==========
theorem pm_frame_577_self (initPM : Store) :
    denoteGraph pm initPM 577 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 572) := by
  rw [pm_val initPM 60 577 (by native_decide) (by native_decide)]
  rw [show pm.nodes[60]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [572], outs := [577], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 60 572 (by native_decide)]

-- ========== 总装 ==========
theorem goal_9_cut_to_full (h : goal_9_stmt_cut) : goal_9_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg6 := goal_6_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_9.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_9.numRanks goal_9_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_9_cut_initGoals, goal_9_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg6
      · exact hg257
      · exact hg261
  -- 572 = goal_6.ts; (Ssm 572).shape = [1,8,32] (from hg6)
  have h572_smsh : (Ssm 572).shape = [1, 8, 32] := by
    have h := hg6.1; simp only [goal_6] at h; exact h
  have hSM9 : StoreShapesHold Ssm sm_goal_9InitEnv := by
    intro tid sh hsh
    rw [sm_goal_9InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_9InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h572_smsh
  have hPM9 : StoreShapesHold Spm pm_goal_9InitEnv := by
    intro tid sh hsh
    rw [pm_goal_9InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_9InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    -- pm 上 572 = goal_6.tps[0] = goal_6 单 tp, shape [1,8,32]
    have h := hg6.2.1; simp only [goal_6, List.map, List.cons.injEq, and_true] at h
    exact h
  have hcut := h Ssm Spm hSM9 hPM9 hInitCut
  have hsmf : Ssm 577 = denoteGraph sm_goal_9 Ssm 577 := by
    rw [hSsm]; exact sm_frame_577_self initSM
  have hpm577 : Spm 577 = denoteGraph pm_goal_9 Spm 577 := by
    rw [denote_pm_goal_9_577]
    rw [hSpm]; exact pm_frame_577_self initPM
  rw [hnr] at hcut
  simp only [goal_9, List.map] at hcut ⊢
  rw [hsmf, hpm577]
  exact hcut

theorem goal_9_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_9 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_9_stmt := goal_9_cut_to_full prove_goal_9_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_9] using this

end TrainVerify.Denote.GeneratedGoals

