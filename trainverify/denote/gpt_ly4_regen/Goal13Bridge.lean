/- goal_13 桥 (prereqs=[2,3,4,5,8,257,265])。SM=FW_view(576)→581; PM=4×FW_view(576)→581 (4 rank 都写同 tid, replicated 输出).
   576=goal_8 输出。无 weight, 无 collective。 -/
import denote.gpt_ly4_regen.Goal8Bridge
import denote.gpt_ly4_regen.Goal_13

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_13 算 581 ==========
theorem denote_sm_goal_13_581 (s : Store) :
    denoteGraph sm_goal_13 s 581 = fw_view [1, 8, 4, 8] (s 576) := by
  simp only [sm_goal_13, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_13 算 581 ==========
theorem denote_pm_goal_13_581 (s : Store) :
    denoteGraph pm_goal_13 s 581 = fw_view [1, 8, 4, 8] (s 576) := by
  simp only [pm_goal_13, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 576 (by decide),
      applyNode_skip _ _ _ 576 (by decide),
      applyNode_skip _ _ _ 576 (by decide)]

-- ========== goal_8 中间产物: 提供 (initSM 576).shape + reconstruct 等式 ==========
-- 直接复用 goal_8_intermediate

-- ========== SM self-frame: full sm 算 581 (node 11, FW_view) ==========
theorem sm_frame_581_self (initSM : Store) :
    denoteGraph sm initSM 581 = denoteGraph sm_goal_13 (denoteGraph sm initSM) 581 := by
  rw [denote_sm_goal_13_581]
  rw [sm_val initSM 11 581 (by native_decide) (by native_decide)]
  rw [show sm.nodes[11]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [576], outs := [581], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 11 576 (by native_decide)]

-- ========== PM self-frame: full pm 算 581 (4 rank 都写, 取最后 = node 68) ==========
theorem pm_frame_581_self (initPM : Store) :
    denoteGraph pm initPM 581 = fw_view [1, 8, 4, 8] (denoteGraph pm initPM 576) := by
  rw [pm_val initPM 68 581 (by native_decide) (by native_decide)]
  rw [show pm.nodes[68]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [576], outs := [581], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 68 576 (by native_decide)]

-- ========== 总装 ==========
theorem goal_13_cut_to_full (h : goal_13_stmt_cut) : goal_13_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg8 := goal_8_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg8 hg257 hg265 hinitC
  have hnr : pm_goal_13.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_13.numRanks goal_13_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_13_cut_initGoals, goal_13_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg8, hg257, hg265, List.forall_mem_nil _⟩
  -- 576 = goal_8.ts; (Ssm 576).shape = [1,8,32] (from hg8)
  have h576_smsh : (Ssm 576).shape = [1, 8, 32] := by
    have h := hg8.1; simp only [goal_8] at h; exact h
  have hSM13 : StoreShapesHold Ssm sm_goal_13InitEnv := by
    intro tid sh hsh
    rw [sm_goal_13InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_13InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h576_smsh
  have hPM13 : StoreShapesHold Spm pm_goal_13InitEnv := by
    intro tid sh hsh
    rw [pm_goal_13InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_13InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    -- pm 上 576 = goal_8.tps[0] = goal_8 单 tp, shape [1,8,32]
    have h := hg8.2.1; simp only [goal_8, List.map, List.cons.injEq, and_true] at h
    exact h
  have hcut := h Ssm Spm hSM13 hPM13 hInitCut
  have hsmf : Ssm 581 = denoteGraph sm_goal_13 Ssm 581 := by
    rw [hSsm]; exact sm_frame_581_self initSM
  have hpm581 : Spm 581 = denoteGraph pm_goal_13 Spm 581 := by
    rw [denote_pm_goal_13_581]
    rw [hSpm]; exact pm_frame_581_self initPM
  rw [hnr] at hcut
  simp only [goal_13, List.map] at hcut ⊢
  rw [hsmf, hpm581]
  exact hcut

theorem goal_13_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_13 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_13_stmt := goal_13_cut_to_full prove_goal_13_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals

