/- goal_259 桥 (非 base case, prereqs=[goal_2,goal_3,goal_4])。
   算子: SM=FW_multiref 第二输出(907); PM=FW_multiref 第二输出(1501..) 直接 = 输入(1117..)。
   比 goal_257 少 AllToAll 层。复用 Goal4Bridge 齿轮 + goal_2/3/4_intermediate。 -/
import denote.gpt_ly4_regen.Goal4Bridge
import denote.gpt_ly4_regen.Goal257Bridge
import denote.gpt_ly4_regen.Goal_259

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 pm_goal_259 算 1501-1504 (FW_multiref 第二输出 = s 1117..1120) ==========
theorem denote_pm_goal_259_1501 (s : Store) :
    denoteGraph pm_goal_259 s 1501 = s 1117 := by
  simp only [pm_goal_259, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1501 (by decide), applyNode_skip _ _ _ 1501 (by decide),
      applyNode_skip _ _ _ 1501 (by decide),
      applyNode_fw_multiref2_second_out_g259 _ _ 0 1117 3413 1501 (by decide)]

theorem denote_pm_goal_259_1502 (s : Store) :
    denoteGraph pm_goal_259 s 1502 = s 1118 := by
  simp only [pm_goal_259, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1502 (by decide), applyNode_skip _ _ _ 1502 (by decide),
      applyNode_fw_multiref2_second_out_g259 _ _ 1 1118 3419 1502 (by decide),
      applyNode_skip _ _ _ 1118 (by decide)]

theorem denote_pm_goal_259_1503 (s : Store) :
    denoteGraph pm_goal_259 s 1503 = s 1119 := by
  simp only [pm_goal_259, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1503 (by decide),
      applyNode_fw_multiref2_second_out_g259 _ _ 2 1119 3425 1503 (by decide),
      applyNode_skip _ _ _ 1119 (by decide), applyNode_skip _ _ _ 1119 (by decide)]

theorem denote_pm_goal_259_1504 (s : Store) :
    denoteGraph pm_goal_259 s 1504 = s 1120 := by
  simp only [pm_goal_259, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_g259 _ _ 3 1120 3431 1504 (by decide),
      applyNode_skip _ _ _ 1120 (by decide), applyNode_skip _ _ _ 1120 (by decide),
      applyNode_skip _ _ _ 1120 (by decide)]

-- ========== 迷你图 sm_goal_259 算 907 (FW_multiref 第二输出 = s 567) ==========
theorem denote_sm_goal_259_907 (s : Store) :
    denoteGraph sm_goal_259 s 907 = s 567 := by
  simp only [sm_goal_259, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_g259 _ _ 0 567 903 907 (by decide)]

-- ========== SM self-frame: full 算 907 (node 3 第二输出) ==========
theorem sm_frame_907_self (initSM : Store) :
    denoteGraph sm initSM 907 = denoteGraph sm_goal_259 (denoteGraph sm initSM) 907 := by
  rw [denote_sm_goal_259_907]
  rw [sm_val initSM 3 907 (by native_decide) (by native_decide)]
  rw [show sm.nodes[3]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [567], outs := [903, 907], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g259 _ _ 0 567 903 907 (by decide)]
  rw [sm_prefix_eq initSM 3 567 (by native_decide)]

-- ========== PM self-frame: 1501-1504 (node 25-28 第二输出) ==========
theorem pm_frame_1501_self (initPM : Store) :
    denoteGraph pm initPM 1501 = denoteGraph pm_goal_259 (denoteGraph pm initPM) 1501 := by
  rw [denote_pm_goal_259_1501]
  rw [pm_val initPM 25 1501 (by native_decide) (by native_decide)]
  rw [show pm.nodes[25]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1117], outs := [3413, 1501], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g259 _ _ 0 1117 3413 1501 (by decide)]
  rw [pm_prefix_eq initPM 25 1117 (by native_decide)]

theorem pm_frame_1502_self (initPM : Store) :
    denoteGraph pm initPM 1502 = denoteGraph pm_goal_259 (denoteGraph pm initPM) 1502 := by
  rw [denote_pm_goal_259_1502]
  rw [pm_val initPM 26 1502 (by native_decide) (by native_decide)]
  rw [show pm.nodes[26]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1118], outs := [3419, 1502], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g259 _ _ 1 1118 3419 1502 (by decide)]
  rw [pm_prefix_eq initPM 26 1118 (by native_decide)]

theorem pm_frame_1503_self (initPM : Store) :
    denoteGraph pm initPM 1503 = denoteGraph pm_goal_259 (denoteGraph pm initPM) 1503 := by
  rw [denote_pm_goal_259_1503]
  rw [pm_val initPM 27 1503 (by native_decide) (by native_decide)]
  rw [show pm.nodes[27]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1119], outs := [3425, 1503], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g259 _ _ 2 1119 3425 1503 (by decide)]
  rw [pm_prefix_eq initPM 27 1119 (by native_decide)]

theorem pm_frame_1504_self (initPM : Store) :
    denoteGraph pm initPM 1504 = denoteGraph pm_goal_259 (denoteGraph pm initPM) 1504 := by
  rw [denote_pm_goal_259_1504]
  rw [pm_val initPM 28 1504 (by native_decide) (by native_decide)]
  rw [show pm.nodes[28]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1120], outs := [3431, 1504], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g259 _ _ 3 1120 3431 1504 (by decide)]
  rw [pm_prefix_eq initPM 28 1120 (by native_decide)]

-- ========== 总装: goal_259_cut_to_full ==========
theorem goal_259_cut_to_full (h : goal_259_stmt_cut) : goal_259_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 : InitGoalHolds pm.numRanks goal_2 Ssm Spm := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 : InitGoalHolds pm.numRanks goal_3 Ssm Spm := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 : InitGoalHolds pm.numRanks goal_4 Ssm Spm := goal_4_intermediate initSM initPM hSM hPM hInit
  have hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_259.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_259.numRanks goal_259_cut_initGoals Ssm Spm := by
    rw [hnr]
    intro g hg
    simp only [goal_259_cut_initGoals, goal_259_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
  -- shape 全从 hg4 抽 (567=goal_4.ts; 1117-1120=goal_4.tps)
  have h567_smsh : (Ssm 567).shape = [1, 8, 32] := by
    have h := hg4.1; simp only [goal_4] at h; exact h
  have h4 : (Spm 1117).shape = [1,8,8] ∧ (Spm 1118).shape = [1,8,8] ∧
           (Spm 1119).shape = [1,8,8] ∧ (Spm 1120).shape = [1,8,8] := by
    have h := hg4.2.1
    simp only [goal_4, List.map, List.cons.injEq, and_true, and_assoc] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1117sh, h1118sh, h1119sh, h1120sh⟩ := h4
  have hSM259 : StoreShapesHold Ssm sm_goal_259InitEnv := by
    intro tid sh hsh
    rw [sm_goal_259InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_259InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h567_smsh
  have hPM259 : StoreShapesHold Spm pm_goal_259InitEnv := by
    intro tid sh hsh
    rw [pm_goal_259InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_259InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1117sh
    · exact h1118sh
    · exact h1119sh
    · exact h1120sh
  have hcut := h Ssm Spm hSM259 hPM259 hInitCut
  have hsmf : Ssm 907 = denoteGraph sm_goal_259 Ssm 907 := by
    rw [hSsm]; exact sm_frame_907_self initSM
  have hpm1501 : Spm 1501 = denoteGraph pm_goal_259 Spm 1501 := by
    rw [hSpm]; exact pm_frame_1501_self initPM
  have hpm1502 : Spm 1502 = denoteGraph pm_goal_259 Spm 1502 := by
    rw [hSpm]; exact pm_frame_1502_self initPM
  have hpm1503 : Spm 1503 = denoteGraph pm_goal_259 Spm 1503 := by
    rw [hSpm]; exact pm_frame_1503_self initPM
  have hpm1504 : Spm 1504 = denoteGraph pm_goal_259 Spm 1504 := by
    rw [hSpm]; exact pm_frame_1504_self initPM
  rw [hnr] at hcut
  simp only [goal_259, List.map] at hcut ⊢
  rw [hsmf, hpm1501, hpm1502, hpm1503, hpm1504]
  exact hcut

theorem goal_259_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_259 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_259_stmt := goal_259_cut_to_full prove_goal_259_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_259] using this

end TrainVerify.Denote.GeneratedGoals
