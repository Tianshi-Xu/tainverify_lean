/- goal_263 桥 (prereqs=[2,3,4,5,257])。FW_multiref 3输出取第2输出(922/1201..)。
   输入 570/1145-1148 = goal_5 输出。 -/
import denote.gpt_ly4_regen.Goal5Bridge
import denote.gpt_ly4_regen.Goal_263

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 pm_goal_263 算 1201-1204 (multiref 第2输出 = s 1145..1148) ==========
theorem denote_pm_goal_263_1201 (s : Store) :
    denoteGraph pm_goal_263 s 1201 = s 1145 := by
  simp only [pm_goal_263, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1176 1204 3463 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1175 1203 3455 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1174 1202 3447 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide)]

theorem denote_pm_goal_263_1202 (s : Store) :
    denoteGraph pm_goal_263 s 1202 = s 1146 := by
  simp only [pm_goal_263, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1176 1204 3463 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1175 1203 3455 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1173 1201 3439 _ (by decide) (by decide) (by decide)]

theorem denote_pm_goal_263_1203 (s : Store) :
    denoteGraph pm_goal_263 s 1203 = s 1147 := by
  simp only [pm_goal_263, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1176 1204 3463 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1174 1202 3447 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1173 1201 3439 _ (by decide) (by decide) (by decide)]

theorem denote_pm_goal_263_1204 (s : Store) :
    denoteGraph pm_goal_263 s 1204 = s 1148 := by
  simp only [pm_goal_263, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1175 1203 3455 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1174 1202 3447 _ (by decide) (by decide) (by decide),
      applyNode_fw_multiref3_passthrough_g263 _ _ _ _ 1173 1201 3439 _ (by decide) (by decide) (by decide)]

-- ========== 迷你图 sm_goal_263 算 922 ==========
theorem denote_sm_goal_263_922 (s : Store) :
    denoteGraph sm_goal_263 s 922 = s 570 := by
  simp only [sm_goal_263, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide)]

-- ========== SM self-frame: full 算 922 (node 5) ==========
theorem sm_frame_922_self (initSM : Store) :
    denoteGraph sm initSM 922 = denoteGraph sm_goal_263 (denoteGraph sm initSM) 922 := by
  rw [denote_sm_goal_263_922]
  rw [sm_val initSM 5 922 (by native_decide) (by native_decide)]
  rw [show sm.nodes[5]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [570], outs := [918, 922, 926], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide)]
  rw [sm_prefix_eq initSM 5 570 (by native_decide)]

-- ========== PM self-frame: 1201-1204 (node 37-40) ==========
theorem pm_frame_1201_self (initPM : Store) :
    denoteGraph pm initPM 1201 = denoteGraph pm_goal_263 (denoteGraph pm initPM) 1201 := by
  rw [denote_pm_goal_263_1201]
  rw [pm_val initPM 37 1201 (by native_decide) (by native_decide)]
  rw [show pm.nodes[37]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1145], outs := [1173, 1201, 3439], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide)]
  rw [pm_prefix_eq initPM 37 1145 (by native_decide)]

theorem pm_frame_1202_self (initPM : Store) :
    denoteGraph pm initPM 1202 = denoteGraph pm_goal_263 (denoteGraph pm initPM) 1202 := by
  rw [denote_pm_goal_263_1202]
  rw [pm_val initPM 38 1202 (by native_decide) (by native_decide)]
  rw [show pm.nodes[38]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1146], outs := [1174, 1202, 3447], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide)]
  rw [pm_prefix_eq initPM 38 1146 (by native_decide)]

theorem pm_frame_1203_self (initPM : Store) :
    denoteGraph pm initPM 1203 = denoteGraph pm_goal_263 (denoteGraph pm initPM) 1203 := by
  rw [denote_pm_goal_263_1203]
  rw [pm_val initPM 39 1203 (by native_decide) (by native_decide)]
  rw [show pm.nodes[39]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1147], outs := [1175, 1203, 3455], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide)]
  rw [pm_prefix_eq initPM 39 1147 (by native_decide)]

theorem pm_frame_1204_self (initPM : Store) :
    denoteGraph pm initPM 1204 = denoteGraph pm_goal_263 (denoteGraph pm initPM) 1204 := by
  rw [denote_pm_goal_263_1204]
  rw [pm_val initPM 40 1204 (by native_decide) (by native_decide)]
  rw [show pm.nodes[40]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1148], outs := [1176, 1204, 3463], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g263 _ _ _ _ _ _ _ (by decide)]
  rw [pm_prefix_eq initPM 40 1148 (by native_decide)]

-- ========== 总装 ==========
theorem goal_263_cut_to_full (h : goal_263_stmt_cut) : goal_263_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_263.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_263.numRanks goal_263_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_263_cut_initGoals, goal_263_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg257
  have h570_smsh : (Ssm 570).shape = [1, 8, 32] := by
    have h := hg5.1; simp only [goal_5] at h; exact h
  have h4 : (Spm 1145).shape = [1,2,32] ∧ (Spm 1146).shape = [1,2,32] ∧
           (Spm 1147).shape = [1,2,32] ∧ (Spm 1148).shape = [1,2,32] := by
    have h := hg5.2.1
    simp only [goal_5, List.map, List.cons.injEq, and_true, and_assoc] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1145sh, h1146sh, h1147sh, h1148sh⟩ := h4
  have hSM263 : StoreShapesHold Ssm sm_goal_263InitEnv := by
    intro tid sh hsh
    rw [sm_goal_263InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_263InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h570_smsh
  have hPM263 : StoreShapesHold Spm pm_goal_263InitEnv := by
    intro tid sh hsh
    rw [pm_goal_263InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_263InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1145sh
    · exact h1146sh
    · exact h1147sh
    · exact h1148sh
  have hcut := h Ssm Spm hSM263 hPM263 hInitCut
  have hsmf : Ssm 922 = denoteGraph sm_goal_263 Ssm 922 := by
    rw [hSsm]; exact sm_frame_922_self initSM
  have hpm1201 : Spm 1201 = denoteGraph pm_goal_263 Spm 1201 := by
    rw [hSpm]; exact pm_frame_1201_self initPM
  have hpm1202 : Spm 1202 = denoteGraph pm_goal_263 Spm 1202 := by
    rw [hSpm]; exact pm_frame_1202_self initPM
  have hpm1203 : Spm 1203 = denoteGraph pm_goal_263 Spm 1203 := by
    rw [hSpm]; exact pm_frame_1203_self initPM
  have hpm1204 : Spm 1204 = denoteGraph pm_goal_263 Spm 1204 := by
    rw [hSpm]; exact pm_frame_1204_self initPM
  rw [hnr] at hcut
  simp only [goal_263, List.map] at hcut ⊢
  rw [hsmf, hpm1201, hpm1202, hpm1203, hpm1204]
  exact hcut

end TrainVerify.Denote.GeneratedGoals
