/- goal_261 桥 (prereqs=[2,3,4,5,257])。算子: FW_multiref 3输出取第1输出(918/1173..)。
   输入 570(sm)/1145-1148(pm) = goal_5 输出。复用齿轮 + goal_5_intermediate。 -/
import denote.gpt_ly4_regen.Goal5Bridge
import denote.gpt_ly4_regen.Goal_261

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 pm_goal_261 算 1173-1176 (multiref 第1输出 = s 1145..1148) ==========
theorem denote_pm_goal_261_1173 (s : Store) :
    denoteGraph pm_goal_261 s 1173 = s 1145 := by
  simp only [pm_goal_261, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1173 : Tid) ∉ ([1176, 1204, 3463] : List Tid)),
      applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1173 : Tid) ∉ ([1175, 1203, 3455] : List Tid)),
      applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1173 : Tid) ∉ ([1174, 1202, 3447] : List Tid))]
  exact applyNode_fw_multiref_first_out_g261 _ _ 0 3 1145 1173 [1201, 3439] (by decide)

theorem denote_pm_goal_261_1174 (s : Store) :
    denoteGraph pm_goal_261 s 1174 = s 1146 := by
  simp only [pm_goal_261, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1174 : Tid) ∉ ([1176, 1204, 3463] : List Tid)),
      applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1174 : Tid) ∉ ([1175, 1203, 3455] : List Tid))]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 1 3 1146 1174 [1202, 3447] (by decide)]
  exact applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1146 : Tid) ∉ ([1173, 1201, 3439] : List Tid))

theorem denote_pm_goal_261_1175 (s : Store) :
    denoteGraph pm_goal_261 s 1175 = s 1147 := by
  simp only [pm_goal_261, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1175 : Tid) ∉ ([1176, 1204, 3463] : List Tid))]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 2 3 1147 1175 [1203, 3455] (by decide)]
  rw [applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1147 : Tid) ∉ ([1174, 1202, 3447] : List Tid))]
  exact applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1147 : Tid) ∉ ([1173, 1201, 3439] : List Tid))

theorem denote_pm_goal_261_1176 (s : Store) :
    denoteGraph pm_goal_261 s 1176 = s 1148 := by
  simp only [pm_goal_261, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 3 3 1148 1176 [1204, 3463] (by decide)]
  rw [applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1148 : Tid) ∉ ([1175, 1203, 3455] : List Tid))]
  rw [applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1148 : Tid) ∉ ([1174, 1202, 3447] : List Tid))]
  exact applyNode_eq_of_not_mem_outs _ _ _ _ (by decide : (1148 : Tid) ∉ ([1173, 1201, 3439] : List Tid))

-- ========== 迷你图 sm_goal_261 算 918 (multiref 第1输出 = s 570) ==========
theorem denote_sm_goal_261_918 (s : Store) :
    denoteGraph sm_goal_261 s 918 = s 570 := by
  simp only [sm_goal_261, denoteGraph, List.foldl]
  exact applyNode_fw_multiref_first_out_g261 _ _ 0 3 570 918 [922, 926] (by decide)

-- ========== SM self-frame: full 算 918 (node 5) ==========
theorem sm_frame_918_self (initSM : Store) :
    denoteGraph sm initSM 918 = denoteGraph sm_goal_261 (denoteGraph sm initSM) 918 := by
  rw [denote_sm_goal_261_918]
  rw [sm_val initSM 5 918 (by native_decide) (by native_decide)]
  rw [show sm.nodes[5]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [570], outs := [918, 922, 926], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 0 3 570 918 [922, 926] (by decide)]
  rw [sm_prefix_eq initSM 5 570 (by native_decide)]

-- ========== PM self-frame: 1173-1176 (node 37-40) ==========
theorem pm_frame_1173_self (initPM : Store) :
    denoteGraph pm initPM 1173 = denoteGraph pm_goal_261 (denoteGraph pm initPM) 1173 := by
  rw [denote_pm_goal_261_1173]
  rw [pm_val initPM 37 1173 (by native_decide) (by native_decide)]
  rw [show pm.nodes[37]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1145], outs := [1173, 1201, 3439], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 0 3 1145 1173 [1201, 3439] (by decide)]
  rw [pm_prefix_eq initPM 37 1145 (by native_decide)]

theorem pm_frame_1174_self (initPM : Store) :
    denoteGraph pm initPM 1174 = denoteGraph pm_goal_261 (denoteGraph pm initPM) 1174 := by
  rw [denote_pm_goal_261_1174]
  rw [pm_val initPM 38 1174 (by native_decide) (by native_decide)]
  rw [show pm.nodes[38]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1146], outs := [1174, 1202, 3447], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 1 3 1146 1174 [1202, 3447] (by decide)]
  rw [pm_prefix_eq initPM 38 1146 (by native_decide)]

theorem pm_frame_1175_self (initPM : Store) :
    denoteGraph pm initPM 1175 = denoteGraph pm_goal_261 (denoteGraph pm initPM) 1175 := by
  rw [denote_pm_goal_261_1175]
  rw [pm_val initPM 39 1175 (by native_decide) (by native_decide)]
  rw [show pm.nodes[39]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1147], outs := [1175, 1203, 3455], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 2 3 1147 1175 [1203, 3455] (by decide)]
  rw [pm_prefix_eq initPM 39 1147 (by native_decide)]

theorem pm_frame_1176_self (initPM : Store) :
    denoteGraph pm initPM 1176 = denoteGraph pm_goal_261 (denoteGraph pm initPM) 1176 := by
  rw [denote_pm_goal_261_1176]
  rw [pm_val initPM 40 1176 (by native_decide) (by native_decide)]
  rw [show pm.nodes[40]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1148], outs := [1176, 1204, 3463], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref_first_out_g261 _ _ 3 3 1148 1176 [1204, 3463] (by decide)]
  rw [pm_prefix_eq initPM 40 1148 (by native_decide)]

-- ========== 总装 ==========
theorem goal_261_cut_to_full (h : goal_261_stmt_cut) : goal_261_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg257 hinitC
  have hnr : pm_goal_261.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_261.numRanks goal_261_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_261_cut_initGoals, goal_261_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg257, List.forall_mem_nil _⟩
  -- shape: 570 = goal_5.ts; 1145-1148 = goal_5.tps
  have h570_smsh : (Ssm 570).shape = [1, 8, 32] := by
    have h := hg5.1; simp only [goal_5] at h; exact h
  have h4 : (Spm 1145).shape = [1,2,32] ∧ (Spm 1146).shape = [1,2,32] ∧
           (Spm 1147).shape = [1,2,32] ∧ (Spm 1148).shape = [1,2,32] := by
    have h := hg5.2.1
    simp only [goal_5, List.map, List.cons.injEq, and_true, and_assoc] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1145sh, h1146sh, h1147sh, h1148sh⟩ := h4
  have hSM261 : StoreShapesHold Ssm sm_goal_261InitEnv := by
    intro tid sh hsh
    rw [sm_goal_261InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_261InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h570_smsh
  have hPM261 : StoreShapesHold Spm pm_goal_261InitEnv := by
    intro tid sh hsh
    rw [pm_goal_261InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_261InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1145sh
    · exact h1146sh
    · exact h1147sh
    · exact h1148sh
  have hcut := h Ssm Spm hSM261 hPM261 hInitCut
  have hsmf : Ssm 918 = denoteGraph sm_goal_261 Ssm 918 := by
    rw [hSsm]; exact sm_frame_918_self initSM
  have hpm1173 : Spm 1173 = denoteGraph pm_goal_261 Spm 1173 := by
    rw [hSpm]; exact pm_frame_1173_self initPM
  have hpm1174 : Spm 1174 = denoteGraph pm_goal_261 Spm 1174 := by
    rw [hSpm]; exact pm_frame_1174_self initPM
  have hpm1175 : Spm 1175 = denoteGraph pm_goal_261 Spm 1175 := by
    rw [hSpm]; exact pm_frame_1175_self initPM
  have hpm1176 : Spm 1176 = denoteGraph pm_goal_261 Spm 1176 := by
    rw [hSpm]; exact pm_frame_1176_self initPM
  rw [hnr] at hcut
  simp only [goal_261, List.map] at hcut ⊢
  rw [hsmf, hpm1173, hpm1174, hpm1175, hpm1176]
  exact hcut

theorem goal_261_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_261 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_261_stmt := goal_261_cut_to_full prove_goal_261_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
