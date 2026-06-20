/- goal_265 桥 (prereqs=[2,3,4,5,257])。SM=multiref 第3输出(926); PM=multiref 第3输出→AllGather(917, 单tp)。
   PM 内部两级: multiref(node 37-40 第3输出 3439-3463) → AllGather(node 47 → 917)。 -/
import denote.gpt_ly4_regen.Goal5Bridge
import denote.gpt_ly4_regen.Goal_265

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_265 算 926 (multiref 第3输出 = s 570) ==========
theorem denote_sm_goal_265_926 (s : Store) :
    denoteGraph sm_goal_265 s 926 = s 570 := by
  simp only [sm_goal_265, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_third_out_g265 _ _ _ _ _ _ _ (by decide) (by decide)]

-- ========== 迷你图 pm_goal_265 算 917 (multiref 3rd → AllGather = allGather[s1145..s1148]) ==========
theorem denote_pm_goal_265_917 (s : Store) :
    denoteGraph pm_goal_265 s 917 = allGatherPrimDimN 1 4 0 [s 1145, s 1146, s 1147, s 1148] := by
  simp only [pm_goal_265, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  congr 1 <;>
    simp only [applyNode_fw_multiref3_third_out_g265 _ _ _ _ _ _ _ (by decide) (by decide)] <;>
    rfl

-- ========== SM self-frame: full 算 926 (node 5) ==========
theorem sm_frame_926_self (initSM : Store) :
    denoteGraph sm initSM 926 = denoteGraph sm_goal_265 (denoteGraph sm initSM) 926 := by
  rw [denote_sm_goal_265_926]
  rw [sm_val initSM 5 926 (by native_decide) (by native_decide)]
  rw [show sm.nodes[5]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [570], outs := [918, 922, 926], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g265 _ _ _ _ _ _ _ (by decide) (by decide)]
  rw [sm_prefix_eq initSM 5 570 (by native_decide)]

-- ========== full pm 算 multiref 第3输出 3439-3463 (node 37-40) = Spm 1145-1148 ==========
-- 3439 由 node 37 写, 输入 1145 (node 33 写). full pm 算 3439 = full pm 算 1145.
theorem pm_full_3439 (initPM : Store) :
    denoteGraph pm initPM 3439 = denoteGraph pm initPM 1145 := by
  rw [pm_val initPM 37 3439 (by native_decide) (by native_decide)]
  rw [show pm.nodes[37]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1145], outs := [1173, 1201, 3439], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g265 _ _ _ _ _ _ _ (by decide) (by decide)]
  rw [pm_prefix_eq initPM 37 1145 (by native_decide)]

theorem pm_full_3447 (initPM : Store) :
    denoteGraph pm initPM 3447 = denoteGraph pm initPM 1146 := by
  rw [pm_val initPM 38 3447 (by native_decide) (by native_decide)]
  rw [show pm.nodes[38]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1146], outs := [1174, 1202, 3447], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g265 _ _ _ _ _ _ _ (by decide) (by decide)]
  rw [pm_prefix_eq initPM 38 1146 (by native_decide)]

theorem pm_full_3455 (initPM : Store) :
    denoteGraph pm initPM 3455 = denoteGraph pm initPM 1147 := by
  rw [pm_val initPM 39 3455 (by native_decide) (by native_decide)]
  rw [show pm.nodes[39]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1147], outs := [1175, 1203, 3455], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g265 _ _ _ _ _ _ _ (by decide) (by decide)]
  rw [pm_prefix_eq initPM 39 1147 (by native_decide)]

theorem pm_full_3463 (initPM : Store) :
    denoteGraph pm initPM 3463 = denoteGraph pm initPM 1148 := by
  rw [pm_val initPM 40 3463 (by native_decide) (by native_decide)]
  rw [show pm.nodes[40]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1148], outs := [1176, 1204, 3463], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g265 _ _ _ _ _ _ _ (by decide) (by decide)]
  rw [pm_prefix_eq initPM 40 1148 (by native_decide)]

-- ========== PM self-frame: 917 (AllGather node 47, ins=3439-3463) ==========
theorem pm_frame_917_self (initPM : Store) :
    denoteGraph pm initPM 917
      = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 1145, denoteGraph pm initPM 1146,
           denoteGraph pm initPM 1147, denoteGraph pm initPM 1148] := by
  rw [pm_val initPM 47 917 (by native_decide) (by native_decide)]
  rw [show pm.nodes[47]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim", ins := [3439, 3447, 3455, 3463], outs := [917], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  -- take47 store 上 3439-3463 = 全图 3439-3463 (pm_prefix_eq 47 反向) = 全图 1145-1148
  rw [pm_prefix_eq initPM 47 3439 (by native_decide),
      pm_prefix_eq initPM 47 3447 (by native_decide),
      pm_prefix_eq initPM 47 3455 (by native_decide),
      pm_prefix_eq initPM 47 3463 (by native_decide)]
  rw [pm_full_3439, pm_full_3447, pm_full_3455, pm_full_3463]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_265_cut_to_full (h : goal_265_stmt_cut) : goal_265_stmt := by
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
  have hnr : pm_goal_265.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_265.numRanks goal_265_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_265_cut_initGoals, goal_265_prereqs, List.mem_append] at hg
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
    simp only [goal_5, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1145sh, h1146sh, h1147sh, h1148sh⟩ := h4
  have hSM265 : StoreShapesHold Ssm sm_goal_265InitEnv := by
    intro tid sh hsh
    rw [sm_goal_265InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_265InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h570_smsh
  have hPM265 : StoreShapesHold Spm pm_goal_265InitEnv := by
    intro tid sh hsh
    rw [pm_goal_265InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_265InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1145sh
    · exact h1146sh
    · exact h1147sh
    · exact h1148sh
  have hcut := h Ssm Spm hSM265 hPM265 hInitCut
  have hsmf : Ssm 926 = denoteGraph sm_goal_265 Ssm 926 := by
    rw [hSsm]; exact sm_frame_926_self initSM
  have hpm917 : Spm 917 = denoteGraph pm_goal_265 Spm 917 := by
    rw [denote_pm_goal_265_917]
    rw [hSpm]
    exact pm_frame_917_self initPM
  rw [hnr] at hcut
  simp only [goal_265, List.map] at hcut ⊢
  rw [hsmf, hpm917]
  exact hcut

theorem goal_265_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_265 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_265_stmt := goal_265_cut_to_full prove_goal_265_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
