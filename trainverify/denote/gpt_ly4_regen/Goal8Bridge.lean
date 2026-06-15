/- goal_8 桥 (prereqs=[2,3,4,5,257,265])。SM=FW_linear(926,575)→576; PM=4×FW_linear(917,1229-1232)→1233-1236 →AllGather(dim2)→576.
   917=goal_265 单tp(replicated); 1229-1232=initGoal_575 dim0分片(init); 575=weight. -/
import denote.gpt_ly4_regen.Goal265Bridge
import denote.gpt_ly4_regen.Goal_8

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_8 算 576 ==========
theorem denote_sm_goal_8_576 (s : Store) :
    denoteGraph sm_goal_8 s 576 = fw_linear (s 926) (s 575) := by
  simp only [sm_goal_8, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_8 算 576 (4×FW_linear(917,weight_r) → AllGather dim2) ==========
theorem denote_pm_goal_8_576 (s : Store) :
    denoteGraph pm_goal_8 s 576 = allGatherPrimDimN 2 4 0
      [fw_linear (s 917) (s 1229), fw_linear (s 917) (s 1230),
       fw_linear (s 917) (s 1231), fw_linear (s 917) (s 1232)] := by
  simp only [pm_goal_8, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out]
  simp only [List.map]
  set_option maxHeartbeats 800000 in congr 1

-- ========== SM self-frame: full 算 576 (node 8) ==========
theorem sm_frame_576_self (initSM : Store) :
    denoteGraph sm initSM 576 = denoteGraph sm_goal_8 (denoteGraph sm initSM) 576 := by
  rw [denote_sm_goal_8_576]
  rw [sm_val initSM 8 576 (by native_decide) (by native_decide)]
  rw [show sm.nodes[8]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [926, 575], outs := [576] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 8 926 (by native_decide),
      sm_prefix_eq initSM 8 575 (by native_decide)]

-- ========== full pm 算 FW_linear 输出 1233-1236 (node 50-53) ==========
theorem pm_full_1233 (initPM : Store) :
    denoteGraph pm initPM 1233 = fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1229) := by
  rw [pm_val initPM 50 1233 (by native_decide) (by native_decide)]
  rw [show pm.nodes[50]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [917, 1229], outs := [1233] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 50 917 (by native_decide),
      pm_prefix_eq initPM 50 1229 (by native_decide)]

theorem pm_full_1234 (initPM : Store) :
    denoteGraph pm initPM 1234 = fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1230) := by
  rw [pm_val initPM 51 1234 (by native_decide) (by native_decide)]
  rw [show pm.nodes[51]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [917, 1230], outs := [1234] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 51 917 (by native_decide),
      pm_prefix_eq initPM 51 1230 (by native_decide)]

theorem pm_full_1235 (initPM : Store) :
    denoteGraph pm initPM 1235 = fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1231) := by
  rw [pm_val initPM 52 1235 (by native_decide) (by native_decide)]
  rw [show pm.nodes[52]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [917, 1231], outs := [1235] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 52 917 (by native_decide),
      pm_prefix_eq initPM 52 1231 (by native_decide)]

theorem pm_full_1236 (initPM : Store) :
    denoteGraph pm initPM 1236 = fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1232) := by
  rw [pm_val initPM 53 1236 (by native_decide) (by native_decide)]
  rw [show pm.nodes[53]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [917, 1232], outs := [1236] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 53 917 (by native_decide),
      pm_prefix_eq initPM 53 1232 (by native_decide)]

-- ========== PM self-frame: 576 (AllGather node 56, dim2, computed ins) ==========
theorem pm_frame_576_self (initPM : Store) :
    denoteGraph pm initPM 576
      = allGatherPrimDimN 2 4 0
          [fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1229),
           fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1230),
           fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1231),
           fw_linear (denoteGraph pm initPM 917) (denoteGraph pm initPM 1232)] := by
  rw [pm_val initPM 56 576 (by native_decide) (by native_decide)]
  rw [show pm.nodes[56]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 1233 + r)), outs := [576], params := [2] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 56 1233 (by native_decide),
      pm_prefix_eq initPM 56 1234 (by native_decide),
      pm_prefix_eq initPM 56 1235 (by native_decide),
      pm_prefix_eq initPM 56 1236 (by native_decide)]
  rw [pm_full_1233, pm_full_1234, pm_full_1235, pm_full_1236]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_8_cut_to_full (h : goal_8_stmt_cut) : goal_8_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_8.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_8.numRanks goal_8_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_8_cut_initGoals, goal_8_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg257
      · exact hg265
  -- 926 = goal_265.ts; 575 = initGoal_575.ts (sm weight); 917 = goal_265.tps[0]; 1229-1232 = initGoal_575.tps
  have h926_smsh : (Ssm 926).shape = [1, 8, 32] := by
    have h := hg265.1; simp only [goal_265] at h; exact h
  have h917_pmsh : (Spm 917).shape = [1, 8, 32] := by
    have h := hg265.2.1; simp only [goal_265, List.map, List.cons.injEq] at h; exact h.1
  have h575_sm : (Ssm 575).shape = [32, 32] := by
    have hg := hinitC initGoal_575 (by simp only [initGoals]; decide)
    have h := hg.1; simp only [initGoal_575] at h; exact h
  have h575w : (Spm 1229).shape = [8,32] ∧ (Spm 1230).shape = [8,32] ∧
              (Spm 1231).shape = [8,32] ∧ (Spm 1232).shape = [8,32] := by
    have hg := hinitC initGoal_575 (by simp only [initGoals]; decide)
    have h := hg.2.1
    simp only [initGoal_575, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1229sh, h1230sh, h1231sh, h1232sh⟩ := h575w
  have hSM8 : StoreShapesHold Ssm sm_goal_8InitEnv := by
    intro tid sh hsh
    rw [sm_goal_8InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_8InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h575_sm
    · exact h926_smsh
  have hPM8 : StoreShapesHold Spm pm_goal_8InitEnv := by
    intro tid sh hsh
    rw [pm_goal_8InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_8InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h917_pmsh
    · exact h1229sh
    · exact h1230sh
    · exact h1231sh
    · exact h1232sh
  have hcut := h Ssm Spm hSM8 hPM8 hInitCut
  have hsmf : Ssm 576 = denoteGraph sm_goal_8 Ssm 576 := by
    rw [hSsm]; exact sm_frame_576_self initSM
  have hpm576 : Spm 576 = denoteGraph pm_goal_8 Spm 576 := by
    rw [denote_pm_goal_8_576]
    rw [hSpm]; exact pm_frame_576_self initPM
  rw [hnr] at hcut
  simp only [goal_8, List.map] at hcut ⊢
  rw [hsmf, hpm576]
  exact hcut

theorem goal_8_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_8 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_8_stmt := goal_8_cut_to_full prove_goal_8_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_8] using this

end TrainVerify.Denote.GeneratedGoals

