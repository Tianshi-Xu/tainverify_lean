/- goal_257 桥 (非 base case, prereqs=[goal_2,goal_3,goal_4])。
   算子: SM=FW_multiref(903); PM=FW_multiref(3413..)→AllToAll(1141..)。
   复用 Goal4Bridge 的通用齿轮 pm_val/pm_prefix_eq/initGoals_preserved + goal_2/3/4_intermediate。 -/
import denote.gpt_ly4_regen.BridgeKit
import denote.gpt_ly4_regen.Goal4Bridge
import denote.gpt_ly4_regen.Goal_257

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 pm_goal_257 以任意 store s 算 1141-1144 (AllToAll 输出) ==========
-- pm_goal_257 节点: 0-3=FW_multiref(3413/3419/3425/3431), 4-7=AllToAll(1141/1142/1143/1144)
theorem denote_pm_goal_257_1141 (s : Store) :
    denoteGraph pm_goal_257 s 1141 =
      allToAllPrimWithDims 4 0 [s 1117, s 1118, s 1119, s 1120] 2 1 := by
  simp only [pm_goal_257, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  congr 1

theorem denote_pm_goal_257_1142 (s : Store) :
    denoteGraph pm_goal_257 s 1142 =
      allToAllPrimWithDims 4 1 [s 1117, s 1118, s 1119, s 1120] 2 1 := by
  simp only [pm_goal_257, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  congr 1

theorem denote_pm_goal_257_1143 (s : Store) :
    denoteGraph pm_goal_257 s 1143 =
      allToAllPrimWithDims 4 2 [s 1117, s 1118, s 1119, s 1120] 2 1 := by
  simp only [pm_goal_257, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  congr 1

theorem denote_pm_goal_257_1144 (s : Store) :
    denoteGraph pm_goal_257 s 1144 =
      allToAllPrimWithDims 4 3 [s 1117, s 1118, s 1119, s 1120] 2 1 := by
  simp only [pm_goal_257, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  congr 1

-- ========== 迷你图 sm_goal_257 算 903 (FW_multiref 第一输出) ==========
theorem denote_sm_goal_257_903 (s : Store) :
    denoteGraph sm_goal_257 s 903 = s 567 := by
  simp only [sm_goal_257, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_first_out]

-- ========== SM 通用齿轮 sm_val/sm_prefix_eq 已移至 BridgeKit ==========

-- ========== SM self-frame: full 算 903 = 迷你图以 full store 为 init 算 903 ==========
-- full sm node 3 = FW_multiref ins=[567] outs=[903,907]; 567 由 node 2 (FW_add) 写
theorem sm_frame_903_self (initSM : Store) :
    denoteGraph sm initSM 903 = denoteGraph sm_goal_257 (denoteGraph sm initSM) 903 := by
  rw [denote_sm_goal_257_903]
  -- full: 903 写在 node 3
  rw [sm_val initSM 3 903 (by native_decide) (by native_decide)]
  rw [show sm.nodes[3]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [567], outs := [903, 907], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  -- (take 3 store) 567 = full store 567 (node 3+ 不写 567)
  rw [sm_prefix_eq initSM 3 567 (by native_decide)]

-- ========== PM 中间 frame: 3413/3419/3425/3431 = FW_multiref 第一输出 (node 25-28) ==========
-- 复用 Goal4Bridge 的 pm_val/pm_prefix_eq (同一个 full pm)
theorem pm_frame_3413 (initPM : Store) :
    denoteGraph pm initPM 3413 = denoteGraph pm initPM 1117 := by
  rw [pm_val initPM 25 3413 (by native_decide) (by native_decide)]
  rw [show pm.nodes[25]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1117], outs := [3413, 1501], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out, pm_prefix_eq initPM 25 1117 (by native_decide)]

theorem pm_frame_3419 (initPM : Store) :
    denoteGraph pm initPM 3419 = denoteGraph pm initPM 1118 := by
  rw [pm_val initPM 26 3419 (by native_decide) (by native_decide)]
  rw [show pm.nodes[26]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1118], outs := [3419, 1502], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out, pm_prefix_eq initPM 26 1118 (by native_decide)]

theorem pm_frame_3425 (initPM : Store) :
    denoteGraph pm initPM 3425 = denoteGraph pm initPM 1119 := by
  rw [pm_val initPM 27 3425 (by native_decide) (by native_decide)]
  rw [show pm.nodes[27]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1119], outs := [3425, 1503], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out, pm_prefix_eq initPM 27 1119 (by native_decide)]

theorem pm_frame_3431 (initPM : Store) :
    denoteGraph pm initPM 3431 = denoteGraph pm initPM 1120 := by
  rw [pm_val initPM 28 3431 (by native_decide) (by native_decide)]
  rw [show pm.nodes[28]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1120], outs := [3431, 1504], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out, pm_prefix_eq initPM 28 1120 (by native_decide)]

-- ========== PM self-frame: 1141-1144 (node 29-32 AllToAll) ==========
theorem pm_frame_1141_self (initPM : Store) :
    denoteGraph pm initPM 1141 = denoteGraph pm_goal_257 (denoteGraph pm initPM) 1141 := by
  rw [denote_pm_goal_257_1141]
  rw [pm_val initPM 29 1141 (by native_decide) (by native_decide)]
  rw [show pm.nodes[29]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim", ins := [3413, 3419, 3425, 3431], outs := [1141], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 29 3413 (by native_decide),
      pm_prefix_eq initPM 29 3419 (by native_decide),
      pm_prefix_eq initPM 29 3425 (by native_decide),
      pm_prefix_eq initPM 29 3431 (by native_decide),
      pm_frame_3413, pm_frame_3419, pm_frame_3425, pm_frame_3431]

theorem pm_frame_1142_self (initPM : Store) :
    denoteGraph pm initPM 1142 = denoteGraph pm_goal_257 (denoteGraph pm initPM) 1142 := by
  rw [denote_pm_goal_257_1142]
  rw [pm_val initPM 30 1142 (by native_decide) (by native_decide)]
  rw [show pm.nodes[30]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim", ins := [3413, 3419, 3425, 3431], outs := [1142], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 30 3413 (by native_decide),
      pm_prefix_eq initPM 30 3419 (by native_decide),
      pm_prefix_eq initPM 30 3425 (by native_decide),
      pm_prefix_eq initPM 30 3431 (by native_decide),
      pm_frame_3413, pm_frame_3419, pm_frame_3425, pm_frame_3431]

theorem pm_frame_1143_self (initPM : Store) :
    denoteGraph pm initPM 1143 = denoteGraph pm_goal_257 (denoteGraph pm initPM) 1143 := by
  rw [denote_pm_goal_257_1143]
  rw [pm_val initPM 31 1143 (by native_decide) (by native_decide)]
  rw [show pm.nodes[31]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim", ins := [3413, 3419, 3425, 3431], outs := [1143], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 31 3413 (by native_decide),
      pm_prefix_eq initPM 31 3419 (by native_decide),
      pm_prefix_eq initPM 31 3425 (by native_decide),
      pm_prefix_eq initPM 31 3431 (by native_decide),
      pm_frame_3413, pm_frame_3419, pm_frame_3425, pm_frame_3431]

theorem pm_frame_1144_self (initPM : Store) :
    denoteGraph pm initPM 1144 = denoteGraph pm_goal_257 (denoteGraph pm initPM) 1144 := by
  rw [denote_pm_goal_257_1144]
  rw [pm_val initPM 32 1144 (by native_decide) (by native_decide)]
  rw [show pm.nodes[32]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim", ins := [3413, 3419, 3425, 3431], outs := [1144], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 32 3413 (by native_decide),
      pm_prefix_eq initPM 32 3419 (by native_decide),
      pm_prefix_eq initPM 32 3425 (by native_decide),
      pm_prefix_eq initPM 32 3431 (by native_decide),
      pm_frame_3413, pm_frame_3419, pm_frame_3425, pm_frame_3431]

-- ========== 总装: goal_257_cut_to_full ==========
theorem goal_257_cut_to_full (h : goal_257_stmt_cut) : goal_257_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  -- 拓扑归纳: goal_2/3/4 在 computed store 上的 InitGoalHolds
  have hg2 : InitGoalHolds pm.numRanks goal_2 Ssm Spm := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 : InitGoalHolds pm.numRanks goal_3 Ssm Spm := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 : InitGoalHolds pm.numRanks goal_4 Ssm Spm := goal_4_intermediate initSM initPM hSM hPM hInit
  have hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_257.numRanks = pm.numRanks := by native_decide
  -- cut 要的 InitGoalsHold (initGoals ++ [goal_2,goal_3,goal_4]) 在 computed store
  have hInitCut : InitGoalsHold pm_goal_257.numRanks goal_257_cut_initGoals Ssm Spm := by
    rw [hnr]
    intro g hg
    simp only [goal_257_cut_initGoals, goal_257_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
  -- StoreShapesHold (computed): 全从 hg4 抽 (567 = goal_4.ts; 1117-1120 = goal_4.tps)
  have h567_smsh : (Ssm 567).shape = [1, 8, 32] := by
    have h := hg4.1; simp only [goal_4] at h; exact h
  have h4 : (Spm 1117).shape = [1,8,8] ∧ (Spm 1118).shape = [1,8,8] ∧
           (Spm 1119).shape = [1,8,8] ∧ (Spm 1120).shape = [1,8,8] := by
    have h := hg4.2.1
    simp only [goal_4, List.map, List.cons.injEq, and_true, and_assoc] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1117sh, h1118sh, h1119sh, h1120sh⟩ := h4
  have hSM257 : StoreShapesHold Ssm sm_goal_257InitEnv := by
    intro tid sh hsh
    rw [sm_goal_257InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_257InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h567_smsh
  have hPM257 : StoreShapesHold Spm pm_goal_257InitEnv := by
    intro tid sh hsh
    rw [pm_goal_257InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_257InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1117sh
    · exact h1118sh
    · exact h1119sh
    · exact h1120sh
  -- 应用 cut h, 传 computed store
  have hcut := h Ssm Spm hSM257 hPM257 hInitCut
  -- frame 引理 LHS 用 Ssm/Spm 形态 (匹配 set 后的目标)
  have hsmf : Ssm 903 = denoteGraph sm_goal_257 Ssm 903 := by
    rw [hSsm]; exact sm_frame_903_self initSM
  have hpm1141 : Spm 1141 = denoteGraph pm_goal_257 Spm 1141 := by
    rw [hSpm]; exact pm_frame_1141_self initPM
  have hpm1142 : Spm 1142 = denoteGraph pm_goal_257 Spm 1142 := by
    rw [hSpm]; exact pm_frame_1142_self initPM
  have hpm1143 : Spm 1143 = denoteGraph pm_goal_257 Spm 1143 := by
    rw [hSpm]; exact pm_frame_1143_self initPM
  have hpm1144 : Spm 1144 = denoteGraph pm_goal_257 Spm 1144 := by
    rw [hSpm]; exact pm_frame_1144_self initPM
  rw [hnr] at hcut
  simp only [goal_257, List.map] at hcut ⊢
  rw [hsmf, hpm1141, hpm1142, hpm1143, hpm1144]
  exact hcut

-- ========== 导出 goal_257_intermediate (供后续依赖 goal_257 的 goal 复用) ==========
theorem goal_257_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_257 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_257_stmt := goal_257_cut_to_full prove_goal_257_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_257] using this

end TrainVerify.Denote.GeneratedGoals
