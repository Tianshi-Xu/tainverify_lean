/- goal_47 桥 (prereqs 56 个: goal_2..goal_46 + 257,259,261,263,265,267,269,271,275,277,279)。
   Trivial 复制结构: SM=FW_view(624,p=[1,8,32])→625 (sm node 50, 单 rank);
   PM=4×FW_view(624,p=[1,8,32])→625 (pm node 326-329, 4 rank 都写同 tid 625, replicated 输出),
   single-tp ts==tid 625 (goal_47.tps=[{0,625}])。624=goal_46 输出 (single-tp, shape [1,8,4,8])。
   FW_view 把 [1,8,4,8] reshape 成 [1,8,32]; 各 rank 独立同操作, 无 weight, 无 collective。
   完全同构 goal_9 (FW_view replicated, single-tp), 直接套 Goal9Bridge 模板。 -/
import denote.gpt_ly4_regen.Goal46Bridge
import denote.gpt_ly4_regen.Goal_47

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_47 算 625 ==========
theorem denote_sm_goal_47_625 (s : Store) :
    denoteGraph sm_goal_47 s 625 = fw_view [1, 8, 32] (s 624) := by
  simp only [sm_goal_47, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_47 算 625 (4 rank 都写同 tid, 取最后) ==========
theorem denote_pm_goal_47_625 (s : Store) :
    denoteGraph pm_goal_47 s 625 = fw_view [1, 8, 32] (s 624) := by
  simp only [pm_goal_47, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 624 (by decide),
      applyNode_skip _ _ _ 624 (by decide),
      applyNode_skip _ _ _ 624 (by decide)]

-- ========== SM self-frame: full sm 算 625 (node 50) ==========
theorem sm_frame_625_self (initSM : Store) :
    denoteGraph sm initSM 625 = denoteGraph sm_goal_47 (denoteGraph sm initSM) 625 := by
  rw [denote_sm_goal_47_625]
  rw [sm_val initSM 50 625 (by native_decide) (by native_decide)]
  rw [show sm.nodes[50]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [624], outs := [625], params := [1, 8, 32] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 50 624 (by native_decide)]

-- ========== PM self-frame: full pm 算 625 (4 rank, 最后 = node 329 rank 3) ==========
theorem pm_frame_625_self (initPM : Store) :
    denoteGraph pm initPM 625 = fw_view [1, 8, 32] (denoteGraph pm initPM 624) := by
  rw [pm_val initPM 329 625 (by native_decide) (by native_decide)]
  rw [show pm.nodes[329]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [624], outs := [625], params := [1, 8, 32] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 329 624 (by native_decide)]

-- ========== 总装 ==========
theorem goal_47_cut_to_full (h : goal_47_stmt_cut) : goal_47_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg6 := goal_6_intermediate initSM initPM hSM hPM hInit
  have hg7 := goal_7_intermediate initSM initPM hSM hPM hInit
  have hg8 := goal_8_intermediate initSM initPM hSM hPM hInit
  have hg9 := goal_9_intermediate initSM initPM hSM hPM hInit
  have hg10 := goal_10_intermediate initSM initPM hSM hPM hInit
  have hg11 := goal_11_intermediate initSM initPM hSM hPM hInit
  have hg12 := goal_12_intermediate initSM initPM hSM hPM hInit
  have hg13 := goal_13_intermediate initSM initPM hSM hPM hInit
  have hg14 := goal_14_intermediate initSM initPM hSM hPM hInit
  have hg15 := goal_15_intermediate initSM initPM hSM hPM hInit
  have hg16 := goal_16_intermediate initSM initPM hSM hPM hInit
  have hg17 := goal_17_intermediate initSM initPM hSM hPM hInit
  have hg18 := goal_18_intermediate initSM initPM hSM hPM hInit
  have hg19 := goal_19_intermediate initSM initPM hSM hPM hInit
  have hg20 := goal_20_intermediate initSM initPM hSM hPM hInit
  have hg21 := goal_21_intermediate initSM initPM hSM hPM hInit
  have hg22 := goal_22_intermediate initSM initPM hSM hPM hInit
  have hg23 := goal_23_intermediate initSM initPM hSM hPM hInit
  have hg24 := goal_24_intermediate initSM initPM hSM hPM hInit
  have hg25 := goal_25_intermediate initSM initPM hSM hPM hInit
  have hg26 := goal_26_intermediate initSM initPM hSM hPM hInit
  have hg27 := goal_27_intermediate initSM initPM hSM hPM hInit
  have hg28 := goal_28_intermediate initSM initPM hSM hPM hInit
  have hg29 := goal_29_intermediate initSM initPM hSM hPM hInit
  have hg30 := goal_30_intermediate initSM initPM hSM hPM hInit
  have hg31 := goal_31_intermediate initSM initPM hSM hPM hInit
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg33 := goal_33_intermediate initSM initPM hSM hPM hInit
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg38 := goal_38_intermediate initSM initPM hSM hPM hInit
  have hg39 := goal_39_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg41 := goal_41_intermediate initSM initPM hSM hPM hInit
  have hg42 := goal_42_intermediate initSM initPM hSM hPM hInit
  have hg43 := goal_43_intermediate initSM initPM hSM hPM hInit
  have hg44 := goal_44_intermediate initSM initPM hSM hPM hInit
  have hg45 := goal_45_intermediate initSM initPM hSM hPM hInit
  have hg46 := goal_46_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hg277 hg279 hinitC
  have hnr : pm_goal_47.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_47.numRanks goal_47_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_47_cut_initGoals, goal_47_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg6
      · exact hg7
      · exact hg8
      · exact hg9
      · exact hg10
      · exact hg11
      · exact hg12
      · exact hg13
      · exact hg14
      · exact hg15
      · exact hg16
      · exact hg17
      · exact hg18
      · exact hg19
      · exact hg20
      · exact hg21
      · exact hg22
      · exact hg23
      · exact hg24
      · exact hg25
      · exact hg26
      · exact hg27
      · exact hg28
      · exact hg29
      · exact hg30
      · exact hg31
      · exact hg32
      · exact hg33
      · exact hg34
      · exact hg35
      · exact hg36
      · exact hg37
      · exact hg38
      · exact hg39
      · exact hg40
      · exact hg41
      · exact hg42
      · exact hg43
      · exact hg44
      · exact hg45
      · exact hg46
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg275
      · exact hg277
      · exact hg279
  -- 624 = goal_46.ts (single-tp); (Ssm 624).shape = [1,8,4,8] (from hg46)
  have h624_smsh : (Ssm 624).shape = [1, 8, 4, 8] := by
    have h := hg46.1; simp only [goal_46] at h; exact h
  have h624_pmsh : (Spm 624).shape = [1, 8, 4, 8] := by
    have h := hg46.2.1; simp only [goal_46, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM47 : StoreShapesHold Ssm sm_goal_47InitEnv := by
    intro tid sh hsh
    rw [sm_goal_47InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_47InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h624_smsh
  have hPM47 : StoreShapesHold Spm pm_goal_47InitEnv := by
    intro tid sh hsh
    rw [pm_goal_47InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_47InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h624_pmsh
  have hcut := h Ssm Spm hSM47 hPM47 hInitCut
  have hsmf : Ssm 625 = denoteGraph sm_goal_47 Ssm 625 := by
    rw [hSsm]; exact sm_frame_625_self initSM
  have hpm625 : Spm 625 = denoteGraph pm_goal_47 Spm 625 := by
    rw [denote_pm_goal_47_625]
    rw [hSpm]; exact pm_frame_625_self initPM
  rw [hnr] at hcut
  simp only [goal_47, List.map] at hcut ⊢
  rw [hsmf, hpm625]
  exact hcut

theorem goal_47_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_47 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_47_stmt := goal_47_cut_to_full prove_goal_47_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
