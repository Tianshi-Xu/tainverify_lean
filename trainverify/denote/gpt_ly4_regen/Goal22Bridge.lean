/- goal_22 桥 (prereqs=[2..21,257,261,263,265])。
   SM=FW_view(589)→590 (node 22, [1,8,32]); PM=4×FW_view(589)→590 (node 140-143, 4 rank 都写同 tid, replicated 输出, single tp 同 tid)。
   589=goal_21 输出 [1,8,4,8] (replicated 单 tp 同 tid)。无 weight, 无 collective。
   结构同 goal_11 (replicated FW_view, single-tp same-tid), 仅 tids/shapes/node 下标和 prereq 链不同。 -/
import denote.gpt_ly4_regen.Goal14Bridge
import denote.gpt_ly4_regen.Goal18Bridge
import denote.gpt_ly4_regen.Goal19Bridge
import denote.gpt_ly4_regen.Goal20Bridge
import denote.gpt_ly4_regen.Goal21Bridge
import denote.gpt_ly4_regen.Goal_22

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_22 算 590 ==========
theorem denote_sm_goal_22_590 (s : Store) :
    denoteGraph sm_goal_22 s 590 = fw_view [1, 8, 32] (s 589) := by
  simp only [sm_goal_22, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_22 算 590 (4 rank 写同 tid) ==========
theorem denote_pm_goal_22_590 (s : Store) :
    denoteGraph pm_goal_22 s 590 = fw_view [1, 8, 32] (s 589) := by
  simp only [pm_goal_22, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 589 (by decide),
      applyNode_skip _ _ _ 589 (by decide),
      applyNode_skip _ _ _ 589 (by decide)]

-- ========== SM self-frame: full sm 算 590 (node 22) ==========
theorem sm_frame_590_self (initSM : Store) :
    denoteGraph sm initSM 590 = denoteGraph sm_goal_22 (denoteGraph sm initSM) 590 := by
  rw [denote_sm_goal_22_590]
  rw [sm_val initSM 22 590 (by native_decide) (by native_decide)]
  rw [show sm.nodes[22]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [589], outs := [590], params := [1, 8, 32] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 22 589 (by native_decide)]

-- ========== PM self-frame: full pm 算 590 (4 rank 都写, 取最后 = node 143) ==========
theorem pm_frame_590_self (initPM : Store) :
    denoteGraph pm initPM 590 = fw_view [1, 8, 32] (denoteGraph pm initPM 589) := by
  rw [pm_val initPM 143 590 (by native_decide) (by native_decide)]
  rw [show pm.nodes[143]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [589], outs := [590], params := [1, 8, 32] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 143 589 (by native_decide)]

-- ========== 总装 ==========
theorem goal_22_cut_to_full (h : goal_22_stmt_cut) : goal_22_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg257 hg261 hg263 hg265 hinitC
  have hnr : pm_goal_22.numRanks = pm.numRanks := by native_decide
  -- 589 = goal_21.ts; (Ssm 589).shape = [1,8,4,8] (from hg21)
  have h589_smsh : (Ssm 589).shape = [1, 8, 4, 8] := by
    have h := hg21.1; simp only [goal_21] at h; exact h
  have hSM22 : StoreShapesHold Ssm sm_goal_22InitEnv := by
    intro tid sh hsh
    rw [sm_goal_22InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_22InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h589_smsh
  have hPM22 : StoreShapesHold Spm pm_goal_22InitEnv := by
    intro tid sh hsh
    rw [pm_goal_22InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_22InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    -- pm 上 589 = goal_21.tps[0] = goal_21 单 tp, shape [1,8,4,8]
    have h := hg21.2.1; simp only [goal_21, List.map, List.cons.injEq, and_true] at h
    exact h
  have hInitCut : InitGoalsHold pm_goal_22.numRanks goal_22_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_22_cut_initGoals, goal_22_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg261
      · exact hg263
      · exact hg265
  have hcut := h Ssm Spm hSM22 hPM22 hInitCut
  have hsmf : Ssm 590 = denoteGraph sm_goal_22 Ssm 590 := by
    rw [hSsm]; exact sm_frame_590_self initSM
  have hpm590 : Spm 590 = denoteGraph pm_goal_22 Spm 590 := by
    rw [denote_pm_goal_22_590]
    rw [hSpm]; exact pm_frame_590_self initPM
  rw [hnr] at hcut
  simp only [goal_22, List.map] at hcut ⊢
  rw [hsmf, hpm590]
  exact hcut

theorem goal_22_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_22 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_22_stmt := goal_22_cut_to_full prove_goal_22_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
