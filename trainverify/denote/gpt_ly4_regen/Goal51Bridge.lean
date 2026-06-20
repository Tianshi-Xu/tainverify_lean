/- goal_51 桥 (prereqs=[2..50,257,259,261,263,265,267,269,271,273,275,277,279,281] = 62)。
   第N种结构: column-parallel FW_linear, multi-tps gatherDim=2, no follow-on collective。
   SM=FW_linear(631,632)→633 (node 55, [1,8,128])。
   PM=4×FW_linear(631,2113+r)→2117+r (node 363-366, 各 rank 一份 tp, 各 [1,8,32]).
      数据输入 631 在每个 rank 共享 (replicated, 来自 goal_50 single-tp [1,8,32]);
      weight 2113-2116 来自 initGoal_632 (column-sharded [128,32]→4×[32,32]).
   multi-tps 输出, gatherDim=2 (reconstruct dim2: 4×[1,8,32] → [1,8,128]);
   PM mini-graph 无 collective (weight 已分片, data 共享)。
   与 Goal30Bridge 同构 (multi-tps, no collective tail), 仅:
     (a) 算子 ternary FW_layernorm → binary FW_linear (2 输入: shared data + per-rank weight);
     (b) 每 rank 数据输入从 per-rank 分片 (1661-1664) 换成共享 631 (goal_50 single-tp);
     (c) per-rank 第二输入从复制 weight/bias 换成分片 weight 2113-2116 (initGoal_632);
     (d) gatherDim 1 → 2。
   语义 (fw_linear column-parallel: 共享 X 对每 rank 列分片 W 分别算 + dim2 拼接 = 全 W 的 fw_linear)
   已在 prove_goal_51_cut 里处理 (fw_linear_column_parallel_4_1_8_32_32), bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal50Bridge
import denote.gpt_ly4_regen.Goal_51

set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Silence noisy cosmetic/convention linters (same rationale as Goal30/50Bridge):
-- native_decide is the sanctioned graph-lookup convention; auto-generated frame
-- produces many style/unused diagnostics that do not affect soundness.
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_51 算 633 (FW_linear 631,632) ==========
theorem denote_sm_goal_51_633 (s : Store) :
    denoteGraph sm_goal_51 s 633 = fw_linear (s 631) (s 632) := by
  simp only [sm_goal_51, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_51 算 2117-2120 (4×FW_linear, 共享 631 + per-rank weight) ==========
theorem denote_pm_goal_51_2117 (s : Store) :
    denoteGraph pm_goal_51 s 2117 = fw_linear (s 631) (s 2113) := by
  simp only [pm_goal_51, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]

theorem denote_pm_goal_51_2118 (s : Store) :
    denoteGraph pm_goal_51 s 2118 = fw_linear (s 631) (s 2114) := by
  simp only [pm_goal_51, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_51_2119 (s : Store) :
    denoteGraph pm_goal_51 s 2119 = fw_linear (s 631) (s 2115) := by
  simp only [pm_goal_51, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_51_2120 (s : Store) :
    denoteGraph pm_goal_51 s 2120 = fw_linear (s 631) (s 2116) := by
  simp only [pm_goal_51, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 633 (node 55 FW_linear) ==========
theorem sm_frame_633_self (initSM : Store) :
    denoteGraph sm initSM 633 = denoteGraph sm_goal_51 (denoteGraph sm initSM) 633 := by
  rw [denote_sm_goal_51_633]
  rw [sm_val initSM 55 633 (by native_decide) (by native_decide)]
  rw [show sm.nodes[55]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [631, 632], outs := [633] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 55 631 (by native_decide),
      sm_prefix_eq initSM 55 632 (by native_decide)]

-- ========== PM self-frame: 2117-2120 (4×FW_linear, node 363-366) ==========
theorem pm_frame_2117_self (initPM : Store) :
    denoteGraph pm initPM 2117
      = fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2113) := by
  rw [pm_val initPM 363 2117 (by native_decide) (by native_decide)]
  rw [show pm.nodes[363]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [631, 2113], outs := [2117] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 363 631 (by native_decide),
      pm_prefix_eq initPM 363 2113 (by native_decide)]

theorem pm_frame_2118_self (initPM : Store) :
    denoteGraph pm initPM 2118
      = fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2114) := by
  rw [pm_val initPM 364 2118 (by native_decide) (by native_decide)]
  rw [show pm.nodes[364]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [631, 2114], outs := [2118] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 364 631 (by native_decide),
      pm_prefix_eq initPM 364 2114 (by native_decide)]

theorem pm_frame_2119_self (initPM : Store) :
    denoteGraph pm initPM 2119
      = fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2115) := by
  rw [pm_val initPM 365 2119 (by native_decide) (by native_decide)]
  rw [show pm.nodes[365]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [631, 2115], outs := [2119] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 365 631 (by native_decide),
      pm_prefix_eq initPM 365 2115 (by native_decide)]

theorem pm_frame_2120_self (initPM : Store) :
    denoteGraph pm initPM 2120
      = fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2116) := by
  rw [pm_val initPM 366 2120 (by native_decide) (by native_decide)]
  rw [show pm.nodes[366]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [631, 2116], outs := [2120] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 366 631 (by native_decide),
      pm_prefix_eq initPM 366 2116 (by native_decide)]

-- ========== helper: hInitCut 分离成独立 lemma 避免单次 heartbeat 超时 (62 prereqs) ==========
lemma goal_51_hInitCut_helper (Ssm Spm : Store)
    (hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm)
    (hg2 : InitGoalHolds pm.numRanks goal_2 Ssm Spm)
    (hg3 : InitGoalHolds pm.numRanks goal_3 Ssm Spm)
    (hg4 : InitGoalHolds pm.numRanks goal_4 Ssm Spm)
    (hg5 : InitGoalHolds pm.numRanks goal_5 Ssm Spm)
    (hg6 : InitGoalHolds pm.numRanks goal_6 Ssm Spm)
    (hg7 : InitGoalHolds pm.numRanks goal_7 Ssm Spm)
    (hg8 : InitGoalHolds pm.numRanks goal_8 Ssm Spm)
    (hg9 : InitGoalHolds pm.numRanks goal_9 Ssm Spm)
    (hg10 : InitGoalHolds pm.numRanks goal_10 Ssm Spm)
    (hg11 : InitGoalHolds pm.numRanks goal_11 Ssm Spm)
    (hg12 : InitGoalHolds pm.numRanks goal_12 Ssm Spm)
    (hg13 : InitGoalHolds pm.numRanks goal_13 Ssm Spm)
    (hg14 : InitGoalHolds pm.numRanks goal_14 Ssm Spm)
    (hg15 : InitGoalHolds pm.numRanks goal_15 Ssm Spm)
    (hg16 : InitGoalHolds pm.numRanks goal_16 Ssm Spm)
    (hg17 : InitGoalHolds pm.numRanks goal_17 Ssm Spm)
    (hg18 : InitGoalHolds pm.numRanks goal_18 Ssm Spm)
    (hg19 : InitGoalHolds pm.numRanks goal_19 Ssm Spm)
    (hg20 : InitGoalHolds pm.numRanks goal_20 Ssm Spm)
    (hg21 : InitGoalHolds pm.numRanks goal_21 Ssm Spm)
    (hg22 : InitGoalHolds pm.numRanks goal_22 Ssm Spm)
    (hg23 : InitGoalHolds pm.numRanks goal_23 Ssm Spm)
    (hg24 : InitGoalHolds pm.numRanks goal_24 Ssm Spm)
    (hg25 : InitGoalHolds pm.numRanks goal_25 Ssm Spm)
    (hg26 : InitGoalHolds pm.numRanks goal_26 Ssm Spm)
    (hg27 : InitGoalHolds pm.numRanks goal_27 Ssm Spm)
    (hg28 : InitGoalHolds pm.numRanks goal_28 Ssm Spm)
    (hg29 : InitGoalHolds pm.numRanks goal_29 Ssm Spm)
    (hg30 : InitGoalHolds pm.numRanks goal_30 Ssm Spm)
    (hg31 : InitGoalHolds pm.numRanks goal_31 Ssm Spm)
    (hg32 : InitGoalHolds pm.numRanks goal_32 Ssm Spm)
    (hg33 : InitGoalHolds pm.numRanks goal_33 Ssm Spm)
    (hg34 : InitGoalHolds pm.numRanks goal_34 Ssm Spm)
    (hg35 : InitGoalHolds pm.numRanks goal_35 Ssm Spm)
    (hg36 : InitGoalHolds pm.numRanks goal_36 Ssm Spm)
    (hg37 : InitGoalHolds pm.numRanks goal_37 Ssm Spm)
    (hg38 : InitGoalHolds pm.numRanks goal_38 Ssm Spm)
    (hg39 : InitGoalHolds pm.numRanks goal_39 Ssm Spm)
    (hg40 : InitGoalHolds pm.numRanks goal_40 Ssm Spm)
    (hg41 : InitGoalHolds pm.numRanks goal_41 Ssm Spm)
    (hg42 : InitGoalHolds pm.numRanks goal_42 Ssm Spm)
    (hg43 : InitGoalHolds pm.numRanks goal_43 Ssm Spm)
    (hg44 : InitGoalHolds pm.numRanks goal_44 Ssm Spm)
    (hg45 : InitGoalHolds pm.numRanks goal_45 Ssm Spm)
    (hg46 : InitGoalHolds pm.numRanks goal_46 Ssm Spm)
    (hg47 : InitGoalHolds pm.numRanks goal_47 Ssm Spm)
    (hg48 : InitGoalHolds pm.numRanks goal_48 Ssm Spm)
    (hg49 : InitGoalHolds pm.numRanks goal_49 Ssm Spm)
    (hg50 : InitGoalHolds pm.numRanks goal_50 Ssm Spm)
    (hg257 : InitGoalHolds pm.numRanks goal_257 Ssm Spm)
    (hg259 : InitGoalHolds pm.numRanks goal_259 Ssm Spm)
    (hg261 : InitGoalHolds pm.numRanks goal_261 Ssm Spm)
    (hg263 : InitGoalHolds pm.numRanks goal_263 Ssm Spm)
    (hg265 : InitGoalHolds pm.numRanks goal_265 Ssm Spm)
    (hg267 : InitGoalHolds pm.numRanks goal_267 Ssm Spm)
    (hg269 : InitGoalHolds pm.numRanks goal_269 Ssm Spm)
    (hg271 : InitGoalHolds pm.numRanks goal_271 Ssm Spm)
    (hg273 : InitGoalHolds pm.numRanks goal_273 Ssm Spm)
    (hg275 : InitGoalHolds pm.numRanks goal_275 Ssm Spm)
    (hg277 : InitGoalHolds pm.numRanks goal_277 Ssm Spm)
    (hg279 : InitGoalHolds pm.numRanks goal_279 Ssm Spm)
    (hg281 : InitGoalHolds pm.numRanks goal_281 Ssm Spm) :
    InitGoalsHold pm_goal_51.numRanks goal_51_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_51.numRanks = pm.numRanks := by native_decide
  rw [hnr]; intro g hg
  simp only [goal_51_cut_initGoals, goal_51_prereqs, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hinitC g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact hg47
    · exact hg48
    · exact hg49
    · exact hg50
    · exact hg257
    · exact hg259
    · exact hg261
    · exact hg263
    · exact hg265
    · exact hg267
    · exact hg269
    · exact hg271
    · exact hg273
    · exact hg275
    · exact hg277
    · exact hg279
    · exact hg281

-- ========== 总装: goal_51_cut_to_full ==========
theorem goal_51_cut_to_full (h : goal_51_stmt_cut) : goal_51_stmt := by
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
  have hg47 := goal_47_intermediate initSM initPM hSM hPM hInit
  have hg48 := goal_48_intermediate initSM initPM hSM hPM hInit
  have hg49 := goal_49_intermediate initSM initPM hSM hPM hInit
  have hg50 := goal_50_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg273 := goal_273_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hg281 := goal_281_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hinitC
  have hnr : pm_goal_51.numRanks = pm.numRanks := by native_decide
  -- 631 = goal_50.ts [1,8,32], single-tp (ts==tid==631), replicated on all PM ranks.
  have h631_smsh : (Ssm 631).shape = [1, 8, 32] := by
    have h := hg50.1; simp only [goal_50] at h; exact h
  have h631_pmsh : (Spm 631).shape = [1, 8, 32] := by
    have h := hg50.2.1; simp only [goal_50, List.map] at h
    have := congrArg List.head? h; simpa using this
  -- 632 weight = initGoal_632 [128,32], column-sharded → 2113-2116 each [32,32].
  have hg632 := hinitC initGoal_632 (by simp only [initGoals]; decide)
  have h632_smsh : (Ssm 632).shape = [128, 32] := by
    have h := hg632.1; simp only [initGoal_632] at h; exact h
  have h632tp := hg632.2.1
  simp only [initGoal_632, List.map, List.cons.injEq, and_true] at h632tp
  obtain ⟨h2113_pmsh, h2114_pmsh, h2115_pmsh, h2116_pmsh⟩ := h632tp
  have hSM51 : StoreShapesHold Ssm sm_goal_51InitEnv := by
    intro tid sh hsh
    rw [sm_goal_51InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_51InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h631_smsh
    · exact h632_smsh
  have hPM51 : StoreShapesHold Spm pm_goal_51InitEnv := by
    intro tid sh hsh
    rw [pm_goal_51InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_51InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h631_pmsh
    · exact h2113_pmsh
    · exact h2114_pmsh
    · exact h2115_pmsh
    · exact h2116_pmsh
  have hInitCut : InitGoalsHold pm_goal_51.numRanks goal_51_cut_initGoals Ssm Spm :=
    goal_51_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281
  have hcut := h Ssm Spm hSM51 hPM51 hInitCut
  -- Frame: 633 (sm), 2117-2120 (pm).
  have hsmf : Ssm 633 = denoteGraph sm_goal_51 Ssm 633 := by
    rw [hSsm]; exact sm_frame_633_self initSM
  have hpm2117 : Spm 2117 = denoteGraph pm_goal_51 Spm 2117 := by
    rw [denote_pm_goal_51_2117]; rw [hSpm]; exact pm_frame_2117_self initPM
  have hpm2118 : Spm 2118 = denoteGraph pm_goal_51 Spm 2118 := by
    rw [denote_pm_goal_51_2118]; rw [hSpm]; exact pm_frame_2118_self initPM
  have hpm2119 : Spm 2119 = denoteGraph pm_goal_51 Spm 2119 := by
    rw [denote_pm_goal_51_2119]; rw [hSpm]; exact pm_frame_2119_self initPM
  have hpm2120 : Spm 2120 = denoteGraph pm_goal_51 Spm 2120 := by
    rw [denote_pm_goal_51_2120]; rw [hSpm]; exact pm_frame_2120_self initPM
  rw [hnr] at hcut
  simp only [goal_51, List.map] at hcut ⊢
  rw [hsmf, hpm2117, hpm2118, hpm2119, hpm2120]
  exact hcut

theorem goal_51_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_51 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_51_stmt := goal_51_cut_to_full prove_goal_51_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals