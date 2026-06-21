/- goal_50 桥 (prereqs=[2..49,257-281 odd])。
   第29种结构: per-rank FW_layernorm (共享 w/b 629/630) + 末尾 AllGatherPrim dim1 → single-tp 631。
   SM=FW_layernorm(977,629,630)→631 (node 54, 1 node)。
   PM=4×FW_layernorm([2081+r,629,630])→2085+r (node 358-361) +
      AllGatherPrim(ins=range(2085..2088),params=[1])→631 (node 362, single output)。
   输入: 977 来自 goal_281 first-output [1,8,32]; tps 2081-2084 来自 goal_281 AllToAll chunk dim1 [1,2,32]。
   共享权重/bias: 629 (gamma [32]) / 630 (beta [32]) 来自 initGoal_629/630 复制。
   核心语义 (fw_layernorm 分配到 allGatherPrimDimN dim1) 已在 prove_goal_50_cut 处理,
   bridge 只做 frame。
   模板: Goal30Bridge[per-rank FW_layernorm 共享 w/b, mini-graph 4×FW_layernorm 每rank独立] +
         Goal46Bridge[末尾 AllGather single-output frame].
   Full pm AllGather ins: ((List.range 4).map (fun r => 2085+r)) → 用 List.range/loop/map simp。
   Mini-graph pm_goal_50 AllGather ins: 字面 [2085,2086,2087,2088] → 只用 List.map simp。
   注意: initGoal_629/630 在 sm/pm 均恒等 (replicated), 取 hW_eq/hB_eq 来自 prove_goal_50_cut。 -/
import denote.gpt_ly4_regen.Goal49Bridge
import denote.gpt_ly4_regen.Goal281Bridge
import denote.gpt_ly4_regen.Goal_50

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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

-- ========== 迷你图 sm_goal_50 算 631 (FW_layernorm 977,629,630) ==========
theorem denote_sm_goal_50_631 (s : Store) :
    denoteGraph sm_goal_50 s 631 = fw_layernorm (s 977) (s 629) (s 630) := by
  simp only [sm_goal_50, denoteGraph, List.foldl]
  rw [applyNode_fw_layernorm_out]

-- ========== 迷你图 pm_goal_50 算 2085-2088 (4×FW_layernorm) ==========
theorem denote_pm_goal_50_2085 (s : Store) :
    denoteGraph pm_goal_50 s 2085 = fw_layernorm (s 2081) (s 629) (s 630) := by
  simp only [pm_goal_50, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]

theorem denote_pm_goal_50_2086 (s : Store) :
    denoteGraph pm_goal_50 s 2086 = fw_layernorm (s 2082) (s 629) (s 630) := by
  simp only [pm_goal_50, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_50_2087 (s : Store) :
    denoteGraph pm_goal_50 s 2087 = fw_layernorm (s 2083) (s 629) (s 630) := by
  simp only [pm_goal_50, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_50_2088 (s : Store) :
    denoteGraph pm_goal_50 s 2088 = fw_layernorm (s 2084) (s 629) (s 630) := by
  simp only [pm_goal_50, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== 迷你图 pm_goal_50 算 631 (AllGather) ==========
theorem denote_pm_goal_50_631 (s : Store) :
    denoteGraph pm_goal_50 s 631
      = allGatherPrimDimN 1 4 0
          [fw_layernorm (s 2081) (s 629) (s 630),
           fw_layernorm (s 2082) (s 629) (s 630),
           fw_layernorm (s 2083) (s 629) (s 630),
           fw_layernorm (s 2084) (s 629) (s 630)] := by
  simp only [pm_goal_50, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full sm 算 631 (node 54 FW_layernorm) ==========
theorem sm_frame_631_self (initSM : Store) :
    denoteGraph sm initSM 631 = denoteGraph sm_goal_50 (denoteGraph sm initSM) 631 := by
  rw [denote_sm_goal_50_631]
  rw [sm_val initSM 54 631 (by native_decide) (by native_decide)]
  rw [show sm.nodes[54]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [977, 629, 630], outs := [631] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [sm_prefix_eq initSM 54 977 (by native_decide),
      sm_prefix_eq initSM 54 629 (by native_decide),
      sm_prefix_eq initSM 54 630 (by native_decide)]

-- ========== full pm: 4×FW_layernorm 输出 2085-2088 (node 358-361) ==========
theorem pm_full_2085 (initPM : Store) :
    denoteGraph pm initPM 2085
      = fw_layernorm (denoteGraph pm initPM 2081)
          (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  rw [pm_val initPM 358 2085 (by native_decide) (by native_decide)]
  rw [show pm.nodes[358]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [2081, 629, 630], outs := [2085] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 358 2081 (by native_decide),
      pm_prefix_eq initPM 358 629 (by native_decide),
      pm_prefix_eq initPM 358 630 (by native_decide)]

theorem pm_full_2086 (initPM : Store) :
    denoteGraph pm initPM 2086
      = fw_layernorm (denoteGraph pm initPM 2082)
          (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  rw [pm_val initPM 359 2086 (by native_decide) (by native_decide)]
  rw [show pm.nodes[359]'(by native_decide)
      = { rank := 1, op := "OpName.FW_layernorm", ins := [2082, 629, 630], outs := [2086] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 359 2082 (by native_decide),
      pm_prefix_eq initPM 359 629 (by native_decide),
      pm_prefix_eq initPM 359 630 (by native_decide)]

theorem pm_full_2087 (initPM : Store) :
    denoteGraph pm initPM 2087
      = fw_layernorm (denoteGraph pm initPM 2083)
          (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  rw [pm_val initPM 360 2087 (by native_decide) (by native_decide)]
  rw [show pm.nodes[360]'(by native_decide)
      = { rank := 2, op := "OpName.FW_layernorm", ins := [2083, 629, 630], outs := [2087] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 360 2083 (by native_decide),
      pm_prefix_eq initPM 360 629 (by native_decide),
      pm_prefix_eq initPM 360 630 (by native_decide)]

theorem pm_full_2088 (initPM : Store) :
    denoteGraph pm initPM 2088
      = fw_layernorm (denoteGraph pm initPM 2084)
          (denoteGraph pm initPM 629) (denoteGraph pm initPM 630) := by
  rw [pm_val initPM 361 2088 (by native_decide) (by native_decide)]
  rw [show pm.nodes[361]'(by native_decide)
      = { rank := 3, op := "OpName.FW_layernorm", ins := [2084, 629, 630], outs := [2088] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 361 2084 (by native_decide),
      pm_prefix_eq initPM 361 629 (by native_decide),
      pm_prefix_eq initPM 361 630 (by native_decide)]

-- ========== PM self-frame: 631 (full = mini via AllGather node 362) ==========
theorem pm_frame_631_self (initPM : Store) :
    denoteGraph pm initPM 631 = denoteGraph pm_goal_50 (denoteGraph pm initPM) 631 := by
  rw [denote_pm_goal_50_631]
  rw [pm_val initPM 362 631 (by native_decide) (by native_decide)]
  rw [show pm.nodes[362]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 2085 + r)), outs := [631], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 362 2085 (by native_decide),
      pm_prefix_eq initPM 362 2086 (by native_decide),
      pm_prefix_eq initPM 362 2087 (by native_decide),
      pm_prefix_eq initPM 362 2088 (by native_decide)]
  rw [pm_full_2085, pm_full_2086, pm_full_2087, pm_full_2088]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== helper: hInitCut (extracted to avoid heartbeat timeout in main theorem) ==========
lemma goal_50_hInitCut_helper (Ssm Spm : Store)
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
    InitGoalsHold pm_goal_50.numRanks goal_50_cut_initGoals Ssm Spm := by
  rw [show pm_goal_50.numRanks = pm.numRanks from by native_decide]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_50_cut_initGoals, goal_50_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, hg281, List.forall_mem_nil _⟩

-- ========== 总装: goal_50_cut_to_full ==========
theorem goal_50_cut_to_full (h : goal_50_stmt_cut) : goal_50_stmt := by
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
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hinitC
  have hnr : pm_goal_50.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_50.numRanks goal_50_cut_initGoals Ssm Spm :=
    goal_50_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281
  -- 977 = goal_281.ts (single-tp on SM, shape [1,8,32]); tps 2081-2084 each [1,2,32]
  have h977_smsh : (Ssm 977).shape = [1, 8, 32] := by
    have h := hg281.1; simp only [goal_281] at h; exact h
  have hpmsh281 : (Spm 2081).shape = [1,2,32] ∧ (Spm 2082).shape = [1,2,32] ∧
                  (Spm 2083).shape = [1,2,32] ∧ (Spm 2084).shape = [1,2,32] := by
    have h := hg281.2.1
    simp only [goal_281, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h2081sh, h2082sh, h2083sh, h2084sh⟩ := hpmsh281
  -- 629 (gamma [32]) / 630 (beta [32]) = initGoal_629/630 (replicated weights).
  have hg629 := hinitC initGoal_629 (by simp only [initGoals]; decide)
  have hg630 := hinitC initGoal_630 (by simp only [initGoals]; decide)
  have h629_smsh : (Ssm 629).shape = [32] := by
    have h := hg629.1; simp only [initGoal_629] at h; exact h
  have h630_smsh : (Ssm 630).shape = [32] := by
    have h := hg630.1; simp only [initGoal_630] at h; exact h
  have h629_pmsh : (Spm 629).shape = [32] := by
    have h := hg629.2.1; simp only [initGoal_629, List.map] at h
    have := congrArg List.head? h; simpa using this
  have h630_pmsh : (Spm 630).shape = [32] := by
    have h := hg630.2.1; simp only [initGoal_630, List.map] at h
    have := congrArg List.head? h; simpa using this
  have hSM50 : StoreShapesHold Ssm sm_goal_50InitEnv := by
    intro tid sh hsh
    rw [sm_goal_50InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_50InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h629_smsh
    · exact h630_smsh
    · exact h977_smsh
  have hPM50 : StoreShapesHold Spm pm_goal_50InitEnv := by
    intro tid sh hsh
    rw [pm_goal_50InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_50InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
               | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h629_pmsh
    · exact h630_pmsh
    · exact h2081sh
    · exact h2082sh
    · exact h2083sh
    · exact h2084sh
  have hcut := h Ssm Spm hSM50 hPM50 hInitCut
  have hsmf : Ssm 631 = denoteGraph sm_goal_50 Ssm 631 := by
    rw [hSsm]; exact sm_frame_631_self initSM
  have hpm631 : Spm 631 = denoteGraph pm_goal_50 Spm 631 := by
    rw [hSpm]; exact pm_frame_631_self initPM
  rw [hnr] at hcut
  simp only [goal_50, List.map] at hcut ⊢
  rw [hsmf, hpm631]
  exact hcut

theorem goal_50_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_50 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_50_stmt := goal_50_cut_to_full prove_goal_50_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
