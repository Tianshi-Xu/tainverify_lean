/- goal_43 桥 (prereqs 48 个)。
   结构: 单输入 pointwise op (FW_softmax) over dim2-shard, **无 collective**。
   SM: FW_softmax(620)→621 (sm node 46)。620=goal_42 输出 (dim2-gather, shape [1,4,8,8])。
   PM: 4×FW_softmax(1909+r)→1929-1932 (pm node 296-299)。tps=4个, gatherDim=2。
       上游 1909-1912 = goal_42 输出 (FW_div over AllToAll), 不需 pm_full（直接是已有 tid）。
   核心语义(fw_softmax distributes over allGatherPrimDimN dim2)已在 prove_goal_43_cut 处理,
   bridge 只做 frame。比 goal_42 简单: 无 AllToAll 层, PM frame 直接落到 1909-1912。
   套 Goal42Bridge 模板, 去掉 AllToAll pm_full_*, FW_div→FW_softmax (无 scalar param)。 -/
import denote.gpt_ly4_regen.Goal42Bridge
import denote.gpt_ly4_regen.Goal_43

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

-- ========== 迷你图 pm_goal_43 算 1929-1932 (4×FW_softmax) ==========
theorem denote_pm_goal_43_1932 (s : Store) :
    denoteGraph pm_goal_43 s 1932 = fw_softmax (s 1912) := by
  simp only [pm_goal_43, denoteGraph, List.foldl]
  rw [applyNode_fw_softmax_out_g43]; congr 1

theorem denote_pm_goal_43_1931 (s : Store) :
    denoteGraph pm_goal_43 s 1931 = fw_softmax (s 1911) := by
  simp only [pm_goal_43, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_softmax_out_g43]; congr 1

theorem denote_pm_goal_43_1930 (s : Store) :
    denoteGraph pm_goal_43 s 1930 = fw_softmax (s 1910) := by
  simp only [pm_goal_43, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_softmax_out_g43]; congr 1

theorem denote_pm_goal_43_1929 (s : Store) :
    denoteGraph pm_goal_43 s 1929 = fw_softmax (s 1909) := by
  simp only [pm_goal_43, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_softmax_out_g43]

-- ========== SM self-frame: full sm 算 621 (node 46 FW_softmax) ==========
theorem sm_frame_621_self (initSM : Store) :
    denoteGraph sm initSM 621 = denoteGraph sm_goal_43 (denoteGraph sm initSM) 621 := by
  have hsm : denoteGraph sm_goal_43 (denoteGraph sm initSM) 621
      = fw_softmax (denoteGraph sm initSM 620) := by
    simp only [sm_goal_43, denoteGraph, List.foldl]
    rw [applyNode_fw_softmax_out_g43]
  rw [hsm]
  rw [sm_val initSM 46 621 (by native_decide) (by native_decide)]
  rw [show sm.nodes[46]'(by native_decide)
      = { rank := 0, op := "OpName.FW_softmax", ins := [620], outs := [621] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g43]
  rw [sm_prefix_eq initSM 46 620 (by native_decide)]

-- ========== full pm: FW_softmax 输出 1929-1932 (node 296-299) ==========
-- 上游 1909-1912 是 goal_42 的 tid（已存在于 pm 中），直接 prefix_eq 即可。
theorem pm_frame_1929_self (initPM : Store) :
    denoteGraph pm initPM 1929 = fw_softmax (denoteGraph pm initPM 1909) := by
  rw [pm_val initPM 296 1929 (by native_decide) (by native_decide)]
  rw [show pm.nodes[296]'(by native_decide)
      = { rank := 0, op := "OpName.FW_softmax", ins := [1909], outs := [1929] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g43]
  rw [pm_prefix_eq initPM 296 1909 (by native_decide)]

theorem pm_frame_1930_self (initPM : Store) :
    denoteGraph pm initPM 1930 = fw_softmax (denoteGraph pm initPM 1910) := by
  rw [pm_val initPM 297 1930 (by native_decide) (by native_decide)]
  rw [show pm.nodes[297]'(by native_decide)
      = { rank := 1, op := "OpName.FW_softmax", ins := [1910], outs := [1930] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g43]
  rw [pm_prefix_eq initPM 297 1910 (by native_decide)]

theorem pm_frame_1931_self (initPM : Store) :
    denoteGraph pm initPM 1931 = fw_softmax (denoteGraph pm initPM 1911) := by
  rw [pm_val initPM 298 1931 (by native_decide) (by native_decide)]
  rw [show pm.nodes[298]'(by native_decide)
      = { rank := 2, op := "OpName.FW_softmax", ins := [1911], outs := [1931] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g43]
  rw [pm_prefix_eq initPM 298 1911 (by native_decide)]

theorem pm_frame_1932_self (initPM : Store) :
    denoteGraph pm initPM 1932 = fw_softmax (denoteGraph pm initPM 1912) := by
  rw [pm_val initPM 299 1932 (by native_decide) (by native_decide)]
  rw [show pm.nodes[299]'(by native_decide)
      = { rank := 3, op := "OpName.FW_softmax", ins := [1912], outs := [1932] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g43]
  rw [pm_prefix_eq initPM 299 1912 (by native_decide)]

-- ========== PM self-frame: 1929-1932 to mini ==========
theorem pm_frame_1929_to_mini (initPM : Store) :
    denoteGraph pm initPM 1929 = denoteGraph pm_goal_43 (denoteGraph pm initPM) 1929 := by
  rw [denote_pm_goal_43_1929, pm_frame_1929_self]

theorem pm_frame_1930_to_mini (initPM : Store) :
    denoteGraph pm initPM 1930 = denoteGraph pm_goal_43 (denoteGraph pm initPM) 1930 := by
  rw [denote_pm_goal_43_1930, pm_frame_1930_self]

theorem pm_frame_1931_to_mini (initPM : Store) :
    denoteGraph pm initPM 1931 = denoteGraph pm_goal_43 (denoteGraph pm initPM) 1931 := by
  rw [denote_pm_goal_43_1931, pm_frame_1931_self]

theorem pm_frame_1932_to_mini (initPM : Store) :
    denoteGraph pm initPM 1932 = denoteGraph pm_goal_43 (denoteGraph pm initPM) 1932 := by
  rw [denote_pm_goal_43_1932, pm_frame_1932_self]

-- ========== 总装 ==========
theorem goal_43_cut_to_full (h : goal_43_stmt_cut) : goal_43_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
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
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg41 := goal_41_intermediate initSM initPM hSM hPM hInit
  have hg42 := goal_42_intermediate initSM initPM hSM hPM hInit
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
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_43.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_43.numRanks goal_43_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_43_cut_initGoals, goal_43_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg34
      · exact hg35
      · exact hg36
      · exact hg37
      · exact hg40
      · exact hg41
      · exact hg42
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
  -- shape: 620 = goal_42.ts (singleton on SM), shape [1,4,8,8]; 1909-1912 = goal_42.tps, each [1,4,2,8]
  have h620_smsh : (Ssm 620).shape = [1, 4, 8, 8] := by
    have h := hg42.1; simp only [goal_42] at h; exact h
  have hpmsh : (Spm 1909).shape = [1,4,2,8] ∧ (Spm 1910).shape = [1,4,2,8] ∧
               (Spm 1911).shape = [1,4,2,8] ∧ (Spm 1912).shape = [1,4,2,8] := by
    have h := hg42.2.1
    simp only [goal_42, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1909sh, h1910sh, h1911sh, h1912sh⟩ := hpmsh
  have hSM43 : StoreShapesHold Ssm sm_goal_43InitEnv := by
    intro tid sh hsh
    rw [sm_goal_43InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_43InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h620_smsh
  have hPM43 : StoreShapesHold Spm pm_goal_43InitEnv := by
    intro tid sh hsh
    rw [pm_goal_43InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_43InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1909sh
    · exact h1910sh
    · exact h1911sh
    · exact h1912sh
  have hcut := h Ssm Spm hSM43 hPM43 hInitCut
  have hsmf : Ssm 621 = denoteGraph sm_goal_43 Ssm 621 := by
    rw [hSsm]; exact sm_frame_621_self initSM
  have hpm1929 : Spm 1929 = denoteGraph pm_goal_43 Spm 1929 := by
    rw [hSpm]; exact pm_frame_1929_to_mini initPM
  have hpm1930 : Spm 1930 = denoteGraph pm_goal_43 Spm 1930 := by
    rw [hSpm]; exact pm_frame_1930_to_mini initPM
  have hpm1931 : Spm 1931 = denoteGraph pm_goal_43 Spm 1931 := by
    rw [hSpm]; exact pm_frame_1931_to_mini initPM
  have hpm1932 : Spm 1932 = denoteGraph pm_goal_43 Spm 1932 := by
    rw [hSpm]; exact pm_frame_1932_to_mini initPM
  rw [hnr] at hcut
  simp only [goal_43, List.map] at hcut ⊢
  rw [hsmf, hpm1929, hpm1930, hpm1931, hpm1932]
  exact hcut

theorem goal_43_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_43 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_43_stmt := goal_43_cut_to_full prove_goal_43_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_43] using this

end TrainVerify.Denote.GeneratedGoals
