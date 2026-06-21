/- goal_61 桥 (prereqs=[2..55,57,257-285 odd,291], 71 个)。
   FW_view replicated 结构 (同 goal_34/36/38/59, 无 collective, single-tp)。
   SM=FW_view(644)→649 (sm node 66, params=[1,8,4,8], reshape [1,8,32]→[1,8,4,8])。
   PM=4×FW_view(644)→649 (pm node 425/426/427/428, ranks 0/1/2/3, 复制同一个 op,
      非 sharding——4 个 rank 各自把同一个输入 644 reshape 成同样输出)。
   644=goal_57 输出 [1,8,32] (single-tp, reconstructWithDim_singleton)。
   single-tp 输出 (goal_61.tps=[{0,649}]): PM frame 挂 foldl 最后写者 node 428 (rank-3)。
   bridge 只做 frame; fw_view reshape 语义在 prove_goal_61_cut 已处理。
   1:1 twin of Goal59Bridge (input 642→644, output 647→649, upstream goal_56→goal_57,
   sm node 65→66, pm node 424→428, prereq goal_56→goal_57 & goal_289→goal_291). -/
import denote.gpt_ly4_regen.Goal57Bridge
import denote.gpt_ly4_regen.Goal_61

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_61 算 649 (FW_view) ==========
theorem denote_sm_goal_61_649 (s : Store) :
    denoteGraph sm_goal_61 s 649 = fw_view [1, 8, 4, 8] (s 644) := by
  simp only [sm_goal_61, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_61 算 649 (4×FW_view 复制, foldl 最后写者 = rank-3) ==========
theorem denote_pm_goal_61_649 (s : Store) :
    denoteGraph pm_goal_61 s 649 = fw_view [1, 8, 4, 8] (s 644) := by
  simp only [pm_goal_61, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 644 (by decide),
      applyNode_skip _ _ _ 644 (by decide),
      applyNode_skip _ _ _ 644 (by decide)]

-- ========== SM self-frame: full sm 算 649 (node 66 FW_view) ==========
theorem sm_frame_649_self (initSM : Store) :
    denoteGraph sm initSM 649 = denoteGraph sm_goal_61 (denoteGraph sm initSM) 649 := by
  rw [denote_sm_goal_61_649]
  rw [sm_val initSM 66 649 (by native_decide) (by native_decide)]
  rw [show sm.nodes[66]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [644], outs := [649], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 66 644 (by native_decide)]

-- ========== PM self-frame: full pm 算 649 (foldl 最后写者 = node 428 rank-3 FW_view) ==========
theorem pm_frame_649_self (initPM : Store) :
    denoteGraph pm initPM 649 = denoteGraph pm_goal_61 (denoteGraph pm initPM) 649 := by
  rw [denote_pm_goal_61_649]
  rw [pm_val initPM 428 649 (by native_decide) (by native_decide)]
  rw [show pm.nodes[428]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [644], outs := [649], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 428 644 (by native_decide)]

-- ========== 总装 ==========
theorem goal_61_cut_to_full (h : goal_61_stmt_cut) : goal_61_stmt := by
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
  have hg51 := goal_51_intermediate initSM initPM hSM hPM hInit
  have hg52 := goal_52_intermediate initSM initPM hSM hPM hInit
  have hg53 := goal_53_intermediate initSM initPM hSM hPM hInit
  have hg54 := goal_54_intermediate initSM initPM hSM hPM hInit
  have hg55 := goal_55_intermediate initSM initPM hSM hPM hInit
  have hg57 := goal_57_intermediate initSM initPM hSM hPM hInit
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
  have hg283 := goal_283_intermediate initSM initPM hSM hPM hInit
  have hg285 := goal_285_intermediate initSM initPM hSM hPM hInit
  have hg291 := goal_291_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg55 hg57 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hg291 hinitC
  have hnr : pm_goal_61.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_61.numRanks goal_61_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_61_cut_initGoals, goal_61_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg50, hg51, hg52, hg53, hg54, hg55, hg57, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, hg281, hg283, hg285, hg291, List.forall_mem_nil _⟩
  -- SM input shape: 644 = goal_57.ts [1,8,32]
  have h644_smsh : (Ssm 644).shape = [1, 8, 32] := by
    have h := hg57.1; simp only [goal_57] at h; exact h
  -- PM input shape: 644 = goal_57.tps rank-0 [1,8,32] (single-tp)
  have h644_pmsh : (Spm 644).shape = [1, 8, 32] := by
    have h := hg57.2.1
    simp only [goal_57, List.map, List.cons.injEq, and_true] at h
    exact h
  have hSM61 : StoreShapesHold Ssm sm_goal_61InitEnv := by
    intro tid sh hsh
    rw [sm_goal_61InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_61InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h644_smsh
  have hPM61 : StoreShapesHold Spm pm_goal_61InitEnv := by
    intro tid sh hsh
    rw [pm_goal_61InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_61InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h644_pmsh
  have hcut := h Ssm Spm hSM61 hPM61 hInitCut
  -- Frame: 649 (sm node 66), 649 (pm last-writer node 428)
  have hsmf : Ssm 649 = denoteGraph sm_goal_61 Ssm 649 := by
    rw [hSsm]; exact sm_frame_649_self initSM
  have hpmf : Spm 649 = denoteGraph pm_goal_61 Spm 649 := by
    rw [hSpm]; exact pm_frame_649_self initPM
  rw [hnr] at hcut
  simp only [goal_61, List.map] at hcut ⊢
  rw [hsmf, hpmf]
  exact hcut

theorem goal_61_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_61 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_61_stmt := goal_61_cut_to_full prove_goal_61_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
