/- goal_38 桥 (prereqs=[2..30,33,257,259,261,263,265,267,269,271,279], 39 个)。
   FW_view replicated 结构 (同 goal_34/goal_36, 无 collective, single-tp)。
   SM=FW_view(611)→616 (sm node 39, params=[1,8,4,8], reshape [1,8,32]→[1,8,4,8])。
   PM=4×FW_view(611)→616 (pm node 240/241/242/243, ranks 0/1/2/3, 复制同一个 op,
      非 sharding——4 个 rank 各自把同一个输入 611 reshape 成同样输出)。
   611=goal_33 输出 [1,8,32] (single-tp, reconstructWithDim_singleton)。
   single-tp 输出 (goal_38.tps=[{0,616}]): PM frame 挂 foldl 最后写者 node 243 (rank-3)。
   bridge 只做 frame (把 mini-graph 计算挂到 full sm/pm 上); fw_view reshape 语义在
   prove_goal_38_cut 已处理。 -/
import denote.gpt_ly4_regen.Goal37Bridge
import denote.gpt_ly4_regen.Goal33Bridge
import denote.gpt_ly4_regen.Goal_38

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_38 算 616 (FW_view) ==========
theorem denote_sm_goal_38_616 (s : Store) :
    denoteGraph sm_goal_38 s 616 = fw_view [1, 8, 4, 8] (s 611) := by
  simp only [sm_goal_38, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_38 算 616 (4×FW_view 复制, foldl 最后写者 = rank-3) ==========
theorem denote_pm_goal_38_616 (s : Store) :
    denoteGraph pm_goal_38 s 616 = fw_view [1, 8, 4, 8] (s 611) := by
  simp only [pm_goal_38, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 611 (by decide),
      applyNode_skip _ _ _ 611 (by decide),
      applyNode_skip _ _ _ 611 (by decide)]

-- ========== SM self-frame: full sm 算 616 (node 39 FW_view) ==========
theorem sm_frame_616_self (initSM : Store) :
    denoteGraph sm initSM 616 = denoteGraph sm_goal_38 (denoteGraph sm initSM) 616 := by
  rw [denote_sm_goal_38_616]
  rw [sm_val initSM 39 616 (by native_decide) (by native_decide)]
  rw [show sm.nodes[39]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [611], outs := [616], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 39 611 (by native_decide)]

-- ========== PM self-frame: full pm 算 616 (foldl 最后写者 = node 243 rank-3 FW_view) ==========
theorem pm_frame_616_self (initPM : Store) :
    denoteGraph pm initPM 616 = denoteGraph pm_goal_38 (denoteGraph pm initPM) 616 := by
  rw [denote_pm_goal_38_616]
  rw [pm_val initPM 243 616 (by native_decide) (by native_decide)]
  rw [show pm.nodes[243]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [611], outs := [616], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 243 611 (by native_decide)]

-- ========== 总装 ==========
theorem goal_38_cut_to_full (h : goal_38_stmt_cut) : goal_38_stmt := by
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
  have hg33 := goal_33_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_38.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_38.numRanks goal_38_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_38_cut_initGoals, goal_38_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg33
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg279
  -- SM input shape: 611 = goal_33.ts [1,8,32]
  have h611_smsh : (Ssm 611).shape = [1, 8, 32] := by
    have h := hg33.1; simp only [goal_33] at h; exact h
  -- PM input shape: 611 = goal_33.tps rank-0 [1,8,32] (single-tp)
  have h611_pmsh : (Spm 611).shape = [1, 8, 32] := by
    have h := hg33.2.1
    simp only [goal_33, List.map, List.cons.injEq, and_true] at h
    exact h
  have hSM38 : StoreShapesHold Ssm sm_goal_38InitEnv := by
    intro tid sh hsh
    rw [sm_goal_38InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_38InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h611_smsh
  have hPM38 : StoreShapesHold Spm pm_goal_38InitEnv := by
    intro tid sh hsh
    rw [pm_goal_38InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_38InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h611_pmsh
  have hcut := h Ssm Spm hSM38 hPM38 hInitCut
  -- Frame: 616 (sm node 39), 616 (pm last-writer node 243)
  have hsmf : Ssm 616 = denoteGraph sm_goal_38 Ssm 616 := by
    rw [hSsm]; exact sm_frame_616_self initSM
  have hpmf : Spm 616 = denoteGraph pm_goal_38 Spm 616 := by
    rw [hSpm]; exact pm_frame_616_self initPM
  rw [hnr] at hcut
  simp only [goal_38, List.map] at hcut ⊢
  rw [hsmf, hpmf]
  exact hcut

theorem goal_38_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_38 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_38_stmt := goal_38_cut_to_full prove_goal_38_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_38] using this

end TrainVerify.Denote.GeneratedGoals
