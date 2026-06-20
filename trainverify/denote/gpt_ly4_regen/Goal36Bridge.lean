/- goal_36 桥 (prereqs=[2..30,32,257,259,261,263,265,267,269,271,277], 39 个)。
   第 25 种结构 (FW_view replicated, 无 collective)。
   SM=FW_view(609)→614 (sm node 38, params=[1,8,4,8], reshape [1,8,32]→[1,8,4,8])。
   PM=4×FW_view(609)→614 (pm node 227/228/229/230, ranks 0/1/2/3, 复制同一个 op,
      非 sharding——4 个 rank 各自把同一个输入 609 reshape 成同样输出)。
   609=goal_32 输出 [1,8,32] (single-tp, reconstructWithDim_singleton)。
   single-tp 输出 (goal_36.tps=[{0,614}]), reconstructWithDim_singleton: PM 只取 rank-0 节点 227。
   最简单的 single-tp 无 collective 结构: SM/PM 都直接是一个 FW_view, 输出经 singleton 重构。
   bridge 只做 frame (把 mini-graph 计算挂到 full sm/pm 上)。
   注: fw_view 语义 (reshape) 在 prove_goal_36_cut 里已处理; bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal35Bridge
import denote.gpt_ly4_regen.Goal32Bridge
import denote.gpt_ly4_regen.Goal277Bridge
import denote.gpt_ly4_regen.Goal_36

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_36 算 614 (FW_view) ==========
theorem denote_sm_goal_36_614 (s : Store) :
    denoteGraph sm_goal_36 s 614 = fw_view [1, 8, 4, 8] (s 609) := by
  simp only [sm_goal_36, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_36 算 614 (4×FW_view 复制, foldl 最后写者 = rank-3) ==========
-- 4 个 rank 都把同一个 609 reshape 成同样输出; foldl 最后写者 (rank-3) 决定 614 的值,
-- 但所有 rank 算出的 fw_view [1,8,4,8] (s 609) 完全相同 (同 prove_goal_36_cut 的 hpm)。
theorem denote_pm_goal_36_614 (s : Store) :
    denoteGraph pm_goal_36 s 614 = fw_view [1, 8, 4, 8] (s 609) := by
  simp only [pm_goal_36, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 609 (by decide),
      applyNode_skip _ _ _ 609 (by decide),
      applyNode_skip _ _ _ 609 (by decide)]

-- ========== SM self-frame: full sm 算 614 (node 38 FW_view) ==========
theorem sm_frame_614_self (initSM : Store) :
    denoteGraph sm initSM 614 = denoteGraph sm_goal_36 (denoteGraph sm initSM) 614 := by
  rw [denote_sm_goal_36_614]
  rw [sm_val initSM 38 614 (by native_decide) (by native_decide)]
  rw [show sm.nodes[38]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [609], outs := [614], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 38 609 (by native_decide)]

-- ========== PM self-frame: full pm 算 614 (foldl 最后写者 = node 230 rank-3 FW_view) ==========
-- 4 个 rank (node 227/228/229/230) 都写 614; foldl 最后写者是 node 230。
-- node 230 以后无节点写 614; node 230 起无节点写 609。所有 rank 值相同。
theorem pm_frame_614_self (initPM : Store) :
    denoteGraph pm initPM 614 = denoteGraph pm_goal_36 (denoteGraph pm initPM) 614 := by
  rw [denote_pm_goal_36_614]
  rw [pm_val initPM 230 614 (by native_decide) (by native_decide)]
  rw [show pm.nodes[230]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [609], outs := [614], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 230 609 (by native_decide)]

-- ========== 总装 ==========
theorem goal_36_cut_to_full (h : goal_36_stmt_cut) : goal_36_stmt := by
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
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg32 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg277 hinitC
  have hnr : pm_goal_36.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_36.numRanks goal_36_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_36_cut_initGoals, goal_36_prereqs, List.mem_append] at hg
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
      · exact hg32
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg277
  -- SM input shape: 609 = goal_32.ts [1,8,32]
  have h609_smsh : (Ssm 609).shape = [1, 8, 32] := by
    have h := hg32.1; simp only [goal_32] at h; exact h
  -- PM input shape: 609 = goal_32.tps rank-0 [1,8,32] (single-tp)
  have h609_pmsh : (Spm 609).shape = [1, 8, 32] := by
    have h := hg32.2.1
    simp only [goal_32, List.map, List.cons.injEq, and_true] at h
    exact h
  have hSM36 : StoreShapesHold Ssm sm_goal_36InitEnv := by
    intro tid sh hsh
    rw [sm_goal_36InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_36InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h609_smsh
  have hPM36 : StoreShapesHold Spm pm_goal_36InitEnv := by
    intro tid sh hsh
    rw [pm_goal_36InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_36InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h609_pmsh
  have hcut := h Ssm Spm hSM36 hPM36 hInitCut
  -- Frame: 614 (sm node 38), 614 (pm node 227)
  have hsmf : Ssm 614 = denoteGraph sm_goal_36 Ssm 614 := by
    rw [hSsm]; exact sm_frame_614_self initSM
  have hpmf : Spm 614 = denoteGraph pm_goal_36 Spm 614 := by
    rw [hSpm]; exact pm_frame_614_self initPM
  rw [hnr] at hcut
  simp only [goal_36, List.map] at hcut ⊢
  rw [hsmf, hpmf]
  exact hcut

theorem goal_36_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_36 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_36_stmt := goal_36_cut_to_full prove_goal_36_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
