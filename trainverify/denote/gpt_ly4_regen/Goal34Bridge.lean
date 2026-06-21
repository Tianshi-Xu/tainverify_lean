/- goal_34 桥 (prereqs=[2..31,257,259,261,263,265,267,269,271,275], 39 个)。
   第 25 种结构 (新结构: FW_view replicated, 无 collective)。
   SM=FW_view(607)→612 (sm node 37, params=[1,8,4,8], reshape [1,8,32]→[1,8,4,8])。
   PM=4×FW_view(607)→612 (pm node 232/233/234/235, ranks 0/1/2/3, 复制同一个 op,
      非 sharding——4 个 rank 各自把同一个输入 607 reshape 成同样输出)。
   607=goal_31 输出 [1,8,32] (single-tp, reconstructWithDim_singleton)。
   single-tp 输出 (goal_34.tps=[{0,612}]), reconstructWithDim_singleton: PM 只取 rank-0 节点 232。
   最简单的 single-tp 无 collective 结构: SM/PM 都直接是一个 FW_view, 输出经 singleton 重构。
   bridge 只做 frame (把 mini-graph 计算挂到 full sm/pm 上)。
   注: fw_view 语义 (reshape) 在 prove_goal_34_cut 里已处理; bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal4Bridge
import denote.gpt_ly4_regen.Goal257Bridge
import denote.gpt_ly4_regen.Goal31Bridge
import denote.gpt_ly4_regen.Goal_34

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_34 算 612 (FW_view) ==========
theorem denote_sm_goal_34_612 (s : Store) :
    denoteGraph sm_goal_34 s 612 = fw_view [1, 8, 4, 8] (s 607) := by
  simp only [sm_goal_34, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]

-- ========== 迷你图 pm_goal_34 算 612 (4×FW_view 复制, foldl 最后写者 = rank-3) ==========
-- 4 个 rank 都把同一个 607 reshape 成同样输出; foldl 最后写者 (rank-3) 决定 612 的值,
-- 但所有 rank 算出的 fw_view [1,8,4,8] (s 607) 完全相同 (同 prove_goal_34_cut 的 hpm)。
theorem denote_pm_goal_34_612 (s : Store) :
    denoteGraph pm_goal_34 s 612 = fw_view [1, 8, 4, 8] (s 607) := by
  simp only [pm_goal_34, denoteGraph, List.foldl]
  rw [applyNode_fw_view_out]
  rw [applyNode_skip _ _ _ 607 (by decide),
      applyNode_skip _ _ _ 607 (by decide),
      applyNode_skip _ _ _ 607 (by decide)]

-- ========== SM self-frame: full sm 算 612 (node 37 FW_view) ==========
theorem sm_frame_612_self (initSM : Store) :
    denoteGraph sm initSM 612 = denoteGraph sm_goal_34 (denoteGraph sm initSM) 612 := by
  rw [denote_sm_goal_34_612]
  rw [sm_val initSM 37 612 (by native_decide) (by native_decide)]
  rw [show sm.nodes[37]'(by native_decide)
      = { rank := 0, op := "OpName.FW_view", ins := [607], outs := [612], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [sm_prefix_eq initSM 37 607 (by native_decide)]

-- ========== PM self-frame: full pm 算 612 (foldl 最后写者 = node 235 rank-3 FW_view) ==========
-- 4 个 rank (node 232/233/234/235) 都写 612; foldl 最后写者是 node 235。
-- node 235 以后无节点写 612; node 235 起无节点写 607。所有 rank 值相同。
theorem pm_frame_612_self (initPM : Store) :
    denoteGraph pm initPM 612 = denoteGraph pm_goal_34 (denoteGraph pm initPM) 612 := by
  rw [denote_pm_goal_34_612]
  rw [pm_val initPM 235 612 (by native_decide) (by native_decide)]
  rw [show pm.nodes[235]'(by native_decide)
      = { rank := 3, op := "OpName.FW_view", ins := [607], outs := [612], params := [1, 8, 4, 8] }
      from by native_decide]
  rw [applyNode_fw_view_out]
  rw [pm_prefix_eq initPM 235 607 (by native_decide)]

-- ========== 总装 ==========
theorem goal_34_cut_to_full (h : goal_34_stmt_cut) : goal_34_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hinitC
  have hnr : pm_goal_34.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_34.numRanks goal_34_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_34_cut_initGoals, goal_34_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg275, List.forall_mem_nil _⟩
  -- SM input shape: 607 = goal_31.ts [1,8,32]
  have h607_smsh : (Ssm 607).shape = [1, 8, 32] := by
    have h := hg31.1; simp only [goal_31] at h; exact h
  -- PM input shape: 607 = goal_31.tps rank-0 [1,8,32] (single-tp)
  have h607_pmsh : (Spm 607).shape = [1, 8, 32] := by
    have h := hg31.2.1
    simp only [goal_31, List.map, List.cons.injEq, and_true] at h
    exact h
  have hSM34 : StoreShapesHold Ssm sm_goal_34InitEnv := by
    intro tid sh hsh
    rw [sm_goal_34InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_34InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h607_smsh
  have hPM34 : StoreShapesHold Spm pm_goal_34InitEnv := by
    intro tid sh hsh
    rw [pm_goal_34InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_34InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h607_pmsh
  have hcut := h Ssm Spm hSM34 hPM34 hInitCut
  -- Frame: 612 (sm node 37), 612 (pm node 232)
  have hsmf : Ssm 612 = denoteGraph sm_goal_34 Ssm 612 := by
    rw [hSsm]; exact sm_frame_612_self initSM
  have hpmf : Spm 612 = denoteGraph pm_goal_34 Spm 612 := by
    rw [hSpm]; exact pm_frame_612_self initPM
  rw [hnr] at hcut
  simp only [goal_34, List.map] at hcut ⊢
  rw [hsmf, hpmf]
  exact hcut

theorem goal_34_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_34 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_34_stmt := goal_34_cut_to_full prove_goal_34_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
