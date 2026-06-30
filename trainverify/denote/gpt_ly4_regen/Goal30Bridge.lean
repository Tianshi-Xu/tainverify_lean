/- goal_30 桥 (prereqs=[2..29,257,259,261,263,265,267,269,271])。
   第26种结构: pointwise FW_layernorm 多输入 (data + replicated weight + replicated bias),
   multi-tps gatherDim=1, no follow-on collective。
   SM=FW_layernorm(946,603,604)→605 (node 32, [1,8,32])。
   PM=4×FW_layernorm(166X,603,604)→166(5+r) (node 197-200, 各 rank 一份 tp,
      数据输入 [1,2,32], weight/bias 复制 [32]).
   输入 946=goal_271 输出 [1,8,32] (AllToAll dim2→1 reshard, gatherDim=1);
   1661-1664=goal_271 的 4 个 tp ([1,2,32]); 603/604=initGoal_603/604 复制权重。
   multi-tps 输出, gatherDim=1; PM mini-graph 无 collective (输入已分片)。
   与 Goal27Bridge 同构, 仅算子从 unary FW_gelu 换成 ternary FW_layernorm
   (3 输入: data + weight + bias), 上游从 goal_26 (AllGather) 换成 goal_271 (AllToAll reshard);
   语义 (fw_layernorm 对每 rank 输入分别独立计算 + 拼接 = 全张量 layernorm) 已在
   prove_goal_30_cut 里处理, bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal27Bridge
import denote.gpt_ly4_regen.Goal28Bridge
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal269Bridge
import denote.gpt_ly4_regen.Goal271Bridge
import denote.gpt_ly4_regen.Goal_30

set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Silence noisy cosmetic/convention linters (same rationale as Goal29/271Bridge):
-- native_decide is the sanctioned graph-lookup convention; auto-generated frame
-- produces many style/unused diagnostics that do not affect soundness.
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_30 算 605 (FW_layernorm 946,603,604) ==========
theorem denote_sm_goal_30_605 (s : Store) :
    denoteGraph sm_goal_30 s 605 = fw_layernorm (s 946) (s 603) (s 604) := by
  simp only [sm_goal_30, denoteGraph, List.foldl]
  rw [applyNode_fw_layernorm_out]

-- ========== 迷你图 pm_goal_30 算 1665-1668 (4×FW_layernorm) ==========
theorem denote_pm_goal_30_1665 (s : Store) :
    denoteGraph pm_goal_30 s 1665 = fw_layernorm (s 1661) (s 603) (s 604) := by
  simp only [pm_goal_30, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]

theorem denote_pm_goal_30_1666 (s : Store) :
    denoteGraph pm_goal_30 s 1666 = fw_layernorm (s 1662) (s 603) (s 604) := by
  simp only [pm_goal_30, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_30_1667 (s : Store) :
    denoteGraph pm_goal_30 s 1667 = fw_layernorm (s 1663) (s 603) (s 604) := by
  simp only [pm_goal_30, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_30_1668 (s : Store) :
    denoteGraph pm_goal_30 s 1668 = fw_layernorm (s 1664) (s 603) (s 604) := by
  simp only [pm_goal_30, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 605 (node 32 FW_layernorm) ==========
theorem sm_frame_605_self (initSM : Store) :
    denoteGraph sm initSM 605 = denoteGraph sm_goal_30 (denoteGraph sm initSM) 605 := by
  rw [denote_sm_goal_30_605]
  rw [sm_val initSM 32 605 (by native_decide) (by native_decide)]
  rw [show sm.nodes[32]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [946, 603, 604], outs := [605] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [sm_prefix_eq initSM 32 946 (by native_decide),
      sm_prefix_eq initSM 32 603 (by native_decide),
      sm_prefix_eq initSM 32 604 (by native_decide)]

-- ========== PM self-frame: 1665-1668 (4×FW_layernorm, node 197-200) ==========
theorem pm_frame_1665_self (initPM : Store) :
    denoteGraph pm initPM 1665
      = fw_layernorm (denoteGraph pm initPM 1661)
          (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  rw [pm_val initPM 197 1665 (by native_decide) (by native_decide)]
  rw [show pm.nodes[197]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [1661, 603, 604], outs := [1665] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 197 1661 (by native_decide),
      pm_prefix_eq initPM 197 603 (by native_decide),
      pm_prefix_eq initPM 197 604 (by native_decide)]

theorem pm_frame_1666_self (initPM : Store) :
    denoteGraph pm initPM 1666
      = fw_layernorm (denoteGraph pm initPM 1662)
          (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  rw [pm_val initPM 198 1666 (by native_decide) (by native_decide)]
  rw [show pm.nodes[198]'(by native_decide)
      = { rank := 1, op := "OpName.FW_layernorm", ins := [1662, 603, 604], outs := [1666] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 198 1662 (by native_decide),
      pm_prefix_eq initPM 198 603 (by native_decide),
      pm_prefix_eq initPM 198 604 (by native_decide)]

theorem pm_frame_1667_self (initPM : Store) :
    denoteGraph pm initPM 1667
      = fw_layernorm (denoteGraph pm initPM 1663)
          (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  rw [pm_val initPM 199 1667 (by native_decide) (by native_decide)]
  rw [show pm.nodes[199]'(by native_decide)
      = { rank := 2, op := "OpName.FW_layernorm", ins := [1663, 603, 604], outs := [1667] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 199 1663 (by native_decide),
      pm_prefix_eq initPM 199 603 (by native_decide),
      pm_prefix_eq initPM 199 604 (by native_decide)]

theorem pm_frame_1668_self (initPM : Store) :
    denoteGraph pm initPM 1668
      = fw_layernorm (denoteGraph pm initPM 1664)
          (denoteGraph pm initPM 603) (denoteGraph pm initPM 604) := by
  rw [pm_val initPM 200 1668 (by native_decide) (by native_decide)]
  rw [show pm.nodes[200]'(by native_decide)
      = { rank := 3, op := "OpName.FW_layernorm", ins := [1664, 603, 604], outs := [1668] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 200 1664 (by native_decide),
      pm_prefix_eq initPM 200 603 (by native_decide),
      pm_prefix_eq initPM 200 604 (by native_decide)]

-- ========== helper: hInitCut 分离成独立 lemma 避免单次 heartbeat 超时 ==========
lemma goal_30_hInitCut_helper (Ssm Spm : Store)
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
    (hg257 : InitGoalHolds pm.numRanks goal_257 Ssm Spm)
    (hg259 : InitGoalHolds pm.numRanks goal_259 Ssm Spm)
    (hg261 : InitGoalHolds pm.numRanks goal_261 Ssm Spm)
    (hg263 : InitGoalHolds pm.numRanks goal_263 Ssm Spm)
    (hg265 : InitGoalHolds pm.numRanks goal_265 Ssm Spm)
    (hg267 : InitGoalHolds pm.numRanks goal_267 Ssm Spm)
    (hg269 : InitGoalHolds pm.numRanks goal_269 Ssm Spm)
    (hg271 : InitGoalHolds pm.numRanks goal_271 Ssm Spm) :
    InitGoalsHold pm_goal_30.numRanks goal_30_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_30.numRanks = pm.numRanks := by native_decide
  rw [hnr]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_30_cut_initGoals, goal_30_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, List.forall_mem_nil _⟩

-- ========== 总装: goal_30_cut_to_full ==========
theorem goal_30_cut_to_full (h : goal_30_stmt_cut) : goal_30_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hinitC
  have hnr : pm_goal_30.numRanks = pm.numRanks := by native_decide
  -- 946 = goal_271.ts [1,8,32]; 1661-1664 = goal_271.tps each [1,2,32].
  have h946_smsh : (Ssm 946).shape = [1, 8, 32] := by
    have h := hg271.1; simp only [goal_271] at h; exact h
  have h271tp := hg271.2.1
  simp only [goal_271, List.map, List.cons.injEq, and_true] at h271tp
  obtain ⟨h1661_pmsh, h1662_pmsh, h1663_pmsh, h1664_pmsh⟩ := h271tp
  -- 603 = initGoal_603 (replicated [32]); 604 = initGoal_604 (replicated [32]).
  have hg603 := hinitC initGoal_603 (by simp only [initGoals]; decide)
  have hg604 := hinitC initGoal_604 (by simp only [initGoals]; decide)
  have h603_smsh : (Ssm 603).shape = [32] := by
    have h := hg603.1; simp only [initGoal_603] at h; exact h
  have h604_smsh : (Ssm 604).shape = [32] := by
    have h := hg604.1; simp only [initGoal_604] at h; exact h
  have h603_pmsh : (Spm 603).shape = [32] := by
    have h := hg603.2.1; simp only [initGoal_603, List.map] at h
    have := congrArg List.head? h; simpa using this
  have h604_pmsh : (Spm 604).shape = [32] := by
    have h := hg604.2.1; simp only [initGoal_604, List.map] at h
    have := congrArg List.head? h; simpa using this
  have hSM30 : StoreShapesHold Ssm sm_goal_30InitEnv := by
    intro tid sh hsh
    rw [sm_goal_30InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_30InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h603_smsh
    · exact h604_smsh
    · exact h946_smsh
  have hPM30 : StoreShapesHold Spm pm_goal_30InitEnv := by
    intro tid sh hsh
    rw [pm_goal_30InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_30InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h603_pmsh
    · exact h604_pmsh
    · exact h1661_pmsh
    · exact h1662_pmsh
    · exact h1663_pmsh
    · exact h1664_pmsh
  have hInitCut : InitGoalsHold pm_goal_30.numRanks goal_30_cut_initGoals Ssm Spm :=
    goal_30_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271
  have hcut := h Ssm Spm hSM30 hPM30 hInitCut
  -- Frame: 605 (sm), 1665-1668 (pm).
  have hsmf : Ssm 605 = denoteGraph sm_goal_30 Ssm 605 := by
    rw [hSsm]; exact sm_frame_605_self initSM
  have hpm1665 : Spm 1665 = denoteGraph pm_goal_30 Spm 1665 := by
    rw [denote_pm_goal_30_1665]; rw [hSpm]; exact pm_frame_1665_self initPM
  have hpm1666 : Spm 1666 = denoteGraph pm_goal_30 Spm 1666 := by
    rw [denote_pm_goal_30_1666]; rw [hSpm]; exact pm_frame_1666_self initPM
  have hpm1667 : Spm 1667 = denoteGraph pm_goal_30 Spm 1667 := by
    rw [denote_pm_goal_30_1667]; rw [hSpm]; exact pm_frame_1667_self initPM
  have hpm1668 : Spm 1668 = denoteGraph pm_goal_30 Spm 1668 := by
    rw [denote_pm_goal_30_1668]; rw [hSpm]; exact pm_frame_1668_self initPM
  rw [hnr] at hcut
  simp only [goal_30, List.map] at hcut ⊢
  rw [hsmf, hpm1665, hpm1666, hpm1667, hpm1668]
  exact hcut

theorem goal_30_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_30 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_30_stmt := goal_30_cut_to_full prove_goal_30_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
