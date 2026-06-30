/- goal_279 桥 (prereqs=[2..30,257,259,261,263,265,267,269,271]，与 goal_275 完全相同)。
   FW_multiref 第三输出 (params=[3], outs=[961,965,969] 选 969) +
   AllToAll(dim1→2 re-shard, idim=1 odim=2 params=[1,2]), multi-tps gatherDim=2。
   SM=FW_multiref(605)→[961,965,969] (node 33), 取第三输出 969 = 605。
   PM=4×FW_multiref(166(5+r))→[35XX,17XX,35YY] (node 201-204, 各取第三输出 3521/3531/3541/3551 = 各 rank 输入 1665-1668),
      4×AllToAllPrim(ins=[3521,3531,3541,3551], idim=1 odim=2)→1749-1752
      (node 209/211/213/216, 非相邻 — 中间穿插其他 AllToAll/FW_linear 节点, params=[1,2])。
   605=goal_30 输出 [1,8,32] (FW_layernorm, gatherDim=1, dim1-sharded tps=1665-1668 [1,2,32])。
   核心语义已在 prove_goal_279_cut 处理 (third_out_g279 + AllToAll dim1→2 = chunk dim2),
   bridge 只做 frame。套 Goal275Bridge 模板 (区别: 第三输出 third_out_g279, AllToAll 上游用第三 slot 3521/3531/3541/3551,
   AllToAll 节点 209/211/213/216, 输出 tids 1749-1752, ts 969)。
   注: Denote.lean 不动 (applyNode_fw_multiref3_third_out_g279 已存在)。 -/
import denote.gpt_ly4_regen.Goal27Bridge
import denote.gpt_ly4_regen.Goal28Bridge
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal269Bridge
import denote.gpt_ly4_regen.Goal271Bridge
import denote.gpt_ly4_regen.Goal_279

set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Silence noisy cosmetic/convention linters (same rationale as Goal275Bridge):
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

-- ========== 迷你图 sm_goal_279 算 969 (FW_multiref params=[3] 第三输出 = s 605) ==========
theorem denote_sm_goal_279_969 (s : Store) :
    denoteGraph sm_goal_279 s 969 = s 605 := by
  simp only [sm_goal_279, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]

-- ========== SM self-frame: full sm 算 969 (node 33 FW_multiref 第三输出) ==========
theorem sm_frame_969_self (initSM : Store) :
    denoteGraph sm initSM 969 = denoteGraph sm_goal_279 (denoteGraph sm initSM) 969 := by
  rw [denote_sm_goal_279_969]
  rw [sm_val initSM 33 969 (by native_decide) (by native_decide)]
  rw [show sm.nodes[33]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [605], outs := [961, 965, 969], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
  rw [sm_prefix_eq initSM 33 605 (by native_decide)]

-- ========== full pm: multiref 第三输出 3521/3531/3541/3551 (node 201-204) = s 166X ==========
theorem pm_full_g279_3521 (initPM : Store) :
    denoteGraph pm initPM 3521 = denoteGraph pm initPM 1665 := by
  rw [pm_val initPM 201 3521 (by native_decide) (by native_decide)]
  rw [show pm.nodes[201]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1665], outs := [3519, 1721, 3521], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
  rw [pm_prefix_eq initPM 201 1665 (by native_decide)]

theorem pm_full_g279_3531 (initPM : Store) :
    denoteGraph pm initPM 3531 = denoteGraph pm initPM 1666 := by
  rw [pm_val initPM 202 3531 (by native_decide) (by native_decide)]
  rw [show pm.nodes[202]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1666], outs := [3529, 1722, 3531], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
  rw [pm_prefix_eq initPM 202 1666 (by native_decide)]

theorem pm_full_g279_3541 (initPM : Store) :
    denoteGraph pm initPM 3541 = denoteGraph pm initPM 1667 := by
  rw [pm_val initPM 203 3541 (by native_decide) (by native_decide)]
  rw [show pm.nodes[203]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1667], outs := [3539, 1723, 3541], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
  rw [pm_prefix_eq initPM 203 1667 (by native_decide)]

theorem pm_full_g279_3551 (initPM : Store) :
    denoteGraph pm initPM 3551 = denoteGraph pm initPM 1668 := by
  rw [pm_val initPM 204 3551 (by native_decide) (by native_decide)]
  rw [show pm.nodes[204]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1668], outs := [3549, 1724, 3551], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
  rw [pm_prefix_eq initPM 204 1668 (by native_decide)]

-- ========== full pm: AllToAll 输出 1749-1752 (node 209/211/213/216, 非相邻) ==========
theorem pm_full_g279_1749 (initPM : Store) :
    denoteGraph pm initPM 1749
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 3521, denoteGraph pm initPM 3531,
           denoteGraph pm initPM 3541, denoteGraph pm initPM 3551] 1 2 := by
  rw [pm_val initPM 209 1749 (by native_decide) (by native_decide)]
  rw [show pm.nodes[209]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := [3521, 3531, 3541, 3551], outs := [1749], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 209 3521 (by native_decide),
      pm_prefix_eq initPM 209 3531 (by native_decide),
      pm_prefix_eq initPM 209 3541 (by native_decide),
      pm_prefix_eq initPM 209 3551 (by native_decide)]

theorem pm_full_g279_1750 (initPM : Store) :
    denoteGraph pm initPM 1750
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 3521, denoteGraph pm initPM 3531,
           denoteGraph pm initPM 3541, denoteGraph pm initPM 3551] 1 2 := by
  rw [pm_val initPM 211 1750 (by native_decide) (by native_decide)]
  rw [show pm.nodes[211]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := [3521, 3531, 3541, 3551], outs := [1750], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 211 3521 (by native_decide),
      pm_prefix_eq initPM 211 3531 (by native_decide),
      pm_prefix_eq initPM 211 3541 (by native_decide),
      pm_prefix_eq initPM 211 3551 (by native_decide)]

theorem pm_full_g279_1751 (initPM : Store) :
    denoteGraph pm initPM 1751
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 3521, denoteGraph pm initPM 3531,
           denoteGraph pm initPM 3541, denoteGraph pm initPM 3551] 1 2 := by
  rw [pm_val initPM 213 1751 (by native_decide) (by native_decide)]
  rw [show pm.nodes[213]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := [3521, 3531, 3541, 3551], outs := [1751], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 213 3521 (by native_decide),
      pm_prefix_eq initPM 213 3531 (by native_decide),
      pm_prefix_eq initPM 213 3541 (by native_decide),
      pm_prefix_eq initPM 213 3551 (by native_decide)]

theorem pm_full_g279_1752 (initPM : Store) :
    denoteGraph pm initPM 1752
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 3521, denoteGraph pm initPM 3531,
           denoteGraph pm initPM 3541, denoteGraph pm initPM 3551] 1 2 := by
  rw [pm_val initPM 216 1752 (by native_decide) (by native_decide)]
  rw [show pm.nodes[216]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := [3521, 3531, 3541, 3551], outs := [1752], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 216 3521 (by native_decide),
      pm_prefix_eq initPM 216 3531 (by native_decide),
      pm_prefix_eq initPM 216 3541 (by native_decide),
      pm_prefix_eq initPM 216 3551 (by native_decide)]

-- ========== 迷你图 pm_goal_279 算 1749-1752 ==========
-- mini-graph 里 AllToAll 上游 (3521/3531/3541/3551) 由各 rank 的 FW_multiref 第三输出给出 = s 1665-1668。
theorem denote_pm_goal_279_1749 (s : Store) :
    denoteGraph pm_goal_279 s 1749
      = allToAllPrimWithDims 4 0 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_279, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_279_1750 (s : Store) :
    denoteGraph pm_goal_279 s 1750
      = allToAllPrimWithDims 4 1 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_279, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_279_1751 (s : Store) :
    denoteGraph pm_goal_279 s 1751
      = allToAllPrimWithDims 4 2 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_279, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_279_1752 (s : Store) :
    denoteGraph pm_goal_279 s 1752
      = allToAllPrimWithDims 4 3 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_279, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_third_out_g279 (h1 := by decide) (h2 := by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== PM self-frame: 1749-1752 (full = mini) ==========
theorem pm_frame_1749_self (initPM : Store) :
    denoteGraph pm initPM 1749 = denoteGraph pm_goal_279 (denoteGraph pm initPM) 1749 := by
  rw [denote_pm_goal_279_1749]
  rw [pm_full_g279_1749]
  rw [pm_full_g279_3521, pm_full_g279_3531, pm_full_g279_3541, pm_full_g279_3551]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1750_self (initPM : Store) :
    denoteGraph pm initPM 1750 = denoteGraph pm_goal_279 (denoteGraph pm initPM) 1750 := by
  rw [denote_pm_goal_279_1750]
  rw [pm_full_g279_1750]
  rw [pm_full_g279_3521, pm_full_g279_3531, pm_full_g279_3541, pm_full_g279_3551]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1751_self (initPM : Store) :
    denoteGraph pm initPM 1751 = denoteGraph pm_goal_279 (denoteGraph pm initPM) 1751 := by
  rw [denote_pm_goal_279_1751]
  rw [pm_full_g279_1751]
  rw [pm_full_g279_3521, pm_full_g279_3531, pm_full_g279_3541, pm_full_g279_3551]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1752_self (initPM : Store) :
    denoteGraph pm initPM 1752 = denoteGraph pm_goal_279 (denoteGraph pm initPM) 1752 := by
  rw [denote_pm_goal_279_1752]
  rw [pm_full_g279_1752]
  rw [pm_full_g279_3521, pm_full_g279_3531, pm_full_g279_3541, pm_full_g279_3551]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== helper: hInitCut 分离成独立 lemma 避免单次 heartbeat 超时 ==========
lemma goal_279_hInitCut_helper (Ssm Spm : Store)
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
    (hg257 : InitGoalHolds pm.numRanks goal_257 Ssm Spm)
    (hg259 : InitGoalHolds pm.numRanks goal_259 Ssm Spm)
    (hg261 : InitGoalHolds pm.numRanks goal_261 Ssm Spm)
    (hg263 : InitGoalHolds pm.numRanks goal_263 Ssm Spm)
    (hg265 : InitGoalHolds pm.numRanks goal_265 Ssm Spm)
    (hg267 : InitGoalHolds pm.numRanks goal_267 Ssm Spm)
    (hg269 : InitGoalHolds pm.numRanks goal_269 Ssm Spm)
    (hg271 : InitGoalHolds pm.numRanks goal_271 Ssm Spm) :
    InitGoalsHold pm_goal_279.numRanks goal_279_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_279.numRanks = pm.numRanks := by native_decide
  rw [hnr]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_279_cut_initGoals, goal_279_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, List.forall_mem_nil _⟩

-- ========== 总装: goal_279_cut_to_full ==========
theorem goal_279_cut_to_full (h : goal_279_stmt_cut) : goal_279_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hinitC
  have hnr : pm_goal_279.numRanks = pm.numRanks := by native_decide
  -- 605 = goal_30.ts [1,8,32]; 1665-1668 = goal_30 tps each [1,2,32].
  have h605_smsh : (Ssm 605).shape = [1, 8, 32] := by
    have h := hg30.1; simp only [goal_30] at h; exact h
  have h30tp := hg30.2.1
  simp only [goal_30, List.map, List.cons.injEq, and_true] at h30tp
  obtain ⟨h1665_pmsh, h1666_pmsh, h1667_pmsh, h1668_pmsh⟩ := h30tp
  have hSM279 : StoreShapesHold Ssm sm_goal_279InitEnv := by
    intro tid sh hsh
    rw [sm_goal_279InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_279InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h605_smsh
  have hPM279 : StoreShapesHold Spm pm_goal_279InitEnv := by
    intro tid sh hsh
    rw [pm_goal_279InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_279InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1665_pmsh
    · exact h1666_pmsh
    · exact h1667_pmsh
    · exact h1668_pmsh
  have hInitCut : InitGoalsHold pm_goal_279.numRanks goal_279_cut_initGoals Ssm Spm :=
    goal_279_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271
  have hcut := h Ssm Spm hSM279 hPM279 hInitCut
  have hsmf : Ssm 969 = denoteGraph sm_goal_279 Ssm 969 := by
    rw [hSsm]; exact sm_frame_969_self initSM
  have hpm1749 : Spm 1749 = denoteGraph pm_goal_279 Spm 1749 := by
    rw [hSpm]; exact pm_frame_1749_self initPM
  have hpm1750 : Spm 1750 = denoteGraph pm_goal_279 Spm 1750 := by
    rw [hSpm]; exact pm_frame_1750_self initPM
  have hpm1751 : Spm 1751 = denoteGraph pm_goal_279 Spm 1751 := by
    rw [hSpm]; exact pm_frame_1751_self initPM
  have hpm1752 : Spm 1752 = denoteGraph pm_goal_279 Spm 1752 := by
    rw [hSpm]; exact pm_frame_1752_self initPM
  rw [hnr] at hcut
  simp only [goal_279, List.map] at hcut ⊢
  rw [hsmf, hpm1749, hpm1750, hpm1751, hpm1752]
  exact hcut

theorem goal_279_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_279 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_279_stmt := goal_279_cut_to_full prove_goal_279_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals