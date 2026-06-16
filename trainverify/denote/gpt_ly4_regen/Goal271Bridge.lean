/- goal_271 桥 (prereqs=[2..29,257,259,261,263,265,267,269])。
   FW_multiref 第一输出 (params=[2], outs=[946,950] 选 946) + AllToAll(dim2→dim1 re-shard,
   idim=2 odim=1 params=[2,1]), multi-tps gatherDim=1。
   SM=FW_multiref(602)→[946,950] (node 31), 取第一输出 946 = 602。
   PM=4×FW_multiref(163(7+r))→[349X,204X] (node 189-192, 各取第一输出 = 各 rank 输入 1637-1640),
      4×AllToAllPrim(ins=[3493,3499,3505,3511], idim=2 odim=1)→1661-1664 (node 193-196, params=[2,1])。
   602=goal_29 输出 [1,8,32] (FW_add, dim2-sharded tps=1637-1640 [1,8,8])。
   AllToAll 把 dim2-sharded 的 602(经 multiref 复制成 3493-3511) 重排成 dim1-sharded chunk [1,2,32]。
   核心语义 (multiref 第一输出复制 + allToAll dim2→1 重排 = chunk dim1) 已在 prove_goal_271_cut 处理,
   bridge 只做 frame。套 Goal29Bridge 的 AllToAll multi-tps 模板 + Goal269Bridge 的 multiref 模板,
   但 AllToAll ins 为字面列表 [3493,3499,3505,3511] (非 range.map), 上游为 multiref 第一输出。 -/
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal25Bridge
import denote.gpt_ly4_regen.Goal26Bridge
import denote.gpt_ly4_regen.Goal27Bridge
import denote.gpt_ly4_regen.Goal28Bridge
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal257Bridge
import denote.gpt_ly4_regen.Goal259Bridge
import denote.gpt_ly4_regen.Goal261Bridge
import denote.gpt_ly4_regen.Goal263Bridge
import denote.gpt_ly4_regen.Goal265Bridge
import denote.gpt_ly4_regen.Goal267Bridge
import denote.gpt_ly4_regen.Goal269Bridge
import denote.gpt_ly4_regen.Goal_271

set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Silence noisy cosmetic/convention linters (same rationale as Goal29Bridge):
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

-- ========== 迷你图 sm_goal_271 算 946 (FW_multiref 第一输出 = s 602) ==========
theorem denote_sm_goal_271_946 (s : Store) :
    denoteGraph sm_goal_271 s 946 = s 602 := by
  simp only [sm_goal_271, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_first_out]

-- ========== SM self-frame: full sm 算 946 (node 31 FW_multiref 第一输出) ==========
theorem sm_frame_946_self (initSM : Store) :
    denoteGraph sm initSM 946 = denoteGraph sm_goal_271 (denoteGraph sm initSM) 946 := by
  rw [denote_sm_goal_271_946]
  rw [sm_val initSM 31 946 (by native_decide) (by native_decide)]
  rw [show sm.nodes[31]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [602], outs := [946, 950], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [sm_prefix_eq initSM 31 602 (by native_decide)]

-- ========== full pm: multiref 第一输出 3493/3499/3505/3511 (node 189-192) = s 163X ==========
theorem pm_full_3493 (initPM : Store) :
    denoteGraph pm initPM 3493 = denoteGraph pm initPM 1637 := by
  rw [pm_val initPM 189 3493 (by native_decide) (by native_decide)]
  rw [show pm.nodes[189]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1637], outs := [3493, 2049], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 189 1637 (by native_decide)]

theorem pm_full_3499 (initPM : Store) :
    denoteGraph pm initPM 3499 = denoteGraph pm initPM 1638 := by
  rw [pm_val initPM 190 3499 (by native_decide) (by native_decide)]
  rw [show pm.nodes[190]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1638], outs := [3499, 2050], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 190 1638 (by native_decide)]

theorem pm_full_3505 (initPM : Store) :
    denoteGraph pm initPM 3505 = denoteGraph pm initPM 1639 := by
  rw [pm_val initPM 191 3505 (by native_decide) (by native_decide)]
  rw [show pm.nodes[191]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1639], outs := [3505, 2051], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 191 1639 (by native_decide)]

theorem pm_full_3511 (initPM : Store) :
    denoteGraph pm initPM 3511 = denoteGraph pm initPM 1640 := by
  rw [pm_val initPM 192 3511 (by native_decide) (by native_decide)]
  rw [show pm.nodes[192]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1640], outs := [3511, 2052], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 192 1640 (by native_decide)]

-- ========== full pm: AllToAll 输出 1661-1664 (node 193-196, 字面 ins 列表) ==========
theorem pm_full_1661 (initPM : Store) :
    denoteGraph pm initPM 1661
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 3493, denoteGraph pm initPM 3499,
           denoteGraph pm initPM 3505, denoteGraph pm initPM 3511] 2 1 := by
  rw [pm_val initPM 193 1661 (by native_decide) (by native_decide)]
  rw [show pm.nodes[193]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := [3493, 3499, 3505, 3511], outs := [1661], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 193 3493 (by native_decide),
      pm_prefix_eq initPM 193 3499 (by native_decide),
      pm_prefix_eq initPM 193 3505 (by native_decide),
      pm_prefix_eq initPM 193 3511 (by native_decide)]

theorem pm_full_1662 (initPM : Store) :
    denoteGraph pm initPM 1662
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 3493, denoteGraph pm initPM 3499,
           denoteGraph pm initPM 3505, denoteGraph pm initPM 3511] 2 1 := by
  rw [pm_val initPM 194 1662 (by native_decide) (by native_decide)]
  rw [show pm.nodes[194]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := [3493, 3499, 3505, 3511], outs := [1662], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 194 3493 (by native_decide),
      pm_prefix_eq initPM 194 3499 (by native_decide),
      pm_prefix_eq initPM 194 3505 (by native_decide),
      pm_prefix_eq initPM 194 3511 (by native_decide)]

theorem pm_full_1663 (initPM : Store) :
    denoteGraph pm initPM 1663
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 3493, denoteGraph pm initPM 3499,
           denoteGraph pm initPM 3505, denoteGraph pm initPM 3511] 2 1 := by
  rw [pm_val initPM 195 1663 (by native_decide) (by native_decide)]
  rw [show pm.nodes[195]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := [3493, 3499, 3505, 3511], outs := [1663], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 195 3493 (by native_decide),
      pm_prefix_eq initPM 195 3499 (by native_decide),
      pm_prefix_eq initPM 195 3505 (by native_decide),
      pm_prefix_eq initPM 195 3511 (by native_decide)]

theorem pm_full_1664 (initPM : Store) :
    denoteGraph pm initPM 1664
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 3493, denoteGraph pm initPM 3499,
           denoteGraph pm initPM 3505, denoteGraph pm initPM 3511] 2 1 := by
  rw [pm_val initPM 196 1664 (by native_decide) (by native_decide)]
  rw [show pm.nodes[196]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := [3493, 3499, 3505, 3511], outs := [1664], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 196 3493 (by native_decide),
      pm_prefix_eq initPM 196 3499 (by native_decide),
      pm_prefix_eq initPM 196 3505 (by native_decide),
      pm_prefix_eq initPM 196 3511 (by native_decide)]

-- ========== 迷你图 pm_goal_271 算 1661-1664 ==========
-- mini-graph 里 AllToAll 上游 (3493-3511) 由各 rank 的 FW_multiref 第一输出给出 = s 1637-1640。
theorem denote_pm_goal_271_1661 (s : Store) :
    denoteGraph pm_goal_271 s 1661
      = allToAllPrimWithDims 4 0 [s 1637, s 1638, s 1639, s 1640] 2 1 := by
  simp only [pm_goal_271, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_271_1662 (s : Store) :
    denoteGraph pm_goal_271 s 1662
      = allToAllPrimWithDims 4 1 [s 1637, s 1638, s 1639, s 1640] 2 1 := by
  simp only [pm_goal_271, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_271_1663 (s : Store) :
    denoteGraph pm_goal_271 s 1663
      = allToAllPrimWithDims 4 2 [s 1637, s 1638, s 1639, s 1640] 2 1 := by
  simp only [pm_goal_271, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_271_1664 (s : Store) :
    denoteGraph pm_goal_271 s 1664
      = allToAllPrimWithDims 4 3 [s 1637, s 1638, s 1639, s 1640] 2 1 := by
  simp only [pm_goal_271, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== PM self-frame: 1661-1664 (full = mini) ==========
-- full 侧 AllToAll 上游为 multiref 第一输出 3493-3511 (= s 1637-1640 via pm_full_349X);
-- mini 侧直接是 s 1637-1640。两边对齐。
theorem pm_frame_1661_self (initPM : Store) :
    denoteGraph pm initPM 1661 = denoteGraph pm_goal_271 (denoteGraph pm initPM) 1661 := by
  rw [denote_pm_goal_271_1661]
  rw [pm_full_1661]
  rw [pm_full_3493, pm_full_3499, pm_full_3505, pm_full_3511]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1662_self (initPM : Store) :
    denoteGraph pm initPM 1662 = denoteGraph pm_goal_271 (denoteGraph pm initPM) 1662 := by
  rw [denote_pm_goal_271_1662]
  rw [pm_full_1662]
  rw [pm_full_3493, pm_full_3499, pm_full_3505, pm_full_3511]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1663_self (initPM : Store) :
    denoteGraph pm initPM 1663 = denoteGraph pm_goal_271 (denoteGraph pm initPM) 1663 := by
  rw [denote_pm_goal_271_1663]
  rw [pm_full_1663]
  rw [pm_full_3493, pm_full_3499, pm_full_3505, pm_full_3511]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1664_self (initPM : Store) :
    denoteGraph pm initPM 1664 = denoteGraph pm_goal_271 (denoteGraph pm initPM) 1664 := by
  rw [denote_pm_goal_271_1664]
  rw [pm_full_1664]
  rw [pm_full_3493, pm_full_3499, pm_full_3505, pm_full_3511]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== helper: hInitCut 分离成独立 lemma 避免单次 heartbeat 超时 ==========
lemma goal_271_hInitCut_helper (Ssm Spm : Store)
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
    (hg269 : InitGoalHolds pm.numRanks goal_269 Ssm Spm) :
    InitGoalsHold pm_goal_271.numRanks goal_271_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_271.numRanks = pm.numRanks := by native_decide
  rw [hnr]; intro g hg
  simp only [goal_271_cut_initGoals, goal_271_prereqs, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hinitC g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact hg257
    · exact hg259
    · exact hg261
    · exact hg263
    · exact hg265
    · exact hg267
    · exact hg269

-- ========== 总装: goal_271_cut_to_full ==========
theorem goal_271_cut_to_full (h : goal_271_stmt_cut) : goal_271_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_271.numRanks = pm.numRanks := by native_decide
  -- 602 = goal_29.ts [1,8,32]; 1637-1640 = goal_29 tps [1,8,8]
  have h602_smsh : (Ssm 602).shape = [1, 8, 32] := by
    have h := hg29.1; simp only [goal_29] at h; exact h
  have h29tp := hg29.2.1
  simp only [goal_29, List.map, List.cons.injEq, and_true] at h29tp
  obtain ⟨h1637_pmsh, h1638_pmsh, h1639_pmsh, h1640_pmsh⟩ := h29tp
  have hSM271 : StoreShapesHold Ssm sm_goal_271InitEnv := by
    intro tid sh hsh
    rw [sm_goal_271InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_271InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h602_smsh
  have hPM271 : StoreShapesHold Spm pm_goal_271InitEnv := by
    intro tid sh hsh
    rw [pm_goal_271InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_271InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1637_pmsh
    · exact h1638_pmsh
    · exact h1639_pmsh
    · exact h1640_pmsh
  have hInitCut : InitGoalsHold pm_goal_271.numRanks goal_271_cut_initGoals Ssm Spm :=
    goal_271_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg257 hg259 hg261 hg263 hg265 hg267 hg269
  have hcut := h Ssm Spm hSM271 hPM271 hInitCut
  have hsmf : Ssm 946 = denoteGraph sm_goal_271 Ssm 946 := by
    rw [hSsm]; exact sm_frame_946_self initSM
  have hpm1661 : Spm 1661 = denoteGraph pm_goal_271 Spm 1661 := by
    rw [hSpm]; exact pm_frame_1661_self initPM
  have hpm1662 : Spm 1662 = denoteGraph pm_goal_271 Spm 1662 := by
    rw [hSpm]; exact pm_frame_1662_self initPM
  have hpm1663 : Spm 1663 = denoteGraph pm_goal_271 Spm 1663 := by
    rw [hSpm]; exact pm_frame_1663_self initPM
  have hpm1664 : Spm 1664 = denoteGraph pm_goal_271 Spm 1664 := by
    rw [hSpm]; exact pm_frame_1664_self initPM
  rw [hnr] at hcut
  simp only [goal_271, List.map] at hcut ⊢
  rw [hsmf, hpm1661, hpm1662, hpm1663, hpm1664]
  exact hcut

theorem goal_271_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_271 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_271_stmt := goal_271_cut_to_full prove_goal_271_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_271] using this

end TrainVerify.Denote.GeneratedGoals
