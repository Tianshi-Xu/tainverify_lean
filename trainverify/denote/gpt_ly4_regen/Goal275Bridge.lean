/- goal_275 桥 (prereqs=[2..30,257,259,261,263,265,267,269,271])。
   FW_multiref 第一输出 (params=[3], outs=[961,965,969] 选 961) +
   AllToAll(dim1→2 re-shard, idim=1 odim=2 params=[1,2]), multi-tps gatherDim=2。
   SM=FW_multiref(605)→[961,965,969] (node 33), 取第一输出 961 = 605。
   PM=4×FW_multiref(166(5+r))→[35XX,17XX,35YY] (node 201-204, 各取第一输出 = 各 rank 输入 1665-1668),
      4×AllToAllPrim(ins=[3519,3529,3539,3549], idim=1 odim=2)→1693-1696
      (node 208/210/212/214, 非相邻 — 中间穿插 goal_277 等其他 AllToAll/FW_linear 节点, params=[1,2])。
   605=goal_30 输出 [1,8,32] (FW_layernorm, dim2-sharded? NO — gatherDim=1, dim1-sharded
     tps=1665-1668 [1,2,32]). 
   goal_271 类型: multiref-first-output 复制 + AllToAll dim1→2 reshard = chunk dim2。
   核心语义已在 prove_goal_275_cut 处理, bridge 只做 frame。套 Goal271Bridge 的模板。 -/
import denote.gpt_ly4_regen.Goal27Bridge
import denote.gpt_ly4_regen.Goal28Bridge
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal269Bridge
import denote.gpt_ly4_regen.Goal271Bridge
import denote.gpt_ly4_regen.Goal_275

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
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_275 算 961 (FW_multiref params=[3] 第一输出 = s 605) ==========
theorem denote_sm_goal_275_961 (s : Store) :
    denoteGraph sm_goal_275 s 961 = s 605 := by
  simp only [sm_goal_275, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_first_out_g275]

-- ========== SM self-frame: full sm 算 961 (node 33 FW_multiref 第一输出) ==========
theorem sm_frame_961_self (initSM : Store) :
    denoteGraph sm initSM 961 = denoteGraph sm_goal_275 (denoteGraph sm initSM) 961 := by
  rw [denote_sm_goal_275_961]
  rw [sm_val initSM 33 961 (by native_decide) (by native_decide)]
  rw [show sm.nodes[33]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [605], outs := [961, 965, 969], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out_g275]
  rw [sm_prefix_eq initSM 33 605 (by native_decide)]

-- ========== full pm: multiref 第一输出 3519/3529/3539/3549 (node 201-204) = s 166X ==========
theorem pm_full_3519 (initPM : Store) :
    denoteGraph pm initPM 3519 = denoteGraph pm initPM 1665 := by
  rw [pm_val initPM 201 3519 (by native_decide) (by native_decide)]
  rw [show pm.nodes[201]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1665], outs := [3519, 1721, 3521], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out_g275]
  rw [pm_prefix_eq initPM 201 1665 (by native_decide)]

theorem pm_full_3529 (initPM : Store) :
    denoteGraph pm initPM 3529 = denoteGraph pm initPM 1666 := by
  rw [pm_val initPM 202 3529 (by native_decide) (by native_decide)]
  rw [show pm.nodes[202]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1666], outs := [3529, 1722, 3531], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out_g275]
  rw [pm_prefix_eq initPM 202 1666 (by native_decide)]

theorem pm_full_3539 (initPM : Store) :
    denoteGraph pm initPM 3539 = denoteGraph pm initPM 1667 := by
  rw [pm_val initPM 203 3539 (by native_decide) (by native_decide)]
  rw [show pm.nodes[203]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1667], outs := [3539, 1723, 3541], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out_g275]
  rw [pm_prefix_eq initPM 203 1667 (by native_decide)]

theorem pm_full_3549 (initPM : Store) :
    denoteGraph pm initPM 3549 = denoteGraph pm initPM 1668 := by
  rw [pm_val initPM 204 3549 (by native_decide) (by native_decide)]
  rw [show pm.nodes[204]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1668], outs := [3549, 1724, 3551], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out_g275]
  rw [pm_prefix_eq initPM 204 1668 (by native_decide)]

-- ========== full pm: AllToAll 输出 1693-1696 (node 208/210/212/214, 非相邻) ==========
theorem pm_full_1693 (initPM : Store) :
    denoteGraph pm initPM 1693
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 3519, denoteGraph pm initPM 3529,
           denoteGraph pm initPM 3539, denoteGraph pm initPM 3549] 1 2 := by
  rw [pm_val initPM 208 1693 (by native_decide) (by native_decide)]
  rw [show pm.nodes[208]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := [3519, 3529, 3539, 3549], outs := [1693], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 208 3519 (by native_decide),
      pm_prefix_eq initPM 208 3529 (by native_decide),
      pm_prefix_eq initPM 208 3539 (by native_decide),
      pm_prefix_eq initPM 208 3549 (by native_decide)]

theorem pm_full_1694 (initPM : Store) :
    denoteGraph pm initPM 1694
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 3519, denoteGraph pm initPM 3529,
           denoteGraph pm initPM 3539, denoteGraph pm initPM 3549] 1 2 := by
  rw [pm_val initPM 210 1694 (by native_decide) (by native_decide)]
  rw [show pm.nodes[210]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := [3519, 3529, 3539, 3549], outs := [1694], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 210 3519 (by native_decide),
      pm_prefix_eq initPM 210 3529 (by native_decide),
      pm_prefix_eq initPM 210 3539 (by native_decide),
      pm_prefix_eq initPM 210 3549 (by native_decide)]

theorem pm_full_1695 (initPM : Store) :
    denoteGraph pm initPM 1695
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 3519, denoteGraph pm initPM 3529,
           denoteGraph pm initPM 3539, denoteGraph pm initPM 3549] 1 2 := by
  rw [pm_val initPM 212 1695 (by native_decide) (by native_decide)]
  rw [show pm.nodes[212]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := [3519, 3529, 3539, 3549], outs := [1695], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 212 3519 (by native_decide),
      pm_prefix_eq initPM 212 3529 (by native_decide),
      pm_prefix_eq initPM 212 3539 (by native_decide),
      pm_prefix_eq initPM 212 3549 (by native_decide)]

theorem pm_full_1696 (initPM : Store) :
    denoteGraph pm initPM 1696
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 3519, denoteGraph pm initPM 3529,
           denoteGraph pm initPM 3539, denoteGraph pm initPM 3549] 1 2 := by
  rw [pm_val initPM 214 1696 (by native_decide) (by native_decide)]
  rw [show pm.nodes[214]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := [3519, 3529, 3539, 3549], outs := [1696], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 214 3519 (by native_decide),
      pm_prefix_eq initPM 214 3529 (by native_decide),
      pm_prefix_eq initPM 214 3539 (by native_decide),
      pm_prefix_eq initPM 214 3549 (by native_decide)]

-- ========== 迷你图 pm_goal_275 算 1693-1696 ==========
-- mini-graph 里 AllToAll 上游 (3519-3549) 由各 rank 的 FW_multiref 第一输出给出 = s 1665-1668。
theorem denote_pm_goal_275_1693 (s : Store) :
    denoteGraph pm_goal_275 s 1693
      = allToAllPrimWithDims 4 0 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_275, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_first_out_g275]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_275_1694 (s : Store) :
    denoteGraph pm_goal_275 s 1694
      = allToAllPrimWithDims 4 1 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_275, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_first_out_g275]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_275_1695 (s : Store) :
    denoteGraph pm_goal_275 s 1695
      = allToAllPrimWithDims 4 2 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_275, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_first_out_g275]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_275_1696 (s : Store) :
    denoteGraph pm_goal_275 s 1696
      = allToAllPrimWithDims 4 3 [s 1665, s 1666, s 1667, s 1668] 1 2 := by
  simp only [pm_goal_275, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref3_first_out_g275]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== PM self-frame: 1693-1696 (full = mini) ==========
theorem pm_frame_1693_self (initPM : Store) :
    denoteGraph pm initPM 1693 = denoteGraph pm_goal_275 (denoteGraph pm initPM) 1693 := by
  rw [denote_pm_goal_275_1693]
  rw [pm_full_1693]
  rw [pm_full_3519, pm_full_3529, pm_full_3539, pm_full_3549]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1694_self (initPM : Store) :
    denoteGraph pm initPM 1694 = denoteGraph pm_goal_275 (denoteGraph pm initPM) 1694 := by
  rw [denote_pm_goal_275_1694]
  rw [pm_full_1694]
  rw [pm_full_3519, pm_full_3529, pm_full_3539, pm_full_3549]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1695_self (initPM : Store) :
    denoteGraph pm initPM 1695 = denoteGraph pm_goal_275 (denoteGraph pm initPM) 1695 := by
  rw [denote_pm_goal_275_1695]
  rw [pm_full_1695]
  rw [pm_full_3519, pm_full_3529, pm_full_3539, pm_full_3549]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1696_self (initPM : Store) :
    denoteGraph pm initPM 1696 = denoteGraph pm_goal_275 (denoteGraph pm initPM) 1696 := by
  rw [denote_pm_goal_275_1696]
  rw [pm_full_1696]
  rw [pm_full_3519, pm_full_3529, pm_full_3539, pm_full_3549]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== helper: hInitCut 分离成独立 lemma 避免单次 heartbeat 超时 ==========
lemma goal_275_hInitCut_helper (Ssm Spm : Store)
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
    InitGoalsHold pm_goal_275.numRanks goal_275_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_275.numRanks = pm.numRanks := by native_decide
  rw [hnr]; intro g hg
  simp only [goal_275_cut_initGoals, goal_275_prereqs, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hinitC g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact hg257
    · exact hg259
    · exact hg261
    · exact hg263
    · exact hg265
    · exact hg267
    · exact hg269
    · exact hg271

-- ========== 总装: goal_275_cut_to_full ==========
theorem goal_275_cut_to_full (h : goal_275_stmt_cut) : goal_275_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_275.numRanks = pm.numRanks := by native_decide
  -- 605 = goal_30.ts [1,8,32]; 1665-1668 = goal_30 tps each [1,2,32].
  have h605_smsh : (Ssm 605).shape = [1, 8, 32] := by
    have h := hg30.1; simp only [goal_30] at h; exact h
  have h30tp := hg30.2.1
  simp only [goal_30, List.map, List.cons.injEq, and_true] at h30tp
  obtain ⟨h1665_pmsh, h1666_pmsh, h1667_pmsh, h1668_pmsh⟩ := h30tp
  have hSM275 : StoreShapesHold Ssm sm_goal_275InitEnv := by
    intro tid sh hsh
    rw [sm_goal_275InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_275InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h605_smsh
  have hPM275 : StoreShapesHold Spm pm_goal_275InitEnv := by
    intro tid sh hsh
    rw [pm_goal_275InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_275InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1665_pmsh
    · exact h1666_pmsh
    · exact h1667_pmsh
    · exact h1668_pmsh
  have hInitCut : InitGoalsHold pm_goal_275.numRanks goal_275_cut_initGoals Ssm Spm :=
    goal_275_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271
  have hcut := h Ssm Spm hSM275 hPM275 hInitCut
  have hsmf : Ssm 961 = denoteGraph sm_goal_275 Ssm 961 := by
    rw [hSsm]; exact sm_frame_961_self initSM
  have hpm1693 : Spm 1693 = denoteGraph pm_goal_275 Spm 1693 := by
    rw [hSpm]; exact pm_frame_1693_self initPM
  have hpm1694 : Spm 1694 = denoteGraph pm_goal_275 Spm 1694 := by
    rw [hSpm]; exact pm_frame_1694_self initPM
  have hpm1695 : Spm 1695 = denoteGraph pm_goal_275 Spm 1695 := by
    rw [hSpm]; exact pm_frame_1695_self initPM
  have hpm1696 : Spm 1696 = denoteGraph pm_goal_275 Spm 1696 := by
    rw [hSpm]; exact pm_frame_1696_self initPM
  rw [hnr] at hcut
  simp only [goal_275, List.map] at hcut ⊢
  rw [hsmf, hpm1693, hpm1694, hpm1695, hpm1696]
  exact hcut

theorem goal_275_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_275 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_275_stmt := goal_275_cut_to_full prove_goal_275_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_275] using this

end TrainVerify.Denote.GeneratedGoals
