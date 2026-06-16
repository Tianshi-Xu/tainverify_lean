/- goal_281 桥 (prereqs=[2..49,257-279 odd])。
   第28种结构 (复用 goal_275/279 的 FW_multiref + AllToAll 模板，但 params=[2] 且取第一输出)。
   SM=FW_multiref(628)→[977,981] (node 53, params=[2]),
      取第一输出 977 = 628 (用 applyNode_fw_multiref2_first_out)。
   PM=4×FW_multiref(2057+r)→[3557+8r, 3559+8r] (node 346-349, params=[2]，每 rank 取第一输出
      3557/3565/3573/3581 = 各 rank 输入 2057-2060),
      4×AllToAllPrim(ins=[3557,3565,3573,3581], idim=2 odim=1)→2081-2084
      (node 350/352/354/356, 非相邻 — 与其他 goal 的节点交错, params=[2,1])。
   628=goal_49 输出 [1,8,32] (FW_add 重分布合并, gatherDim=2, dim2-sharded tps=2057-2060 [1,8,8])。
   核心语义已在 prove_goal_281_cut 处理 (first_out + AllToAll dim2→1 = chunk dim1),
   bridge 只做 frame。套 Goal279Bridge 模板 (区别: 第一输出 fw_multiref2_first_out 通用 lemma,
   AllToAll 上游用第一 slot 3557/3565/3573/3581, AllToAll 节点 350/352/354/356,
   输出 tids 2081-2084, ts 977; SM 节点 53)。
   注: Denote.lean 不动 (applyNode_fw_multiref2_first_out 已通用存在)。
   本桥是第一个需要 goal_281 的下游 (goal_50) 之前必须先证。 -/
import denote.gpt_ly4_regen.Goal49Bridge
import denote.gpt_ly4_regen.Goal273Bridge
import denote.gpt_ly4_regen.Goal275Bridge
import denote.gpt_ly4_regen.Goal277Bridge
import denote.gpt_ly4_regen.Goal279Bridge
import denote.gpt_ly4_regen.Goal_281

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
-- Silence noisy cosmetic/convention linters (same rationale as Goal279Bridge):
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

-- ========== 迷你图 sm_goal_281 算 977 (FW_multiref params=[2] 第一输出 = s 628) ==========
theorem denote_sm_goal_281_977 (s : Store) :
    denoteGraph sm_goal_281 s 977 = s 628 := by
  simp only [sm_goal_281, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_first_out]

-- ========== SM self-frame: full sm 算 977 (node 53 FW_multiref 第一输出) ==========
theorem sm_frame_977_self (initSM : Store) :
    denoteGraph sm initSM 977 = denoteGraph sm_goal_281 (denoteGraph sm initSM) 977 := by
  rw [denote_sm_goal_281_977]
  rw [sm_val initSM 53 977 (by native_decide) (by native_decide)]
  rw [show sm.nodes[53]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [628], outs := [977, 981], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [sm_prefix_eq initSM 53 628 (by native_decide)]

-- ========== full pm: multiref 第一输出 3557/3565/3573/3581 (node 346-349) = s 2057-2060 ==========
theorem pm_full_3557 (initPM : Store) :
    denoteGraph pm initPM 3557 = denoteGraph pm initPM 2057 := by
  rw [pm_val initPM 346 3557 (by native_decide) (by native_decide)]
  rw [show pm.nodes[346]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [2057], outs := [3557, 3559], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 346 2057 (by native_decide)]

theorem pm_full_3565 (initPM : Store) :
    denoteGraph pm initPM 3565 = denoteGraph pm initPM 2058 := by
  rw [pm_val initPM 347 3565 (by native_decide) (by native_decide)]
  rw [show pm.nodes[347]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [2058], outs := [3565, 3567], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 347 2058 (by native_decide)]

theorem pm_full_3573 (initPM : Store) :
    denoteGraph pm initPM 3573 = denoteGraph pm initPM 2059 := by
  rw [pm_val initPM 348 3573 (by native_decide) (by native_decide)]
  rw [show pm.nodes[348]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [2059], outs := [3573, 3575], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 348 2059 (by native_decide)]

theorem pm_full_3581 (initPM : Store) :
    denoteGraph pm initPM 3581 = denoteGraph pm initPM 2060 := by
  rw [pm_val initPM 349 3581 (by native_decide) (by native_decide)]
  rw [show pm.nodes[349]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [2060], outs := [3581, 3583], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 349 2060 (by native_decide)]

-- ========== full pm: AllToAll 输出 2081-2084 (node 350/352/354/356, 非相邻) ==========
theorem pm_full_2081 (initPM : Store) :
    denoteGraph pm initPM 2081
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 3557, denoteGraph pm initPM 3565,
           denoteGraph pm initPM 3573, denoteGraph pm initPM 3581] 2 1 := by
  rw [pm_val initPM 350 2081 (by native_decide) (by native_decide)]
  rw [show pm.nodes[350]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := [3557, 3565, 3573, 3581], outs := [2081], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 350 3557 (by native_decide),
      pm_prefix_eq initPM 350 3565 (by native_decide),
      pm_prefix_eq initPM 350 3573 (by native_decide),
      pm_prefix_eq initPM 350 3581 (by native_decide)]

theorem pm_full_2082 (initPM : Store) :
    denoteGraph pm initPM 2082
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 3557, denoteGraph pm initPM 3565,
           denoteGraph pm initPM 3573, denoteGraph pm initPM 3581] 2 1 := by
  rw [pm_val initPM 352 2082 (by native_decide) (by native_decide)]
  rw [show pm.nodes[352]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := [3557, 3565, 3573, 3581], outs := [2082], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 352 3557 (by native_decide),
      pm_prefix_eq initPM 352 3565 (by native_decide),
      pm_prefix_eq initPM 352 3573 (by native_decide),
      pm_prefix_eq initPM 352 3581 (by native_decide)]

theorem pm_full_2083 (initPM : Store) :
    denoteGraph pm initPM 2083
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 3557, denoteGraph pm initPM 3565,
           denoteGraph pm initPM 3573, denoteGraph pm initPM 3581] 2 1 := by
  rw [pm_val initPM 354 2083 (by native_decide) (by native_decide)]
  rw [show pm.nodes[354]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := [3557, 3565, 3573, 3581], outs := [2083], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 354 3557 (by native_decide),
      pm_prefix_eq initPM 354 3565 (by native_decide),
      pm_prefix_eq initPM 354 3573 (by native_decide),
      pm_prefix_eq initPM 354 3581 (by native_decide)]

theorem pm_full_2084 (initPM : Store) :
    denoteGraph pm initPM 2084
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 3557, denoteGraph pm initPM 3565,
           denoteGraph pm initPM 3573, denoteGraph pm initPM 3581] 2 1 := by
  rw [pm_val initPM 356 2084 (by native_decide) (by native_decide)]
  rw [show pm.nodes[356]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := [3557, 3565, 3573, 3581], outs := [2084], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 356 3557 (by native_decide),
      pm_prefix_eq initPM 356 3565 (by native_decide),
      pm_prefix_eq initPM 356 3573 (by native_decide),
      pm_prefix_eq initPM 356 3581 (by native_decide)]

-- ========== 迷你图 pm_goal_281 算 2081-2084 ==========
-- mini-graph 里 AllToAll 上游 (3557/3565/3573/3581) 由各 rank 的 FW_multiref 第一输出给出 = s 2057-2060。
theorem denote_pm_goal_281_2081 (s : Store) :
    denoteGraph pm_goal_281 s 2081
      = allToAllPrimWithDims 4 0 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_281, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_281_2082 (s : Store) :
    denoteGraph pm_goal_281 s 2082
      = allToAllPrimWithDims 4 1 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_281, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_281_2083 (s : Store) :
    denoteGraph pm_goal_281 s 2083
      = allToAllPrimWithDims 4 2 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_281, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_281_2084 (s : Store) :
    denoteGraph pm_goal_281 s 2084
      = allToAllPrimWithDims 4 3 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_281, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== PM self-frame: 2081-2084 (full = mini) ==========
theorem pm_frame_2081_self (initPM : Store) :
    denoteGraph pm initPM 2081 = denoteGraph pm_goal_281 (denoteGraph pm initPM) 2081 := by
  rw [denote_pm_goal_281_2081]
  rw [pm_full_2081]
  rw [pm_full_3557, pm_full_3565, pm_full_3573, pm_full_3581]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2082_self (initPM : Store) :
    denoteGraph pm initPM 2082 = denoteGraph pm_goal_281 (denoteGraph pm initPM) 2082 := by
  rw [denote_pm_goal_281_2082]
  rw [pm_full_2082]
  rw [pm_full_3557, pm_full_3565, pm_full_3573, pm_full_3581]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2083_self (initPM : Store) :
    denoteGraph pm initPM 2083 = denoteGraph pm_goal_281 (denoteGraph pm initPM) 2083 := by
  rw [denote_pm_goal_281_2083]
  rw [pm_full_2083]
  rw [pm_full_3557, pm_full_3565, pm_full_3573, pm_full_3581]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2084_self (initPM : Store) :
    denoteGraph pm initPM 2084 = denoteGraph pm_goal_281 (denoteGraph pm initPM) 2084 := by
  rw [denote_pm_goal_281_2084]
  rw [pm_full_2084]
  rw [pm_full_3557, pm_full_3565, pm_full_3573, pm_full_3581]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装: goal_281_cut_to_full ==========
theorem goal_281_cut_to_full (h : goal_281_stmt_cut) : goal_281_stmt := by
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
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_281.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_281.numRanks goal_281_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_281_cut_initGoals, goal_281_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg33
      · exact hg34
      · exact hg35
      · exact hg36
      · exact hg37
      · exact hg38
      · exact hg39
      · exact hg40
      · exact hg41
      · exact hg42
      · exact hg43
      · exact hg44
      · exact hg45
      · exact hg46
      · exact hg47
      · exact hg48
      · exact hg49
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg273
      · exact hg275
      · exact hg277
      · exact hg279
  -- 628 = goal_49.ts (single-tp on SM, shape [1,8,32]); tps 2057-2060 each [1,8,8]
  have h628_smsh : (Ssm 628).shape = [1, 8, 32] := by
    have h := hg49.1; simp only [goal_49] at h; exact h
  have hpmsh49 : (Spm 2057).shape = [1,8,8] ∧ (Spm 2058).shape = [1,8,8] ∧
                 (Spm 2059).shape = [1,8,8] ∧ (Spm 2060).shape = [1,8,8] := by
    have h := hg49.2.1
    simp only [goal_49, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h2057sh, h2058sh, h2059sh, h2060sh⟩ := hpmsh49
  have hSM281 : StoreShapesHold Ssm sm_goal_281InitEnv := by
    intro tid sh hsh
    rw [sm_goal_281InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_281InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h628_smsh
  have hPM281 : StoreShapesHold Spm pm_goal_281InitEnv := by
    intro tid sh hsh
    rw [pm_goal_281InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_281InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2057sh
    · exact h2058sh
    · exact h2059sh
    · exact h2060sh
  have hcut := h Ssm Spm hSM281 hPM281 hInitCut
  have hsmf : Ssm 977 = denoteGraph sm_goal_281 Ssm 977 := by
    rw [hSsm]; exact sm_frame_977_self initSM
  have hpm2081 : Spm 2081 = denoteGraph pm_goal_281 Spm 2081 := by
    rw [hSpm]; exact pm_frame_2081_self initPM
  have hpm2082 : Spm 2082 = denoteGraph pm_goal_281 Spm 2082 := by
    rw [hSpm]; exact pm_frame_2082_self initPM
  have hpm2083 : Spm 2083 = denoteGraph pm_goal_281 Spm 2083 := by
    rw [hSpm]; exact pm_frame_2083_self initPM
  have hpm2084 : Spm 2084 = denoteGraph pm_goal_281 Spm 2084 := by
    rw [hSpm]; exact pm_frame_2084_self initPM
  rw [hnr] at hcut
  simp only [goal_281, List.map] at hcut ⊢
  rw [hsmf, hpm2081, hpm2082, hpm2083, hpm2084]
  exact hcut

theorem goal_281_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_281 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_281_stmt := goal_281_cut_to_full prove_goal_281_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_281] using this

end TrainVerify.Denote.GeneratedGoals
