/- goal_29 桥 (prereqs=[2..28,257,259,261,263,265,267,269])。
   第25种结构: 两输入 FW_add + AllToAll(dim1→dim2 re-shard, params=[1,2]), multi-tps gatherDim=2。
   SM=FW_add(938,601)→602 (node 30, [1,8,32])。
   PM=4×AllToAllPrim(1605-1608, idim=1, odim=2)→1633-1636 (node 181-184, params=[1,2]),
      4×FW_add(162X,163X)→1637-1640 (node 185-188, dim2-sharded [1,8,8])。
   938=goal_269 输出 (FW_multiref 第二输出, gatherDim=2, tps=1629-1632 [1,8,8])。
   601=goal_28 输出 (FW_linear, gatherDim=1, tps=1605-1608 [1,2,32])。
   AllToAll 把 dim1-sharded 的 601 重排成 dim2-sharded chunk, 每 rank 做 FW_add 与 1629-1632 配对得 dim2 分片。
   PM mini-graph 有 collective (AllToAll); 套 Goal28Bridge 的 AllToAll 模板,
   但 op 为 binary FW_add (第二参数来自 prereq goal_269), 而非 FW_linear。
   核心语义 (fw_add 对 dim2-chunk 的分配 + allToAll dim1→2 重排) 已在 prove_goal_29_cut 处理,
   bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal25Bridge
import denote.gpt_ly4_regen.Goal26Bridge
import denote.gpt_ly4_regen.Goal27Bridge
import denote.gpt_ly4_regen.Goal28Bridge
import denote.gpt_ly4_regen.Goal267Bridge
import denote.gpt_ly4_regen.Goal269Bridge
import denote.gpt_ly4_regen.Goal_29

set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Silence noisy cosmetic/convention linters: native_decide is the sanctioned
-- graph-lookup convention here, and the auto-generated frame produces many
-- style/unused diagnostics. These do not affect proof soundness, and the sheer
-- volume (2600+ diagnostics) otherwise overwhelms the build diagnostic pipeline.
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

-- ========== 迷你图 sm_goal_29 算 602 (FW_add) ==========
theorem denote_sm_goal_29_602 (s : Store) :
    denoteGraph sm_goal_29 s 602 = elemwiseAdd (s 938) (s 601) := by
  simp only [sm_goal_29, denoteGraph, List.foldl]
  rw [applyNode_fw_add2_out]

-- ========== SM self-frame: full sm 算 602 (node 30 FW_add) ==========
theorem sm_frame_602_self (initSM : Store) :
    denoteGraph sm initSM 602 = denoteGraph sm_goal_29 (denoteGraph sm initSM) 602 := by
  rw [denote_sm_goal_29_602]
  rw [sm_val initSM 30 602 (by native_decide) (by native_decide)]
  rw [show sm.nodes[30]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [938, 601], outs := [602] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [sm_prefix_eq initSM 30 938 (by native_decide),
      sm_prefix_eq initSM 30 601 (by native_decide)]

theorem pm_full_1633 (initPM : Store) :
    denoteGraph pm initPM 1633
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
           denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2 := by
  rw [pm_val initPM 181 1633 (by native_decide) (by native_decide)]
  rw [show pm.nodes[181]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1605 + r)), outs := [1633], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 181 1605 (by native_decide),
      pm_prefix_eq initPM 181 1606 (by native_decide),
      pm_prefix_eq initPM 181 1607 (by native_decide),
      pm_prefix_eq initPM 181 1608 (by native_decide)]

theorem pm_full_1634 (initPM : Store) :
    denoteGraph pm initPM 1634
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
           denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2 := by
  rw [pm_val initPM 182 1634 (by native_decide) (by native_decide)]
  rw [show pm.nodes[182]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1605 + r)), outs := [1634], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 182 1605 (by native_decide),
      pm_prefix_eq initPM 182 1606 (by native_decide),
      pm_prefix_eq initPM 182 1607 (by native_decide),
      pm_prefix_eq initPM 182 1608 (by native_decide)]

theorem pm_full_1635 (initPM : Store) :
    denoteGraph pm initPM 1635
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
           denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2 := by
  rw [pm_val initPM 183 1635 (by native_decide) (by native_decide)]
  rw [show pm.nodes[183]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1605 + r)), outs := [1635], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 183 1605 (by native_decide),
      pm_prefix_eq initPM 183 1606 (by native_decide),
      pm_prefix_eq initPM 183 1607 (by native_decide),
      pm_prefix_eq initPM 183 1608 (by native_decide)]

theorem pm_full_1636 (initPM : Store) :
    denoteGraph pm initPM 1636
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
           denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2 := by
  rw [pm_val initPM 184 1636 (by native_decide) (by native_decide)]
  rw [show pm.nodes[184]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1605 + r)), outs := [1636], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 184 1605 (by native_decide),
      pm_prefix_eq initPM 184 1606 (by native_decide),
      pm_prefix_eq initPM 184 1607 (by native_decide),
      pm_prefix_eq initPM 184 1608 (by native_decide)]

theorem pm_full_1637 (initPM : Store) :
    denoteGraph pm initPM 1637
      = elemwiseAdd (denoteGraph pm initPM 1629)
          (allToAllPrimWithDims pm.numRanks 0
            [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
             denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2) := by
  rw [pm_val initPM 185 1637 (by native_decide) (by native_decide)]
  rw [show pm.nodes[185]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [1629, 1633], outs := [1637] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 185 1629 (by native_decide),
      pm_prefix_eq initPM 185 1633 (by native_decide)]
  rw [pm_full_1633]

theorem pm_full_1638 (initPM : Store) :
    denoteGraph pm initPM 1638
      = elemwiseAdd (denoteGraph pm initPM 1630)
          (allToAllPrimWithDims pm.numRanks 1
            [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
             denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2) := by
  rw [pm_val initPM 186 1638 (by native_decide) (by native_decide)]
  rw [show pm.nodes[186]'(by native_decide)
      = { rank := 1, op := "OpName.FW_add", ins := [1630, 1634], outs := [1638] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 186 1630 (by native_decide),
      pm_prefix_eq initPM 186 1634 (by native_decide)]
  rw [pm_full_1634]

theorem pm_full_1639 (initPM : Store) :
    denoteGraph pm initPM 1639
      = elemwiseAdd (denoteGraph pm initPM 1631)
          (allToAllPrimWithDims pm.numRanks 2
            [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
             denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2) := by
  rw [pm_val initPM 187 1639 (by native_decide) (by native_decide)]
  rw [show pm.nodes[187]'(by native_decide)
      = { rank := 2, op := "OpName.FW_add", ins := [1631, 1635], outs := [1639] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 187 1631 (by native_decide),
      pm_prefix_eq initPM 187 1635 (by native_decide)]
  rw [pm_full_1635]

theorem pm_full_1640 (initPM : Store) :
    denoteGraph pm initPM 1640
      = elemwiseAdd (denoteGraph pm initPM 1632)
          (allToAllPrimWithDims pm.numRanks 3
            [denoteGraph pm initPM 1605, denoteGraph pm initPM 1606,
             denoteGraph pm initPM 1607, denoteGraph pm initPM 1608] 1 2) := by
  rw [pm_val initPM 188 1640 (by native_decide) (by native_decide)]
  rw [show pm.nodes[188]'(by native_decide)
      = { rank := 3, op := "OpName.FW_add", ins := [1632, 1636], outs := [1640] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 188 1632 (by native_decide),
      pm_prefix_eq initPM 188 1636 (by native_decide)]
  rw [pm_full_1636]

theorem denote_pm_goal_29_1637 (s : Store) :
    denoteGraph pm_goal_29 s 1637
      = elemwiseAdd (s 1629)
          (allToAllPrimWithDims 4 0 [s 1605, s 1606, s 1607, s 1608] 1 2) := by
  simp only [pm_goal_29, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_29_1638 (s : Store) :
    denoteGraph pm_goal_29 s 1638
      = elemwiseAdd (s 1630)
          (allToAllPrimWithDims 4 1 [s 1605, s 1606, s 1607, s 1608] 1 2) := by
  simp only [pm_goal_29, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_29_1639 (s : Store) :
    denoteGraph pm_goal_29 s 1639
      = elemwiseAdd (s 1631)
          (allToAllPrimWithDims 4 2 [s 1605, s 1606, s 1607, s 1608] 1 2) := by
  simp only [pm_goal_29, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_29_1640 (s : Store) :
    denoteGraph pm_goal_29 s 1640
      = elemwiseAdd (s 1632)
          (allToAllPrimWithDims 4 3 [s 1605, s 1606, s 1607, s 1608] 1 2) := by
  simp only [pm_goal_29, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem pm_frame_1637_self (initPM : Store) :
    denoteGraph pm initPM 1637 = denoteGraph pm_goal_29 (denoteGraph pm initPM) 1637 := by
  rw [denote_pm_goal_29_1637]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1637 initPM

theorem pm_frame_1638_self (initPM : Store) :
    denoteGraph pm initPM 1638 = denoteGraph pm_goal_29 (denoteGraph pm initPM) 1638 := by
  rw [denote_pm_goal_29_1638]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1638 initPM

theorem pm_frame_1639_self (initPM : Store) :
    denoteGraph pm initPM 1639 = denoteGraph pm_goal_29 (denoteGraph pm initPM) 1639 := by
  rw [denote_pm_goal_29_1639]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1639 initPM

theorem pm_frame_1640_self (initPM : Store) :
    denoteGraph pm initPM 1640 = denoteGraph pm_goal_29 (denoteGraph pm initPM) 1640 := by
  rw [denote_pm_goal_29_1640]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1640 initPM

-- ========== helper: hInitCut 分离成独立 lemma 避免单次 heartbeat 超时 ==========
lemma goal_29_hInitCut_helper (Ssm Spm : Store)
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
    (hg257 : InitGoalHolds pm.numRanks goal_257 Ssm Spm) 
    (hg259 : InitGoalHolds pm.numRanks goal_259 Ssm Spm) 
    (hg261 : InitGoalHolds pm.numRanks goal_261 Ssm Spm) 
    (hg263 : InitGoalHolds pm.numRanks goal_263 Ssm Spm) 
    (hg265 : InitGoalHolds pm.numRanks goal_265 Ssm Spm) 
    (hg267 : InitGoalHolds pm.numRanks goal_267 Ssm Spm) 
    (hg269 : InitGoalHolds pm.numRanks goal_269 Ssm Spm) :
    InitGoalsHold pm_goal_29.numRanks goal_29_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_29.numRanks = pm.numRanks := by native_decide
  rw [hnr]; intro g hg
  simp only [goal_29_cut_initGoals, goal_29_prereqs, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hinitC g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact hg257
    · exact hg259
    · exact hg261
    · exact hg263
    · exact hg265
    · exact hg267
    · exact hg269

-- ========== 总装 ==========
theorem goal_29_cut_to_full (h : goal_29_stmt_cut) : goal_29_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_29.numRanks = pm.numRanks := by native_decide
  -- 938 = goal_269.ts [1,8,32]; 1629-1632 = goal_269 tps [1,8,8]; 601 = goal_28.ts [1,8,32]; 1605-1608 = goal_28 tps [1,2,32]
  have h938_smsh : (Ssm 938).shape = [1, 8, 32] := by
    have h := hg269.1; simp only [goal_269] at h; exact h
  have h601_smsh : (Ssm 601).shape = [1, 8, 32] := by
    have h := hg28.1; simp only [goal_28] at h; exact h
  -- shape 提取改用 obtain 模式 (goal_28 同款), 避免 simpa 触发整图 whnf (line~397 deterministic timeout 根因)
  have h269tp := hg269.2.1
  simp only [goal_269, List.map, List.cons.injEq, and_true] at h269tp
  obtain ⟨h1629_pmsh, h1630_pmsh, h1631_pmsh, h1632_pmsh⟩ := h269tp
  have h28tp := hg28.2.1
  simp only [goal_28, List.map, List.cons.injEq, and_true] at h28tp
  obtain ⟨h1605_pmsh, h1606_pmsh, h1607_pmsh, h1608_pmsh⟩ := h28tp
  have hSM29 : StoreShapesHold Ssm sm_goal_29InitEnv := by
    intro tid sh hsh
    rw [sm_goal_29InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_29InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h601_smsh
    · exact h938_smsh
  have hPM29 : StoreShapesHold Spm pm_goal_29InitEnv := by
    intro tid sh hsh
    rw [pm_goal_29InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_29InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1605_pmsh
    · exact h1606_pmsh
    · exact h1607_pmsh
    · exact h1608_pmsh
    · exact h1629_pmsh
    · exact h1630_pmsh
    · exact h1631_pmsh
    · exact h1632_pmsh
  have hInitCut : InitGoalsHold pm_goal_29.numRanks goal_29_cut_initGoals Ssm Spm :=
    goal_29_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg257 hg259 hg261 hg263 hg265 hg267 hg269
  have hcut := h Ssm Spm hSM29 hPM29 hInitCut
  have hsmf : Ssm 602 = denoteGraph sm_goal_29 Ssm 602 := by
    rw [hSsm]; exact sm_frame_602_self initSM
  have hpm1637 : Spm 1637 = denoteGraph pm_goal_29 Spm 1637 := by
    rw [hSpm]; exact pm_frame_1637_self initPM
  have hpm1638 : Spm 1638 = denoteGraph pm_goal_29 Spm 1638 := by
    rw [hSpm]; exact pm_frame_1638_self initPM
  have hpm1639 : Spm 1639 = denoteGraph pm_goal_29 Spm 1639 := by
    rw [hSpm]; exact pm_frame_1639_self initPM
  have hpm1640 : Spm 1640 = denoteGraph pm_goal_29 Spm 1640 := by
    rw [hSpm]; exact pm_frame_1640_self initPM
  rw [hnr] at hcut
  simp only [goal_29, List.map] at hcut ⊢
  rw [hsmf, hpm1637, hpm1638, hpm1639, hpm1640]
  exact hcut

theorem goal_29_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_29 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_29_stmt := goal_29_cut_to_full prove_goal_29_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_29] using this

end TrainVerify.Denote.GeneratedGoals
