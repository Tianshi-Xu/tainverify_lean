/- goal_28 桥 (prereqs=[2..27,257,259,261,263,265,267])。
   第23种结构: AllToAll(dim2→dim1 re-shard) + column-parallel FW_linear, multi-tps, gatherDim=1。
   SM=FW_linear(599,600)→601 (node 29, [1,8,128]→[1,8,32], W=[32,128] 列并行)。
   PM=4×AllToAllPrim((range4).map(1585+),idim=2,odim=1)→1601-1604 (node 173-176, params=[2,1]),
      4×FW_linear(160X,600)→1605-1608 (node 177-180, 各 rank 一份 tp, 输出 [1,2,32])。
   输入 599=goal_27 输出 [1,8,128] (AllGather of 1585-1588 on dim2); 1585-1588=goal_27 的 4 个 tp [1,8,32]。
   600 复制 (initGoal_600, SM 600 = PM 600, [32,128])。
   AllToAll 把 dim2-sharded 的 599 重排成 dim1-sharded chunk, 每 rank FW_linear 得 dim1 分片,
   multi-tps gatherDim=1。PM mini-graph 有 collective (AllToAll), 套 Goal21Bridge AllToAll 模板。
   核心语义已在 prove_goal_28_cut 处理, bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal25Bridge
import denote.gpt_ly4_regen.Goal26Bridge
import denote.gpt_ly4_regen.Goal27Bridge
import denote.gpt_ly4_regen.Goal_28

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_28 算 601 (FW_linear) ==========
theorem denote_sm_goal_28_601 (s : Store) :
    denoteGraph sm_goal_28 s 601 = fw_linear (s 599) (s 600) := by
  simp only [sm_goal_28, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== SM self-frame: full sm 算 601 (node 29 FW_linear) ==========
theorem sm_frame_601_self (initSM : Store) :
    denoteGraph sm initSM 601 = denoteGraph sm_goal_28 (denoteGraph sm initSM) 601 := by
  rw [denote_sm_goal_28_601]
  rw [sm_val initSM 29 601 (by native_decide) (by native_decide)]
  rw [show sm.nodes[29]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [599, 600], outs := [601] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 29 599 (by native_decide),
      sm_prefix_eq initSM 29 600 (by native_decide)]

theorem pm_full_1601 (initPM : Store) :
    denoteGraph pm initPM 1601
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
           denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1 := by
  rw [pm_val initPM 173 1601 (by native_decide) (by native_decide)]
  rw [show pm.nodes[173]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1585 + r)), outs := [1601], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 173 1585 (by native_decide),
      pm_prefix_eq initPM 173 1586 (by native_decide),
      pm_prefix_eq initPM 173 1587 (by native_decide),
      pm_prefix_eq initPM 173 1588 (by native_decide)]

theorem pm_full_1602 (initPM : Store) :
    denoteGraph pm initPM 1602
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
           denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1 := by
  rw [pm_val initPM 174 1602 (by native_decide) (by native_decide)]
  rw [show pm.nodes[174]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1585 + r)), outs := [1602], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 174 1585 (by native_decide),
      pm_prefix_eq initPM 174 1586 (by native_decide),
      pm_prefix_eq initPM 174 1587 (by native_decide),
      pm_prefix_eq initPM 174 1588 (by native_decide)]

theorem pm_full_1603 (initPM : Store) :
    denoteGraph pm initPM 1603
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
           denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1 := by
  rw [pm_val initPM 175 1603 (by native_decide) (by native_decide)]
  rw [show pm.nodes[175]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1585 + r)), outs := [1603], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 175 1585 (by native_decide),
      pm_prefix_eq initPM 175 1586 (by native_decide),
      pm_prefix_eq initPM 175 1587 (by native_decide),
      pm_prefix_eq initPM 175 1588 (by native_decide)]

theorem pm_full_1604 (initPM : Store) :
    denoteGraph pm initPM 1604
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
           denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1 := by
  rw [pm_val initPM 176 1604 (by native_decide) (by native_decide)]
  rw [show pm.nodes[176]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1585 + r)), outs := [1604], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 176 1585 (by native_decide),
      pm_prefix_eq initPM 176 1586 (by native_decide),
      pm_prefix_eq initPM 176 1587 (by native_decide),
      pm_prefix_eq initPM 176 1588 (by native_decide)]

theorem pm_full_1605 (initPM : Store) :
    denoteGraph pm initPM 1605
      = fw_linear
          (allToAllPrimWithDims pm.numRanks 0
            [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
             denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1)
          (denoteGraph pm initPM 600) := by
  rw [pm_val initPM 177 1605 (by native_decide) (by native_decide)]
  rw [show pm.nodes[177]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1601, 600], outs := [1605] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 177 1601 (by native_decide),
      pm_prefix_eq initPM 177 600 (by native_decide)]
  rw [pm_full_1601]

theorem pm_full_1606 (initPM : Store) :
    denoteGraph pm initPM 1606
      = fw_linear
          (allToAllPrimWithDims pm.numRanks 1
            [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
             denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1)
          (denoteGraph pm initPM 600) := by
  rw [pm_val initPM 178 1606 (by native_decide) (by native_decide)]
  rw [show pm.nodes[178]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [1602, 600], outs := [1606] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 178 1602 (by native_decide),
      pm_prefix_eq initPM 178 600 (by native_decide)]
  rw [pm_full_1602]

theorem pm_full_1607 (initPM : Store) :
    denoteGraph pm initPM 1607
      = fw_linear
          (allToAllPrimWithDims pm.numRanks 2
            [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
             denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1)
          (denoteGraph pm initPM 600) := by
  rw [pm_val initPM 179 1607 (by native_decide) (by native_decide)]
  rw [show pm.nodes[179]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [1603, 600], outs := [1607] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 179 1603 (by native_decide),
      pm_prefix_eq initPM 179 600 (by native_decide)]
  rw [pm_full_1603]

theorem pm_full_1608 (initPM : Store) :
    denoteGraph pm initPM 1608
      = fw_linear
          (allToAllPrimWithDims pm.numRanks 3
            [denoteGraph pm initPM 1585, denoteGraph pm initPM 1586,
             denoteGraph pm initPM 1587, denoteGraph pm initPM 1588] 2 1)
          (denoteGraph pm initPM 600) := by
  rw [pm_val initPM 180 1608 (by native_decide) (by native_decide)]
  rw [show pm.nodes[180]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [1604, 600], outs := [1608] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 180 1604 (by native_decide),
      pm_prefix_eq initPM 180 600 (by native_decide)]
  rw [pm_full_1604]

theorem denote_pm_goal_28_1605 (s : Store) :
    denoteGraph pm_goal_28 s 1605
      = fw_linear (allToAllPrimWithDims 4 0 [s 1585, s 1586, s 1587, s 1588] 2 1) (s 600) := by
  simp only [pm_goal_28, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_28_1606 (s : Store) :
    denoteGraph pm_goal_28 s 1606
      = fw_linear (allToAllPrimWithDims 4 1 [s 1585, s 1586, s 1587, s 1588] 2 1) (s 600) := by
  simp only [pm_goal_28, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_28_1607 (s : Store) :
    denoteGraph pm_goal_28 s 1607
      = fw_linear (allToAllPrimWithDims 4 2 [s 1585, s 1586, s 1587, s 1588] 2 1) (s 600) := by
  simp only [pm_goal_28, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_28_1608 (s : Store) :
    denoteGraph pm_goal_28 s 1608
      = fw_linear (allToAllPrimWithDims 4 3 [s 1585, s 1586, s 1587, s 1588] 2 1) (s 600) := by
  simp only [pm_goal_28, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem pm_frame_1605_self (initPM : Store) :
    denoteGraph pm initPM 1605 = denoteGraph pm_goal_28 (denoteGraph pm initPM) 1605 := by
  rw [denote_pm_goal_28_1605]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1605 initPM

theorem pm_frame_1606_self (initPM : Store) :
    denoteGraph pm initPM 1606 = denoteGraph pm_goal_28 (denoteGraph pm initPM) 1606 := by
  rw [denote_pm_goal_28_1606]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1606 initPM

theorem pm_frame_1607_self (initPM : Store) :
    denoteGraph pm initPM 1607 = denoteGraph pm_goal_28 (denoteGraph pm initPM) 1607 := by
  rw [denote_pm_goal_28_1607]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1607 initPM

theorem pm_frame_1608_self (initPM : Store) :
    denoteGraph pm initPM 1608 = denoteGraph pm_goal_28 (denoteGraph pm initPM) 1608 := by
  rw [denote_pm_goal_28_1608]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_1608 initPM

-- ========== 总装 ==========
theorem goal_28_cut_to_full (h : goal_28_stmt_cut) : goal_28_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg257 hg259 hg261 hg263 hg265 hg267 hinitC
  have hnr : pm_goal_28.numRanks = pm.numRanks := by native_decide
  -- shape 弱化
  have h599_smsh : (Ssm 599).shape = [1, 8, 128] := by
    have h := hg27.1; simp only [goal_27] at h; exact h
  have hg600 := hinitC initGoal_600 (by simp only [initGoals]; decide)
  have h600_smsh : (Ssm 600).shape = [32, 128] := by
    have h := hg600.1; simp only [initGoal_600] at h; exact h
  have h600_repl : Ssm 600 = Spm 600 := by
    have hrec := hg600.2.2
    simp only [initGoal_600, List.map] at hrec
    rw [reconstructWithDim_singleton] at hrec
    exact hrec
  have h600_pmsh : (Spm 600).shape = [32, 128] := by rw [← h600_repl]; exact h600_smsh
  have h27tp := hg27.2.1
  simp only [goal_27, List.map, List.cons.injEq, and_true] at h27tp
  obtain ⟨e1585, e1586, e1587, e1588⟩ := h27tp
  have hSM28 : StoreShapesHold Ssm sm_goal_28InitEnv := by
    intro tid sh hsh
    rw [sm_goal_28InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_28InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h599_smsh
    · exact h600_smsh
  have hPM28 : StoreShapesHold Spm pm_goal_28InitEnv := by
    intro tid sh hsh
    rw [pm_goal_28InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_28InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h600_pmsh
    · exact e1585
    · exact e1586
    · exact e1587
    · exact e1588
  have hInitCut : InitGoalsHold pm_goal_28.numRanks goal_28_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_28_cut_initGoals, goal_28_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg257, hg259, hg261, hg263, hg265, hg267, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM28 hPM28 hInitCut
  have hsmf : Ssm 601 = denoteGraph sm_goal_28 Ssm 601 := by
    rw [hSsm]; exact sm_frame_601_self initSM
  have hpm1605 : Spm 1605 = denoteGraph pm_goal_28 Spm 1605 := by
    rw [hSpm]; exact pm_frame_1605_self initPM
  have hpm1606 : Spm 1606 = denoteGraph pm_goal_28 Spm 1606 := by
    rw [hSpm]; exact pm_frame_1606_self initPM
  have hpm1607 : Spm 1607 = denoteGraph pm_goal_28 Spm 1607 := by
    rw [hSpm]; exact pm_frame_1607_self initPM
  have hpm1608 : Spm 1608 = denoteGraph pm_goal_28 Spm 1608 := by
    rw [hSpm]; exact pm_frame_1608_self initPM
  rw [hnr] at hcut
  simp only [goal_28, List.map] at hcut ⊢
  rw [hsmf, hpm1605, hpm1606, hpm1607, hpm1608]
  exact hcut

theorem goal_28_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_28 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_28_stmt := goal_28_cut_to_full prove_goal_28_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
