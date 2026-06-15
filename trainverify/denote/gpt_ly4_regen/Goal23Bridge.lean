/- goal_23 桥 (prereqs=[2..22,257,261,263,265])。
   第17种结构: column-parallel FW_linear。
   SM=FW_linear(590,591)→592 (node 23, [1,8,32])。
   PM=4×FW_linear(590,1473-1476)→1477-1480 (node 144-147, 各 rank 一份 tp, 输出 dim2-sharded [1,8,8])。
   590=goal_22 输出 [1,8,32] (replicated 单 tp 同 tid); 591=initGoal_591 (AllGather of 1473-1476, weight column-split)。
   multi-tps 输出, gatherDim=2 (reconstructWithDim 2 4 0)。
   套 Goal19Bridge (SM 单 op + 4×PM multi-tps frame + reconstructWithDim 总装) 模板;
   语义 (column-parallel split, fw_linear_column_parallel_4_1_8_32_8) 已在 prove_goal_23_cut 里处理, bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal19Bridge
import denote.gpt_ly4_regen.Goal20Bridge
import denote.gpt_ly4_regen.Goal21Bridge
import denote.gpt_ly4_regen.Goal22Bridge
import denote.gpt_ly4_regen.Goal_23

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_23 算 592 (FW_linear) ==========
theorem denote_sm_goal_23_592 (s : Store) :
    denoteGraph sm_goal_23 s 592 = fw_linear (s 590) (s 591) := by
  simp only [sm_goal_23, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_23 算 1477-1480 (4×FW_linear) ==========
theorem denote_pm_goal_23_1477 (s : Store) :
    denoteGraph pm_goal_23 s 1477 = fw_linear (s 590) (s 1473) := by
  simp only [pm_goal_23, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]

theorem denote_pm_goal_23_1478 (s : Store) :
    denoteGraph pm_goal_23 s 1478 = fw_linear (s 590) (s 1474) := by
  simp only [pm_goal_23, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_23_1479 (s : Store) :
    denoteGraph pm_goal_23 s 1479 = fw_linear (s 590) (s 1475) := by
  simp only [pm_goal_23, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_23_1480 (s : Store) :
    denoteGraph pm_goal_23 s 1480 = fw_linear (s 590) (s 1476) := by
  simp only [pm_goal_23, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 592 (node 23 FW_linear) ==========
theorem sm_frame_592_self (initSM : Store) :
    denoteGraph sm initSM 592 = denoteGraph sm_goal_23 (denoteGraph sm initSM) 592 := by
  rw [denote_sm_goal_23_592]
  rw [sm_val initSM 23 592 (by native_decide) (by native_decide)]
  rw [show sm.nodes[23]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [590, 591], outs := [592] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 23 590 (by native_decide),
      sm_prefix_eq initSM 23 591 (by native_decide)]

-- ========== PM self-frame: 1477-1480 (4×FW_linear, node 144-147) ==========
theorem pm_frame_1477_self (initPM : Store) :
    denoteGraph pm initPM 1477
      = fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1473) := by
  rw [pm_val initPM 144 1477 (by native_decide) (by native_decide)]
  rw [show pm.nodes[144]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [590, 1473], outs := [1477] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 144 590 (by native_decide),
      pm_prefix_eq initPM 144 1473 (by native_decide)]

theorem pm_frame_1478_self (initPM : Store) :
    denoteGraph pm initPM 1478
      = fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1474) := by
  rw [pm_val initPM 145 1478 (by native_decide) (by native_decide)]
  rw [show pm.nodes[145]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [590, 1474], outs := [1478] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 145 590 (by native_decide),
      pm_prefix_eq initPM 145 1474 (by native_decide)]

theorem pm_frame_1479_self (initPM : Store) :
    denoteGraph pm initPM 1479
      = fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1475) := by
  rw [pm_val initPM 146 1479 (by native_decide) (by native_decide)]
  rw [show pm.nodes[146]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [590, 1475], outs := [1479] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 146 590 (by native_decide),
      pm_prefix_eq initPM 146 1475 (by native_decide)]

theorem pm_frame_1480_self (initPM : Store) :
    denoteGraph pm initPM 1480
      = fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1476) := by
  rw [pm_val initPM 147 1480 (by native_decide) (by native_decide)]
  rw [show pm.nodes[147]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [590, 1476], outs := [1480] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 147 590 (by native_decide),
      pm_prefix_eq initPM 147 1476 (by native_decide)]

-- ========== 总装 ==========
theorem goal_23_cut_to_full (h : goal_23_stmt_cut) : goal_23_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_23.numRanks = pm.numRanks := by native_decide
  -- 590 = goal_22.ts (replicated, [1,8,32]); 591 = initGoal_591 (AllGather of weight cols).
  have h590_smsh : (Ssm 590).shape = [1, 8, 32] := by
    have h := hg22.1; simp only [goal_22] at h; exact h
  have h591_smsh : (Ssm 591).shape = [32, 32] := by
    have h := hinitC initGoal_591 (by simp only [initGoals]; decide)
    exact h.1
  have hSM23 : StoreShapesHold Ssm sm_goal_23InitEnv := by
    intro tid sh hsh
    rw [sm_goal_23InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_23InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h590_smsh
    · exact h591_smsh
  have hPM23 : StoreShapesHold Spm pm_goal_23InitEnv := by
    intro tid sh hsh
    rw [pm_goal_23InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_23InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    -- pm 上 590 = goal_22 单 tp (replicated, 同 tid 590), [1,8,32];
    -- 1473-1476 = initGoal_591 的 4 个 tp (column-split weight), 各 [8,32]。
    have h590_pmsh : (Spm 590).shape = [1, 8, 32] := by
      have h := hg22.2.1; simp only [goal_22, List.map, List.cons.injEq, and_true] at h
      exact h
    have h591_full := hinitC initGoal_591 (by simp only [initGoals]; decide)
    have h591tp := h591_full.2.1
    simp only [initGoal_591, List.map] at h591tp
    have h1473_pmsh : (Spm 1473).shape = [8, 32] := by
      have := congrArg List.head? h591tp; simpa using this
    have h1474_pmsh : (Spm 1474).shape = [8, 32] := by
      have := congrArg List.tail h591tp
      have := congrArg List.head? this; simpa using this
    have h1475_pmsh : (Spm 1475).shape = [8, 32] := by
      have := congrArg (List.tail ∘ List.tail) h591tp
      have := congrArg List.head? this; simpa using this
    have h1476_pmsh : (Spm 1476).shape = [8, 32] := by
      have := congrArg (List.tail ∘ List.tail ∘ List.tail) h591tp
      have := congrArg List.head? this; simpa using this
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h590_pmsh
    · exact h1473_pmsh
    · exact h1474_pmsh
    · exact h1475_pmsh
    · exact h1476_pmsh
  have hInitCut : InitGoalsHold pm_goal_23.numRanks goal_23_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_23_cut_initGoals, goal_23_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg261
      · exact hg263
      · exact hg265
  have hcut := h Ssm Spm hSM23 hPM23 hInitCut
  -- Frame: 592 (sm), 1477-1480 (pm)
  have hsmf : Ssm 592 = denoteGraph sm_goal_23 Ssm 592 := by
    rw [hSsm]; exact sm_frame_592_self initSM
  have hpm1477 : Spm 1477 = denoteGraph pm_goal_23 Spm 1477 := by
    rw [denote_pm_goal_23_1477]; rw [hSpm]; exact pm_frame_1477_self initPM
  have hpm1478 : Spm 1478 = denoteGraph pm_goal_23 Spm 1478 := by
    rw [denote_pm_goal_23_1478]; rw [hSpm]; exact pm_frame_1478_self initPM
  have hpm1479 : Spm 1479 = denoteGraph pm_goal_23 Spm 1479 := by
    rw [denote_pm_goal_23_1479]; rw [hSpm]; exact pm_frame_1479_self initPM
  have hpm1480 : Spm 1480 = denoteGraph pm_goal_23 Spm 1480 := by
    rw [denote_pm_goal_23_1480]; rw [hSpm]; exact pm_frame_1480_self initPM
  rw [hnr] at hcut
  simp only [goal_23, List.map] at hcut ⊢
  rw [hsmf, hpm1477, hpm1478, hpm1479, hpm1480]
  exact hcut

theorem goal_23_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_23 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_23_stmt := goal_23_cut_to_full prove_goal_23_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_23] using this

end TrainVerify.Denote.GeneratedGoals
