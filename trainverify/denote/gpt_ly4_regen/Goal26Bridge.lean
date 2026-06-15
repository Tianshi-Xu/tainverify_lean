/- goal_26 桥 (prereqs=[2..25,257,259,261,263,265,267])。
   第21种结构: column-parallel FW_linear (与 goal_23 完全同构, 仅 tids/shape 不同)。
   SM=FW_linear(596,597)→598 (node 27, [1,8,128])。
   PM=4×FW_linear(596,1557-1560)→1561-1564 (node 165-168, 各 rank 一份 tp, 输出 dim2-sharded [1,8,32])。
   596=goal_25 输出 [1,8,32] (replicated 单 tp 同 tid); 597=initGoal_597 (AllGather of 1557-1560, weight column-split)。
   multi-tps 输出, gatherDim=2 (reconstructWithDim 2 4 0); PM mini-graph 无 AllGather 节点。
   套 Goal23Bridge (SM 单 op + 4×PM multi-tps frame + reconstructWithDim 总装) 模板;
   语义 (column-parallel split, fw_linear_column_parallel_4_1_8_32_32) 已在 prove_goal_26_cut 里处理, bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal22Bridge
import denote.gpt_ly4_regen.Goal23Bridge
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal25Bridge
import denote.gpt_ly4_regen.Goal_26

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_26 算 598 (FW_linear) ==========
theorem denote_sm_goal_26_598 (s : Store) :
    denoteGraph sm_goal_26 s 598 = fw_linear (s 596) (s 597) := by
  simp only [sm_goal_26, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_26 算 1561-1564 (4×FW_linear) ==========
theorem denote_pm_goal_26_1561 (s : Store) :
    denoteGraph pm_goal_26 s 1561 = fw_linear (s 596) (s 1557) := by
  simp only [pm_goal_26, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]

theorem denote_pm_goal_26_1562 (s : Store) :
    denoteGraph pm_goal_26 s 1562 = fw_linear (s 596) (s 1558) := by
  simp only [pm_goal_26, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_26_1563 (s : Store) :
    denoteGraph pm_goal_26 s 1563 = fw_linear (s 596) (s 1559) := by
  simp only [pm_goal_26, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_26_1564 (s : Store) :
    denoteGraph pm_goal_26 s 1564 = fw_linear (s 596) (s 1560) := by
  simp only [pm_goal_26, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 598 (node 27 FW_linear) ==========
theorem sm_frame_598_self (initSM : Store) :
    denoteGraph sm initSM 598 = denoteGraph sm_goal_26 (denoteGraph sm initSM) 598 := by
  rw [denote_sm_goal_26_598]
  rw [sm_val initSM 27 598 (by native_decide) (by native_decide)]
  rw [show sm.nodes[27]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [596, 597], outs := [598] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 27 596 (by native_decide),
      sm_prefix_eq initSM 27 597 (by native_decide)]

-- ========== PM self-frame: 1561-1564 (4×FW_linear, node 165-168) ==========
theorem pm_frame_1561_self (initPM : Store) :
    denoteGraph pm initPM 1561
      = fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1557) := by
  rw [pm_val initPM 165 1561 (by native_decide) (by native_decide)]
  rw [show pm.nodes[165]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [596, 1557], outs := [1561] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 165 596 (by native_decide),
      pm_prefix_eq initPM 165 1557 (by native_decide)]

theorem pm_frame_1562_self (initPM : Store) :
    denoteGraph pm initPM 1562
      = fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1558) := by
  rw [pm_val initPM 166 1562 (by native_decide) (by native_decide)]
  rw [show pm.nodes[166]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [596, 1558], outs := [1562] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 166 596 (by native_decide),
      pm_prefix_eq initPM 166 1558 (by native_decide)]

theorem pm_frame_1563_self (initPM : Store) :
    denoteGraph pm initPM 1563
      = fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1559) := by
  rw [pm_val initPM 167 1563 (by native_decide) (by native_decide)]
  rw [show pm.nodes[167]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [596, 1559], outs := [1563] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 167 596 (by native_decide),
      pm_prefix_eq initPM 167 1559 (by native_decide)]

theorem pm_frame_1564_self (initPM : Store) :
    denoteGraph pm initPM 1564
      = fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1560) := by
  rw [pm_val initPM 168 1564 (by native_decide) (by native_decide)]
  rw [show pm.nodes[168]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [596, 1560], outs := [1564] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 168 596 (by native_decide),
      pm_prefix_eq initPM 168 1560 (by native_decide)]

-- ========== 总装 ==========
theorem goal_26_cut_to_full (h : goal_26_stmt_cut) : goal_26_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_26.numRanks = pm.numRanks := by native_decide
  -- 596 = goal_25.ts (replicated, [1,8,32]); 597 = initGoal_597 (AllGather of weight cols).
  have h596_smsh : (Ssm 596).shape = [1, 8, 32] := by
    have h := hg25.1; simp only [goal_25] at h; exact h
  have h597_smsh : (Ssm 597).shape = [128, 32] := by
    have h := hinitC initGoal_597 (by simp only [initGoals]; decide)
    exact h.1
  have hSM26 : StoreShapesHold Ssm sm_goal_26InitEnv := by
    intro tid sh hsh
    rw [sm_goal_26InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_26InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h596_smsh
    · exact h597_smsh
  have hPM26 : StoreShapesHold Spm pm_goal_26InitEnv := by
    intro tid sh hsh
    rw [pm_goal_26InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_26InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    -- pm 上 596 = goal_25 单 tp (replicated, 同 tid 596), [1,8,32];
    -- 1557-1560 = initGoal_597 的 4 个 tp (column-split weight), 各 [32,32]。
    have h596_pmsh : (Spm 596).shape = [1, 8, 32] := by
      have h := hg25.2.1; simp only [goal_25, List.map, List.cons.injEq, and_true] at h
      exact h
    have h597_full := hinitC initGoal_597 (by simp only [initGoals]; decide)
    have h597tp := h597_full.2.1
    simp only [initGoal_597, List.map] at h597tp
    have h1557_pmsh : (Spm 1557).shape = [32, 32] := by
      have := congrArg List.head? h597tp; simpa using this
    have h1558_pmsh : (Spm 1558).shape = [32, 32] := by
      have := congrArg List.tail h597tp
      have := congrArg List.head? this; simpa using this
    have h1559_pmsh : (Spm 1559).shape = [32, 32] := by
      have := congrArg (List.tail ∘ List.tail) h597tp
      have := congrArg List.head? this; simpa using this
    have h1560_pmsh : (Spm 1560).shape = [32, 32] := by
      have := congrArg (List.tail ∘ List.tail ∘ List.tail) h597tp
      have := congrArg List.head? this; simpa using this
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h596_pmsh
    · exact h1557_pmsh
    · exact h1558_pmsh
    · exact h1559_pmsh
    · exact h1560_pmsh
  have hInitCut : InitGoalsHold pm_goal_26.numRanks goal_26_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_26_cut_initGoals, goal_26_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
  have hcut := h Ssm Spm hSM26 hPM26 hInitCut
  -- Frame: 598 (sm), 1561-1564 (pm)
  have hsmf : Ssm 598 = denoteGraph sm_goal_26 Ssm 598 := by
    rw [hSsm]; exact sm_frame_598_self initSM
  have hpm1561 : Spm 1561 = denoteGraph pm_goal_26 Spm 1561 := by
    rw [denote_pm_goal_26_1561]; rw [hSpm]; exact pm_frame_1561_self initPM
  have hpm1562 : Spm 1562 = denoteGraph pm_goal_26 Spm 1562 := by
    rw [denote_pm_goal_26_1562]; rw [hSpm]; exact pm_frame_1562_self initPM
  have hpm1563 : Spm 1563 = denoteGraph pm_goal_26 Spm 1563 := by
    rw [denote_pm_goal_26_1563]; rw [hSpm]; exact pm_frame_1563_self initPM
  have hpm1564 : Spm 1564 = denoteGraph pm_goal_26 Spm 1564 := by
    rw [denote_pm_goal_26_1564]; rw [hSpm]; exact pm_frame_1564_self initPM
  rw [hnr] at hcut
  simp only [goal_26, List.map] at hcut ⊢
  rw [hsmf, hpm1561, hpm1562, hpm1563, hpm1564]
  exact hcut

theorem goal_26_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_26 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_26_stmt := goal_26_cut_to_full prove_goal_26_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_26] using this

end TrainVerify.Denote.GeneratedGoals
