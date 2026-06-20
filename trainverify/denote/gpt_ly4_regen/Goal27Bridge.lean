/- goal_27 桥 (prereqs=[2..26,257,259,261,263,265,267])。
   第22种结构: pointwise FW_gelu over AllGather(dim2), multi-tps。
   SM=FW_gelu(598)→599 (node 28, [1,8,128])。
   PM=4×FW_gelu(1561-1564)→1585-1588 (node 169-172, 各 rank 一份 tp, 输入 dim2-sharded [1,8,32])。
   输入 598=goal_26 输出 [1,8,128] (AllGather of 1561-1564, gatherDim2); 1561-1564=goal_26 的 4 个 tp。
   multi-tps 输出, gatherDim=2 (reconstructWithDim 2 4 0); PM mini-graph 无 collective (输入已分片)。
   与 Goal26Bridge 同构, 仅算子从 binary FW_linear 换成 unary FW_gelu (单输入);
   语义 (fw_gelu 对 allGatherPrimDimN dim2 的逐点分配, fw_gelu_allGatherPrimDimN_eq) 已在
   prove_goal_27_cut 里处理, bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal23Bridge
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal25Bridge
import denote.gpt_ly4_regen.Goal26Bridge
import denote.gpt_ly4_regen.Goal_27

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_27 算 599 (FW_gelu) ==========
theorem denote_sm_goal_27_599 (s : Store) :
    denoteGraph sm_goal_27 s 599 = fw_gelu (s 598) := by
  simp only [sm_goal_27, denoteGraph, List.foldl]
  rw [applyNode_fw_gelu_out]

-- ========== 迷你图 pm_goal_27 算 1585-1588 (4×FW_gelu) ==========
theorem denote_pm_goal_27_1585 (s : Store) :
    denoteGraph pm_goal_27 s 1585 = fw_gelu (s 1561) := by
  simp only [pm_goal_27, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_gelu_out]

theorem denote_pm_goal_27_1586 (s : Store) :
    denoteGraph pm_goal_27 s 1586 = fw_gelu (s 1562) := by
  simp only [pm_goal_27, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_gelu_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_27_1587 (s : Store) :
    denoteGraph pm_goal_27 s 1587 = fw_gelu (s 1563) := by
  simp only [pm_goal_27, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_gelu_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_27_1588 (s : Store) :
    denoteGraph pm_goal_27 s 1588 = fw_gelu (s 1564) := by
  simp only [pm_goal_27, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_gelu_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 599 (node 28 FW_gelu) ==========
theorem sm_frame_599_self (initSM : Store) :
    denoteGraph sm initSM 599 = denoteGraph sm_goal_27 (denoteGraph sm initSM) 599 := by
  rw [denote_sm_goal_27_599]
  rw [sm_val initSM 28 599 (by native_decide) (by native_decide)]
  rw [show sm.nodes[28]'(by native_decide)
      = { rank := 0, op := "OpName.FW_gelu", ins := [598], outs := [599] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [sm_prefix_eq initSM 28 598 (by native_decide)]

-- ========== PM self-frame: 1585-1588 (4×FW_gelu, node 169-172) ==========
theorem pm_frame_1585_self (initPM : Store) :
    denoteGraph pm initPM 1585
      = fw_gelu (denoteGraph pm initPM 1561) := by
  rw [pm_val initPM 169 1585 (by native_decide) (by native_decide)]
  rw [show pm.nodes[169]'(by native_decide)
      = { rank := 0, op := "OpName.FW_gelu", ins := [1561], outs := [1585] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 169 1561 (by native_decide)]

theorem pm_frame_1586_self (initPM : Store) :
    denoteGraph pm initPM 1586
      = fw_gelu (denoteGraph pm initPM 1562) := by
  rw [pm_val initPM 170 1586 (by native_decide) (by native_decide)]
  rw [show pm.nodes[170]'(by native_decide)
      = { rank := 1, op := "OpName.FW_gelu", ins := [1562], outs := [1586] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 170 1562 (by native_decide)]

theorem pm_frame_1587_self (initPM : Store) :
    denoteGraph pm initPM 1587
      = fw_gelu (denoteGraph pm initPM 1563) := by
  rw [pm_val initPM 171 1587 (by native_decide) (by native_decide)]
  rw [show pm.nodes[171]'(by native_decide)
      = { rank := 2, op := "OpName.FW_gelu", ins := [1563], outs := [1587] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 171 1563 (by native_decide)]

theorem pm_frame_1588_self (initPM : Store) :
    denoteGraph pm initPM 1588
      = fw_gelu (denoteGraph pm initPM 1564) := by
  rw [pm_val initPM 172 1588 (by native_decide) (by native_decide)]
  rw [show pm.nodes[172]'(by native_decide)
      = { rank := 3, op := "OpName.FW_gelu", ins := [1564], outs := [1588] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 172 1564 (by native_decide)]

-- ========== 总装 ==========
theorem goal_27_cut_to_full (h : goal_27_stmt_cut) : goal_27_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg257 hg259 hg261 hg263 hg265 hg267 hinitC
  have hnr : pm_goal_27.numRanks = pm.numRanks := by native_decide
  -- 598 = goal_26.ts (AllGather of 1561-1564, [1,8,128]); 1561-1564 = goal_26.tps (各 [1,8,32]).
  have h598_smsh : (Ssm 598).shape = [1, 8, 128] := by
    have h := hg26.1; simp only [goal_26] at h; exact h
  -- goal_26 的 4 个 tp shape, 从 InitGoalHolds 的第二投影拆。
  have h26tp := hg26.2.1
  simp only [goal_26, List.map] at h26tp
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at h26tp
  obtain ⟨e1, e2, e3, e4, _⟩ := h26tp
  -- SM init env: 只有 598 → [1,8,128]
  have hSM27 : StoreShapesHold Ssm sm_goal_27InitEnv := by
    intro tid sh hsh
    rw [sm_goal_27InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_27InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h598_smsh
  -- PM init env: 1561-1564 → [1,8,32]
  have hPM27 : StoreShapesHold Spm pm_goal_27InitEnv := by
    intro tid sh hsh
    rw [pm_goal_27InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_27InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  have hInitCut : InitGoalsHold pm_goal_27.numRanks goal_27_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_27_cut_initGoals, goal_27_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
  have hcut := h Ssm Spm hSM27 hPM27 hInitCut
  -- Frame: 599 (sm), 1585-1588 (pm)
  have hsmf : Ssm 599 = denoteGraph sm_goal_27 Ssm 599 := by
    rw [hSsm]; exact sm_frame_599_self initSM
  have hpm1585 : Spm 1585 = denoteGraph pm_goal_27 Spm 1585 := by
    rw [denote_pm_goal_27_1585]; rw [hSpm]; exact pm_frame_1585_self initPM
  have hpm1586 : Spm 1586 = denoteGraph pm_goal_27 Spm 1586 := by
    rw [denote_pm_goal_27_1586]; rw [hSpm]; exact pm_frame_1586_self initPM
  have hpm1587 : Spm 1587 = denoteGraph pm_goal_27 Spm 1587 := by
    rw [denote_pm_goal_27_1587]; rw [hSpm]; exact pm_frame_1587_self initPM
  have hpm1588 : Spm 1588 = denoteGraph pm_goal_27 Spm 1588 := by
    rw [denote_pm_goal_27_1588]; rw [hSpm]; exact pm_frame_1588_self initPM
  rw [hnr] at hcut
  simp only [goal_27, List.map] at hcut ⊢
  rw [hsmf, hpm1585, hpm1586, hpm1587, hpm1588]
  exact hcut

theorem goal_27_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_27 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_27_stmt := goal_27_cut_to_full prove_goal_27_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
