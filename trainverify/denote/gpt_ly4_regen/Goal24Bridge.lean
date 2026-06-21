/- goal_24 桥 (prereqs=[2..23,257,259,261,263,265])。
   第18种结构: FW_add over two AllGather(dim2) inputs, multi-tps。
   SM=FW_add(907,592)→593 (node 24, [1,8,32])。
   PM=4×FW_add(1501-1504,1477-1480)→1505-1508 (node 148-151, 各 rank 一份 tp, dim2-sharded [1,8,8])。
   907=goal_259 输出 [1,8,32] (AllGather of 1501-1504); 592=goal_23 输出 [1,8,32] (AllGather of 1477-1480)。
   multi-tps 输出, gatherDim=2 (reconstructWithDim 2 4 0)。
   套 Goal23Bridge (SM 单 op + 4×PM multi-tps frame + reconstructWithDim 总装) 模板;
   语义 (add 分配进两个 gather, fw_add_split_dim2_4_1_8_32) 已在 prove_goal_24_cut 里处理, bridge 只做 frame。
   SM node idx=24, PM node idx=148-151。 -/
import denote.gpt_ly4_regen.Goal20Bridge
import denote.gpt_ly4_regen.Goal21Bridge
import denote.gpt_ly4_regen.Goal22Bridge
import denote.gpt_ly4_regen.Goal23Bridge
import denote.gpt_ly4_regen.Goal259Bridge
import denote.gpt_ly4_regen.Goal_24

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_24 算 593 (FW_add) ==========
theorem denote_sm_goal_24_593 (s : Store) :
    denoteGraph sm_goal_24 s 593 = elemwiseAdd (s 907) (s 592) := by
  simp only [sm_goal_24, denoteGraph, List.foldl]
  rw [applyNode_fw_add2_out]

-- ========== 迷你图 pm_goal_24 算 1505-1508 (4×FW_add) ==========
theorem denote_pm_goal_24_1505 (s : Store) :
    denoteGraph pm_goal_24 s 1505 = elemwiseAdd (s 1501) (s 1477) := by
  simp only [pm_goal_24, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]

theorem denote_pm_goal_24_1506 (s : Store) :
    denoteGraph pm_goal_24 s 1506 = elemwiseAdd (s 1502) (s 1478) := by
  simp only [pm_goal_24, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_24_1507 (s : Store) :
    denoteGraph pm_goal_24 s 1507 = elemwiseAdd (s 1503) (s 1479) := by
  simp only [pm_goal_24, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_24_1508 (s : Store) :
    denoteGraph pm_goal_24 s 1508 = elemwiseAdd (s 1504) (s 1480) := by
  simp only [pm_goal_24, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 593 (node 24 FW_add) ==========
theorem sm_frame_593_self (initSM : Store) :
    denoteGraph sm initSM 593 = denoteGraph sm_goal_24 (denoteGraph sm initSM) 593 := by
  rw [denote_sm_goal_24_593]
  rw [sm_val initSM 24 593 (by native_decide) (by native_decide)]
  rw [show sm.nodes[24]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [907, 592], outs := [593] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [sm_prefix_eq initSM 24 907 (by native_decide),
      sm_prefix_eq initSM 24 592 (by native_decide)]

-- ========== PM self-frame: 1505-1508 (4×FW_add, node 148-151) ==========
theorem pm_frame_1505_self (initPM : Store) :
    denoteGraph pm initPM 1505
      = elemwiseAdd (denoteGraph pm initPM 1501) (denoteGraph pm initPM 1477) := by
  rw [pm_val initPM 148 1505 (by native_decide) (by native_decide)]
  rw [show pm.nodes[148]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [1501, 1477], outs := [1505] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 148 1501 (by native_decide),
      pm_prefix_eq initPM 148 1477 (by native_decide)]

theorem pm_frame_1506_self (initPM : Store) :
    denoteGraph pm initPM 1506
      = elemwiseAdd (denoteGraph pm initPM 1502) (denoteGraph pm initPM 1478) := by
  rw [pm_val initPM 149 1506 (by native_decide) (by native_decide)]
  rw [show pm.nodes[149]'(by native_decide)
      = { rank := 1, op := "OpName.FW_add", ins := [1502, 1478], outs := [1506] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 149 1502 (by native_decide),
      pm_prefix_eq initPM 149 1478 (by native_decide)]

theorem pm_frame_1507_self (initPM : Store) :
    denoteGraph pm initPM 1507
      = elemwiseAdd (denoteGraph pm initPM 1503) (denoteGraph pm initPM 1479) := by
  rw [pm_val initPM 150 1507 (by native_decide) (by native_decide)]
  rw [show pm.nodes[150]'(by native_decide)
      = { rank := 2, op := "OpName.FW_add", ins := [1503, 1479], outs := [1507] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 150 1503 (by native_decide),
      pm_prefix_eq initPM 150 1479 (by native_decide)]

theorem pm_frame_1508_self (initPM : Store) :
    denoteGraph pm initPM 1508
      = elemwiseAdd (denoteGraph pm initPM 1504) (denoteGraph pm initPM 1480) := by
  rw [pm_val initPM 151 1508 (by native_decide) (by native_decide)]
  rw [show pm.nodes[151]'(by native_decide)
      = { rank := 3, op := "OpName.FW_add", ins := [1504, 1480], outs := [1508] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 151 1504 (by native_decide),
      pm_prefix_eq initPM 151 1480 (by native_decide)]

-- ========== 总装 ==========
theorem goal_24_cut_to_full (h : goal_24_stmt_cut) : goal_24_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg257 hg259 hg261 hg263 hg265 hinitC
  have hnr : pm_goal_24.numRanks = pm.numRanks := by native_decide
  -- 907 = goal_259.ts (gathered, [1,8,32]); 592 = goal_23.ts (gathered, [1,8,32]).
  have h907_smsh : (Ssm 907).shape = [1, 8, 32] := by
    have h := hg259.1; simp only [goal_259] at h; exact h
  have h592_smsh : (Ssm 592).shape = [1, 8, 32] := by
    have h := hg23.1; simp only [goal_23] at h; exact h
  have hSM24 : StoreShapesHold Ssm sm_goal_24InitEnv := by
    intro tid sh hsh
    rw [sm_goal_24InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_24InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h592_smsh
    · exact h907_smsh
  have hPM24 : StoreShapesHold Spm pm_goal_24InitEnv := by
    intro tid sh hsh
    rw [pm_goal_24InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_24InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    -- pm 上 1477-1480 = goal_23 的 4 个 tp (dim2-sharded), 各 [1,8,8];
    -- 1501-1504 = goal_259 的 4 个 tp (dim2-sharded), 各 [1,8,8]。
    have h592tp := hg23.2.1
    simp only [goal_23, List.map] at h592tp
    have h1477_pmsh : (Spm 1477).shape = [1, 8, 8] := by
      have := congrArg List.head? h592tp; simpa using this
    have h1478_pmsh : (Spm 1478).shape = [1, 8, 8] := by
      have := congrArg List.tail h592tp
      have := congrArg List.head? this; simpa using this
    have h1479_pmsh : (Spm 1479).shape = [1, 8, 8] := by
      have := congrArg (List.tail ∘ List.tail) h592tp
      have := congrArg List.head? this; simpa using this
    have h1480_pmsh : (Spm 1480).shape = [1, 8, 8] := by
      have := congrArg (List.tail ∘ List.tail ∘ List.tail) h592tp
      have := congrArg List.head? this; simpa using this
    have h907tp := hg259.2.1
    simp only [goal_259, List.map] at h907tp
    have h1501_pmsh : (Spm 1501).shape = [1, 8, 8] := by
      have := congrArg List.head? h907tp; simpa using this
    have h1502_pmsh : (Spm 1502).shape = [1, 8, 8] := by
      have := congrArg List.tail h907tp
      have := congrArg List.head? this; simpa using this
    have h1503_pmsh : (Spm 1503).shape = [1, 8, 8] := by
      have := congrArg (List.tail ∘ List.tail) h907tp
      have := congrArg List.head? this; simpa using this
    have h1504_pmsh : (Spm 1504).shape = [1, 8, 8] := by
      have := congrArg (List.tail ∘ List.tail ∘ List.tail) h907tp
      have := congrArg List.head? this; simpa using this
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1477_pmsh
    · exact h1478_pmsh
    · exact h1479_pmsh
    · exact h1480_pmsh
    · exact h1501_pmsh
    · exact h1502_pmsh
    · exact h1503_pmsh
    · exact h1504_pmsh
  have hInitCut : InitGoalsHold pm_goal_24.numRanks goal_24_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_24_cut_initGoals, goal_24_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg257, hg259, hg261, hg263, hg265, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM24 hPM24 hInitCut
  -- Frame: 593 (sm), 1505-1508 (pm)
  have hsmf : Ssm 593 = denoteGraph sm_goal_24 Ssm 593 := by
    rw [hSsm]; exact sm_frame_593_self initSM
  have hpm1505 : Spm 1505 = denoteGraph pm_goal_24 Spm 1505 := by
    rw [denote_pm_goal_24_1505]; rw [hSpm]; exact pm_frame_1505_self initPM
  have hpm1506 : Spm 1506 = denoteGraph pm_goal_24 Spm 1506 := by
    rw [denote_pm_goal_24_1506]; rw [hSpm]; exact pm_frame_1506_self initPM
  have hpm1507 : Spm 1507 = denoteGraph pm_goal_24 Spm 1507 := by
    rw [denote_pm_goal_24_1507]; rw [hSpm]; exact pm_frame_1507_self initPM
  have hpm1508 : Spm 1508 = denoteGraph pm_goal_24 Spm 1508 := by
    rw [denote_pm_goal_24_1508]; rw [hSpm]; exact pm_frame_1508_self initPM
  rw [hnr] at hcut
  simp only [goal_24, List.map] at hcut ⊢
  rw [hsmf, hpm1505, hpm1506, hpm1507, hpm1508]
  exact hcut

theorem goal_24_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_24 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_24_stmt := goal_24_cut_to_full prove_goal_24_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
