/- goal_267 桥 (prereqs=[2..24,257,259,261,263,265])。
   第19种结构: FW_multiref (第一输出 934) over X(593), 然后 PM 用 AllToAll 重新分片。
   SM=FW_multiref(593)→[934,938] 取第一输出 934 (node 25, [1,8,32])。
   PM=4×FW_multiref(150X)→[346X,162X] 取第一输出 3469/3475/3481/3487 (node 152-155),
      4×AllToAllPrim([3469,3475,3481,3487], idim=2, odim=1)→1525-1528 (node 156-159)。
   goal_267: SM 934 = gather(dim1) of PM[1525-1528]。
   1505-1508=goal_24 的 4 个 tp (dim2-sharded [1,8,8]); 593=goal_24.ts [1,8,32]。
   语义 (multiref 第一输出=输入, allToAll=chunk∘allGather, gather 恢复) 已在 prove_goal_267_cut 里处理。
   bridge 只做 frame: SM node 25 第一输出; PM node 156-159 (AllToAll, 上游 multiref 第一输出 152-155)。
   套 Goal259Bridge (multiref frame) + Goal257Bridge (AllToAll frame) 混合模板。 -/
import denote.gpt_ly4_regen.Goal20Bridge
import denote.gpt_ly4_regen.Goal21Bridge
import denote.gpt_ly4_regen.Goal22Bridge
import denote.gpt_ly4_regen.Goal23Bridge
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal_267

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_267 算 934 (FW_multiref 第一输出 = s 593) ==========
theorem denote_sm_goal_267_934 (s : Store) :
    denoteGraph sm_goal_267 s 934 = s 593 := by
  simp only [sm_goal_267, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_first_out]

-- ========== 迷你图 pm_goal_267 算 1525-1528 (AllToAll, 上游 multiref 第一输出) ==========
-- 上游 multiref 第一输出 3469/3475/3481/3487 = s 1505/1506/1507/1508
theorem denote_pm_goal_267_1525 (s : Store) :
    denoteGraph pm_goal_267 s 1525 =
      allToAllPrimWithDims 4 0 [s 1505, s 1506, s 1507, s 1508] 2 1 := by
  simp only [pm_goal_267, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  repeat (first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)])

theorem denote_pm_goal_267_1526 (s : Store) :
    denoteGraph pm_goal_267 s 1526 =
      allToAllPrimWithDims 4 1 [s 1505, s 1506, s 1507, s 1508] 2 1 := by
  simp only [pm_goal_267, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  repeat (first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)])

theorem denote_pm_goal_267_1527 (s : Store) :
    denoteGraph pm_goal_267 s 1527 =
      allToAllPrimWithDims 4 2 [s 1505, s 1506, s 1507, s 1508] 2 1 := by
  simp only [pm_goal_267, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  repeat (first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)])

theorem denote_pm_goal_267_1528 (s : Store) :
    denoteGraph pm_goal_267 s 1528 =
      allToAllPrimWithDims 4 3 [s 1505, s 1506, s 1507, s 1508] 2 1 := by
  simp only [pm_goal_267, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  repeat (first
    | rw [applyNode_fw_multiref2_first_out]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)])

-- ========== SM self-frame: full sm 算 934 (node 25 FW_multiref 第一输出) ==========
theorem sm_frame_934_self (initSM : Store) :
    denoteGraph sm initSM 934 = denoteGraph sm_goal_267 (denoteGraph sm initSM) 934 := by
  rw [denote_sm_goal_267_934]
  rw [sm_val initSM 25 934 (by native_decide) (by native_decide)]
  rw [show sm.nodes[25]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [593], outs := [934, 938], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [sm_prefix_eq initSM 25 593 (by native_decide)]

-- ========== full pm: multiref 第一输出 3469/3475/3481/3487 (node 152-155) = s 1505..1508 ==========
theorem pm_full_3469 (initPM : Store) :
    denoteGraph pm initPM 3469 = denoteGraph pm initPM 1505 := by
  rw [pm_val initPM 152 3469 (by native_decide) (by native_decide)]
  rw [show pm.nodes[152]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1505], outs := [3469, 1629], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 152 1505 (by native_decide)]

theorem pm_full_3475 (initPM : Store) :
    denoteGraph pm initPM 3475 = denoteGraph pm initPM 1506 := by
  rw [pm_val initPM 153 3475 (by native_decide) (by native_decide)]
  rw [show pm.nodes[153]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1506], outs := [3475, 1630], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 153 1506 (by native_decide)]

theorem pm_full_3481 (initPM : Store) :
    denoteGraph pm initPM 3481 = denoteGraph pm initPM 1507 := by
  rw [pm_val initPM 154 3481 (by native_decide) (by native_decide)]
  rw [show pm.nodes[154]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1507], outs := [3481, 1631], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 154 1507 (by native_decide)]

theorem pm_full_3487 (initPM : Store) :
    denoteGraph pm initPM 3487 = denoteGraph pm initPM 1508 := by
  rw [pm_val initPM 155 3487 (by native_decide) (by native_decide)]
  rw [show pm.nodes[155]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1508], outs := [3487, 1632], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_first_out]
  rw [pm_prefix_eq initPM 155 1508 (by native_decide)]

-- ========== PM self-frame: 1525-1528 (AllToAll node 156-159) ==========
theorem pm_frame_1525_self (initPM : Store) :
    denoteGraph pm initPM 1525
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1505, denoteGraph pm initPM 1506,
           denoteGraph pm initPM 1507, denoteGraph pm initPM 1508] 2 1 := by
  rw [pm_val initPM 156 1525 (by native_decide) (by native_decide)]
  rw [show pm.nodes[156]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim", ins := [3469, 3475, 3481, 3487],
          outs := [1525], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  rw [pm_prefix_eq initPM 156 3469 (by native_decide),
      pm_prefix_eq initPM 156 3475 (by native_decide),
      pm_prefix_eq initPM 156 3481 (by native_decide),
      pm_prefix_eq initPM 156 3487 (by native_decide)]
  rw [pm_full_3469, pm_full_3475, pm_full_3481, pm_full_3487]

theorem pm_frame_1526_self (initPM : Store) :
    denoteGraph pm initPM 1526
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1505, denoteGraph pm initPM 1506,
           denoteGraph pm initPM 1507, denoteGraph pm initPM 1508] 2 1 := by
  rw [pm_val initPM 157 1526 (by native_decide) (by native_decide)]
  rw [show pm.nodes[157]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim", ins := [3469, 3475, 3481, 3487],
          outs := [1526], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  rw [pm_prefix_eq initPM 157 3469 (by native_decide),
      pm_prefix_eq initPM 157 3475 (by native_decide),
      pm_prefix_eq initPM 157 3481 (by native_decide),
      pm_prefix_eq initPM 157 3487 (by native_decide)]
  rw [pm_full_3469, pm_full_3475, pm_full_3481, pm_full_3487]

theorem pm_frame_1527_self (initPM : Store) :
    denoteGraph pm initPM 1527
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1505, denoteGraph pm initPM 1506,
           denoteGraph pm initPM 1507, denoteGraph pm initPM 1508] 2 1 := by
  rw [pm_val initPM 158 1527 (by native_decide) (by native_decide)]
  rw [show pm.nodes[158]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim", ins := [3469, 3475, 3481, 3487],
          outs := [1527], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  rw [pm_prefix_eq initPM 158 3469 (by native_decide),
      pm_prefix_eq initPM 158 3475 (by native_decide),
      pm_prefix_eq initPM 158 3481 (by native_decide),
      pm_prefix_eq initPM 158 3487 (by native_decide)]
  rw [pm_full_3469, pm_full_3475, pm_full_3481, pm_full_3487]

theorem pm_frame_1528_self (initPM : Store) :
    denoteGraph pm initPM 1528
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1505, denoteGraph pm initPM 1506,
           denoteGraph pm initPM 1507, denoteGraph pm initPM 1508] 2 1 := by
  rw [pm_val initPM 159 1528 (by native_decide) (by native_decide)]
  rw [show pm.nodes[159]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim", ins := [3469, 3475, 3481, 3487],
          outs := [1528], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map_cons, List.map_nil]
  rw [pm_prefix_eq initPM 159 3469 (by native_decide),
      pm_prefix_eq initPM 159 3475 (by native_decide),
      pm_prefix_eq initPM 159 3481 (by native_decide),
      pm_prefix_eq initPM 159 3487 (by native_decide)]
  rw [pm_full_3469, pm_full_3475, pm_full_3481, pm_full_3487]

-- ========== 总装: goal_267_cut_to_full ==========
theorem goal_267_cut_to_full (h : goal_267_stmt_cut) : goal_267_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg257 hg259 hg261 hg263 hg265 hinitC
  have hnr : pm_goal_267.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 593=goal_24.ts [1,8,32]; 1505-1508=goal_24.tps [1,8,8]
  have h593_smsh : (Ssm 593).shape = [1, 8, 32] := by
    have h := hg24.1; simp only [goal_24] at h; exact h
  have h24tp := hg24.2.1
  simp only [goal_24, List.map] at h24tp
  have h1505_pmsh : (Spm 1505).shape = [1, 8, 8] := by
    have := congrArg List.head? h24tp; simpa using this
  have h1506_pmsh : (Spm 1506).shape = [1, 8, 8] := by
    have := congrArg List.tail h24tp
    have := congrArg List.head? this; simpa using this
  have h1507_pmsh : (Spm 1507).shape = [1, 8, 8] := by
    have := congrArg (List.tail ∘ List.tail) h24tp
    have := congrArg List.head? this; simpa using this
  have h1508_pmsh : (Spm 1508).shape = [1, 8, 8] := by
    have := congrArg (List.tail ∘ List.tail ∘ List.tail) h24tp
    have := congrArg List.head? this; simpa using this
  have hSM267 : StoreShapesHold Ssm sm_goal_267InitEnv := by
    intro tid sh hsh
    rw [sm_goal_267InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_267InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h593_smsh
  have hPM267 : StoreShapesHold Spm pm_goal_267InitEnv := by
    intro tid sh hsh
    rw [pm_goal_267InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_267InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1505_pmsh
    · exact h1506_pmsh
    · exact h1507_pmsh
    · exact h1508_pmsh
  have hInitCut : InitGoalsHold pm_goal_267.numRanks goal_267_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_267_cut_initGoals, goal_267_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
  have hcut := h Ssm Spm hSM267 hPM267 hInitCut
  -- Frame: 934 (sm), 1525-1528 (pm)
  have hsmf : Ssm 934 = denoteGraph sm_goal_267 Ssm 934 := by
    rw [hSsm]; exact sm_frame_934_self initSM
  have hpm1525 : Spm 1525 = denoteGraph pm_goal_267 Spm 1525 := by
    rw [denote_pm_goal_267_1525]; rw [hSpm]
    have := pm_frame_1525_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1526 : Spm 1526 = denoteGraph pm_goal_267 Spm 1526 := by
    rw [denote_pm_goal_267_1526]; rw [hSpm]
    have := pm_frame_1526_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1527 : Spm 1527 = denoteGraph pm_goal_267 Spm 1527 := by
    rw [denote_pm_goal_267_1527]; rw [hSpm]
    have := pm_frame_1527_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1528 : Spm 1528 = denoteGraph pm_goal_267 Spm 1528 := by
    rw [denote_pm_goal_267_1528]; rw [hSpm]
    have := pm_frame_1528_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_267, List.map] at hcut ⊢
  rw [hsmf, hpm1525, hpm1526, hpm1527, hpm1528]
  exact hcut

theorem goal_267_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_267 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_267_stmt := goal_267_cut_to_full prove_goal_267_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals