/- goal_21 桥 (prereqs=[2..20,257,261,263,265])。
   第16种结构: AllToAll+FW_contiguous+AllGather (单 tp)。结构同 goal_18 (AllToAll+op+AllGather 单 tp), 中间 op 换 contiguous (恒等)。
   SM=FW_contiguous(588)→589 (node 21)。
   PM=4×AllToAllPrim((range4).map(1433+),idim=3,odim=1)→1449-1452 (node 131-134),
      4×FW_contiguous(1449..)→1453-1456 (node 135-138),
      AllGatherPrim((range4).map(1453+),dim=1)→589 (node 139, 单 tp)。
   588=goal_20 输出 [1,8,4,8]; 1433-1436=goal_20 tps [1,8,4,2]。
   套 Goal18Bridge 模板, op 换 applyNode_fw_contiguous_out_g21。bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal14Bridge
import denote.gpt_ly4_regen.Goal18Bridge
import denote.gpt_ly4_regen.Goal19Bridge
import denote.gpt_ly4_regen.Goal20Bridge
import denote.gpt_ly4_regen.Goal_21

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_21 算 589 (FW_contiguous) ==========
theorem denote_sm_goal_21_589 (s : Store) :
    denoteGraph sm_goal_21 s 589 = s 588 := by
  simp only [sm_goal_21, denoteGraph, List.foldl]
  rw [applyNode_fw_contiguous_out_g21]

-- ========== SM self-frame: full sm 算 589 (node 21) ==========
theorem sm_frame_589_self (initSM : Store) :
    denoteGraph sm initSM 589 = denoteGraph sm_goal_21 (denoteGraph sm initSM) 589 := by
  rw [denote_sm_goal_21_589]
  rw [sm_val initSM 21 589 (by native_decide) (by native_decide)]
  rw [show sm.nodes[21]'(by native_decide)
      = { rank := 0, op := "OpName.FW_contiguous", ins := [588], outs := [589] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g21]
  rw [sm_prefix_eq initSM 21 588 (by native_decide)]

-- ========== full pm: AllToAll 输出 1449-1452 (node 131-134) ==========
theorem pm_full_1449 (initPM : Store) :
    denoteGraph pm initPM 1449
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 131 1449 (by native_decide) (by native_decide)]
  rw [show pm.nodes[131]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1433 + r)), outs := [1449], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 131 1433 (by native_decide),
      pm_prefix_eq initPM 131 1434 (by native_decide),
      pm_prefix_eq initPM 131 1435 (by native_decide),
      pm_prefix_eq initPM 131 1436 (by native_decide)]

theorem pm_full_1450 (initPM : Store) :
    denoteGraph pm initPM 1450
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 132 1450 (by native_decide) (by native_decide)]
  rw [show pm.nodes[132]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1433 + r)), outs := [1450], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 132 1433 (by native_decide),
      pm_prefix_eq initPM 132 1434 (by native_decide),
      pm_prefix_eq initPM 132 1435 (by native_decide),
      pm_prefix_eq initPM 132 1436 (by native_decide)]

theorem pm_full_1451 (initPM : Store) :
    denoteGraph pm initPM 1451
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 133 1451 (by native_decide) (by native_decide)]
  rw [show pm.nodes[133]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1433 + r)), outs := [1451], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 133 1433 (by native_decide),
      pm_prefix_eq initPM 133 1434 (by native_decide),
      pm_prefix_eq initPM 133 1435 (by native_decide),
      pm_prefix_eq initPM 133 1436 (by native_decide)]

theorem pm_full_1452 (initPM : Store) :
    denoteGraph pm initPM 1452
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 134 1452 (by native_decide) (by native_decide)]
  rw [show pm.nodes[134]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1433 + r)), outs := [1452], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 134 1433 (by native_decide),
      pm_prefix_eq initPM 134 1434 (by native_decide),
      pm_prefix_eq initPM 134 1435 (by native_decide),
      pm_prefix_eq initPM 134 1436 (by native_decide)]

-- ========== full pm: FW_contiguous 输出 1453-1456 (node 135-138) = AllToAll out (恒等) ==========
theorem pm_full_1453 (initPM : Store) :
    denoteGraph pm initPM 1453
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 135 1453 (by native_decide) (by native_decide)]
  rw [show pm.nodes[135]'(by native_decide)
      = { rank := 0, op := "OpName.FW_contiguous", ins := [1449], outs := [1453] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g21]
  rw [pm_prefix_eq initPM 135 1449 (by native_decide)]
  rw [pm_full_1449]

theorem pm_full_1454 (initPM : Store) :
    denoteGraph pm initPM 1454
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 136 1454 (by native_decide) (by native_decide)]
  rw [show pm.nodes[136]'(by native_decide)
      = { rank := 1, op := "OpName.FW_contiguous", ins := [1450], outs := [1454] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g21]
  rw [pm_prefix_eq initPM 136 1450 (by native_decide)]
  rw [pm_full_1450]

theorem pm_full_1455 (initPM : Store) :
    denoteGraph pm initPM 1455
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 137 1455 (by native_decide) (by native_decide)]
  rw [show pm.nodes[137]'(by native_decide)
      = { rank := 2, op := "OpName.FW_contiguous", ins := [1451], outs := [1455] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g21]
  rw [pm_prefix_eq initPM 137 1451 (by native_decide)]
  rw [pm_full_1451]

theorem pm_full_1456 (initPM : Store) :
    denoteGraph pm initPM 1456
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
           denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1 := by
  rw [pm_val initPM 138 1456 (by native_decide) (by native_decide)]
  rw [show pm.nodes[138]'(by native_decide)
      = { rank := 3, op := "OpName.FW_contiguous", ins := [1452], outs := [1456] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g21]
  rw [pm_prefix_eq initPM 138 1452 (by native_decide)]
  rw [pm_full_1452]

-- ========== PM self-frame: 589 (AllGather node 139, 单 tp) ==========
theorem pm_frame_589_self (initPM : Store) :
    denoteGraph pm initPM 589
      = allGatherPrimDimN 1 4 0
          [allToAllPrimWithDims pm.numRanks 0
              [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
               denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1,
           allToAllPrimWithDims pm.numRanks 1
              [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
               denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1,
           allToAllPrimWithDims pm.numRanks 2
              [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
               denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1,
           allToAllPrimWithDims pm.numRanks 3
              [denoteGraph pm initPM 1433, denoteGraph pm initPM 1434,
               denoteGraph pm initPM 1435, denoteGraph pm initPM 1436] 3 1] := by
  rw [pm_val initPM 139 589 (by native_decide) (by native_decide)]
  rw [show pm.nodes[139]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 1453 + r)), outs := [589], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 139 1453 (by native_decide),
      pm_prefix_eq initPM 139 1454 (by native_decide),
      pm_prefix_eq initPM 139 1455 (by native_decide),
      pm_prefix_eq initPM 139 1456 (by native_decide)]
  rw [pm_full_1453, pm_full_1454, pm_full_1455, pm_full_1456]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 迷你图 pm_goal_21 算 589 ==========
theorem denote_pm_goal_21_589 (s : Store) :
    denoteGraph pm_goal_21 s 589 = allGatherPrimDimN 1 4 0
      [allToAllPrimWithDims 4 0 [s 1433, s 1434, s 1435, s 1436] 3 1,
       allToAllPrimWithDims 4 1 [s 1433, s 1434, s 1435, s 1436] 3 1,
       allToAllPrimWithDims 4 2 [s 1433, s 1434, s 1435, s 1436] 3 1,
       allToAllPrimWithDims 4 3 [s 1433, s 1434, s 1435, s 1436] 3 1] := by
  simp only [pm_goal_21, denoteGraph, GraphDecl.nodes, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  repeat rw [applyNode_fw_contiguous_out_g21]
  congr 1 <;>
    · repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== 总装 ==========
theorem goal_21_cut_to_full (h : goal_21_stmt_cut) : goal_21_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg257 hg261 hg263 hg265 hinitC
  have hnr : pm_goal_21.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 588=goal_20.ts [1,8,4,8]; 1433-1436=goal_20.tps [1,8,4,2]
  have h588_smsh : (Ssm 588).shape = [1, 8, 4, 8] := by
    have h := hg20.1; simp only [goal_20] at h; exact h
  have h1433_pmsh : (Spm 1433).shape = [1, 8, 4, 2] := by
    have h := hg20.2.1; simp only [goal_20, List.map, List.cons.injEq, and_true] at h; exact h.1
  have h1434_pmsh : (Spm 1434).shape = [1, 8, 4, 2] := by
    have h := hg20.2.1; simp only [goal_20, List.map, List.cons.injEq, and_true] at h; exact h.2.1
  have h1435_pmsh : (Spm 1435).shape = [1, 8, 4, 2] := by
    have h := hg20.2.1; simp only [goal_20, List.map, List.cons.injEq, and_true] at h; exact h.2.2.1
  have h1436_pmsh : (Spm 1436).shape = [1, 8, 4, 2] := by
    have h := hg20.2.1; simp only [goal_20, List.map, List.cons.injEq, and_true] at h; exact h.2.2.2
  have hSM21 : StoreShapesHold Ssm sm_goal_21InitEnv := by
    intro tid sh hsh
    rw [sm_goal_21InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_21InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h588_smsh
  have hPM21 : StoreShapesHold Spm pm_goal_21InitEnv := by
    intro tid sh hsh
    rw [pm_goal_21InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_21InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1433_pmsh
    · exact h1434_pmsh
    · exact h1435_pmsh
    · exact h1436_pmsh
  have hInitCut : InitGoalsHold pm_goal_21.numRanks goal_21_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_21_cut_initGoals, goal_21_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg261
      · exact hg263
      · exact hg265
  have hcut := h Ssm Spm hSM21 hPM21 hInitCut
  -- Frame: 589 (sm) 与 589 (pm) 对齐到 mini-graph
  have hsmf : Ssm 589 = denoteGraph sm_goal_21 Ssm 589 := by
    rw [hSsm]; exact sm_frame_589_self initSM
  have hpmf : Spm 589 = denoteGraph pm_goal_21 Spm 589 := by
    rw [denote_pm_goal_21_589]
    rw [hSpm]
    have := pm_frame_589_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_21, List.map] at hcut ⊢
  rw [hsmf, hpmf]
  exact hcut

theorem goal_21_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_21 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_21_stmt := goal_21_cut_to_full prove_goal_21_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
