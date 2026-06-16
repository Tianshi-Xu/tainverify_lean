/- goal_40 桥 (prereqs=[2..30,32,36,37,257,259,261,263,265,267,269,271,277], 41 个)。
   结构: FW_transpose(params=[2,3]) + AllToAll(dim1→2 re-shard, idim=1 odim=2), multi-tps gatherDim=3。
   SM=FW_transpose(615,p=[2,3])→618 (sm node 43)。
   PM=4×AllToAllPrim(ins=(range4).map(1805+r), idim=1 odim=2)→1849-1852 (pm node 260-263),
      然后 4×FW_transpose(1849+r, p=[2,3])→1853-1856 (pm node 272-275, 非相邻)。
   615=goal_37 输出 [1,4,8,8] (dim1-sharded tps=1805-1808 [1,1,8,8], gatherDim=1)。
   核心语义已在 prove_goal_40_cut 处理, bridge 只做 frame。套 Goal279Bridge 模板。 -/
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal32Bridge
import denote.gpt_ly4_regen.Goal36Bridge
import denote.gpt_ly4_regen.Goal37Bridge
import denote.gpt_ly4_regen.Goal277Bridge
import denote.gpt_ly4_regen.Goal_40

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_40 算 618 (FW_transpose p=[2,3]) ==========
theorem denote_sm_goal_40_618 (s : Store) :
    denoteGraph sm_goal_40 s 618 = transposeAxes 2 3 (s 615) := by
  simp only [sm_goal_40, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_40 算 1853-1856 (AllToAll→FW_transpose) ==========
theorem denote_pm_goal_40_1853 (s : Store) :
    denoteGraph pm_goal_40 s 1853 =
      transposeAxes 2 3 (allToAllPrimWithDims 4 0 [s 1805, s 1806, s 1807, s 1808] 1 2) := by
  simp only [pm_goal_40, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_40_1854 (s : Store) :
    denoteGraph pm_goal_40 s 1854 =
      transposeAxes 2 3 (allToAllPrimWithDims 4 1 [s 1805, s 1806, s 1807, s 1808] 1 2) := by
  simp only [pm_goal_40, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_40_1855 (s : Store) :
    denoteGraph pm_goal_40 s 1855 =
      transposeAxes 2 3 (allToAllPrimWithDims 4 2 [s 1805, s 1806, s 1807, s 1808] 1 2) := by
  simp only [pm_goal_40, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_40_1856 (s : Store) :
    denoteGraph pm_goal_40 s 1856 =
      transposeAxes 2 3 (allToAllPrimWithDims 4 3 [s 1805, s 1806, s 1807, s 1808] 1 2) := by
  simp only [pm_goal_40, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 618 (node 43 FW_transpose) ==========
theorem sm_frame_618_self (initSM : Store) :
    denoteGraph sm initSM 618 = denoteGraph sm_goal_40 (denoteGraph sm initSM) 618 := by
  rw [denote_sm_goal_40_618]
  rw [sm_val initSM 43 618 (by native_decide) (by native_decide)]
  rw [show sm.nodes[43]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [615], outs := [618], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 43 615 (by native_decide)]

-- ========== full pm: AllToAll 输出 1849-1852 (node 260-263) ==========
theorem pm_full_1849 (initPM : Store) :
    denoteGraph pm initPM 1849
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1805, denoteGraph pm initPM 1806,
           denoteGraph pm initPM 1807, denoteGraph pm initPM 1808] 1 2 := by
  rw [pm_val initPM 260 1849 (by native_decide) (by native_decide)]
  rw [show pm.nodes[260]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := [1805, 1806, 1807, 1808], outs := [1849], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 260 1805 (by native_decide),
      pm_prefix_eq initPM 260 1806 (by native_decide),
      pm_prefix_eq initPM 260 1807 (by native_decide),
      pm_prefix_eq initPM 260 1808 (by native_decide)]

theorem pm_full_1850 (initPM : Store) :
    denoteGraph pm initPM 1850
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1805, denoteGraph pm initPM 1806,
           denoteGraph pm initPM 1807, denoteGraph pm initPM 1808] 1 2 := by
  rw [pm_val initPM 261 1850 (by native_decide) (by native_decide)]
  rw [show pm.nodes[261]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := [1805, 1806, 1807, 1808], outs := [1850], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 261 1805 (by native_decide),
      pm_prefix_eq initPM 261 1806 (by native_decide),
      pm_prefix_eq initPM 261 1807 (by native_decide),
      pm_prefix_eq initPM 261 1808 (by native_decide)]

theorem pm_full_1851 (initPM : Store) :
    denoteGraph pm initPM 1851
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1805, denoteGraph pm initPM 1806,
           denoteGraph pm initPM 1807, denoteGraph pm initPM 1808] 1 2 := by
  rw [pm_val initPM 262 1851 (by native_decide) (by native_decide)]
  rw [show pm.nodes[262]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := [1805, 1806, 1807, 1808], outs := [1851], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 262 1805 (by native_decide),
      pm_prefix_eq initPM 262 1806 (by native_decide),
      pm_prefix_eq initPM 262 1807 (by native_decide),
      pm_prefix_eq initPM 262 1808 (by native_decide)]

theorem pm_full_1852 (initPM : Store) :
    denoteGraph pm initPM 1852
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1805, denoteGraph pm initPM 1806,
           denoteGraph pm initPM 1807, denoteGraph pm initPM 1808] 1 2 := by
  rw [pm_val initPM 263 1852 (by native_decide) (by native_decide)]
  rw [show pm.nodes[263]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := [1805, 1806, 1807, 1808], outs := [1852], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 263 1805 (by native_decide),
      pm_prefix_eq initPM 263 1806 (by native_decide),
      pm_prefix_eq initPM 263 1807 (by native_decide),
      pm_prefix_eq initPM 263 1808 (by native_decide)]

-- ========== full pm: FW_transpose 输出 1853-1856 (node 272-275) ==========
theorem pm_full_1853 (initPM : Store) :
    denoteGraph pm initPM 1853 = transposeAxes 2 3 (denoteGraph pm initPM 1849) := by
  rw [pm_val initPM 272 1853 (by native_decide) (by native_decide)]
  rw [show pm.nodes[272]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1849], outs := [1853], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 272 1849 (by native_decide)]

theorem pm_full_1854 (initPM : Store) :
    denoteGraph pm initPM 1854 = transposeAxes 2 3 (denoteGraph pm initPM 1850) := by
  rw [pm_val initPM 273 1854 (by native_decide) (by native_decide)]
  rw [show pm.nodes[273]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1850], outs := [1854], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 273 1850 (by native_decide)]

theorem pm_full_1855 (initPM : Store) :
    denoteGraph pm initPM 1855 = transposeAxes 2 3 (denoteGraph pm initPM 1851) := by
  rw [pm_val initPM 274 1855 (by native_decide) (by native_decide)]
  rw [show pm.nodes[274]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1851], outs := [1855], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 274 1851 (by native_decide)]

theorem pm_full_1856 (initPM : Store) :
    denoteGraph pm initPM 1856 = transposeAxes 2 3 (denoteGraph pm initPM 1852) := by
  rw [pm_val initPM 275 1856 (by native_decide) (by native_decide)]
  rw [show pm.nodes[275]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1852], outs := [1856], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 275 1852 (by native_decide)]

-- ========== PM self-frame: 1853-1856 (组合 AllToAll + FW_transpose) ==========
theorem pm_frame_1853_self (initPM : Store) :
    denoteGraph pm initPM 1853 = denoteGraph pm_goal_40 (denoteGraph pm initPM) 1853 := by
  rw [denote_pm_goal_40_1853, pm_full_1853, pm_full_1849, show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1854_self (initPM : Store) :
    denoteGraph pm initPM 1854 = denoteGraph pm_goal_40 (denoteGraph pm initPM) 1854 := by
  rw [denote_pm_goal_40_1854, pm_full_1854, pm_full_1850, show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1855_self (initPM : Store) :
    denoteGraph pm initPM 1855 = denoteGraph pm_goal_40 (denoteGraph pm initPM) 1855 := by
  rw [denote_pm_goal_40_1855, pm_full_1855, pm_full_1851, show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1856_self (initPM : Store) :
    denoteGraph pm initPM 1856 = denoteGraph pm_goal_40 (denoteGraph pm initPM) 1856 := by
  rw [denote_pm_goal_40_1856, pm_full_1856, pm_full_1852, show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_40_cut_to_full (h : goal_40_stmt_cut) : goal_40_stmt := by
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
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_40.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_40.numRanks goal_40_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_40_cut_initGoals, goal_40_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg32
      · exact hg36
      · exact hg37
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg277
  -- shape: 615 = goal_37.ts [1,4,8,8]; 1805-1808 = goal_37.tps [1,1,8,8]
  have h615_smsh : (Ssm 615).shape = [1, 4, 8, 8] := by
    have h := hg37.1; simp only [goal_37] at h; exact h
  have hx : (Spm 1805).shape = [1,1,8,8] ∧ (Spm 1806).shape = [1,1,8,8] ∧
            (Spm 1807).shape = [1,1,8,8] ∧ (Spm 1808).shape = [1,1,8,8] := by
    have h := hg37.2.1
    simp only [goal_37, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1805sh, h1806sh, h1807sh, h1808sh⟩ := hx
  have hSM40 : StoreShapesHold Ssm sm_goal_40InitEnv := by
    intro tid sh hsh
    rw [sm_goal_40InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_40InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h615_smsh
  have hPM40 : StoreShapesHold Spm pm_goal_40InitEnv := by
    intro tid sh hsh
    rw [pm_goal_40InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_40InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1805sh
    · exact h1806sh
    · exact h1807sh
    · exact h1808sh
  have hcut := h Ssm Spm hSM40 hPM40 hInitCut
  have hsmf : Ssm 618 = denoteGraph sm_goal_40 Ssm 618 := by
    rw [hSsm]; exact sm_frame_618_self initSM
  have hpm1853 : Spm 1853 = denoteGraph pm_goal_40 Spm 1853 := by
    rw [hSpm]; exact pm_frame_1853_self initPM
  have hpm1854 : Spm 1854 = denoteGraph pm_goal_40 Spm 1854 := by
    rw [hSpm]; exact pm_frame_1854_self initPM
  have hpm1855 : Spm 1855 = denoteGraph pm_goal_40 Spm 1855 := by
    rw [hSpm]; exact pm_frame_1855_self initPM
  have hpm1856 : Spm 1856 = denoteGraph pm_goal_40 Spm 1856 := by
    rw [hSpm]; exact pm_frame_1856_self initPM
  rw [hnr] at hcut
  simp only [goal_40, List.map] at hcut ⊢
  rw [hsmf, hpm1853, hpm1854, hpm1855, hpm1856]
  exact hcut

theorem goal_40_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_40 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_40_stmt := goal_40_cut_to_full prove_goal_40_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_40] using this

end TrainVerify.Denote.GeneratedGoals