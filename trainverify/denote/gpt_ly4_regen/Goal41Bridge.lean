/- goal_41 桥 (prereqs 46 个)。
   新结构: fw_matmul 双输入, 各自经 AllToAll reshard。
   SM: FW_matmul(613,618)→619 (sm node 44)。613=goal_35 输出(dim2-gather), 618=goal_40 输出(dim3-gather)。
   PM: 8×AllToAllPrim + 4×FW_matmul。
     x-reshard: 4×AllToAll(ins=range(1781..1784), params=[2,1])→1873-1876 (pm node 268-271)。
     y-reshard: 4×AllToAll(ins=range(1853..1856), params=[3,1])→1877-1880 (pm node 280-283)。
     matmul: 4×FW_matmul(1873+r,1877+r)→1881-1884 (pm node 284-287)。
   核心语义(matmul-over-AllToAll-reshard + dim1 all-gather)已在 prove_goal_41_cut 处理, bridge 只做 frame。
   ⚠ full pm 的 AllToAll ins 用 ((List.range 4).map (fun r => base + r)) 形式, mini-graph 用字面 list。
   套 Goal40Bridge 模板。 -/
import denote.gpt_ly4_regen.Goal35Bridge
import denote.gpt_ly4_regen.Goal40Bridge
import denote.gpt_ly4_regen.Goal_41

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

-- ========== 迷你图 pm_goal_41 算 1881-1884 (AllToAll x/y → FW_matmul) ==========
theorem denote_pm_goal_41_1881 (s : Store) :
    denoteGraph pm_goal_41 s 1881 =
      fw_matmul
        (allToAllPrimWithDims 4 0 [s 1781, s 1782, s 1783, s 1784] 2 1)
        (allToAllPrimWithDims 4 0 [s 1853, s 1854, s 1855, s 1856] 3 1) := by
  simp only [pm_goal_41, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]
  congr 1
  all_goals repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_41_1882 (s : Store) :
    denoteGraph pm_goal_41 s 1882 =
      fw_matmul
        (allToAllPrimWithDims 4 1 [s 1781, s 1782, s 1783, s 1784] 2 1)
        (allToAllPrimWithDims 4 1 [s 1853, s 1854, s 1855, s 1856] 3 1) := by
  simp only [pm_goal_41, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]
  congr 1
  all_goals repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_41_1883 (s : Store) :
    denoteGraph pm_goal_41 s 1883 =
      fw_matmul
        (allToAllPrimWithDims 4 2 [s 1781, s 1782, s 1783, s 1784] 2 1)
        (allToAllPrimWithDims 4 2 [s 1853, s 1854, s 1855, s 1856] 3 1) := by
  simp only [pm_goal_41, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]
  congr 1
  all_goals repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_41_1884 (s : Store) :
    denoteGraph pm_goal_41 s 1884 =
      fw_matmul
        (allToAllPrimWithDims 4 3 [s 1781, s 1782, s 1783, s 1784] 2 1)
        (allToAllPrimWithDims 4 3 [s 1853, s 1854, s 1855, s 1856] 3 1) := by
  simp only [pm_goal_41, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]
  congr 1
  all_goals repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 619 (node 44 FW_matmul) ==========
theorem sm_frame_619_self (initSM : Store) :
    denoteGraph sm initSM 619 = denoteGraph sm_goal_41 (denoteGraph sm initSM) 619 := by
  have hsm : denoteGraph sm_goal_41 (denoteGraph sm initSM) 619
      = fw_matmul (denoteGraph sm initSM 613) (denoteGraph sm initSM 618) := by
    simp only [sm_goal_41, denoteGraph, List.foldl]
    rw [applyNode_fw_matmul_out]
  rw [hsm]
  rw [sm_val initSM 44 619 (by native_decide) (by native_decide)]
  rw [show sm.nodes[44]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [613, 618], outs := [619] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [sm_prefix_eq initSM 44 613 (by native_decide),
      sm_prefix_eq initSM 44 618 (by native_decide)]

-- ========== full pm: AllToAll x 输出 1873-1876 (node 268-271, ins=range 1781) ==========
theorem pm_full_1873 (initPM : Store) :
    denoteGraph pm initPM 1873
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
           denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  rw [pm_val initPM 268 1873 (by native_decide) (by native_decide)]
  rw [show pm.nodes[268]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1873], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 268 1781 (by native_decide),
      pm_prefix_eq initPM 268 1782 (by native_decide),
      pm_prefix_eq initPM 268 1783 (by native_decide),
      pm_prefix_eq initPM 268 1784 (by native_decide)]

theorem pm_full_1874 (initPM : Store) :
    denoteGraph pm initPM 1874
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
           denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  rw [pm_val initPM 269 1874 (by native_decide) (by native_decide)]
  rw [show pm.nodes[269]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1874], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 269 1781 (by native_decide),
      pm_prefix_eq initPM 269 1782 (by native_decide),
      pm_prefix_eq initPM 269 1783 (by native_decide),
      pm_prefix_eq initPM 269 1784 (by native_decide)]

theorem pm_full_1875 (initPM : Store) :
    denoteGraph pm initPM 1875
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
           denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  rw [pm_val initPM 270 1875 (by native_decide) (by native_decide)]
  rw [show pm.nodes[270]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1875], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 270 1781 (by native_decide),
      pm_prefix_eq initPM 270 1782 (by native_decide),
      pm_prefix_eq initPM 270 1783 (by native_decide),
      pm_prefix_eq initPM 270 1784 (by native_decide)]

theorem pm_full_1876 (initPM : Store) :
    denoteGraph pm initPM 1876
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1781, denoteGraph pm initPM 1782,
           denoteGraph pm initPM 1783, denoteGraph pm initPM 1784] 2 1 := by
  rw [pm_val initPM 271 1876 (by native_decide) (by native_decide)]
  rw [show pm.nodes[271]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1781 + r)), outs := [1876], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 271 1781 (by native_decide),
      pm_prefix_eq initPM 271 1782 (by native_decide),
      pm_prefix_eq initPM 271 1783 (by native_decide),
      pm_prefix_eq initPM 271 1784 (by native_decide)]

-- ========== full pm: AllToAll y 输出 1877-1880 (node 280-283, ins=range 1853) ==========
theorem pm_full_1877 (initPM : Store) :
    denoteGraph pm initPM 1877
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
           denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  rw [pm_val initPM 280 1877 (by native_decide) (by native_decide)]
  rw [show pm.nodes[280]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1877], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 280 1853 (by native_decide),
      pm_prefix_eq initPM 280 1854 (by native_decide),
      pm_prefix_eq initPM 280 1855 (by native_decide),
      pm_prefix_eq initPM 280 1856 (by native_decide)]

theorem pm_full_1878 (initPM : Store) :
    denoteGraph pm initPM 1878
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
           denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  rw [pm_val initPM 281 1878 (by native_decide) (by native_decide)]
  rw [show pm.nodes[281]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1878], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 281 1853 (by native_decide),
      pm_prefix_eq initPM 281 1854 (by native_decide),
      pm_prefix_eq initPM 281 1855 (by native_decide),
      pm_prefix_eq initPM 281 1856 (by native_decide)]

theorem pm_full_1879 (initPM : Store) :
    denoteGraph pm initPM 1879
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
           denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  rw [pm_val initPM 282 1879 (by native_decide) (by native_decide)]
  rw [show pm.nodes[282]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1879], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 282 1853 (by native_decide),
      pm_prefix_eq initPM 282 1854 (by native_decide),
      pm_prefix_eq initPM 282 1855 (by native_decide),
      pm_prefix_eq initPM 282 1856 (by native_decide)]

theorem pm_full_1880 (initPM : Store) :
    denoteGraph pm initPM 1880
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1853, denoteGraph pm initPM 1854,
           denoteGraph pm initPM 1855, denoteGraph pm initPM 1856] 3 1 := by
  rw [pm_val initPM 283 1880 (by native_decide) (by native_decide)]
  rw [show pm.nodes[283]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1853 + r)), outs := [1880], params := [3, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 283 1853 (by native_decide),
      pm_prefix_eq initPM 283 1854 (by native_decide),
      pm_prefix_eq initPM 283 1855 (by native_decide),
      pm_prefix_eq initPM 283 1856 (by native_decide)]

-- ========== full pm: FW_matmul 输出 1881-1884 (node 284-287) ==========
theorem pm_full_1881 (initPM : Store) :
    denoteGraph pm initPM 1881
      = fw_matmul (denoteGraph pm initPM 1873) (denoteGraph pm initPM 1877) := by
  rw [pm_val initPM 284 1881 (by native_decide) (by native_decide)]
  rw [show pm.nodes[284]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [1873, 1877], outs := [1881] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 284 1873 (by native_decide),
      pm_prefix_eq initPM 284 1877 (by native_decide)]

theorem pm_full_1882 (initPM : Store) :
    denoteGraph pm initPM 1882
      = fw_matmul (denoteGraph pm initPM 1874) (denoteGraph pm initPM 1878) := by
  rw [pm_val initPM 285 1882 (by native_decide) (by native_decide)]
  rw [show pm.nodes[285]'(by native_decide)
      = { rank := 1, op := "OpName.FW_matmul", ins := [1874, 1878], outs := [1882] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 285 1874 (by native_decide),
      pm_prefix_eq initPM 285 1878 (by native_decide)]

theorem pm_full_1883 (initPM : Store) :
    denoteGraph pm initPM 1883
      = fw_matmul (denoteGraph pm initPM 1875) (denoteGraph pm initPM 1879) := by
  rw [pm_val initPM 286 1883 (by native_decide) (by native_decide)]
  rw [show pm.nodes[286]'(by native_decide)
      = { rank := 2, op := "OpName.FW_matmul", ins := [1875, 1879], outs := [1883] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 286 1875 (by native_decide),
      pm_prefix_eq initPM 286 1879 (by native_decide)]

theorem pm_full_1884 (initPM : Store) :
    denoteGraph pm initPM 1884
      = fw_matmul (denoteGraph pm initPM 1876) (denoteGraph pm initPM 1880) := by
  rw [pm_val initPM 287 1884 (by native_decide) (by native_decide)]
  rw [show pm.nodes[287]'(by native_decide)
      = { rank := 3, op := "OpName.FW_matmul", ins := [1876, 1880], outs := [1884] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 287 1876 (by native_decide),
      pm_prefix_eq initPM 287 1880 (by native_decide)]

-- ========== PM self-frame: 1881-1884 (组合 AllToAll x/y + matmul) ==========
theorem pm_frame_1881_self (initPM : Store) :
    denoteGraph pm initPM 1881 = denoteGraph pm_goal_41 (denoteGraph pm initPM) 1881 := by
  rw [denote_pm_goal_41_1881, pm_full_1881, pm_full_1873, pm_full_1877,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1882_self (initPM : Store) :
    denoteGraph pm initPM 1882 = denoteGraph pm_goal_41 (denoteGraph pm initPM) 1882 := by
  rw [denote_pm_goal_41_1882, pm_full_1882, pm_full_1874, pm_full_1878,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1883_self (initPM : Store) :
    denoteGraph pm initPM 1883 = denoteGraph pm_goal_41 (denoteGraph pm initPM) 1883 := by
  rw [denote_pm_goal_41_1883, pm_full_1883, pm_full_1875, pm_full_1879,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1884_self (initPM : Store) :
    denoteGraph pm initPM 1884 = denoteGraph pm_goal_41 (denoteGraph pm initPM) 1884 := by
  rw [denote_pm_goal_41_1884, pm_full_1884, pm_full_1876, pm_full_1880,
      show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_41_cut_to_full (h : goal_41_stmt_cut) : goal_41_stmt := by
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
  have hg28 := goal_28_intermediate initSM initPM hSM hPM hInit
  have hg29 := goal_29_intermediate initSM initPM hSM hPM hInit
  have hg30 := goal_30_intermediate initSM initPM hSM hPM hInit
  have hg31 := goal_31_intermediate initSM initPM hSM hPM hInit
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg34 hg35 hg36 hg37 hg40 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hg277 hinitC
  have hnr : pm_goal_41.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_41.numRanks goal_41_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_41_cut_initGoals, goal_41_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg34
      · exact hg35
      · exact hg36
      · exact hg37
      · exact hg40
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg275
      · exact hg277
  -- shape: 613 = goal_35.ts [1,4,8,8]; 618 = goal_40.ts [1,4,8,8]
  -- 1781-1784 = goal_35.tps [1,4,2,8]; 1853-1856 = goal_40.tps [1,4,8,2]
  have h613_smsh : (Ssm 613).shape = [1, 4, 8, 8] := by
    have h := hg35.1; simp only [goal_35] at h; exact h
  have h618_smsh : (Ssm 618).shape = [1, 4, 8, 8] := by
    have h := hg40.1; simp only [goal_40] at h; exact h
  have hx : (Spm 1781).shape = [1,4,2,8] ∧ (Spm 1782).shape = [1,4,2,8] ∧
            (Spm 1783).shape = [1,4,2,8] ∧ (Spm 1784).shape = [1,4,2,8] := by
    have h := hg35.2.1
    simp only [goal_35, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1781sh, h1782sh, h1783sh, h1784sh⟩ := hx
  have hy : (Spm 1853).shape = [1,4,8,2] ∧ (Spm 1854).shape = [1,4,8,2] ∧
            (Spm 1855).shape = [1,4,8,2] ∧ (Spm 1856).shape = [1,4,8,2] := by
    have h := hg40.2.1
    simp only [goal_40, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1853sh, h1854sh, h1855sh, h1856sh⟩ := hy
  have hSM41 : StoreShapesHold Ssm sm_goal_41InitEnv := by
    intro tid sh hsh
    rw [sm_goal_41InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_41InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h613_smsh
    · exact h618_smsh
  have hPM41 : StoreShapesHold Spm pm_goal_41InitEnv := by
    intro tid sh hsh
    rw [pm_goal_41InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_41InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1781sh
    · exact h1782sh
    · exact h1783sh
    · exact h1784sh
    · exact h1853sh
    · exact h1854sh
    · exact h1855sh
    · exact h1856sh
  have hcut := h Ssm Spm hSM41 hPM41 hInitCut
  have hsmf : Ssm 619 = denoteGraph sm_goal_41 Ssm 619 := by
    rw [hSsm]; exact sm_frame_619_self initSM
  have hpm1881 : Spm 1881 = denoteGraph pm_goal_41 Spm 1881 := by
    rw [hSpm]; exact pm_frame_1881_self initPM
  have hpm1882 : Spm 1882 = denoteGraph pm_goal_41 Spm 1882 := by
    rw [hSpm]; exact pm_frame_1882_self initPM
  have hpm1883 : Spm 1883 = denoteGraph pm_goal_41 Spm 1883 := by
    rw [hSpm]; exact pm_frame_1883_self initPM
  have hpm1884 : Spm 1884 = denoteGraph pm_goal_41 Spm 1884 := by
    rw [hSpm]; exact pm_frame_1884_self initPM
  rw [hnr] at hcut
  simp only [goal_41, List.map] at hcut ⊢
  rw [hsmf, hpm1881, hpm1882, hpm1883, hpm1884]
  exact hcut

theorem goal_41_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_41 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_41_stmt := goal_41_cut_to_full prove_goal_41_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
