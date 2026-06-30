/- goal_49 桥 (prereqs 59 个: goal_2..goal_48 + 257,259,261,263,265,267,269,271,273,275,277,279)。
   SM=FW_add(950,627)→628 (sm node 52, 2 inputs: 950 dim2-sharded, 627 dim1-sharded).
   PM=4×AllToAllPrim(ins=range(2025..2028), params=[1,2])→2053-2056 (pm node 338-341, 把 627 的 dim1-shard 重分布成 dim2-shard),
      然后 4×FW_add(2049+r, 2053+r)→2057-2060 (pm node 342-345, 双输入 per-rank pointwise add)。
   950=goal_273 输出 (dim2-shard, tps 2049-2052 each [1,8,8], gather dim2 -> [1,8,32])。
   627=goal_48 输出 (dim1-shard, tps 2025-2028 each [1,2,32], gather dim1 -> [1,8,32]),
      经 AllToAll(idim=1,odim=2) 重分布成 dim2-shard 2053-2056 each [1,8,8]。
   multi-tps 输出 tids 2057-2060, gatherDim=2。
   结构: binary pointwise (FW_add) over 单 AllToAll reshard (627) + 直接 per-rank 输入 (950 的 shard 2049-2052)。
   套 Goal42Bridge (AllToAll frame, single-input pointwise) + Goal48Bridge (binary per-rank op) 组合模板。
   ⚠ full pm 的 AllToAll ins 用 ((List.range 4).map (fun r => 2025 + r)) 形式, mini-graph 用字面 list [2025,2026,2027,2028]。
   ⚠ mini-graph pm_goal_49 把 2025-2028 (AllToAll 输入) 和 2049-2052 (add 直接输入) 都当 init 读取。 -/
import denote.gpt_ly4_regen.Goal48Bridge
import denote.gpt_ly4_regen.Goal273Bridge
import denote.gpt_ly4_regen.Goal_49

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

-- ========== 迷你图 sm_goal_49 算 628 (FW_add(950,627)) ==========
theorem denote_sm_goal_49_628 (s : Store) :
    denoteGraph sm_goal_49 s 628 = elemwiseAdd (s 950) (s 627) := by
  simp only [sm_goal_49, denoteGraph, List.foldl]
  rw [applyNode_fw_add2_out]

-- ========== 迷你图 pm_goal_49 算 2053-2056 (AllToAll, params=[1,2]) ==========
theorem denote_pm_goal_49_2053 (s : Store) :
    denoteGraph pm_goal_49 s 2053
      = allToAllPrimWithDims 4 0 [s 2025, s 2026, s 2027, s 2028] 1 2 := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]; congr 1

theorem denote_pm_goal_49_2054 (s : Store) :
    denoteGraph pm_goal_49 s 2054
      = allToAllPrimWithDims 4 1 [s 2025, s 2026, s 2027, s 2028] 1 2 := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]; congr 1

theorem denote_pm_goal_49_2055 (s : Store) :
    denoteGraph pm_goal_49 s 2055
      = allToAllPrimWithDims 4 2 [s 2025, s 2026, s 2027, s 2028] 1 2 := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]; congr 1

theorem denote_pm_goal_49_2056 (s : Store) :
    denoteGraph pm_goal_49 s 2056
      = allToAllPrimWithDims 4 3 [s 2025, s 2026, s 2027, s 2028] 1 2 := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]; congr 1

-- ========== 迷你图 pm_goal_49 算 2057-2060 (FW_add(2049+r, 2053+r)) ==========
-- 节点顺序: 4×AllToAll(2053-2056) 然后 4×FW_add(2057-2060)。foldl 最后节点在最外。
-- 先剥后面的 FW_add 节点, 再 hit 目标; congr 1 闭合 (simp List.foldl 已全部规约 store 读)。
theorem denote_pm_goal_49_2057 (s : Store) :
    denoteGraph pm_goal_49 s 2057
      = elemwiseAdd (s 2049)
          (allToAllPrimWithDims 4 0 [s 2025, s 2026, s 2027, s 2028] 1 2) := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1

theorem denote_pm_goal_49_2058 (s : Store) :
    denoteGraph pm_goal_49 s 2058
      = elemwiseAdd (s 2050)
          (allToAllPrimWithDims 4 1 [s 2025, s 2026, s 2027, s 2028] 1 2) := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1

theorem denote_pm_goal_49_2059 (s : Store) :
    denoteGraph pm_goal_49 s 2059
      = elemwiseAdd (s 2051)
          (allToAllPrimWithDims 4 2 [s 2025, s 2026, s 2027, s 2028] 1 2) := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1

theorem denote_pm_goal_49_2060 (s : Store) :
    denoteGraph pm_goal_49 s 2060
      = elemwiseAdd (s 2052)
          (allToAllPrimWithDims 4 3 [s 2025, s 2026, s 2027, s 2028] 1 2) := by
  simp only [pm_goal_49, denoteGraph, List.foldl]
  rw [applyNode_fw_add2_out]
  congr 1

-- ========== SM self-frame: full sm 算 628 (node 52) ==========
theorem sm_frame_628_self (initSM : Store) :
    denoteGraph sm initSM 628 = denoteGraph sm_goal_49 (denoteGraph sm initSM) 628 := by
  rw [denote_sm_goal_49_628]
  rw [sm_val initSM 52 628 (by native_decide) (by native_decide)]
  rw [show sm.nodes[52]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [950, 627], outs := [628] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [sm_prefix_eq initSM 52 950 (by native_decide)]
  rw [sm_prefix_eq initSM 52 627 (by native_decide)]

-- ========== full pm: AllToAll 输出 2053-2056 (node 338-341, ins=range 2025, params=[1,2]) ==========
theorem pm_full_g49_2053 (initPM : Store) :
    denoteGraph pm initPM 2053
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
           denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2 := by
  rw [pm_val initPM 338 2053 (by native_decide) (by native_decide)]
  rw [show pm.nodes[338]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2025 + r)), outs := [2053], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 338 2025 (by native_decide),
      pm_prefix_eq initPM 338 2026 (by native_decide),
      pm_prefix_eq initPM 338 2027 (by native_decide),
      pm_prefix_eq initPM 338 2028 (by native_decide)]

theorem pm_full_g49_2054 (initPM : Store) :
    denoteGraph pm initPM 2054
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
           denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2 := by
  rw [pm_val initPM 339 2054 (by native_decide) (by native_decide)]
  rw [show pm.nodes[339]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2025 + r)), outs := [2054], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 339 2025 (by native_decide),
      pm_prefix_eq initPM 339 2026 (by native_decide),
      pm_prefix_eq initPM 339 2027 (by native_decide),
      pm_prefix_eq initPM 339 2028 (by native_decide)]

theorem pm_full_g49_2055 (initPM : Store) :
    denoteGraph pm initPM 2055
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
           denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2 := by
  rw [pm_val initPM 340 2055 (by native_decide) (by native_decide)]
  rw [show pm.nodes[340]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2025 + r)), outs := [2055], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 340 2025 (by native_decide),
      pm_prefix_eq initPM 340 2026 (by native_decide),
      pm_prefix_eq initPM 340 2027 (by native_decide),
      pm_prefix_eq initPM 340 2028 (by native_decide)]

theorem pm_full_g49_2056 (initPM : Store) :
    denoteGraph pm initPM 2056
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
           denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2 := by
  rw [pm_val initPM 341 2056 (by native_decide) (by native_decide)]
  rw [show pm.nodes[341]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2025 + r)), outs := [2056], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 341 2025 (by native_decide),
      pm_prefix_eq initPM 341 2026 (by native_decide),
      pm_prefix_eq initPM 341 2027 (by native_decide),
      pm_prefix_eq initPM 341 2028 (by native_decide)]

-- ========== full pm: FW_add 输出 2057-2060 (node 342-345, ins=[2049+r,2053+r]) ==========
theorem pm_frame_2057_self (initPM : Store) :
    denoteGraph pm initPM 2057
      = elemwiseAdd (denoteGraph pm initPM 2049)
          (allToAllPrimWithDims pm.numRanks 0
            [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
             denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2) := by
  rw [pm_val initPM 342 2057 (by native_decide) (by native_decide)]
  rw [show pm.nodes[342]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [2049, 2053], outs := [2057] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 342 2049 (by native_decide)]
  rw [pm_prefix_eq initPM 342 2053 (by native_decide)]
  rw [pm_full_g49_2053]

theorem pm_frame_2058_self (initPM : Store) :
    denoteGraph pm initPM 2058
      = elemwiseAdd (denoteGraph pm initPM 2050)
          (allToAllPrimWithDims pm.numRanks 1
            [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
             denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2) := by
  rw [pm_val initPM 343 2058 (by native_decide) (by native_decide)]
  rw [show pm.nodes[343]'(by native_decide)
      = { rank := 1, op := "OpName.FW_add", ins := [2050, 2054], outs := [2058] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 343 2050 (by native_decide)]
  rw [pm_prefix_eq initPM 343 2054 (by native_decide)]
  rw [pm_full_g49_2054]

theorem pm_frame_2059_self (initPM : Store) :
    denoteGraph pm initPM 2059
      = elemwiseAdd (denoteGraph pm initPM 2051)
          (allToAllPrimWithDims pm.numRanks 2
            [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
             denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2) := by
  rw [pm_val initPM 344 2059 (by native_decide) (by native_decide)]
  rw [show pm.nodes[344]'(by native_decide)
      = { rank := 2, op := "OpName.FW_add", ins := [2051, 2055], outs := [2059] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 344 2051 (by native_decide)]
  rw [pm_prefix_eq initPM 344 2055 (by native_decide)]
  rw [pm_full_g49_2055]

theorem pm_frame_2060_self (initPM : Store) :
    denoteGraph pm initPM 2060
      = elemwiseAdd (denoteGraph pm initPM 2052)
          (allToAllPrimWithDims pm.numRanks 3
            [denoteGraph pm initPM 2025, denoteGraph pm initPM 2026,
             denoteGraph pm initPM 2027, denoteGraph pm initPM 2028] 1 2) := by
  rw [pm_val initPM 345 2060 (by native_decide) (by native_decide)]
  rw [show pm.nodes[345]'(by native_decide)
      = { rank := 3, op := "OpName.FW_add", ins := [2052, 2056], outs := [2060] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 345 2052 (by native_decide)]
  rw [pm_prefix_eq initPM 345 2056 (by native_decide)]
  rw [pm_full_g49_2056]

-- ========== PM self-frame to mini: 2057-2060 ==========
-- mini-graph 把 2025-2028, 2049-2052 当 init 读取 (s tid)，full pm frame 也归约到 denoteGraph pm initPM tid。
theorem pm_frame_2057_to_mini (initPM : Store) :
    denoteGraph pm initPM 2057 = denoteGraph pm_goal_49 (denoteGraph pm initPM) 2057 := by
  rw [denote_pm_goal_49_2057, pm_frame_2057_self,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2058_to_mini (initPM : Store) :
    denoteGraph pm initPM 2058 = denoteGraph pm_goal_49 (denoteGraph pm initPM) 2058 := by
  rw [denote_pm_goal_49_2058, pm_frame_2058_self,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2059_to_mini (initPM : Store) :
    denoteGraph pm initPM 2059 = denoteGraph pm_goal_49 (denoteGraph pm initPM) 2059 := by
  rw [denote_pm_goal_49_2059, pm_frame_2059_self,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2060_to_mini (initPM : Store) :
    denoteGraph pm initPM 2060 = denoteGraph pm_goal_49 (denoteGraph pm initPM) 2060 := by
  rw [denote_pm_goal_49_2060, pm_frame_2060_self,
      show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_49_cut_to_full (h : goal_49_stmt_cut) : goal_49_stmt := by
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
  have hg33 := goal_33_intermediate initSM initPM hSM hPM hInit
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg38 := goal_38_intermediate initSM initPM hSM hPM hInit
  have hg39 := goal_39_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg41 := goal_41_intermediate initSM initPM hSM hPM hInit
  have hg42 := goal_42_intermediate initSM initPM hSM hPM hInit
  have hg43 := goal_43_intermediate initSM initPM hSM hPM hInit
  have hg44 := goal_44_intermediate initSM initPM hSM hPM hInit
  have hg45 := goal_45_intermediate initSM initPM hSM hPM hInit
  have hg46 := goal_46_intermediate initSM initPM hSM hPM hInit
  have hg47 := goal_47_intermediate initSM initPM hSM hPM hInit
  have hg48 := goal_48_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg273 := goal_273_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hinitC
  have hnr : pm_goal_49.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_49.numRanks goal_49_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_49_cut_initGoals, goal_49_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, List.forall_mem_nil _⟩
  -- 627 = goal_48.ts (single-tp on SM, shape [1,8,32]); tps 2025-2028 each [1,2,32]
  have h627_smsh : (Ssm 627).shape = [1, 8, 32] := by
    have h := hg48.1; simp only [goal_48] at h; exact h
  have hpmsh48 : (Spm 2025).shape = [1,2,32] ∧ (Spm 2026).shape = [1,2,32] ∧
                 (Spm 2027).shape = [1,2,32] ∧ (Spm 2028).shape = [1,2,32] := by
    have h := hg48.2.1
    simp only [goal_48, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h2025sh, h2026sh, h2027sh, h2028sh⟩ := hpmsh48
  -- 950 = goal_273.ts (single-tp on SM, shape [1,8,32]); tps 2049-2052 each [1,8,8]
  have h950_smsh : (Ssm 950).shape = [1, 8, 32] := by
    have h := hg273.1; simp only [goal_273] at h; exact h
  have hpmsh273 : (Spm 2049).shape = [1,8,8] ∧ (Spm 2050).shape = [1,8,8] ∧
                  (Spm 2051).shape = [1,8,8] ∧ (Spm 2052).shape = [1,8,8] := by
    have h := hg273.2.1
    simp only [goal_273, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h2049sh, h2050sh, h2051sh, h2052sh⟩ := hpmsh273
  have hSM49 : StoreShapesHold Ssm sm_goal_49InitEnv := by
    intro tid sh hsh
    rw [sm_goal_49InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_49InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h627_smsh
    · exact h950_smsh
  have hPM49 : StoreShapesHold Spm pm_goal_49InitEnv := by
    intro tid sh hsh
    rw [pm_goal_49InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_49InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
               | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2025sh
    · exact h2026sh
    · exact h2027sh
    · exact h2028sh
    · exact h2049sh
    · exact h2050sh
    · exact h2051sh
    · exact h2052sh
  have hcut := h Ssm Spm hSM49 hPM49 hInitCut
  have hsmf : Ssm 628 = denoteGraph sm_goal_49 Ssm 628 := by
    rw [hSsm]; exact sm_frame_628_self initSM
  have hpm2057 : Spm 2057 = denoteGraph pm_goal_49 Spm 2057 := by
    rw [hSpm]; exact pm_frame_2057_to_mini initPM
  have hpm2058 : Spm 2058 = denoteGraph pm_goal_49 Spm 2058 := by
    rw [hSpm]; exact pm_frame_2058_to_mini initPM
  have hpm2059 : Spm 2059 = denoteGraph pm_goal_49 Spm 2059 := by
    rw [hSpm]; exact pm_frame_2059_to_mini initPM
  have hpm2060 : Spm 2060 = denoteGraph pm_goal_49 Spm 2060 := by
    rw [hSpm]; exact pm_frame_2060_to_mini initPM
  rw [hnr] at hcut
  simp only [goal_49, List.map] at hcut ⊢
  rw [hsmf, hpm2057, hpm2058, hpm2059, hpm2060]
  exact hcut

theorem goal_49_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_49 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_49_stmt := goal_49_cut_to_full prove_goal_49_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals