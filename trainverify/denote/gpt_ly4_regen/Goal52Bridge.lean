/- goal_52 桥 (prereqs 63 个: goal_2..51 + 257,259,261,263,265,267,269,271,273,275,277,279,281)。
   结构与 goal_46 完全同构: 单输入 pointwise (FW_gelu) over AllToAll reshard (dim2→1) + AllGatherPrim (dim1) → single-tp 输出 634 (ts==tid)。
   SM: FW_gelu(633)→634 (sm node 56)。633=goal_51 输出 (gatherDim=2, multi-tps 2117-2120, 各 [1,8,32])。
   PM: 4×AllToAllPrim(ins=range(2117..2120), params=[2,1])→2141-2144 (pm node 367-370),
       然后 4×FW_gelu(2141+r)→2145-2148 (pm node 371-374),
       最后 AllGatherPrim(ins=range(2145..2148), params=[1])→634 (pm node 375)。tps=[{0,634}], single-tp。
   核心语义(fw_gelu pointwise 分配过 AllToAll-reshard dim2→1 + dim1 all-gather)已在 prove_goal_52_cut 处理,
   bridge 只做 frame, single-tp 输出 (ts==tid 634 via AllGather)。套 Goal46Bridge 模板逐字适配。 -/
import denote.gpt_ly4_regen.Goal51Bridge
import denote.gpt_ly4_regen.Goal_52

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

-- ========== 迷你图 sm_goal_52 算 634 (FW_gelu) ==========
theorem denote_sm_goal_52_634 (s : Store) :
    denoteGraph sm_goal_52 s 634 = fw_gelu (s 633) := by
  simp only [sm_goal_52, denoteGraph, List.foldl]
  rw [applyNode_fw_gelu_out]

-- ========== 迷你图 pm_goal_52 算 634 (4×AllToAll → 4×FW_gelu → AllGather) ==========
theorem denote_pm_goal_52_634 (s : Store) :
    denoteGraph pm_goal_52 s 634 = allGatherPrimDimN 1 4 0
      [fw_gelu (allToAllPrimWithDims 4 0 [s 2117, s 2118, s 2119, s 2120] 2 1),
       fw_gelu (allToAllPrimWithDims 4 1 [s 2117, s 2118, s 2119, s 2120] 2 1),
       fw_gelu (allToAllPrimWithDims 4 2 [s 2117, s 2118, s 2119, s 2120] 2 1),
       fw_gelu (allToAllPrimWithDims 4 3 [s 2117, s 2118, s 2119, s 2120] 2 1)] := by
  simp only [pm_goal_52, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full sm 算 634 (node 56 FW_gelu) ==========
theorem sm_frame_634_self (initSM : Store) :
    denoteGraph sm initSM 634 = denoteGraph sm_goal_52 (denoteGraph sm initSM) 634 := by
  rw [denote_sm_goal_52_634]
  rw [sm_val initSM 56 634 (by native_decide) (by native_decide)]
  rw [show sm.nodes[56]'(by native_decide)
      = { rank := 0, op := "OpName.FW_gelu", ins := [633], outs := [634] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [sm_prefix_eq initSM 56 633 (by native_decide)]

-- ========== full pm: AllToAll 输出 2141-2144 (node 367-370, ins=range 2117, params [2,1]) ==========
theorem pm_full_2141 (initPM : Store) :
    denoteGraph pm initPM 2141
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
           denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1 := by
  rw [pm_val initPM 367 2141 (by native_decide) (by native_decide)]
  rw [show pm.nodes[367]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2117 + r)), outs := [2141], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 367 2117 (by native_decide),
      pm_prefix_eq initPM 367 2118 (by native_decide),
      pm_prefix_eq initPM 367 2119 (by native_decide),
      pm_prefix_eq initPM 367 2120 (by native_decide)]

theorem pm_full_2142 (initPM : Store) :
    denoteGraph pm initPM 2142
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
           denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1 := by
  rw [pm_val initPM 368 2142 (by native_decide) (by native_decide)]
  rw [show pm.nodes[368]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2117 + r)), outs := [2142], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 368 2117 (by native_decide),
      pm_prefix_eq initPM 368 2118 (by native_decide),
      pm_prefix_eq initPM 368 2119 (by native_decide),
      pm_prefix_eq initPM 368 2120 (by native_decide)]

theorem pm_full_2143 (initPM : Store) :
    denoteGraph pm initPM 2143
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
           denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1 := by
  rw [pm_val initPM 369 2143 (by native_decide) (by native_decide)]
  rw [show pm.nodes[369]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2117 + r)), outs := [2143], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 369 2117 (by native_decide),
      pm_prefix_eq initPM 369 2118 (by native_decide),
      pm_prefix_eq initPM 369 2119 (by native_decide),
      pm_prefix_eq initPM 369 2120 (by native_decide)]

theorem pm_full_2144 (initPM : Store) :
    denoteGraph pm initPM 2144
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
           denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1 := by
  rw [pm_val initPM 370 2144 (by native_decide) (by native_decide)]
  rw [show pm.nodes[370]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2117 + r)), outs := [2144], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 370 2117 (by native_decide),
      pm_prefix_eq initPM 370 2118 (by native_decide),
      pm_prefix_eq initPM 370 2119 (by native_decide),
      pm_prefix_eq initPM 370 2120 (by native_decide)]

-- ========== full pm: FW_gelu 输出 2145-2148 (node 371-374) ==========
theorem pm_full_2145 (initPM : Store) :
    denoteGraph pm initPM 2145
      = fw_gelu
          (allToAllPrimWithDims pm.numRanks 0
            [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
             denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1) := by
  rw [pm_val initPM 371 2145 (by native_decide) (by native_decide)]
  rw [show pm.nodes[371]'(by native_decide)
      = { rank := 0, op := "OpName.FW_gelu", ins := [2141], outs := [2145] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 371 2141 (by native_decide)]
  rw [pm_full_2141]

theorem pm_full_2146 (initPM : Store) :
    denoteGraph pm initPM 2146
      = fw_gelu
          (allToAllPrimWithDims pm.numRanks 1
            [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
             denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1) := by
  rw [pm_val initPM 372 2146 (by native_decide) (by native_decide)]
  rw [show pm.nodes[372]'(by native_decide)
      = { rank := 1, op := "OpName.FW_gelu", ins := [2142], outs := [2146] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 372 2142 (by native_decide)]
  rw [pm_full_2142]

theorem pm_full_2147 (initPM : Store) :
    denoteGraph pm initPM 2147
      = fw_gelu
          (allToAllPrimWithDims pm.numRanks 2
            [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
             denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1) := by
  rw [pm_val initPM 373 2147 (by native_decide) (by native_decide)]
  rw [show pm.nodes[373]'(by native_decide)
      = { rank := 2, op := "OpName.FW_gelu", ins := [2143], outs := [2147] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 373 2143 (by native_decide)]
  rw [pm_full_2143]

theorem pm_full_2148 (initPM : Store) :
    denoteGraph pm initPM 2148
      = fw_gelu
          (allToAllPrimWithDims pm.numRanks 3
            [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
             denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1) := by
  rw [pm_val initPM 374 2148 (by native_decide) (by native_decide)]
  rw [show pm.nodes[374]'(by native_decide)
      = { rank := 3, op := "OpName.FW_gelu", ins := [2144], outs := [2148] }
      from by native_decide]
  rw [applyNode_fw_gelu_out]
  rw [pm_prefix_eq initPM 374 2144 (by native_decide)]
  rw [pm_full_2144]

-- ========== full pm: AllGather → 634 (node 375, single-tp output) ==========
theorem pm_frame_634_self (initPM : Store) :
    denoteGraph pm initPM 634
      = allGatherPrimDimN 1 pm.numRanks 0
          [fw_gelu
             (allToAllPrimWithDims pm.numRanks 0
               [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
                denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1),
           fw_gelu
             (allToAllPrimWithDims pm.numRanks 1
               [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
                denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1),
           fw_gelu
             (allToAllPrimWithDims pm.numRanks 2
               [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
                denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1),
           fw_gelu
             (allToAllPrimWithDims pm.numRanks 3
               [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
                denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] 2 1)] := by
  rw [pm_val initPM 375 634 (by native_decide) (by native_decide)]
  rw [show pm.nodes[375]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 2145 + r)), outs := [634], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 375 2145 (by native_decide),
      pm_prefix_eq initPM 375 2146 (by native_decide),
      pm_prefix_eq initPM 375 2147 (by native_decide),
      pm_prefix_eq initPM 375 2148 (by native_decide)]
  rw [pm_full_2145, pm_full_2146, pm_full_2147, pm_full_2148]

-- ========== 总装 ==========
theorem goal_52_cut_to_full (h : goal_52_stmt_cut) : goal_52_stmt := by
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
  have hg49 := goal_49_intermediate initSM initPM hSM hPM hInit
  have hg50 := goal_50_intermediate initSM initPM hSM hPM hInit
  have hg51 := goal_51_intermediate initSM initPM hSM hPM hInit
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
  have hg281 := goal_281_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hinitC
  have hnr : pm_goal_52.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_52.numRanks goal_52_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_52_cut_initGoals, goal_52_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg50, hg51, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, hg281, List.forall_mem_nil _⟩
  -- shape: 633 = goal_51.ts [1,8,128] (single on SM); 2117-2120 = goal_51.tps each [1,8,32]
  have h633_smsh : (Ssm 633).shape = [1, 8, 128] := by
    have h := hg51.1; simp only [goal_51] at h; exact h
  have hpmsh : (Spm 2117).shape = [1,8,32] ∧ (Spm 2118).shape = [1,8,32] ∧
               (Spm 2119).shape = [1,8,32] ∧ (Spm 2120).shape = [1,8,32] := by
    have h := hg51.2.1
    simp only [goal_51, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h2117sh, h2118sh, h2119sh, h2120sh⟩ := hpmsh
  have hSM52 : StoreShapesHold Ssm sm_goal_52InitEnv := by
    intro tid sh hsh
    rw [sm_goal_52InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_52InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h633_smsh
  have hPM52 : StoreShapesHold Spm pm_goal_52InitEnv := by
    intro tid sh hsh
    rw [pm_goal_52InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_52InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2117sh
    · exact h2118sh
    · exact h2119sh
    · exact h2120sh
  have hcut := h Ssm Spm hSM52 hPM52 hInitCut
  -- Frame: 634 (sm node 56), 634 (pm node 375)
  have hsmf : Ssm 634 = denoteGraph sm_goal_52 Ssm 634 := by
    rw [hSsm]; exact sm_frame_634_self initSM
  have hpm634 : Spm 634 = denoteGraph pm_goal_52 Spm 634 := by
    rw [denote_pm_goal_52_634]
    rw [hSpm]
    have := pm_frame_634_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_52, List.map] at hcut ⊢
  rw [hsmf, hpm634]
  exact hcut

theorem goal_52_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_52 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_52_stmt := goal_52_cut_to_full prove_goal_52_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
