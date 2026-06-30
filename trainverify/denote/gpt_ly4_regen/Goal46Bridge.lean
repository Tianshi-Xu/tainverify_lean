/- goal_46 桥 (prereqs 55 个: goal_2..goal_45 + 257,259,261,263,265,267,269,271,275,277,279)。
   新结构: 单输入 pointwise (FW_contiguous, identity) over AllToAll reshard (dim3→2) + AllGatherPrim (dim2) → single-tp 输出 624 (ts==tid)。
   SM: FW_contiguous(623)→624 (sm node 49)。623=goal_45 输出 (gatherDim=3, multi-tps 1977-1980, 各 [1,8,4,2])。
   PM: 4×AllToAllPrim(ins=range(1977..1980), params=[3,2])→1997-2000 (pm node 317-320),
       然后 4×FW_contiguous(1997+r)→2001-2004 (pm node 321-324),
       最后 AllGatherPrim(ins=range(2001..2004), params=[2])→624 (pm node 325)。tps=[{0,624}], single-tp。
   核心语义(fw_contiguous=identity 分配过 AllToAll-reshard dim3→2 + dim2 all-gather)已在
   prove_goal_46_cut 处理, bridge 只做 frame, single-tp 输出 (ts==tid 624 via AllGather)。
   ⚠ full pm 的 AllToAll/AllGather ins 用 ((List.range 4).map (fun r => base + r)) 形式, mini-graph 用字面 list。
   套 Goal42Bridge (AllToAll-reshard frame + per-rank pointwise) + Goal44Bridge (single-tp 输出 via 最终 collective) 组合模板。 -/
import denote.gpt_ly4_regen.Goal45Bridge
import denote.gpt_ly4_regen.Goal_46

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

-- ========== 迷你图 sm_goal_46 算 624 (FW_contiguous) ==========
theorem denote_sm_goal_46_624 (s : Store) :
    denoteGraph sm_goal_46 s 624 = fw_contiguous (s 623) := by
  simp only [sm_goal_46, denoteGraph, List.foldl]
  rw [applyNode_fw_contiguous_out_g46]

-- ========== 迷你图 pm_goal_46 算 624 (4×AllToAll → 4×FW_contiguous → AllGather) ==========
theorem denote_pm_goal_46_624 (s : Store) :
    denoteGraph pm_goal_46 s 624 = allGatherPrimDimN 2 4 0
      [fw_contiguous (allToAllPrimWithDims 4 0 [s 1977, s 1978, s 1979, s 1980] 3 2),
       fw_contiguous (allToAllPrimWithDims 4 1 [s 1977, s 1978, s 1979, s 1980] 3 2),
       fw_contiguous (allToAllPrimWithDims 4 2 [s 1977, s 1978, s 1979, s 1980] 3 2),
       fw_contiguous (allToAllPrimWithDims 4 3 [s 1977, s 1978, s 1979, s 1980] 3 2)] := by
  simp only [pm_goal_46, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full sm 算 624 (node 49 FW_contiguous) ==========
theorem sm_frame_624_self (initSM : Store) :
    denoteGraph sm initSM 624 = denoteGraph sm_goal_46 (denoteGraph sm initSM) 624 := by
  rw [denote_sm_goal_46_624]
  rw [sm_val initSM 49 624 (by native_decide) (by native_decide)]
  rw [show sm.nodes[49]'(by native_decide)
      = { rank := 0, op := "OpName.FW_contiguous", ins := [623], outs := [624] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g46]
  rw [sm_prefix_eq initSM 49 623 (by native_decide)]

-- ========== full pm: AllToAll 输出 1997-2000 (node 317-320, ins=range 1977, params [3,2]) ==========
theorem pm_full_g46_1997 (initPM : Store) :
    denoteGraph pm initPM 1997
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
           denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2 := by
  rw [pm_val initPM 317 1997 (by native_decide) (by native_decide)]
  rw [show pm.nodes[317]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1977 + r)), outs := [1997], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 317 1977 (by native_decide),
      pm_prefix_eq initPM 317 1978 (by native_decide),
      pm_prefix_eq initPM 317 1979 (by native_decide),
      pm_prefix_eq initPM 317 1980 (by native_decide)]

theorem pm_full_g46_1998 (initPM : Store) :
    denoteGraph pm initPM 1998
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
           denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2 := by
  rw [pm_val initPM 318 1998 (by native_decide) (by native_decide)]
  rw [show pm.nodes[318]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1977 + r)), outs := [1998], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 318 1977 (by native_decide),
      pm_prefix_eq initPM 318 1978 (by native_decide),
      pm_prefix_eq initPM 318 1979 (by native_decide),
      pm_prefix_eq initPM 318 1980 (by native_decide)]

theorem pm_full_g46_1999 (initPM : Store) :
    denoteGraph pm initPM 1999
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
           denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2 := by
  rw [pm_val initPM 319 1999 (by native_decide) (by native_decide)]
  rw [show pm.nodes[319]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1977 + r)), outs := [1999], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 319 1977 (by native_decide),
      pm_prefix_eq initPM 319 1978 (by native_decide),
      pm_prefix_eq initPM 319 1979 (by native_decide),
      pm_prefix_eq initPM 319 1980 (by native_decide)]

theorem pm_full_g46_2000 (initPM : Store) :
    denoteGraph pm initPM 2000
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
           denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2 := by
  rw [pm_val initPM 320 2000 (by native_decide) (by native_decide)]
  rw [show pm.nodes[320]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1977 + r)), outs := [2000], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 320 1977 (by native_decide),
      pm_prefix_eq initPM 320 1978 (by native_decide),
      pm_prefix_eq initPM 320 1979 (by native_decide),
      pm_prefix_eq initPM 320 1980 (by native_decide)]

-- ========== full pm: FW_contiguous 输出 2001-2004 (node 321-324) ==========
theorem pm_full_g46_2001 (initPM : Store) :
    denoteGraph pm initPM 2001
      = fw_contiguous
          (allToAllPrimWithDims pm.numRanks 0
            [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
             denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2) := by
  rw [pm_val initPM 321 2001 (by native_decide) (by native_decide)]
  rw [show pm.nodes[321]'(by native_decide)
      = { rank := 0, op := "OpName.FW_contiguous", ins := [1997], outs := [2001] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g46]
  rw [pm_prefix_eq initPM 321 1997 (by native_decide)]
  rw [pm_full_g46_1997]

theorem pm_full_g46_2002 (initPM : Store) :
    denoteGraph pm initPM 2002
      = fw_contiguous
          (allToAllPrimWithDims pm.numRanks 1
            [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
             denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2) := by
  rw [pm_val initPM 322 2002 (by native_decide) (by native_decide)]
  rw [show pm.nodes[322]'(by native_decide)
      = { rank := 1, op := "OpName.FW_contiguous", ins := [1998], outs := [2002] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g46]
  rw [pm_prefix_eq initPM 322 1998 (by native_decide)]
  rw [pm_full_g46_1998]

theorem pm_full_g46_2003 (initPM : Store) :
    denoteGraph pm initPM 2003
      = fw_contiguous
          (allToAllPrimWithDims pm.numRanks 2
            [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
             denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2) := by
  rw [pm_val initPM 323 2003 (by native_decide) (by native_decide)]
  rw [show pm.nodes[323]'(by native_decide)
      = { rank := 2, op := "OpName.FW_contiguous", ins := [1999], outs := [2003] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g46]
  rw [pm_prefix_eq initPM 323 1999 (by native_decide)]
  rw [pm_full_g46_1999]

theorem pm_full_g46_2004 (initPM : Store) :
    denoteGraph pm initPM 2004
      = fw_contiguous
          (allToAllPrimWithDims pm.numRanks 3
            [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
             denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2) := by
  rw [pm_val initPM 324 2004 (by native_decide) (by native_decide)]
  rw [show pm.nodes[324]'(by native_decide)
      = { rank := 3, op := "OpName.FW_contiguous", ins := [2000], outs := [2004] }
      from by native_decide]
  rw [applyNode_fw_contiguous_out_g46]
  rw [pm_prefix_eq initPM 324 2000 (by native_decide)]
  rw [pm_full_g46_2000]

-- ========== full pm: AllGather → 624 (node 325, single-tp output) ==========
theorem pm_frame_624_self (initPM : Store) :
    denoteGraph pm initPM 624
      = allGatherPrimDimN 2 pm.numRanks 0
          [fw_contiguous
             (allToAllPrimWithDims pm.numRanks 0
               [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
                denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2),
           fw_contiguous
             (allToAllPrimWithDims pm.numRanks 1
               [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
                denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2),
           fw_contiguous
             (allToAllPrimWithDims pm.numRanks 2
               [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
                denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2),
           fw_contiguous
             (allToAllPrimWithDims pm.numRanks 3
               [denoteGraph pm initPM 1977, denoteGraph pm initPM 1978,
                denoteGraph pm initPM 1979, denoteGraph pm initPM 1980] 3 2)] := by
  rw [pm_val initPM 325 624 (by native_decide) (by native_decide)]
  rw [show pm.nodes[325]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 2001 + r)), outs := [624], params := [2] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 325 2001 (by native_decide),
      pm_prefix_eq initPM 325 2002 (by native_decide),
      pm_prefix_eq initPM 325 2003 (by native_decide),
      pm_prefix_eq initPM 325 2004 (by native_decide)]
  rw [pm_full_g46_2001, pm_full_g46_2002, pm_full_g46_2003, pm_full_g46_2004]

-- ========== 总装 ==========
theorem goal_46_cut_to_full (h : goal_46_stmt_cut) : goal_46_stmt := by
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
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hg277 hg279 hinitC
  have hnr : pm_goal_46.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_46.numRanks goal_46_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_46_cut_initGoals, goal_46_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg275, hg277, hg279, List.forall_mem_nil _⟩
  -- shape: 623 = goal_45.ts [1,8,4,8] (single on SM); 1977-1980 = goal_45.tps each [1,8,4,2]
  have h623_smsh : (Ssm 623).shape = [1, 8, 4, 8] := by
    have h := hg45.1; simp only [goal_45] at h; exact h
  have hpmsh : (Spm 1977).shape = [1,8,4,2] ∧ (Spm 1978).shape = [1,8,4,2] ∧
               (Spm 1979).shape = [1,8,4,2] ∧ (Spm 1980).shape = [1,8,4,2] := by
    have h := hg45.2.1
    simp only [goal_45, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1977sh, h1978sh, h1979sh, h1980sh⟩ := hpmsh
  have hSM46 : StoreShapesHold Ssm sm_goal_46InitEnv := by
    intro tid sh hsh
    rw [sm_goal_46InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_46InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h623_smsh
  have hPM46 : StoreShapesHold Spm pm_goal_46InitEnv := by
    intro tid sh hsh
    rw [pm_goal_46InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_46InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1977sh
    · exact h1978sh
    · exact h1979sh
    · exact h1980sh
  have hcut := h Ssm Spm hSM46 hPM46 hInitCut
  -- Frame: 624 (sm node 49), 624 (pm node 325)
  have hsmf : Ssm 624 = denoteGraph sm_goal_46 Ssm 624 := by
    rw [hSsm]; exact sm_frame_624_self initSM
  have hpm624 : Spm 624 = denoteGraph pm_goal_46 Spm 624 := by
    rw [denote_pm_goal_46_624]
    rw [hSpm]
    have := pm_frame_624_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_46, List.map] at hcut ⊢
  rw [hsmf, hpm624]
  exact hcut

theorem goal_46_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_46 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_46_stmt := goal_46_cut_to_full prove_goal_46_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
