/- goal_42 桥 (prereqs 47 个)。
   新结构: 单输入 pointwise op (FW_div) over 单个 AllToAll reshard。
   SM: FW_div(619, c=2)→620 (sm node 45)。619=goal_41 输出 (dim1-gather, shape [1,4,8,8])。
   PM: 4×AllToAllPrim(ins=range(1881..1884), params=[1,2])→1905-1908 (pm node 288-291),
       然后 4×FW_div(1905+r, c=2)→1909-1912 (pm node 292-295)。tps=4个, gatherDim=2。
   核心语义(fw_div distributes over AllToAll-reshard dim1->dim2 + dim2 all-gather)已在
   prove_goal_42_cut 处理, bridge 只做 frame。
   ⚠ full pm 的 AllToAll ins 用 ((List.range 4).map (fun r => 1881 + r)) 形式, mini-graph 用字面 list。
   套 Goal41Bridge (AllToAll frame) + Goal17Bridge (FW_div frame) 组合模板。 -/
import denote.gpt_ly4_regen.Goal40Bridge
import denote.gpt_ly4_regen.Goal41Bridge
import denote.gpt_ly4_regen.Goal_42

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

-- ========== 迷你图 pm_goal_42 算 1909-1912 (AllToAll → FW_div) ==========
theorem denote_pm_goal_42_1909 (s : Store) :
    denoteGraph pm_goal_42 s 1909 =
      fw_div ((2 : Nat) : Scalar)
        (allToAllPrimWithDims 4 0 [s 1881, s 1882, s 1883, s 1884] 1 2) := by
  simp only [pm_goal_42, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g42]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_42_1910 (s : Store) :
    denoteGraph pm_goal_42 s 1910 =
      fw_div ((2 : Nat) : Scalar)
        (allToAllPrimWithDims 4 1 [s 1881, s 1882, s 1883, s 1884] 1 2) := by
  simp only [pm_goal_42, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g42]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_42_1911 (s : Store) :
    denoteGraph pm_goal_42 s 1911 =
      fw_div ((2 : Nat) : Scalar)
        (allToAllPrimWithDims 4 2 [s 1881, s 1882, s 1883, s 1884] 1 2) := by
  simp only [pm_goal_42, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g42]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_42_1912 (s : Store) :
    denoteGraph pm_goal_42 s 1912 =
      fw_div ((2 : Nat) : Scalar)
        (allToAllPrimWithDims 4 3 [s 1881, s 1882, s 1883, s 1884] 1 2) := by
  simp only [pm_goal_42, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g42]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 620 (node 45 FW_div) ==========
theorem sm_frame_620_self (initSM : Store) :
    denoteGraph sm initSM 620 = denoteGraph sm_goal_42 (denoteGraph sm initSM) 620 := by
  have hsm : denoteGraph sm_goal_42 (denoteGraph sm initSM) 620
      = fw_div ((2 : Nat) : Scalar) (denoteGraph sm initSM 619) := by
    simp only [sm_goal_42, denoteGraph, List.foldl]
    rw [applyNode_fw_div_out_g42]
  rw [hsm]
  rw [sm_val initSM 45 620 (by native_decide) (by native_decide)]
  rw [show sm.nodes[45]'(by native_decide)
      = { rank := 0, op := "OpName.FW_div", ins := [619], outs := [620], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g42]
  rw [sm_prefix_eq initSM 45 619 (by native_decide)]

-- ========== full pm: AllToAll 输出 1905-1908 (node 288-291, ins=range 1881, params=[1,2]) ==========
theorem pm_full_1905 (initPM : Store) :
    denoteGraph pm initPM 1905
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
           denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2 := by
  rw [pm_val initPM 288 1905 (by native_decide) (by native_decide)]
  rw [show pm.nodes[288]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1881 + r)), outs := [1905], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 288 1881 (by native_decide),
      pm_prefix_eq initPM 288 1882 (by native_decide),
      pm_prefix_eq initPM 288 1883 (by native_decide),
      pm_prefix_eq initPM 288 1884 (by native_decide)]

theorem pm_full_1906 (initPM : Store) :
    denoteGraph pm initPM 1906
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
           denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2 := by
  rw [pm_val initPM 289 1906 (by native_decide) (by native_decide)]
  rw [show pm.nodes[289]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1881 + r)), outs := [1906], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 289 1881 (by native_decide),
      pm_prefix_eq initPM 289 1882 (by native_decide),
      pm_prefix_eq initPM 289 1883 (by native_decide),
      pm_prefix_eq initPM 289 1884 (by native_decide)]

theorem pm_full_1907 (initPM : Store) :
    denoteGraph pm initPM 1907
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
           denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2 := by
  rw [pm_val initPM 290 1907 (by native_decide) (by native_decide)]
  rw [show pm.nodes[290]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1881 + r)), outs := [1907], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 290 1881 (by native_decide),
      pm_prefix_eq initPM 290 1882 (by native_decide),
      pm_prefix_eq initPM 290 1883 (by native_decide),
      pm_prefix_eq initPM 290 1884 (by native_decide)]

theorem pm_full_1908 (initPM : Store) :
    denoteGraph pm initPM 1908
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
           denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2 := by
  rw [pm_val initPM 291 1908 (by native_decide) (by native_decide)]
  rw [show pm.nodes[291]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1881 + r)), outs := [1908], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 291 1881 (by native_decide),
      pm_prefix_eq initPM 291 1882 (by native_decide),
      pm_prefix_eq initPM 291 1883 (by native_decide),
      pm_prefix_eq initPM 291 1884 (by native_decide)]

-- ========== full pm: FW_div 输出 1909-1912 (node 292-295) ==========
theorem pm_frame_1909_self (initPM : Store) :
    denoteGraph pm initPM 1909
      = fw_div ((2 : Nat) : Scalar)
          (allToAllPrimWithDims pm.numRanks 0
            [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
             denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2) := by
  rw [pm_val initPM 292 1909 (by native_decide) (by native_decide)]
  rw [show pm.nodes[292]'(by native_decide)
      = { rank := 0, op := "OpName.FW_div", ins := [1905], outs := [1909], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g42]
  rw [pm_prefix_eq initPM 292 1905 (by native_decide)]
  rw [pm_full_1905]

theorem pm_frame_1910_self (initPM : Store) :
    denoteGraph pm initPM 1910
      = fw_div ((2 : Nat) : Scalar)
          (allToAllPrimWithDims pm.numRanks 1
            [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
             denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2) := by
  rw [pm_val initPM 293 1910 (by native_decide) (by native_decide)]
  rw [show pm.nodes[293]'(by native_decide)
      = { rank := 1, op := "OpName.FW_div", ins := [1906], outs := [1910], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g42]
  rw [pm_prefix_eq initPM 293 1906 (by native_decide)]
  rw [pm_full_1906]

theorem pm_frame_1911_self (initPM : Store) :
    denoteGraph pm initPM 1911
      = fw_div ((2 : Nat) : Scalar)
          (allToAllPrimWithDims pm.numRanks 2
            [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
             denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2) := by
  rw [pm_val initPM 294 1911 (by native_decide) (by native_decide)]
  rw [show pm.nodes[294]'(by native_decide)
      = { rank := 2, op := "OpName.FW_div", ins := [1907], outs := [1911], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g42]
  rw [pm_prefix_eq initPM 294 1907 (by native_decide)]
  rw [pm_full_1907]

theorem pm_frame_1912_self (initPM : Store) :
    denoteGraph pm initPM 1912
      = fw_div ((2 : Nat) : Scalar)
          (allToAllPrimWithDims pm.numRanks 3
            [denoteGraph pm initPM 1881, denoteGraph pm initPM 1882,
             denoteGraph pm initPM 1883, denoteGraph pm initPM 1884] 1 2) := by
  rw [pm_val initPM 295 1912 (by native_decide) (by native_decide)]
  rw [show pm.nodes[295]'(by native_decide)
      = { rank := 3, op := "OpName.FW_div", ins := [1908], outs := [1912], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g42]
  rw [pm_prefix_eq initPM 295 1908 (by native_decide)]
  rw [pm_full_1908]

-- ========== PM self-frame: 1909-1912 (组合 AllToAll + FW_div) ==========
theorem pm_frame_1909_to_mini (initPM : Store) :
    denoteGraph pm initPM 1909 = denoteGraph pm_goal_42 (denoteGraph pm initPM) 1909 := by
  rw [denote_pm_goal_42_1909, pm_frame_1909_self,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1910_to_mini (initPM : Store) :
    denoteGraph pm initPM 1910 = denoteGraph pm_goal_42 (denoteGraph pm initPM) 1910 := by
  rw [denote_pm_goal_42_1910, pm_frame_1910_self,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1911_to_mini (initPM : Store) :
    denoteGraph pm initPM 1911 = denoteGraph pm_goal_42 (denoteGraph pm initPM) 1911 := by
  rw [denote_pm_goal_42_1911, pm_frame_1911_self,
      show pm.numRanks = 4 from by native_decide]

theorem pm_frame_1912_to_mini (initPM : Store) :
    denoteGraph pm initPM 1912 = denoteGraph pm_goal_42 (denoteGraph pm initPM) 1912 := by
  rw [denote_pm_goal_42_1912, pm_frame_1912_self,
      show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_42_cut_to_full (h : goal_42_stmt_cut) : goal_42_stmt := by
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
  have hg31 := goal_31_intermediate initSM initPM hSM hPM hInit
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg41 := goal_41_intermediate initSM initPM hSM hPM hInit
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
  have hnr : pm_goal_42.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_42.numRanks goal_42_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_42_cut_initGoals, goal_42_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg41
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
  -- shape: 619 = goal_41.ts (singleton on SM), shape [1,4,8,8]; 1881-1884 = goal_41.tps, each [1,1,8,8]
  have h619_smsh : (Ssm 619).shape = [1, 4, 8, 8] := by
    have h := hg41.1; simp only [goal_41] at h; exact h
  have hpmsh : (Spm 1881).shape = [1,1,8,8] ∧ (Spm 1882).shape = [1,1,8,8] ∧
               (Spm 1883).shape = [1,1,8,8] ∧ (Spm 1884).shape = [1,1,8,8] := by
    have h := hg41.2.1
    simp only [goal_41, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1881sh, h1882sh, h1883sh, h1884sh⟩ := hpmsh
  have hSM42 : StoreShapesHold Ssm sm_goal_42InitEnv := by
    intro tid sh hsh
    rw [sm_goal_42InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_42InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h619_smsh
  have hPM42 : StoreShapesHold Spm pm_goal_42InitEnv := by
    intro tid sh hsh
    rw [pm_goal_42InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_42InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1881sh
    · exact h1882sh
    · exact h1883sh
    · exact h1884sh
  have hcut := h Ssm Spm hSM42 hPM42 hInitCut
  have hsmf : Ssm 620 = denoteGraph sm_goal_42 Ssm 620 := by
    rw [hSsm]; exact sm_frame_620_self initSM
  have hpm1909 : Spm 1909 = denoteGraph pm_goal_42 Spm 1909 := by
    rw [hSpm]; exact pm_frame_1909_to_mini initPM
  have hpm1910 : Spm 1910 = denoteGraph pm_goal_42 Spm 1910 := by
    rw [hSpm]; exact pm_frame_1910_to_mini initPM
  have hpm1911 : Spm 1911 = denoteGraph pm_goal_42 Spm 1911 := by
    rw [hSpm]; exact pm_frame_1911_to_mini initPM
  have hpm1912 : Spm 1912 = denoteGraph pm_goal_42 Spm 1912 := by
    rw [hSpm]; exact pm_frame_1912_to_mini initPM
  rw [hnr] at hcut
  simp only [goal_42, List.map] at hcut ⊢
  rw [hsmf, hpm1909, hpm1910, hpm1911, hpm1912]
  exact hcut

theorem goal_42_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_42 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_42_stmt := goal_42_cut_to_full prove_goal_42_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_42] using this

end TrainVerify.Denote.GeneratedGoals
