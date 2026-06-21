/- goal_33 桥 (prereqs=[2..30,257,259,261,263,265,267,269,271,275], 38 个)。
   第 28 种结构 (新 collective AllReducePrim, row-parallel FW_linear)。
   SM=FW_linear(969,610)→611 (sm node 36, [1,8,32]×[32,32]→[1,8,32], row-parallel)。
   PM=4×FW_linear(1749+r,1753+r)→1757-1760 (pm node 218/220/222/225, 非相邻!),
      然后 AllReducePrim((range4).map(1757+r))→611 (pm node 231)。
   969=goal_279 输出 [1,8,32] (gather dim2, tps 1749-1752 各 [1,8,8]);
   610=initGoal_610 [32,32] (gather dim1, tps 1753-1756 各 [32,8], column-sharded weight, 复制语义)。
   single-tp 输出 (goal_33.tps=[{0,611}]), reconstructWithDim_singleton。
   套 Goal16Bridge 模板 (4×per-rank-op → AllReduce → single output, computed-range ins);
   算子 FW_matmul→FW_linear; initGoal_610 处理仿 Goal28Bridge 的 initGoal_600。
   注: row-split/inner-product 语义在 prove_goal_33_cut 里已处理
   (fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d); bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal279Bridge
import denote.gpt_ly4_regen.Goal_33

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_33 算 611 (FW_linear) ==========
theorem denote_sm_goal_33_611 (s : Store) :
    denoteGraph sm_goal_33 s 611 = fw_linear (s 969) (s 610) := by
  simp only [sm_goal_33, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_33 算 611 (4×FW_linear → AllReduce) ==========
theorem denote_pm_goal_33_611 (s : Store) :
    denoteGraph pm_goal_33 s 611 = allReducePrim 4 0
      [fw_linear (s 1749) (s 1753), fw_linear (s 1750) (s 1754),
       fw_linear (s 1751) (s 1755), fw_linear (s 1752) (s 1756)] := by
  simp only [pm_goal_33, denoteGraph, List.foldl]
  rw [applyNode_allReducePrim_out]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full sm 算 611 (node 36 FW_linear) ==========
theorem sm_frame_611_self (initSM : Store) :
    denoteGraph sm initSM 611 = denoteGraph sm_goal_33 (denoteGraph sm initSM) 611 := by
  rw [denote_sm_goal_33_611]
  rw [sm_val initSM 36 611 (by native_decide) (by native_decide)]
  rw [show sm.nodes[36]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [969, 610], outs := [611] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 36 969 (by native_decide),
      sm_prefix_eq initSM 36 610 (by native_decide)]

-- ========== full pm 算 FW_linear 输出 1757-1760 (node 218/220/222/225) ==========
theorem pm_full_1757 (initPM : Store) :
    denoteGraph pm initPM 1757 = fw_linear (denoteGraph pm initPM 1749) (denoteGraph pm initPM 1753) := by
  rw [pm_val initPM 218 1757 (by native_decide) (by native_decide)]
  rw [show pm.nodes[218]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1749, 1753], outs := [1757] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 218 1749 (by native_decide),
      pm_prefix_eq initPM 218 1753 (by native_decide)]

theorem pm_full_1758 (initPM : Store) :
    denoteGraph pm initPM 1758 = fw_linear (denoteGraph pm initPM 1750) (denoteGraph pm initPM 1754) := by
  rw [pm_val initPM 220 1758 (by native_decide) (by native_decide)]
  rw [show pm.nodes[220]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [1750, 1754], outs := [1758] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 220 1750 (by native_decide),
      pm_prefix_eq initPM 220 1754 (by native_decide)]

theorem pm_full_1759 (initPM : Store) :
    denoteGraph pm initPM 1759 = fw_linear (denoteGraph pm initPM 1751) (denoteGraph pm initPM 1755) := by
  rw [pm_val initPM 222 1759 (by native_decide) (by native_decide)]
  rw [show pm.nodes[222]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [1751, 1755], outs := [1759] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 222 1751 (by native_decide),
      pm_prefix_eq initPM 222 1755 (by native_decide)]

theorem pm_full_1760 (initPM : Store) :
    denoteGraph pm initPM 1760 = fw_linear (denoteGraph pm initPM 1752) (denoteGraph pm initPM 1756) := by
  rw [pm_val initPM 225 1760 (by native_decide) (by native_decide)]
  rw [show pm.nodes[225]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [1752, 1756], outs := [1760] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 225 1752 (by native_decide),
      pm_prefix_eq initPM 225 1756 (by native_decide)]

-- ========== PM self-frame: 611 (AllReduce node 231, ins=computed range) ==========
theorem pm_frame_611_self (initPM : Store) :
    denoteGraph pm initPM 611
      = allReducePrim 4 0
          [fw_linear (denoteGraph pm initPM 1749) (denoteGraph pm initPM 1753),
           fw_linear (denoteGraph pm initPM 1750) (denoteGraph pm initPM 1754),
           fw_linear (denoteGraph pm initPM 1751) (denoteGraph pm initPM 1755),
           fw_linear (denoteGraph pm initPM 1752) (denoteGraph pm initPM 1756)] := by
  rw [pm_val initPM 231 611 (by native_decide) (by native_decide)]
  rw [show pm.nodes[231]'(by native_decide)
      = { rank := 0, op := "OpName.AllReducePrim",
          ins := ((List.range 4).map (fun r => 1757 + r)), outs := [611] }
      from by native_decide]
  rw [applyNode_allReducePrim_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 231 1757 (by native_decide),
      pm_prefix_eq initPM 231 1758 (by native_decide),
      pm_prefix_eq initPM 231 1759 (by native_decide),
      pm_prefix_eq initPM 231 1760 (by native_decide)]
  rw [pm_full_1757, pm_full_1758, pm_full_1759, pm_full_1760]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_33_cut_to_full (h : goal_33_stmt_cut) : goal_33_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg279 hinitC
  have hnr : pm_goal_33.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_33.numRanks goal_33_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_33_cut_initGoals, goal_33_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg279, List.forall_mem_nil _⟩
  -- SM input shapes: 969 = goal_279.ts [1,8,32]; 610 = initGoal_610.ts [32,32]
  have h969_smsh : (Ssm 969).shape = [1, 8, 32] := by
    have h := hg279.1; simp only [goal_279] at h; exact h
  have hg610 := hinitC initGoal_610 (by simp only [initGoals]; decide)
  have h610_smsh : (Ssm 610).shape = [32, 32] := by
    have h := hg610.1; simp only [initGoal_610] at h; exact h
  -- PM tp shapes: 1749-1752 = goal_279.tps [1,8,8]; 1753-1756 = initGoal_610.tps [32,8]
  have hx : (Spm 1749).shape = [1,8,8] ∧ (Spm 1750).shape = [1,8,8] ∧
            (Spm 1751).shape = [1,8,8] ∧ (Spm 1752).shape = [1,8,8] := by
    have h := hg279.2.1
    simp only [goal_279, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1749sh, h1750sh, h1751sh, h1752sh⟩ := hx
  have hy : (Spm 1753).shape = [32,8] ∧ (Spm 1754).shape = [32,8] ∧
            (Spm 1755).shape = [32,8] ∧ (Spm 1756).shape = [32,8] := by
    have h := hg610.2.1
    simp only [initGoal_610, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1753sh, h1754sh, h1755sh, h1756sh⟩ := hy
  have hSM31 : StoreShapesHold Ssm sm_goal_33InitEnv := by
    intro tid sh hsh
    rw [sm_goal_33InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_33InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h610_smsh
    · exact h969_smsh
  have hPM31 : StoreShapesHold Spm pm_goal_33InitEnv := by
    intro tid sh hsh
    rw [pm_goal_33InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_33InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1749sh
    · exact h1750sh
    · exact h1751sh
    · exact h1752sh
    · exact h1753sh
    · exact h1754sh
    · exact h1755sh
    · exact h1756sh
  have hcut := h Ssm Spm hSM31 hPM31 hInitCut
  -- Frame: 611 (sm node 36), 611 (pm node 231)
  have hsmf : Ssm 611 = denoteGraph sm_goal_33 Ssm 611 := by
    rw [hSsm]; exact sm_frame_611_self initSM
  have hpm611 : Spm 611 = denoteGraph pm_goal_33 Spm 611 := by
    rw [denote_pm_goal_33_611]
    rw [hSpm]; exact pm_frame_611_self initPM
  rw [hnr] at hcut
  simp only [goal_33, List.map] at hcut ⊢
  rw [hsmf, hpm611]
  exact hcut

theorem goal_33_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_33 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_33_stmt := goal_33_cut_to_full prove_goal_33_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
