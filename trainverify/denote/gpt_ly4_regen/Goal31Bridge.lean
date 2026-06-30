/- goal_31 桥 (prereqs=[2..30,257,259,261,263,265,267,269,271,275], 38 个)。
   第 28 种结构 (新 collective AllReducePrim, row-parallel FW_linear)。
   SM=FW_linear(961,606)→607 (sm node 34, [1,8,32]×[32,32]→[1,8,32], row-parallel)。
   PM=4×FW_linear(1693+r,1697+r)→1701-1704 (pm node 217/219/221/223, 非相邻!),
      然后 AllReducePrim((range4).map(1701+r))→607 (pm node 226)。
   961=goal_275 输出 [1,8,32] (gather dim2, tps 1693-1696 各 [1,8,8]);
   606=initGoal_606 [32,32] (gather dim1, tps 1697-1700 各 [32,8], column-sharded weight, 复制语义)。
   single-tp 输出 (goal_31.tps=[{0,607}]), reconstructWithDim_singleton。
   套 Goal16Bridge 模板 (4×per-rank-op → AllReduce → single output, computed-range ins);
   算子 FW_matmul→FW_linear; initGoal_606 处理仿 Goal28Bridge 的 initGoal_600。
   注: row-split/inner-product 语义在 prove_goal_31_cut 里已处理
   (fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d); bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal275Bridge
import denote.gpt_ly4_regen.Goal_31

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_31 算 607 (FW_linear) ==========
theorem denote_sm_goal_31_607 (s : Store) :
    denoteGraph sm_goal_31 s 607 = fw_linear (s 961) (s 606) := by
  simp only [sm_goal_31, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_31 算 607 (4×FW_linear → AllReduce) ==========
theorem denote_pm_goal_31_607 (s : Store) :
    denoteGraph pm_goal_31 s 607 = allReducePrim 4 0
      [fw_linear (s 1693) (s 1697), fw_linear (s 1694) (s 1698),
       fw_linear (s 1695) (s 1699), fw_linear (s 1696) (s 1700)] := by
  simp only [pm_goal_31, denoteGraph, List.foldl]
  rw [applyNode_allReducePrim_out]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full sm 算 607 (node 34 FW_linear) ==========
theorem sm_frame_607_self (initSM : Store) :
    denoteGraph sm initSM 607 = denoteGraph sm_goal_31 (denoteGraph sm initSM) 607 := by
  rw [denote_sm_goal_31_607]
  rw [sm_val initSM 34 607 (by native_decide) (by native_decide)]
  rw [show sm.nodes[34]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [961, 606], outs := [607] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 34 961 (by native_decide),
      sm_prefix_eq initSM 34 606 (by native_decide)]

-- ========== full pm 算 FW_linear 输出 1701-1704 (node 217/219/221/223) ==========
theorem pm_full_g31_1701 (initPM : Store) :
    denoteGraph pm initPM 1701 = fw_linear (denoteGraph pm initPM 1693) (denoteGraph pm initPM 1697) := by
  rw [pm_val initPM 217 1701 (by native_decide) (by native_decide)]
  rw [show pm.nodes[217]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1693, 1697], outs := [1701] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 217 1693 (by native_decide),
      pm_prefix_eq initPM 217 1697 (by native_decide)]

theorem pm_full_g31_1702 (initPM : Store) :
    denoteGraph pm initPM 1702 = fw_linear (denoteGraph pm initPM 1694) (denoteGraph pm initPM 1698) := by
  rw [pm_val initPM 219 1702 (by native_decide) (by native_decide)]
  rw [show pm.nodes[219]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [1694, 1698], outs := [1702] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 219 1694 (by native_decide),
      pm_prefix_eq initPM 219 1698 (by native_decide)]

theorem pm_full_g31_1703 (initPM : Store) :
    denoteGraph pm initPM 1703 = fw_linear (denoteGraph pm initPM 1695) (denoteGraph pm initPM 1699) := by
  rw [pm_val initPM 221 1703 (by native_decide) (by native_decide)]
  rw [show pm.nodes[221]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [1695, 1699], outs := [1703] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 221 1695 (by native_decide),
      pm_prefix_eq initPM 221 1699 (by native_decide)]

theorem pm_full_g31_1704 (initPM : Store) :
    denoteGraph pm initPM 1704 = fw_linear (denoteGraph pm initPM 1696) (denoteGraph pm initPM 1700) := by
  rw [pm_val initPM 223 1704 (by native_decide) (by native_decide)]
  rw [show pm.nodes[223]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [1696, 1700], outs := [1704] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 223 1696 (by native_decide),
      pm_prefix_eq initPM 223 1700 (by native_decide)]

-- ========== PM self-frame: 607 (AllReduce node 226, ins=computed range) ==========
theorem pm_frame_607_self (initPM : Store) :
    denoteGraph pm initPM 607
      = allReducePrim 4 0
          [fw_linear (denoteGraph pm initPM 1693) (denoteGraph pm initPM 1697),
           fw_linear (denoteGraph pm initPM 1694) (denoteGraph pm initPM 1698),
           fw_linear (denoteGraph pm initPM 1695) (denoteGraph pm initPM 1699),
           fw_linear (denoteGraph pm initPM 1696) (denoteGraph pm initPM 1700)] := by
  rw [pm_val initPM 226 607 (by native_decide) (by native_decide)]
  rw [show pm.nodes[226]'(by native_decide)
      = { rank := 0, op := "OpName.AllReducePrim",
          ins := ((List.range 4).map (fun r => 1701 + r)), outs := [607] }
      from by native_decide]
  rw [applyNode_allReducePrim_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 226 1701 (by native_decide),
      pm_prefix_eq initPM 226 1702 (by native_decide),
      pm_prefix_eq initPM 226 1703 (by native_decide),
      pm_prefix_eq initPM 226 1704 (by native_decide)]
  rw [pm_full_g31_1701, pm_full_g31_1702, pm_full_g31_1703, pm_full_g31_1704]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_31_cut_to_full (h : goal_31_stmt_cut) : goal_31_stmt := by
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
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hinitC
  have hnr : pm_goal_31.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_31.numRanks goal_31_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_31_cut_initGoals, goal_31_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg275, List.forall_mem_nil _⟩
  -- SM input shapes: 961 = goal_275.ts [1,8,32]; 606 = initGoal_606.ts [32,32]
  have h961_smsh : (Ssm 961).shape = [1, 8, 32] := by
    have h := hg275.1; simp only [goal_275] at h; exact h
  have hg606 := hinitC initGoal_606 (by simp only [initGoals]; decide)
  have h606_smsh : (Ssm 606).shape = [32, 32] := by
    have h := hg606.1; simp only [initGoal_606] at h; exact h
  -- PM tp shapes: 1693-1696 = goal_275.tps [1,8,8]; 1697-1700 = initGoal_606.tps [32,8]
  have hx : (Spm 1693).shape = [1,8,8] ∧ (Spm 1694).shape = [1,8,8] ∧
            (Spm 1695).shape = [1,8,8] ∧ (Spm 1696).shape = [1,8,8] := by
    have h := hg275.2.1
    simp only [goal_275, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1693sh, h1694sh, h1695sh, h1696sh⟩ := hx
  have hy : (Spm 1697).shape = [32,8] ∧ (Spm 1698).shape = [32,8] ∧
            (Spm 1699).shape = [32,8] ∧ (Spm 1700).shape = [32,8] := by
    have h := hg606.2.1
    simp only [initGoal_606, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1697sh, h1698sh, h1699sh, h1700sh⟩ := hy
  have hSM31 : StoreShapesHold Ssm sm_goal_31InitEnv := by
    intro tid sh hsh
    rw [sm_goal_31InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_31InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h606_smsh
    · exact h961_smsh
  have hPM31 : StoreShapesHold Spm pm_goal_31InitEnv := by
    intro tid sh hsh
    rw [pm_goal_31InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_31InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1693sh
    · exact h1694sh
    · exact h1695sh
    · exact h1696sh
    · exact h1697sh
    · exact h1698sh
    · exact h1699sh
    · exact h1700sh
  have hcut := h Ssm Spm hSM31 hPM31 hInitCut
  -- Frame: 607 (sm node 34), 607 (pm node 226)
  have hsmf : Ssm 607 = denoteGraph sm_goal_31 Ssm 607 := by
    rw [hSsm]; exact sm_frame_607_self initSM
  have hpm607 : Spm 607 = denoteGraph pm_goal_31 Spm 607 := by
    rw [denote_pm_goal_31_607]
    rw [hSpm]; exact pm_frame_607_self initPM
  rw [hnr] at hcut
  simp only [goal_31, List.map] at hcut ⊢
  rw [hsmf, hpm607]
  exact hcut

theorem goal_31_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_31 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_31_stmt := goal_31_cut_to_full prove_goal_31_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
