/- goal_32 桥 (prereqs=[2..30, 257, 259, 261, 263, 265, 267, 269, 271, 277], 38 个)。
   第29种结构 (column-parallel FW_linear + AllGatherPrim params=[1], single-tp; 与 goal_6 完全同构, 不同 tids)。
   SM=FW_linear(965,608)→609 (sm node 35, [1,8,32]×[32,32]→[1,8,32], 输出 dim1 收集)。
   PM=4×FW_linear(1721+r, 608)→1725-1728 (pm node 205/206/207/215, **rank3 跳到 215!**),
      然后 AllGatherPrim((range4).map(1725+r)) params=[1] →609 (pm node 224)。
   965=goal_277 输出 [1,8,32] (gather dim1, tps 1721-1724 各 [1,2,32]);
   608=initGoal_608 [32,32] (full weight, single-tp init, rank 0 一份, 复制语义)。
   single-tp 输出 (goal_32.tps=[{0,609}]), reconstructWithDim_singleton。
   套 Goal6Bridge 模板 (4×FW_linear → AllGatherPrim params=[1] → single output, computed-range ins);
   核心语义 (X dim1 shard 后 4×local linear gather 等价 SM linear) 已在 prove_goal_32_cut 处理, bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal31Bridge
import denote.gpt_ly4_regen.Goal277Bridge
import denote.gpt_ly4_regen.Goal_32

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_32 算 609 (FW_linear) ==========
theorem denote_sm_goal_32_609 (s : Store) :
    denoteGraph sm_goal_32 s 609 = fw_linear (s 965) (s 608) := by
  simp only [sm_goal_32, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_32 算 609 (4×FW_linear → AllGather) ==========
theorem denote_pm_goal_32_609 (s : Store) :
    denoteGraph pm_goal_32 s 609 = allGatherPrimDimN 1 4 0
      [fw_linear (s 1721) (s 608), fw_linear (s 1722) (s 608),
       fw_linear (s 1723) (s 608), fw_linear (s 1724) (s 608)] := by
  simp only [pm_goal_32, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out]
  simp only [List.map]
  set_option maxHeartbeats 800000 in congr 1

-- ========== SM self-frame: full sm 算 609 (node 35 FW_linear) ==========
theorem sm_frame_609_self (initSM : Store) :
    denoteGraph sm initSM 609 = denoteGraph sm_goal_32 (denoteGraph sm initSM) 609 := by
  rw [denote_sm_goal_32_609]
  rw [sm_val initSM 35 609 (by native_decide) (by native_decide)]
  rw [show sm.nodes[35]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [965, 608], outs := [609] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 35 965 (by native_decide),
      sm_prefix_eq initSM 35 608 (by native_decide)]

-- ========== full pm 算 FW_linear 输出 1725-1728 (node 205/206/207/215 — rank3 跳!) ==========
theorem pm_full_g32_1725 (initPM : Store) :
    denoteGraph pm initPM 1725 = fw_linear (denoteGraph pm initPM 1721) (denoteGraph pm initPM 608) := by
  rw [pm_val initPM 205 1725 (by native_decide) (by native_decide)]
  rw [show pm.nodes[205]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1721, 608], outs := [1725] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 205 1721 (by native_decide),
      pm_prefix_eq initPM 205 608 (by native_decide)]

theorem pm_full_g32_1726 (initPM : Store) :
    denoteGraph pm initPM 1726 = fw_linear (denoteGraph pm initPM 1722) (denoteGraph pm initPM 608) := by
  rw [pm_val initPM 206 1726 (by native_decide) (by native_decide)]
  rw [show pm.nodes[206]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [1722, 608], outs := [1726] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 206 1722 (by native_decide),
      pm_prefix_eq initPM 206 608 (by native_decide)]

theorem pm_full_g32_1727 (initPM : Store) :
    denoteGraph pm initPM 1727 = fw_linear (denoteGraph pm initPM 1723) (denoteGraph pm initPM 608) := by
  rw [pm_val initPM 207 1727 (by native_decide) (by native_decide)]
  rw [show pm.nodes[207]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [1723, 608], outs := [1727] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 207 1723 (by native_decide),
      pm_prefix_eq initPM 207 608 (by native_decide)]

theorem pm_full_g32_1728 (initPM : Store) :
    denoteGraph pm initPM 1728 = fw_linear (denoteGraph pm initPM 1724) (denoteGraph pm initPM 608) := by
  rw [pm_val initPM 215 1728 (by native_decide) (by native_decide)]
  rw [show pm.nodes[215]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [1724, 608], outs := [1728] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 215 1724 (by native_decide),
      pm_prefix_eq initPM 215 608 (by native_decide)]

-- ========== PM self-frame: 609 (AllGather node 224, ins=computed range, params=[1]) ==========
theorem pm_frame_609_self (initPM : Store) :
    denoteGraph pm initPM 609
      = allGatherPrimDimN 1 4 0
          [fw_linear (denoteGraph pm initPM 1721) (denoteGraph pm initPM 608),
           fw_linear (denoteGraph pm initPM 1722) (denoteGraph pm initPM 608),
           fw_linear (denoteGraph pm initPM 1723) (denoteGraph pm initPM 608),
           fw_linear (denoteGraph pm initPM 1724) (denoteGraph pm initPM 608)] := by
  rw [pm_val initPM 224 609 (by native_decide) (by native_decide)]
  rw [show pm.nodes[224]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 1725 + r)), outs := [609], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 224 1725 (by native_decide),
      pm_prefix_eq initPM 224 1726 (by native_decide),
      pm_prefix_eq initPM 224 1727 (by native_decide),
      pm_prefix_eq initPM 224 1728 (by native_decide)]
  rw [pm_full_g32_1725, pm_full_g32_1726, pm_full_g32_1727, pm_full_g32_1728]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_32_cut_to_full (h : goal_32_stmt_cut) : goal_32_stmt := by
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
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg277 hinitC
  have hnr : pm_goal_32.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_32.numRanks goal_32_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_32_cut_initGoals, goal_32_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg277, List.forall_mem_nil _⟩
  -- SM input shapes: 965 = goal_277.ts [1,8,32]; 608 = initGoal_608.ts [32,32]
  have h965_smsh : (Ssm 965).shape = [1, 8, 32] := by
    have h := hg277.1; simp only [goal_277] at h; exact h
  have hg608 := hinitC initGoal_608 (by simp only [initGoals]; decide)
  have h608_smsh : (Ssm 608).shape = [32, 32] := by
    have h := hg608.1; simp only [initGoal_608] at h; exact h
  -- PM tp shapes: 1721-1724 = goal_277.tps [1,2,32]; 608 = initGoal_608 single-tp [32,32]
  have hx : (Spm 1721).shape = [1,2,32] ∧ (Spm 1722).shape = [1,2,32] ∧
            (Spm 1723).shape = [1,2,32] ∧ (Spm 1724).shape = [1,2,32] := by
    have h := hg277.2.1
    simp only [goal_277, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1721sh, h1722sh, h1723sh, h1724sh⟩ := hx
  have h608_pm : (Spm 608).shape = [32, 32] := by
    have h := hg608.2.1
    simp only [initGoal_608, List.map, List.cons.injEq] at h
    exact h.1
  have hSM32 : StoreShapesHold Ssm sm_goal_32InitEnv := by
    intro tid sh hsh
    rw [sm_goal_32InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_32InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h608_smsh
    · exact h965_smsh
  have hPM32 : StoreShapesHold Spm pm_goal_32InitEnv := by
    intro tid sh hsh
    rw [pm_goal_32InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_32InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h608_pm
    · exact h1721sh
    · exact h1722sh
    · exact h1723sh
    · exact h1724sh
  have hcut := h Ssm Spm hSM32 hPM32 hInitCut
  -- Frame: 609 (sm node 35), 609 (pm node 224)
  have hsmf : Ssm 609 = denoteGraph sm_goal_32 Ssm 609 := by
    rw [hSsm]; exact sm_frame_609_self initSM
  have hpm609 : Spm 609 = denoteGraph pm_goal_32 Spm 609 := by
    rw [denote_pm_goal_32_609]
    rw [hSpm]; exact pm_frame_609_self initPM
  rw [hnr] at hcut
  simp only [goal_32, List.map] at hcut ⊢
  rw [hsmf, hpm609]
  exact hcut

theorem goal_32_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_32 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_32_stmt := goal_32_cut_to_full prove_goal_32_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
