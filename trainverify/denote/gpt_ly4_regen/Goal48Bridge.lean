/- goal_48 桥 (prereqs 57 个: goal_2..goal_47 + 257,259,261,263,265,267,269,271,275,277,279)。
   SM=FW_linear(625,626)→627 (sm node 51, 2 inputs: activation + weight);
   PM=4×ChunkPrim(625,dim=1)→2021-2024 (pm node 330-333), 然后 4×FW_linear(2021+r,626)→2025-2028 (pm node 334-337).
   625=goal_47 输出 (single-tp [1,8,32], ts==tid 625). 626=initGoal_626 (shared weight [32,32], replicated).
   multi-tps 输出 tids 2025-2028, gatherDim=1.
   结构类比 goal_45 (ChunkPrim + per-rank op), 但 per-rank op 是 FW_linear(两 input), 不是 FW_transpose。
   weight 626 在所有 rank 共享（不切）, 直接从 init store 读取。 -/
import denote.gpt_ly4_regen.Goal47Bridge
import denote.gpt_ly4_regen.Goal_48

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

-- ========== 迷你图 sm_goal_48 算 627 ==========
theorem denote_sm_goal_48_627 (s : Store) :
    denoteGraph sm_goal_48 s 627 = fw_linear (s 625) (s 626) := by
  simp only [sm_goal_48, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== 迷你图 pm_goal_48 算 2025-2028 ==========
theorem denote_pm_goal_48_2025 (s : Store) :
    denoteGraph pm_goal_48 s 2025 = fw_linear (chunkPrimDimN 1 4 0 (s 625)) (s 626) := by
  simp only [pm_goal_48, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_48_2026 (s : Store) :
    denoteGraph pm_goal_48 s 2026 = fw_linear (chunkPrimDimN 1 4 1 (s 625)) (s 626) := by
  simp only [pm_goal_48, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_48_2027 (s : Store) :
    denoteGraph pm_goal_48 s 2027 = fw_linear (chunkPrimDimN 1 4 2 (s 625)) (s 626) := by
  simp only [pm_goal_48, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_48_2028 (s : Store) :
    denoteGraph pm_goal_48 s 2028 = fw_linear (chunkPrimDimN 1 4 3 (s 625)) (s 626) := by
  simp only [pm_goal_48, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_linear_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 627 (node 51) ==========
theorem sm_frame_627_self (initSM : Store) :
    denoteGraph sm initSM 627 = denoteGraph sm_goal_48 (denoteGraph sm initSM) 627 := by
  rw [denote_sm_goal_48_627]
  rw [sm_val initSM 51 627 (by native_decide) (by native_decide)]
  rw [show sm.nodes[51]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [625, 626], outs := [627] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 51 625 (by native_decide)]
  rw [sm_prefix_eq initSM 51 626 (by native_decide)]

-- ========== PM full: 2021-2024 (4 ChunkPrim dim=1, node 330-333) ==========
theorem pm_full_g48_2021 (initPM : Store) :
    denoteGraph pm initPM 2021 = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 625) := by
  rw [pm_val initPM 330 2021 (by native_decide) (by native_decide)]
  rw [show pm.nodes[330]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [625], outs := [2021], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 330 625 (by native_decide)]

theorem pm_full_g48_2022 (initPM : Store) :
    denoteGraph pm initPM 2022 = chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 625) := by
  rw [pm_val initPM 331 2022 (by native_decide) (by native_decide)]
  rw [show pm.nodes[331]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [625], outs := [2022], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 331 625 (by native_decide)]

theorem pm_full_g48_2023 (initPM : Store) :
    denoteGraph pm initPM 2023 = chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 625) := by
  rw [pm_val initPM 332 2023 (by native_decide) (by native_decide)]
  rw [show pm.nodes[332]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [625], outs := [2023], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 332 625 (by native_decide)]

theorem pm_full_g48_2024 (initPM : Store) :
    denoteGraph pm initPM 2024 = chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 625) := by
  rw [pm_val initPM 333 2024 (by native_decide) (by native_decide)]
  rw [show pm.nodes[333]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [625], outs := [2024], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 333 625 (by native_decide)]

-- ========== PM full: 2025-2028 (4 FW_linear(chunk_r, 626), node 334-337) ==========
theorem pm_frame_2025_self (initPM : Store) :
    denoteGraph pm initPM 2025
      = fw_linear (chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 625))
                  (denoteGraph pm initPM 626) := by
  rw [pm_val initPM 334 2025 (by native_decide) (by native_decide)]
  rw [show pm.nodes[334]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [2021, 626], outs := [2025] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 334 2021 (by native_decide)]
  rw [pm_prefix_eq initPM 334 626 (by native_decide)]
  rw [pm_full_g48_2021]

theorem pm_frame_2026_self (initPM : Store) :
    denoteGraph pm initPM 2026
      = fw_linear (chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 625))
                  (denoteGraph pm initPM 626) := by
  rw [pm_val initPM 335 2026 (by native_decide) (by native_decide)]
  rw [show pm.nodes[335]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [2022, 626], outs := [2026] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 335 2022 (by native_decide)]
  rw [pm_prefix_eq initPM 335 626 (by native_decide)]
  rw [pm_full_g48_2022]

theorem pm_frame_2027_self (initPM : Store) :
    denoteGraph pm initPM 2027
      = fw_linear (chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 625))
                  (denoteGraph pm initPM 626) := by
  rw [pm_val initPM 336 2027 (by native_decide) (by native_decide)]
  rw [show pm.nodes[336]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [2023, 626], outs := [2027] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 336 2023 (by native_decide)]
  rw [pm_prefix_eq initPM 336 626 (by native_decide)]
  rw [pm_full_g48_2023]

theorem pm_frame_2028_self (initPM : Store) :
    denoteGraph pm initPM 2028
      = fw_linear (chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 625))
                  (denoteGraph pm initPM 626) := by
  rw [pm_val initPM 337 2028 (by native_decide) (by native_decide)]
  rw [show pm.nodes[337]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [2024, 626], outs := [2028] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 337 2024 (by native_decide)]
  rw [pm_prefix_eq initPM 337 626 (by native_decide)]
  rw [pm_full_g48_2024]

-- ========== 总装 ==========
theorem goal_48_cut_to_full (h : goal_48_stmt_cut) : goal_48_stmt := by
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
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hg277 hg279 hinitC
  have hnr : pm_goal_48.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_48.numRanks goal_48_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_48_cut_initGoals, goal_48_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg275, hg277, hg279, List.forall_mem_nil _⟩
  -- 625 = goal_47.ts (single-tp, shape [1,8,32])
  have h625_smsh : (Ssm 625).shape = [1, 8, 32] := by
    have h := hg47.1; simp only [goal_47] at h; exact h
  have h625_pmsh : (Spm 625).shape = [1, 8, 32] := by
    have h := hg47.2.1; simp only [goal_47, List.map, List.cons.injEq, and_true] at h; exact h
  -- 626 = initGoal_626 (replicated weight, shape [32,32])
  have hInit626 : InitGoalHolds pm_goal_48.numRanks initGoal_626 Ssm Spm := by
    rw [hnr]; exact hinitC initGoal_626 (by simp only [initGoals]; decide)
  have h626_smsh : (Ssm 626).shape = [32, 32] := by
    have h := hInit626.1; simp only [initGoal_626] at h; exact h
  have h626_pmsh : (Spm 626).shape = [32, 32] := by
    have h := hInit626.2.1; simp only [initGoal_626, List.map, List.cons.injEq, and_true] at h
    exact h
  have hSM48 : StoreShapesHold Ssm sm_goal_48InitEnv := by
    intro tid sh hsh
    rw [sm_goal_48InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_48InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h625_smsh
    · exact h626_smsh
  have hPM48 : StoreShapesHold Spm pm_goal_48InitEnv := by
    intro tid sh hsh
    rw [pm_goal_48InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_48InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h625_pmsh
    · exact h626_pmsh
  have hcut := h Ssm Spm hSM48 hPM48 hInitCut
  -- Frame: 627 (sm node 51), 2025-2028 (pm nodes 334-337)
  have hsmf : Ssm 627 = denoteGraph sm_goal_48 Ssm 627 := by
    rw [hSsm]; exact sm_frame_627_self initSM
  have hpm625 : Spm 625 = denoteGraph pm initPM 625 := by rw [hSpm]
  have hpm626 : Spm 626 = denoteGraph pm initPM 626 := by rw [hSpm]
  have hpm2025 : Spm 2025 = denoteGraph pm_goal_48 Spm 2025 := by
    rw [denote_pm_goal_48_2025]
    rw [hSpm]
    have := pm_frame_2025_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2026 : Spm 2026 = denoteGraph pm_goal_48 Spm 2026 := by
    rw [denote_pm_goal_48_2026]
    rw [hSpm]
    have := pm_frame_2026_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2027 : Spm 2027 = denoteGraph pm_goal_48 Spm 2027 := by
    rw [denote_pm_goal_48_2027]
    rw [hSpm]
    have := pm_frame_2027_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm2028 : Spm 2028 = denoteGraph pm_goal_48 Spm 2028 := by
    rw [denote_pm_goal_48_2028]
    rw [hSpm]
    have := pm_frame_2028_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_48, List.map] at hcut ⊢
  rw [hsmf, hpm2025, hpm2026, hpm2027, hpm2028]
  exact hcut

theorem goal_48_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_48 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_48_stmt := goal_48_cut_to_full prove_goal_48_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
