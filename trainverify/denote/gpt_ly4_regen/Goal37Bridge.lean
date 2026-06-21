/- goal_37 桥 (prereqs=[2..30,32,36,257,259,261,263,265,267,269,271,277], 40 个)。
   SM=FW_transpose(614,p=[1,2])→615;
   PM=4×ChunkPrim(614,dim=2)→1801-1804, 然后 4×FW_transpose(1801..,p=[1,2])→1805-1808. tps=4个.
   614=goal_36 输出 (single-tp [1,8,4,8])。结构同 goal_35: ChunkPrim+FW_transpose, multi-tps,
   gather distributes over transpose. 唯一差异: ChunkPrim dim=2 (goal_35 是 dim=1)。 -/
import denote.gpt_ly4_regen.Goal36Bridge
import denote.gpt_ly4_regen.Goal_37

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_37 算 615 ==========
theorem denote_sm_goal_37_615 (s : Store) :
    denoteGraph sm_goal_37 s 615 = transposeAxes 1 2 (s 614) := by
  simp only [sm_goal_37, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_37 算 1805-1808 ==========
theorem denote_pm_goal_37_1805 (s : Store) :
    denoteGraph pm_goal_37 s 1805 = transposeAxes 1 2 (chunkPrimDimN 2 4 0 (s 614)) := by
  simp only [pm_goal_37, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_37_1806 (s : Store) :
    denoteGraph pm_goal_37 s 1806 = transposeAxes 1 2 (chunkPrimDimN 2 4 1 (s 614)) := by
  simp only [pm_goal_37, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_37_1807 (s : Store) :
    denoteGraph pm_goal_37 s 1807 = transposeAxes 1 2 (chunkPrimDimN 2 4 2 (s 614)) := by
  simp only [pm_goal_37, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_37_1808 (s : Store) :
    denoteGraph pm_goal_37 s 1808 = transposeAxes 1 2 (chunkPrimDimN 2 4 3 (s 614)) := by
  simp only [pm_goal_37, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 615 (node 41) ==========
theorem sm_frame_615_self (initSM : Store) :
    denoteGraph sm initSM 615 = denoteGraph sm_goal_37 (denoteGraph sm initSM) 615 := by
  rw [denote_sm_goal_37_615]
  rw [sm_val initSM 41 615 (by native_decide) (by native_decide)]
  rw [show sm.nodes[41]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [614], outs := [615], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 41 614 (by native_decide)]

-- ========== PM full: 1801-1804 (4 ChunkPrim dim=2, node 236-239) ==========
theorem pm_full_1801 (initPM : Store) :
    denoteGraph pm initPM 1801 = chunkPrimDimN 2 pm.numRanks 0 (denoteGraph pm initPM 614) := by
  rw [pm_val initPM 236 1801 (by native_decide) (by native_decide)]
  rw [show pm.nodes[236]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [614], outs := [1801], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 236 614 (by native_decide)]

theorem pm_full_1802 (initPM : Store) :
    denoteGraph pm initPM 1802 = chunkPrimDimN 2 pm.numRanks 1 (denoteGraph pm initPM 614) := by
  rw [pm_val initPM 237 1802 (by native_decide) (by native_decide)]
  rw [show pm.nodes[237]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [614], outs := [1802], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 237 614 (by native_decide)]

theorem pm_full_1803 (initPM : Store) :
    denoteGraph pm initPM 1803 = chunkPrimDimN 2 pm.numRanks 2 (denoteGraph pm initPM 614) := by
  rw [pm_val initPM 238 1803 (by native_decide) (by native_decide)]
  rw [show pm.nodes[238]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [614], outs := [1803], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 238 614 (by native_decide)]

theorem pm_full_1804 (initPM : Store) :
    denoteGraph pm initPM 1804 = chunkPrimDimN 2 pm.numRanks 3 (denoteGraph pm initPM 614) := by
  rw [pm_val initPM 239 1804 (by native_decide) (by native_decide)]
  rw [show pm.nodes[239]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [614], outs := [1804], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 239 614 (by native_decide)]

-- ========== PM full: 1805-1808 (4 FW_transpose, node 248-251) ==========
theorem pm_frame_1805_self (initPM : Store) :
    denoteGraph pm initPM 1805 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 0 (denoteGraph pm initPM 614)) := by
  rw [pm_val initPM 248 1805 (by native_decide) (by native_decide)]
  rw [show pm.nodes[248]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1801], outs := [1805], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 248 1801 (by native_decide)]
  rw [pm_full_1801]

theorem pm_frame_1806_self (initPM : Store) :
    denoteGraph pm initPM 1806 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 1 (denoteGraph pm initPM 614)) := by
  rw [pm_val initPM 249 1806 (by native_decide) (by native_decide)]
  rw [show pm.nodes[249]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1802], outs := [1806], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 249 1802 (by native_decide)]
  rw [pm_full_1802]

theorem pm_frame_1807_self (initPM : Store) :
    denoteGraph pm initPM 1807 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 2 (denoteGraph pm initPM 614)) := by
  rw [pm_val initPM 250 1807 (by native_decide) (by native_decide)]
  rw [show pm.nodes[250]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1803], outs := [1807], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 250 1803 (by native_decide)]
  rw [pm_full_1803]

theorem pm_frame_1808_self (initPM : Store) :
    denoteGraph pm initPM 1808 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 3 (denoteGraph pm initPM 614)) := by
  rw [pm_val initPM 251 1808 (by native_decide) (by native_decide)]
  rw [show pm.nodes[251]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1804], outs := [1808], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 251 1804 (by native_decide)]
  rw [pm_full_1804]

-- ========== 总装 ==========
theorem goal_37_cut_to_full (h : goal_37_stmt_cut) : goal_37_stmt := by
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
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
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
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg32 hg36 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg277 hinitC
  have hnr : pm_goal_37.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_37.numRanks goal_37_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_37_cut_initGoals, goal_37_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg32, hg36, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg277, List.forall_mem_nil _⟩
  -- shape: 614 = goal_36.ts/tps (single), shape [1,8,4,8]
  have h614_smsh : (Ssm 614).shape = [1, 8, 4, 8] := by
    have h := hg36.1; simp only [goal_36] at h; exact h
  have h614_pmsh : (Spm 614).shape = [1, 8, 4, 8] := by
    have h := hg36.2.1; simp only [goal_36, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM37 : StoreShapesHold Ssm sm_goal_37InitEnv := by
    intro tid sh hsh
    rw [sm_goal_37InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_37InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h614_smsh
  have hPM37 : StoreShapesHold Spm pm_goal_37InitEnv := by
    intro tid sh hsh
    rw [pm_goal_37InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_37InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h614_pmsh
  have hcut := h Ssm Spm hSM37 hPM37 hInitCut
  -- Frame: 615 (sm), 1805-1808 (pm)
  have hsmf : Ssm 615 = denoteGraph sm_goal_37 Ssm 615 := by
    rw [hSsm]; exact sm_frame_615_self initSM
  have hpm1805 : Spm 1805 = denoteGraph pm_goal_37 Spm 1805 := by
    rw [denote_pm_goal_37_1805]
    rw [hSpm]
    have := pm_frame_1805_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1806 : Spm 1806 = denoteGraph pm_goal_37 Spm 1806 := by
    rw [denote_pm_goal_37_1806]
    rw [hSpm]
    have := pm_frame_1806_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1807 : Spm 1807 = denoteGraph pm_goal_37 Spm 1807 := by
    rw [denote_pm_goal_37_1807]
    rw [hSpm]
    have := pm_frame_1807_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1808 : Spm 1808 = denoteGraph pm_goal_37 Spm 1808 := by
    rw [denote_pm_goal_37_1808]
    rw [hSpm]
    have := pm_frame_1808_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_37, List.map] at hcut ⊢
  rw [hsmf, hpm1805, hpm1806, hpm1807, hpm1808]
  exact hcut

theorem goal_37_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_37 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_37_stmt := goal_37_cut_to_full prove_goal_37_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
