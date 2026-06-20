/- goal_39 桥 (prereqs=[2..30,33,38,257,259,261,263,265,267,269,271,279], 40 个)。
   SM=FW_transpose(616,p=[1,2])→617 (node 42);
   PM=4×ChunkPrim(616,dim=3)→1825-1828 (node 252-255), 然后 4×FW_transpose(1825..,p=[1,2])→1829-1832 (node 264-267). tps=4个.
   616=goal_38 输出 (single-tp [1,8,4,8])。结构同 goal_37: ChunkPrim+FW_transpose, multi-tps,
   gather distributes over transpose. 唯一差异: ChunkPrim dim=3 (goal_37 是 dim=2)。 -/
import denote.gpt_ly4_regen.Goal38Bridge
import denote.gpt_ly4_regen.Goal_39

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_39 算 617 ==========
theorem denote_sm_goal_39_617 (s : Store) :
    denoteGraph sm_goal_39 s 617 = transposeAxes 1 2 (s 616) := by
  simp only [sm_goal_39, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_39 算 1829-1832 ==========
theorem denote_pm_goal_39_1829 (s : Store) :
    denoteGraph pm_goal_39 s 1829 = transposeAxes 1 2 (chunkPrimDimN 3 4 0 (s 616)) := by
  simp only [pm_goal_39, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_39_1830 (s : Store) :
    denoteGraph pm_goal_39 s 1830 = transposeAxes 1 2 (chunkPrimDimN 3 4 1 (s 616)) := by
  simp only [pm_goal_39, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_39_1831 (s : Store) :
    denoteGraph pm_goal_39 s 1831 = transposeAxes 1 2 (chunkPrimDimN 3 4 2 (s 616)) := by
  simp only [pm_goal_39, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_39_1832 (s : Store) :
    denoteGraph pm_goal_39 s 1832 = transposeAxes 1 2 (chunkPrimDimN 3 4 3 (s 616)) := by
  simp only [pm_goal_39, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 617 (node 42) ==========
theorem sm_frame_617_self (initSM : Store) :
    denoteGraph sm initSM 617 = denoteGraph sm_goal_39 (denoteGraph sm initSM) 617 := by
  rw [denote_sm_goal_39_617]
  rw [sm_val initSM 42 617 (by native_decide) (by native_decide)]
  rw [show sm.nodes[42]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [616], outs := [617], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 42 616 (by native_decide)]

-- ========== PM full: 1825-1828 (4 ChunkPrim dim=3, node 252-255) ==========
theorem pm_full_1825 (initPM : Store) :
    denoteGraph pm initPM 1825 = chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 616) := by
  rw [pm_val initPM 252 1825 (by native_decide) (by native_decide)]
  rw [show pm.nodes[252]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [616], outs := [1825], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 252 616 (by native_decide)]

theorem pm_full_1826 (initPM : Store) :
    denoteGraph pm initPM 1826 = chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 616) := by
  rw [pm_val initPM 253 1826 (by native_decide) (by native_decide)]
  rw [show pm.nodes[253]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [616], outs := [1826], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 253 616 (by native_decide)]

theorem pm_full_1827 (initPM : Store) :
    denoteGraph pm initPM 1827 = chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 616) := by
  rw [pm_val initPM 254 1827 (by native_decide) (by native_decide)]
  rw [show pm.nodes[254]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [616], outs := [1827], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 254 616 (by native_decide)]

theorem pm_full_1828 (initPM : Store) :
    denoteGraph pm initPM 1828 = chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 616) := by
  rw [pm_val initPM 255 1828 (by native_decide) (by native_decide)]
  rw [show pm.nodes[255]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [616], outs := [1828], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 255 616 (by native_decide)]

-- ========== PM full: 1829-1832 (4 FW_transpose, node 264-267) ==========
theorem pm_frame_1829_self (initPM : Store) :
    denoteGraph pm initPM 1829 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 616)) := by
  rw [pm_val initPM 264 1829 (by native_decide) (by native_decide)]
  rw [show pm.nodes[264]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1825], outs := [1829], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 264 1825 (by native_decide)]
  rw [pm_full_1825]

theorem pm_frame_1830_self (initPM : Store) :
    denoteGraph pm initPM 1830 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 616)) := by
  rw [pm_val initPM 265 1830 (by native_decide) (by native_decide)]
  rw [show pm.nodes[265]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1826], outs := [1830], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 265 1826 (by native_decide)]
  rw [pm_full_1826]

theorem pm_frame_1831_self (initPM : Store) :
    denoteGraph pm initPM 1831 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 616)) := by
  rw [pm_val initPM 266 1831 (by native_decide) (by native_decide)]
  rw [show pm.nodes[266]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1827], outs := [1831], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 266 1827 (by native_decide)]
  rw [pm_full_1827]

theorem pm_frame_1832_self (initPM : Store) :
    denoteGraph pm initPM 1832 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 616)) := by
  rw [pm_val initPM 267 1832 (by native_decide) (by native_decide)]
  rw [show pm.nodes[267]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1828], outs := [1832], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 267 1828 (by native_decide)]
  rw [pm_full_1828]

-- ========== 总装 ==========
theorem goal_39_cut_to_full (h : goal_39_stmt_cut) : goal_39_stmt := by
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
  have hg33 := goal_33_intermediate initSM initPM hSM hPM hInit
  have hg38 := goal_38_intermediate initSM initPM hSM hPM hInit
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
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg33 hg38 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg279 hinitC
  have hnr : pm_goal_39.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_39.numRanks goal_39_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_39_cut_initGoals, goal_39_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg33
      · exact hg38
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg279
  -- shape: 616 = goal_38.ts/tps (single), shape [1,8,4,8]
  have h616_smsh : (Ssm 616).shape = [1, 8, 4, 8] := by
    have h := hg38.1; simp only [goal_38] at h; exact h
  have h616_pmsh : (Spm 616).shape = [1, 8, 4, 8] := by
    have h := hg38.2.1; simp only [goal_38, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM39 : StoreShapesHold Ssm sm_goal_39InitEnv := by
    intro tid sh hsh
    rw [sm_goal_39InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_39InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h616_smsh
  have hPM39 : StoreShapesHold Spm pm_goal_39InitEnv := by
    intro tid sh hsh
    rw [pm_goal_39InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_39InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h616_pmsh
  have hcut := h Ssm Spm hSM39 hPM39 hInitCut
  -- Frame: 617 (sm), 1829-1832 (pm)
  have hsmf : Ssm 617 = denoteGraph sm_goal_39 Ssm 617 := by
    rw [hSsm]; exact sm_frame_617_self initSM
  have hpm1829 : Spm 1829 = denoteGraph pm_goal_39 Spm 1829 := by
    rw [denote_pm_goal_39_1829]
    rw [hSpm]
    have := pm_frame_1829_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1830 : Spm 1830 = denoteGraph pm_goal_39 Spm 1830 := by
    rw [denote_pm_goal_39_1830]
    rw [hSpm]
    have := pm_frame_1830_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1831 : Spm 1831 = denoteGraph pm_goal_39 Spm 1831 := by
    rw [denote_pm_goal_39_1831]
    rw [hSpm]
    have := pm_frame_1831_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1832 : Spm 1832 = denoteGraph pm_goal_39 Spm 1832 := by
    rw [denote_pm_goal_39_1832]
    rw [hSpm]
    have := pm_frame_1832_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_39, List.map] at hcut ⊢
  rw [hsmf, hpm1829, hpm1830, hpm1831, hpm1832]
  exact hcut

theorem goal_39_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_39 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_39_stmt := goal_39_cut_to_full prove_goal_39_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
