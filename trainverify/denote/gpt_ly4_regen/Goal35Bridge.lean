/- goal_35 桥 (prereqs=[2..31,34,257,259,261,263,265,267,269,271,275], 40 个)。
   SM=FW_transpose(612,p=[1,2])→613;
   PM=4×ChunkPrim(612,dim=1)→1777-1780, 然后 4×FW_transpose(1777..,p=[1,2])→1781-1784. tps=4个.
   612=goal_34 输出。结构同 goal_14: ChunkPrim+FW_transpose, multi-tps, gather distributes over transpose. -/
import denote.gpt_ly4_regen.Goal34Bridge
import denote.gpt_ly4_regen.Goal_35

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_35 算 613 ==========
theorem denote_sm_goal_35_613 (s : Store) :
    denoteGraph sm_goal_35 s 613 = transposeAxes 1 2 (s 612) := by
  simp only [sm_goal_35, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_35 算 1781-1784 ==========
theorem denote_pm_goal_35_1781 (s : Store) :
    denoteGraph pm_goal_35 s 1781 = transposeAxes 1 2 (chunkPrimDimN 1 4 0 (s 612)) := by
  simp only [pm_goal_35, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_35_1782 (s : Store) :
    denoteGraph pm_goal_35 s 1782 = transposeAxes 1 2 (chunkPrimDimN 1 4 1 (s 612)) := by
  simp only [pm_goal_35, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_35_1783 (s : Store) :
    denoteGraph pm_goal_35 s 1783 = transposeAxes 1 2 (chunkPrimDimN 1 4 2 (s 612)) := by
  simp only [pm_goal_35, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_35_1784 (s : Store) :
    denoteGraph pm_goal_35 s 1784 = transposeAxes 1 2 (chunkPrimDimN 1 4 3 (s 612)) := by
  simp only [pm_goal_35, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 613 (node 40) ==========
theorem sm_frame_613_self (initSM : Store) :
    denoteGraph sm initSM 613 = denoteGraph sm_goal_35 (denoteGraph sm initSM) 613 := by
  rw [denote_sm_goal_35_613]
  rw [sm_val initSM 40 613 (by native_decide) (by native_decide)]
  rw [show sm.nodes[40]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [612], outs := [613], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 40 612 (by native_decide)]

-- ========== PM full: 1777-1780 (4 ChunkPrim, node 244-247) ==========
theorem pm_full_1777 (initPM : Store) :
    denoteGraph pm initPM 1777 = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 612) := by
  rw [pm_val initPM 244 1777 (by native_decide) (by native_decide)]
  rw [show pm.nodes[244]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [612], outs := [1777], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 244 612 (by native_decide)]

theorem pm_full_1778 (initPM : Store) :
    denoteGraph pm initPM 1778 = chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 612) := by
  rw [pm_val initPM 245 1778 (by native_decide) (by native_decide)]
  rw [show pm.nodes[245]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [612], outs := [1778], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 245 612 (by native_decide)]

theorem pm_full_1779 (initPM : Store) :
    denoteGraph pm initPM 1779 = chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 612) := by
  rw [pm_val initPM 246 1779 (by native_decide) (by native_decide)]
  rw [show pm.nodes[246]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [612], outs := [1779], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 246 612 (by native_decide)]

theorem pm_full_1780 (initPM : Store) :
    denoteGraph pm initPM 1780 = chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 612) := by
  rw [pm_val initPM 247 1780 (by native_decide) (by native_decide)]
  rw [show pm.nodes[247]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [612], outs := [1780], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 247 612 (by native_decide)]

-- ========== PM full: 1781-1784 (4 FW_transpose, node 256-259) ==========
theorem pm_frame_1781_self (initPM : Store) :
    denoteGraph pm initPM 1781 = transposeAxes 1 2 (chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 612)) := by
  rw [pm_val initPM 256 1781 (by native_decide) (by native_decide)]
  rw [show pm.nodes[256]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1777], outs := [1781], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 256 1777 (by native_decide)]
  rw [pm_full_1777]

theorem pm_frame_1782_self (initPM : Store) :
    denoteGraph pm initPM 1782 = transposeAxes 1 2 (chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 612)) := by
  rw [pm_val initPM 257 1782 (by native_decide) (by native_decide)]
  rw [show pm.nodes[257]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1778], outs := [1782], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 257 1778 (by native_decide)]
  rw [pm_full_1778]

theorem pm_frame_1783_self (initPM : Store) :
    denoteGraph pm initPM 1783 = transposeAxes 1 2 (chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 612)) := by
  rw [pm_val initPM 258 1783 (by native_decide) (by native_decide)]
  rw [show pm.nodes[258]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1779], outs := [1783], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 258 1779 (by native_decide)]
  rw [pm_full_1779]

theorem pm_frame_1784_self (initPM : Store) :
    denoteGraph pm initPM 1784 = transposeAxes 1 2 (chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 612)) := by
  rw [pm_val initPM 259 1784 (by native_decide) (by native_decide)]
  rw [show pm.nodes[259]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1780], outs := [1784], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 259 1780 (by native_decide)]
  rw [pm_full_1780]

-- ========== 总装 ==========
theorem goal_35_cut_to_full (h : goal_35_stmt_cut) : goal_35_stmt := by
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
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
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
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg34 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hinitC
  have hnr : pm_goal_35.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_35.numRanks goal_35_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_35_cut_initGoals, goal_35_prereqs, List.mem_append] at hg
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
      · exact hg31
      · exact hg34
      · exact hg257
      · exact hg259
      · exact hg261
      · exact hg263
      · exact hg265
      · exact hg267
      · exact hg269
      · exact hg271
      · exact hg275
  -- shape: 612 = goal_34.ts/tps (single), shape [1,8,4,8]
  have h612_smsh : (Ssm 612).shape = [1, 8, 4, 8] := by
    have h := hg34.1; simp only [goal_34] at h; exact h
  have h612_pmsh : (Spm 612).shape = [1, 8, 4, 8] := by
    have h := hg34.2.1; simp only [goal_34, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM35 : StoreShapesHold Ssm sm_goal_35InitEnv := by
    intro tid sh hsh
    rw [sm_goal_35InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_35InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h612_smsh
  have hPM35 : StoreShapesHold Spm pm_goal_35InitEnv := by
    intro tid sh hsh
    rw [pm_goal_35InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_35InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h612_pmsh
  have hcut := h Ssm Spm hSM35 hPM35 hInitCut
  -- Frame: 613 (sm), 1781-1784 (pm)
  have hsmf : Ssm 613 = denoteGraph sm_goal_35 Ssm 613 := by
    rw [hSsm]; exact sm_frame_613_self initSM
  have hpm1781 : Spm 1781 = denoteGraph pm_goal_35 Spm 1781 := by
    rw [denote_pm_goal_35_1781]
    rw [hSpm]
    have := pm_frame_1781_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1782 : Spm 1782 = denoteGraph pm_goal_35 Spm 1782 := by
    rw [denote_pm_goal_35_1782]
    rw [hSpm]
    have := pm_frame_1782_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1783 : Spm 1783 = denoteGraph pm_goal_35 Spm 1783 := by
    rw [denote_pm_goal_35_1783]
    rw [hSpm]
    have := pm_frame_1783_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1784 : Spm 1784 = denoteGraph pm_goal_35 Spm 1784 := by
    rw [denote_pm_goal_35_1784]
    rw [hSpm]
    have := pm_frame_1784_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_35, List.map] at hcut ⊢
  rw [hsmf, hpm1781, hpm1782, hpm1783, hpm1784]
  exact hcut

theorem goal_35_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_35 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_35_stmt := goal_35_cut_to_full prove_goal_35_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
