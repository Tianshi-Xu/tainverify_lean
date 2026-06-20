/- goal_14 桥 (prereqs=[2,3,4,5,8,13,257,265])。SM=FW_transpose(581,p=[1,2])→582;
   PM=4×ChunkPrim(581,dim=3)→1305-1308, 然后 4×FW_transpose(1305..,p=[1,2])→1309-1312. tps=4个.
   581=goal_13 输出。第 14 种结构: ChunkPrim+FW_transpose, multi-tps, gather distributes over transpose. -/
import denote.gpt_ly4_regen.Goal13Bridge
import denote.gpt_ly4_regen.Goal_14

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_14 算 582 ==========
theorem denote_sm_goal_14_582 (s : Store) :
    denoteGraph sm_goal_14 s 582 = transposeAxes 1 2 (s 581) := by
  simp only [sm_goal_14, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_14 算 1309-1312 ==========
theorem denote_pm_goal_14_1309 (s : Store) :
    denoteGraph pm_goal_14 s 1309 = transposeAxes 1 2 (chunkPrimDimN 3 4 0 (s 581)) := by
  simp only [pm_goal_14, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_14_1310 (s : Store) :
    denoteGraph pm_goal_14 s 1310 = transposeAxes 1 2 (chunkPrimDimN 3 4 1 (s 581)) := by
  simp only [pm_goal_14, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_14_1311 (s : Store) :
    denoteGraph pm_goal_14 s 1311 = transposeAxes 1 2 (chunkPrimDimN 3 4 2 (s 581)) := by
  simp only [pm_goal_14, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_14_1312 (s : Store) :
    denoteGraph pm_goal_14 s 1312 = transposeAxes 1 2 (chunkPrimDimN 3 4 3 (s 581)) := by
  simp only [pm_goal_14, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 582 (node 14) ==========
theorem sm_frame_582_self (initSM : Store) :
    denoteGraph sm initSM 582 = denoteGraph sm_goal_14 (denoteGraph sm initSM) 582 := by
  rw [denote_sm_goal_14_582]
  rw [sm_val initSM 14 582 (by native_decide) (by native_decide)]
  rw [show sm.nodes[14]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [581], outs := [582], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 14 581 (by native_decide)]

-- ========== PM full: 1305-1308 (4 ChunkPrim, node 77-80) ==========
theorem pm_full_1305 (initPM : Store) :
    denoteGraph pm initPM 1305 = chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 581) := by
  rw [pm_val initPM 77 1305 (by native_decide) (by native_decide)]
  rw [show pm.nodes[77]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [581], outs := [1305], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 77 581 (by native_decide)]

theorem pm_full_1306 (initPM : Store) :
    denoteGraph pm initPM 1306 = chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 581) := by
  rw [pm_val initPM 78 1306 (by native_decide) (by native_decide)]
  rw [show pm.nodes[78]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [581], outs := [1306], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 78 581 (by native_decide)]

theorem pm_full_1307 (initPM : Store) :
    denoteGraph pm initPM 1307 = chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 581) := by
  rw [pm_val initPM 79 1307 (by native_decide) (by native_decide)]
  rw [show pm.nodes[79]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [581], outs := [1307], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 79 581 (by native_decide)]

theorem pm_full_1308 (initPM : Store) :
    denoteGraph pm initPM 1308 = chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 581) := by
  rw [pm_val initPM 80 1308 (by native_decide) (by native_decide)]
  rw [show pm.nodes[80]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [581], outs := [1308], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 80 581 (by native_decide)]

-- ========== PM full: 1309-1312 (4 FW_transpose, node 89-92) ==========
theorem pm_frame_1309_self (initPM : Store) :
    denoteGraph pm initPM 1309 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 581)) := by
  rw [pm_val initPM 89 1309 (by native_decide) (by native_decide)]
  rw [show pm.nodes[89]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1305], outs := [1309], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 89 1305 (by native_decide)]
  rw [pm_full_1305]

theorem pm_frame_1310_self (initPM : Store) :
    denoteGraph pm initPM 1310 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 581)) := by
  rw [pm_val initPM 90 1310 (by native_decide) (by native_decide)]
  rw [show pm.nodes[90]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1306], outs := [1310], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 90 1306 (by native_decide)]
  rw [pm_full_1306]

theorem pm_frame_1311_self (initPM : Store) :
    denoteGraph pm initPM 1311 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 581)) := by
  rw [pm_val initPM 91 1311 (by native_decide) (by native_decide)]
  rw [show pm.nodes[91]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1307], outs := [1311], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 91 1307 (by native_decide)]
  rw [pm_full_1307]

theorem pm_frame_1312_self (initPM : Store) :
    denoteGraph pm initPM 1312 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 581)) := by
  rw [pm_val initPM 92 1312 (by native_decide) (by native_decide)]
  rw [show pm.nodes[92]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1308], outs := [1312], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 92 1308 (by native_decide)]
  rw [pm_full_1308]

-- ========== 总装 ==========
theorem goal_14_cut_to_full (h : goal_14_stmt_cut) : goal_14_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg8 := goal_8_intermediate initSM initPM hSM hPM hInit
  have hg13 := goal_13_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg8 hg13 hg257 hg265 hinitC
  have hnr : pm_goal_14.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_14.numRanks goal_14_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_14_cut_initGoals, goal_14_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg8
      · exact hg13
      · exact hg257
      · exact hg265
  -- shape: 581 = goal_13.ts/tps (single), shape [1,8,4,8]
  have h581_smsh : (Ssm 581).shape = [1, 8, 4, 8] := by
    have h := hg13.1; simp only [goal_13] at h; exact h
  have h581_pmsh : (Spm 581).shape = [1, 8, 4, 8] := by
    have h := hg13.2.1; simp only [goal_13, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM14 : StoreShapesHold Ssm sm_goal_14InitEnv := by
    intro tid sh hsh
    rw [sm_goal_14InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_14InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h581_smsh
  have hPM14 : StoreShapesHold Spm pm_goal_14InitEnv := by
    intro tid sh hsh
    rw [pm_goal_14InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_14InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h581_pmsh
  have hcut := h Ssm Spm hSM14 hPM14 hInitCut
  -- Frame: 582 (sm), 1309-1312 (pm)
  have hsmf : Ssm 582 = denoteGraph sm_goal_14 Ssm 582 := by
    rw [hSsm]; exact sm_frame_582_self initSM
  have hpm1309 : Spm 1309 = denoteGraph pm_goal_14 Spm 1309 := by
    rw [denote_pm_goal_14_1309]
    rw [hSpm]
    have := pm_frame_1309_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1310 : Spm 1310 = denoteGraph pm_goal_14 Spm 1310 := by
    rw [denote_pm_goal_14_1310]
    rw [hSpm]
    have := pm_frame_1310_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1311 : Spm 1311 = denoteGraph pm_goal_14 Spm 1311 := by
    rw [denote_pm_goal_14_1311]
    rw [hSpm]
    have := pm_frame_1311_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1312 : Spm 1312 = denoteGraph pm_goal_14 Spm 1312 := by
    rw [denote_pm_goal_14_1312]
    rw [hSpm]
    have := pm_frame_1312_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_14, List.map] at hcut ⊢
  rw [hsmf, hpm1309, hpm1310, hpm1311, hpm1312]
  exact hcut

theorem goal_14_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_14 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_14_stmt := goal_14_cut_to_full prove_goal_14_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
