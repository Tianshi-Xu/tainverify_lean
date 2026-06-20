/- goal_12 桥 (prereqs=[2,3,4,5,7,11,257,263])。SM=FW_transpose(579,p=[1,2])→580;
   PM=4×ChunkPrim(579,dim=2)→1281-1284, 然后 4×FW_transpose(1281..,p=[1,2])→1285-1288. tps=4个.
   579=goal_11 输出。第 9 种结构: ChunkPrim+FW_transpose, multi-tps, gather distributes over transpose. -/
import denote.gpt_ly4_regen.Goal11Bridge
import denote.gpt_ly4_regen.Goal_12

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_12 算 580 ==========
theorem denote_sm_goal_12_580 (s : Store) :
    denoteGraph sm_goal_12 s 580 = transposeAxes 1 2 (s 579) := by
  simp only [sm_goal_12, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_12 算 1285-1288 ==========
theorem denote_pm_goal_12_1285 (s : Store) :
    denoteGraph pm_goal_12 s 1285 = transposeAxes 1 2 (chunkPrimDimN 2 4 0 (s 579)) := by
  simp only [pm_goal_12, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_12_1286 (s : Store) :
    denoteGraph pm_goal_12 s 1286 = transposeAxes 1 2 (chunkPrimDimN 2 4 1 (s 579)) := by
  simp only [pm_goal_12, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_12_1287 (s : Store) :
    denoteGraph pm_goal_12 s 1287 = transposeAxes 1 2 (chunkPrimDimN 2 4 2 (s 579)) := by
  simp only [pm_goal_12, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_12_1288 (s : Store) :
    denoteGraph pm_goal_12 s 1288 = transposeAxes 1 2 (chunkPrimDimN 2 4 3 (s 579)) := by
  simp only [pm_goal_12, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 580 (node 13) ==========
theorem sm_frame_580_self (initSM : Store) :
    denoteGraph sm initSM 580 = denoteGraph sm_goal_12 (denoteGraph sm initSM) 580 := by
  rw [denote_sm_goal_12_580]
  rw [sm_val initSM 13 580 (by native_decide) (by native_decide)]
  rw [show sm.nodes[13]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [579], outs := [580], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 13 579 (by native_decide)]

-- ========== PM full: 1281-1284 (4 ChunkPrim, node 73-76) ==========
theorem pm_full_1281 (initPM : Store) :
    denoteGraph pm initPM 1281 = chunkPrimDimN 2 pm.numRanks 0 (denoteGraph pm initPM 579) := by
  rw [pm_val initPM 73 1281 (by native_decide) (by native_decide)]
  rw [show pm.nodes[73]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [579], outs := [1281], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 73 579 (by native_decide)]

theorem pm_full_1282 (initPM : Store) :
    denoteGraph pm initPM 1282 = chunkPrimDimN 2 pm.numRanks 1 (denoteGraph pm initPM 579) := by
  rw [pm_val initPM 74 1282 (by native_decide) (by native_decide)]
  rw [show pm.nodes[74]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [579], outs := [1282], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 74 579 (by native_decide)]

theorem pm_full_1283 (initPM : Store) :
    denoteGraph pm initPM 1283 = chunkPrimDimN 2 pm.numRanks 2 (denoteGraph pm initPM 579) := by
  rw [pm_val initPM 75 1283 (by native_decide) (by native_decide)]
  rw [show pm.nodes[75]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [579], outs := [1283], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 75 579 (by native_decide)]

theorem pm_full_1284 (initPM : Store) :
    denoteGraph pm initPM 1284 = chunkPrimDimN 2 pm.numRanks 3 (denoteGraph pm initPM 579) := by
  rw [pm_val initPM 76 1284 (by native_decide) (by native_decide)]
  rw [show pm.nodes[76]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [579], outs := [1284], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 76 579 (by native_decide)]

-- ========== PM full: 1285-1288 (4 FW_transpose, node 85-88) ==========
theorem pm_frame_1285_self (initPM : Store) :
    denoteGraph pm initPM 1285 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 0 (denoteGraph pm initPM 579)) := by
  rw [pm_val initPM 85 1285 (by native_decide) (by native_decide)]
  rw [show pm.nodes[85]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1281], outs := [1285], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 85 1281 (by native_decide)]
  rw [pm_full_1281]

theorem pm_frame_1286_self (initPM : Store) :
    denoteGraph pm initPM 1286 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 1 (denoteGraph pm initPM 579)) := by
  rw [pm_val initPM 86 1286 (by native_decide) (by native_decide)]
  rw [show pm.nodes[86]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1282], outs := [1286], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 86 1282 (by native_decide)]
  rw [pm_full_1282]

theorem pm_frame_1287_self (initPM : Store) :
    denoteGraph pm initPM 1287 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 2 (denoteGraph pm initPM 579)) := by
  rw [pm_val initPM 87 1287 (by native_decide) (by native_decide)]
  rw [show pm.nodes[87]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1283], outs := [1287], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 87 1283 (by native_decide)]
  rw [pm_full_1283]

theorem pm_frame_1288_self (initPM : Store) :
    denoteGraph pm initPM 1288 = transposeAxes 1 2 (chunkPrimDimN 2 pm.numRanks 3 (denoteGraph pm initPM 579)) := by
  rw [pm_val initPM 88 1288 (by native_decide) (by native_decide)]
  rw [show pm.nodes[88]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1284], outs := [1288], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 88 1284 (by native_decide)]
  rw [pm_full_1284]

-- ========== 总装 ==========
theorem goal_12_cut_to_full (h : goal_12_stmt_cut) : goal_12_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg7 := goal_7_intermediate initSM initPM hSM hPM hInit
  have hg11 := goal_11_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg7 hg11 hg257 hg263 hinitC
  have hnr : pm_goal_12.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_12.numRanks goal_12_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_12_cut_initGoals, goal_12_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg7
      · exact hg11
      · exact hg257
      · exact hg263
  -- shape: 579 = goal_11.ts/tps (single), shape [1,8,4,8]
  have h579_smsh : (Ssm 579).shape = [1, 8, 4, 8] := by
    have h := hg11.1; simp only [goal_11] at h; exact h
  have h579_pmsh : (Spm 579).shape = [1, 8, 4, 8] := by
    have h := hg11.2.1; simp only [goal_11, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM12 : StoreShapesHold Ssm sm_goal_12InitEnv := by
    intro tid sh hsh
    rw [sm_goal_12InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_12InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h579_smsh
  have hPM12 : StoreShapesHold Spm pm_goal_12InitEnv := by
    intro tid sh hsh
    rw [pm_goal_12InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_12InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h579_pmsh
  have hcut := h Ssm Spm hSM12 hPM12 hInitCut
  -- Frame: 580 (sm), 1285-1288 (pm)
  have hsmf : Ssm 580 = denoteGraph sm_goal_12 Ssm 580 := by
    rw [hSsm]; exact sm_frame_580_self initSM
  have hpm1285 : Spm 1285 = denoteGraph pm_goal_12 Spm 1285 := by
    rw [denote_pm_goal_12_1285]
    rw [hSpm]
    have := pm_frame_1285_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1286 : Spm 1286 = denoteGraph pm_goal_12 Spm 1286 := by
    rw [denote_pm_goal_12_1286]
    rw [hSpm]
    have := pm_frame_1286_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1287 : Spm 1287 = denoteGraph pm_goal_12 Spm 1287 := by
    rw [denote_pm_goal_12_1287]
    rw [hSpm]
    have := pm_frame_1287_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1288 : Spm 1288 = denoteGraph pm_goal_12 Spm 1288 := by
    rw [denote_pm_goal_12_1288]
    rw [hSpm]
    have := pm_frame_1288_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_12, List.map] at hcut ⊢
  rw [hsmf, hpm1285, hpm1286, hpm1287, hpm1288]
  exact hcut

theorem goal_12_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_12 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_12_stmt := goal_12_cut_to_full prove_goal_12_cut
  exact hfull initSM initPM hSM hPM hInit


end TrainVerify.Denote.GeneratedGoals
