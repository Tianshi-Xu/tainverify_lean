/- goal_10 桥 (prereqs=[2,3,4,5,6,9,257,261])。SM=FW_transpose(577,p=[1,2])→578;
   PM=4×ChunkPrim(577,dim=3)→1257-1260, 然后 4×FW_transpose(1257..,p=[1,2])→1261-1264. tps=4个.
   577=goal_9 输出。第 9 种结构: ChunkPrim+FW_transpose, multi-tps, gather distributes over transpose. -/
import denote.gpt_ly4_regen.Goal9Bridge
import denote.gpt_ly4_regen.Goal_10

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_10 算 578 ==========
theorem denote_sm_goal_10_578 (s : Store) :
    denoteGraph sm_goal_10 s 578 = transposeAxes 1 2 (s 577) := by
  simp only [sm_goal_10, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_10 算 1261-1264 ==========
theorem denote_pm_goal_10_1261 (s : Store) :
    denoteGraph pm_goal_10 s 1261 = transposeAxes 1 2 (chunkPrimDimN 3 4 0 (s 577)) := by
  simp only [pm_goal_10, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_10_1262 (s : Store) :
    denoteGraph pm_goal_10 s 1262 = transposeAxes 1 2 (chunkPrimDimN 3 4 1 (s 577)) := by
  simp only [pm_goal_10, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_10_1263 (s : Store) :
    denoteGraph pm_goal_10 s 1263 = transposeAxes 1 2 (chunkPrimDimN 3 4 2 (s 577)) := by
  simp only [pm_goal_10, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_10_1264 (s : Store) :
    denoteGraph pm_goal_10 s 1264 = transposeAxes 1 2 (chunkPrimDimN 3 4 3 (s 577)) := by
  simp only [pm_goal_10, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 578 (node 12) ==========
theorem sm_frame_578_self (initSM : Store) :
    denoteGraph sm initSM 578 = denoteGraph sm_goal_10 (denoteGraph sm initSM) 578 := by
  rw [denote_sm_goal_10_578]
  rw [sm_val initSM 12 578 (by native_decide) (by native_decide)]
  rw [show sm.nodes[12]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [577], outs := [578], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 12 577 (by native_decide)]

-- ========== PM full: 1257-1260 (4 ChunkPrim, node 69-72) ==========
theorem pm_full_1257 (initPM : Store) :
    denoteGraph pm initPM 1257 = chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 577) := by
  rw [pm_val initPM 69 1257 (by native_decide) (by native_decide)]
  rw [show pm.nodes[69]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [577], outs := [1257], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 69 577 (by native_decide)]

theorem pm_full_1258 (initPM : Store) :
    denoteGraph pm initPM 1258 = chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 577) := by
  rw [pm_val initPM 70 1258 (by native_decide) (by native_decide)]
  rw [show pm.nodes[70]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [577], outs := [1258], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 70 577 (by native_decide)]

theorem pm_full_1259 (initPM : Store) :
    denoteGraph pm initPM 1259 = chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 577) := by
  rw [pm_val initPM 71 1259 (by native_decide) (by native_decide)]
  rw [show pm.nodes[71]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [577], outs := [1259], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 71 577 (by native_decide)]

theorem pm_full_1260 (initPM : Store) :
    denoteGraph pm initPM 1260 = chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 577) := by
  rw [pm_val initPM 72 1260 (by native_decide) (by native_decide)]
  rw [show pm.nodes[72]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [577], outs := [1260], params := [3] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 72 577 (by native_decide)]

-- ========== PM full: 1261-1264 (4 FW_transpose, node 81-84) ==========
theorem pm_frame_1261_self (initPM : Store) :
    denoteGraph pm initPM 1261 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 0 (denoteGraph pm initPM 577)) := by
  rw [pm_val initPM 81 1261 (by native_decide) (by native_decide)]
  rw [show pm.nodes[81]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1257], outs := [1261], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 81 1257 (by native_decide)]
  rw [pm_full_1257]

theorem pm_frame_1262_self (initPM : Store) :
    denoteGraph pm initPM 1262 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 1 (denoteGraph pm initPM 577)) := by
  rw [pm_val initPM 82 1262 (by native_decide) (by native_decide)]
  rw [show pm.nodes[82]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1258], outs := [1262], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 82 1258 (by native_decide)]
  rw [pm_full_1258]

theorem pm_frame_1263_self (initPM : Store) :
    denoteGraph pm initPM 1263 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 2 (denoteGraph pm initPM 577)) := by
  rw [pm_val initPM 83 1263 (by native_decide) (by native_decide)]
  rw [show pm.nodes[83]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1259], outs := [1263], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 83 1259 (by native_decide)]
  rw [pm_full_1259]

theorem pm_frame_1264_self (initPM : Store) :
    denoteGraph pm initPM 1264 = transposeAxes 1 2 (chunkPrimDimN 3 pm.numRanks 3 (denoteGraph pm initPM 577)) := by
  rw [pm_val initPM 84 1264 (by native_decide) (by native_decide)]
  rw [show pm.nodes[84]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1260], outs := [1264], params := [1, 2] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 84 1260 (by native_decide)]
  rw [pm_full_1260]

-- ========== 总装 ==========
theorem goal_10_cut_to_full (h : goal_10_stmt_cut) : goal_10_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg6 := goal_6_intermediate initSM initPM hSM hPM hInit
  have hg9 := goal_9_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_10.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_10.numRanks goal_10_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_10_cut_initGoals, goal_10_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg6
      · exact hg9
      · exact hg257
      · exact hg261
  -- shape: 577 = goal_9.ts/tps (single), shape [1,8,4,8]
  have h577_smsh : (Ssm 577).shape = [1, 8, 4, 8] := by
    have h := hg9.1; simp only [goal_9] at h; exact h
  have h577_pmsh : (Spm 577).shape = [1, 8, 4, 8] := by
    have h := hg9.2.1; simp only [goal_9, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM10 : StoreShapesHold Ssm sm_goal_10InitEnv := by
    intro tid sh hsh
    rw [sm_goal_10InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_10InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h577_smsh
  have hPM10 : StoreShapesHold Spm pm_goal_10InitEnv := by
    intro tid sh hsh
    rw [pm_goal_10InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_10InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h577_pmsh
  have hcut := h Ssm Spm hSM10 hPM10 hInitCut
  -- Frame: 578 (sm), 1261-1264 (pm)
  have hsmf : Ssm 578 = denoteGraph sm_goal_10 Ssm 578 := by
    rw [hSsm]; exact sm_frame_578_self initSM
  have hpm1261 : Spm 1261 = denoteGraph pm_goal_10 Spm 1261 := by
    rw [denote_pm_goal_10_1261]
    rw [hSpm]
    have := pm_frame_1261_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1262 : Spm 1262 = denoteGraph pm_goal_10 Spm 1262 := by
    rw [denote_pm_goal_10_1262]
    rw [hSpm]
    have := pm_frame_1262_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1263 : Spm 1263 = denoteGraph pm_goal_10 Spm 1263 := by
    rw [denote_pm_goal_10_1263]
    rw [hSpm]
    have := pm_frame_1263_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1264 : Spm 1264 = denoteGraph pm_goal_10 Spm 1264 := by
    rw [denote_pm_goal_10_1264]
    rw [hSpm]
    have := pm_frame_1264_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_10, List.map] at hcut ⊢
  rw [hsmf, hpm1261, hpm1262, hpm1263, hpm1264]
  exact hcut

end TrainVerify.Denote.GeneratedGoals
