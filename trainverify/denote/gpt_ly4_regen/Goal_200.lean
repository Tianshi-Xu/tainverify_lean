/- Goal_200 proof. The per-node lemmas live in Goal_200_<name>.lean; see the note
   in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_200_hbw0
import denote.gpt_ly4_regen.Goal_200_hbw1
import denote.gpt_ly4_regen.Goal_200_hbw2
import denote.gpt_ly4_regen.Goal_200_hbw3
import denote.gpt_ly4_regen.Goal_200_hpm0base
import denote.gpt_ly4_regen.Goal_200_hpm1base
import denote.gpt_ly4_regen.Goal_200_hpm2base
import denote.gpt_ly4_regen.Goal_200_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prove_goal_200_cut : goal_200_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- goal_201: tensor 831 (= g) is the dim-1 gather of shards 2519/2522/2525/2528
  have hInit831 : InitGoalHolds pm_goal_200.numRanks goal_201 initSM initPM := by
    apply hInitGoals
    simp only [goal_200_cut_initGoals, goal_200_prereqs]
    decide
  have h831_shape : (initSM 831).shape = [1, 4, 8, 8] := hInit831.1
  have hs831 := hInit831.2.1
  simp only [goal_201, List.map, List.cons.injEq, and_true] at hs831
  obtain ⟨h2519_shape, h2522_shape, h2525_shape, h2528_shape⟩ := hs831
  have h831_gather : initSM 831 = allGatherPrimDimN 1 4 0
      [initPM 2519, initPM 2522, initPM 2525, initPM 2528] := by
    have hrec := hInit831.2.2
    simp only [goal_201, pm_goal_200, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _ (by rw [h2519_shape]; decide)
  -- goal_64: tensor 652 (= y) is the dim-2 gather of shards 2393/2394/2395/2396
  have hInit652 : InitGoalHolds pm_goal_200.numRanks goal_64 initSM initPM := by
    apply hInitGoals
    simp only [goal_200_cut_initGoals, goal_200_prereqs]
    decide
  have h652_shape : (initSM 652).shape = [1, 4, 8, 8] := hInit652.1
  have hs652 := hInit652.2.1
  simp only [goal_64, List.map, List.cons.injEq, and_true] at hs652
  obtain ⟨h2393_shape, h2394_shape, h2395_shape, h2396_shape⟩ := hs652
  have h652_gather : initSM 652 = allGatherPrimDimN 2 4 0
      [initPM 2393, initPM 2394, initPM 2395, initPM 2396] := by
    have hrec := hInit652.2.2
    simp only [goal_64, pm_goal_200, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [h2393_shape]; decide)
  -- Relate the g-shards to dim-1 chunks of 831
  have hg_chunk0 : chunkPrimDimN 1 4 0 (initSM 831) = initPM 2519 := by
    rw [h831_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h2519_shape h2522_shape h2525_shape h2528_shape 0 (by omega)
  have hg_chunk1 : chunkPrimDimN 1 4 1 (initSM 831) = initPM 2522 := by
    rw [h831_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h2519_shape h2522_shape h2525_shape h2528_shape 1 (by omega)
  have hg_chunk2 : chunkPrimDimN 1 4 2 (initSM 831) = initPM 2525 := by
    rw [h831_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h2519_shape h2522_shape h2525_shape h2528_shape 2 (by omega)
  have hg_chunk3 : chunkPrimDimN 1 4 3 (initSM 831) = initPM 2528 := by
    rw [h831_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h2519_shape h2522_shape h2525_shape h2528_shape 3 (by omega)
  -- The AllToAll of y-shards (dims 2→1) is the dim-1 chunk of 652
  have hy_chunk0 : allToAllPrimWithDims 4 0 [initPM 2393, initPM 2394, initPM 2395, initPM 2396] 2 1 =
      chunkPrimDimN 1 4 0 (initSM 652) := by
    simp only [allToAllPrimWithDims]; rw [← h652_gather]
  have hy_chunk1 : allToAllPrimWithDims 4 1 [initPM 2393, initPM 2394, initPM 2395, initPM 2396] 2 1 =
      chunkPrimDimN 1 4 1 (initSM 652) := by
    simp only [allToAllPrimWithDims]; rw [← h652_gather]
  have hy_chunk2 : allToAllPrimWithDims 4 2 [initPM 2393, initPM 2394, initPM 2395, initPM 2396] 2 1 =
      chunkPrimDimN 1 4 2 (initSM 652) := by
    simp only [allToAllPrimWithDims]; rw [← h652_gather]
  have hy_chunk3 : allToAllPrimWithDims 4 3 [initPM 2393, initPM 2394, initPM 2395, initPM 2396] 2 1 =
      chunkPrimDimN 1 4 3 (initSM 652) := by
    simp only [allToAllPrimWithDims]; rw [← h652_gather]
  -- SM store: 830 = dX = batchedMatmul g (transpose2d y)
  have hsm : (denoteGraph sm_goal_200 initSM) 830 =
      batchedMatmul (initSM 831) (transpose2d (initSM 652)) := by
    simp only [sm_goal_200, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_matmul_fst_out _ _ 0 831 656 652 830 826 (by decide), bw_matmul_fst_eq]
  -- PM BW_matmul .1 outputs, in terms of init shards
  have hbw0 := hbw0_200 initPM
  have hbw1 := hbw1_200 initPM
  have hbw2 := hbw2_200 initPM
  have hbw3 := hbw3_200 initPM
  -- Rewrite BW outputs as batchedMatmul of dim-1 chunks of 831 and 652
  have hbw0' : (denoteGraph pm_goal_200 initPM) 2517 =
      batchedMatmul (chunkPrimDimN 1 4 0 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 0 (initSM 652))) := by
    rw [hbw0, hy_chunk0, ← hg_chunk0]
  have hbw1' : (denoteGraph pm_goal_200 initPM) 2520 =
      batchedMatmul (chunkPrimDimN 1 4 1 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 1 (initSM 652))) := by
    rw [hbw1, hy_chunk1, ← hg_chunk1]
  have hbw2' : (denoteGraph pm_goal_200 initPM) 2523 =
      batchedMatmul (chunkPrimDimN 1 4 2 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 2 (initSM 652))) := by
    rw [hbw2, hy_chunk2, ← hg_chunk2]
  have hbw3' : (denoteGraph pm_goal_200 initPM) 2526 =
      batchedMatmul (chunkPrimDimN 1 4 3 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 3 (initSM 652))) := by
    rw [hbw3, hy_chunk3, ← hg_chunk3]
  -- Final AllToAll: gather BW outputs on dim 1, rechunk on dim 2
  have hpm0base := hpm0base_200 initPM
  have hpm1base := hpm1base_200 initPM
  have hpm2base := hpm2base_200 initPM
  have hpm3base := hpm3base_200 initPM
  -- Main distribution: batchedMatmul g yᵀ = gather_dim1 of the per-shard products
  have hVsplit : batchedMatmul (initSM 831) (transpose2d (initSM 652)) =
      allGatherPrimDimN 1 4 0
        [batchedMatmul (chunkPrimDimN 1 4 0 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 0 (initSM 652))),
         batchedMatmul (chunkPrimDimN 1 4 1 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 1 (initSM 652))),
         batchedMatmul (chunkPrimDimN 1 4 2 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 2 (initSM 652))),
         batchedMatmul (chunkPrimDimN 1 4 3 (initSM 831)) (transpose2d (chunkPrimDimN 1 4 3 (initSM 652)))] :=
    bw_matmul_fst_split_dim1_4_1_4_8_8 (initSM 831) (initSM 652) h831_shape h652_shape
  have hpm0' : (denoteGraph pm_goal_200 initPM) 2493 =
      chunkPrimDimN 2 4 0 (batchedMatmul (initSM 831) (transpose2d (initSM 652))) := by
    rw [hpm0base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  have hpm1' : (denoteGraph pm_goal_200 initPM) 2494 =
      chunkPrimDimN 2 4 1 (batchedMatmul (initSM 831) (transpose2d (initSM 652))) := by
    rw [hpm1base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  have hpm2' : (denoteGraph pm_goal_200 initPM) 2495 =
      chunkPrimDimN 2 4 2 (batchedMatmul (initSM 831) (transpose2d (initSM 652))) := by
    rw [hpm2base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  have hpm3' : (denoteGraph pm_goal_200 initPM) 2496 =
      chunkPrimDimN 2 4 3 (batchedMatmul (initSM 831) (transpose2d (initSM 652))) := by
    rw [hpm3base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  -- Shapes
  have hV_shape : (batchedMatmul (initSM 831) (transpose2d (initSM 652))).shape = [1, 4, 8, 8] :=
    fw_matmul_shape_1_4_8_8 _ _ h831_shape (transpose2d_shape_1_4_8_8 _ h652_shape)
  have hchunkV : ∀ r, r < 4 →
      (chunkPrimDimN 2 4 r (batchedMatmul (initSM 831) (transpose2d (initSM 652)))).shape = [1, 4, 2, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ hV_shape (by omega)]
    simp [List.set, List.getD]
  -- Discharge the three conjuncts
  simp only [goal_200, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes,
    LineageGoal.gatherDim, List.map, Piece.tid]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]; exact hV_shape
  · rw [hpm0', hpm1', hpm2', hpm3',
        hchunkV 0 (by omega), hchunkV 1 (by omega), hchunkV 2 (by omega), hchunkV 3 (by omega)]
  · rw [hsm]
    symm
    rw [hpm0', hpm1', hpm2', hpm3']
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    simp only [reconstructWithDim_cons_cons_nonscalar (h := by rw [hchunkV 0 (by omega)]; decide)]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim2_4_8_8 _ hV_shape

end TrainVerify.Denote.GeneratedGoals
