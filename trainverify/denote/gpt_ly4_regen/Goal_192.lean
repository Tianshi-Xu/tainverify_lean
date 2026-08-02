/- Goal_192 proof. The per-node lemmas live in Goal_192_<name>.lean; see the note
   in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_192_hbw0
import denote.gpt_ly4_regen.Goal_192_hbw1
import denote.gpt_ly4_regen.Goal_192_hbw2
import denote.gpt_ly4_regen.Goal_192_hbw3
import denote.gpt_ly4_regen.Goal_192_hpm0base
import denote.gpt_ly4_regen.Goal_192_hpm1base
import denote.gpt_ly4_regen.Goal_192_hpm2base
import denote.gpt_ly4_regen.Goal_192_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prove_goal_192_cut : goal_192_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- goal_198: tensor 828 (= g) is the dim-2 gather of shards 2455/2458/2461/2464
  have hInit828 : InitGoalHolds pm_goal_192.numRanks goal_198 initSM initPM := by
    apply hInitGoals
    simp only [goal_192_cut_initGoals, goal_192_prereqs]
    decide
  have h828_shape : (initSM 828).shape = [1, 4, 8, 8] := hInit828.1
  have hs828 := hInit828.2.1
  simp only [goal_198, List.map, List.cons.injEq, and_true] at hs828
  obtain ⟨h2455_shape, h2458_shape, h2461_shape, h2464_shape⟩ := hs828
  have h828_gather : initSM 828 = allGatherPrimDimN 2 4 0
      [initPM 2455, initPM 2458, initPM 2461, initPM 2464] := by
    have hrec := hInit828.2.2
    simp only [goal_198, pm_goal_192, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [h2455_shape]; decide)
  -- goal_65: tensor 653 (= y) is replicated (singleton)
  have hInit653 : InitGoalHolds pm_goal_192.numRanks goal_65 initSM initPM := by
    apply hInitGoals
    simp only [goal_192_cut_initGoals, goal_192_prereqs]
    decide
  have h653_eq : initSM 653 = initPM 653 := by
    have hrec := hInit653.2.2
    simp only [goal_65, pm_goal_192, List.map] at hrec
    rw [hrec]; rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]; exact reconstructWithDim_singleton _ _ _ _
  have hs653 := hInit653.2.1
  simp only [goal_65, List.map, List.cons.injEq, and_true] at hs653
  have h653_shape : (initPM 653).shape = [1, 4, 8, 8] := hs653
  -- chunk-to-shard roundtrip for the dim-2 shards of 828
  have hg_chunk0 : chunkPrimDimN 2 4 0 (initSM 828) = initPM 2455 := by
    rw [h828_gather]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _
      h2455_shape h2458_shape h2461_shape h2464_shape 0 (by omega)
  have hg_chunk1 : chunkPrimDimN 2 4 1 (initSM 828) = initPM 2458 := by
    rw [h828_gather]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _
      h2455_shape h2458_shape h2461_shape h2464_shape 1 (by omega)
  have hg_chunk2 : chunkPrimDimN 2 4 2 (initSM 828) = initPM 2461 := by
    rw [h828_gather]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _
      h2455_shape h2458_shape h2461_shape h2464_shape 2 (by omega)
  have hg_chunk3 : chunkPrimDimN 2 4 3 (initSM 828) = initPM 2464 := by
    rw [h828_gather]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _
      h2455_shape h2458_shape h2461_shape h2464_shape 3 (by omega)
  -- transpose shapes
  have htY_shape : (transpose2d (initSM 653)).shape = [1, 4, 8, 8] := by
    rw [h653_eq]; exact transpose2d_shape_1_4_8_8 _ h653_shape
  -- SM store: 822 = dX = batchedMatmul g (transpose2d y)
  have hsm : (denoteGraph sm_goal_192 initSM) 822 =
      batchedMatmul (initSM 828) (transpose2d (initSM 653)) := by
    simp only [sm_goal_192, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_matmul_fst_out _ _ 0 828 648 653 822 827 (by decide), bw_matmul_fst_eq]
  -- PM BW_matmul .1 outputs (per-rank dX shards), in terms of init shards
  have hbw0 := hbw0_192 initPM
  have hbw1 := hbw1_192 initPM
  have hbw2 := hbw2_192 initPM
  have hbw3 := hbw3_192 initPM
  -- PM final shards (last AllToAll output per rank), in terms of the dX shards
  have hpm0base := hpm0base_192 initPM
  have hpm1base := hpm1base_192 initPM
  have hpm2base := hpm2base_192 initPM
  have hpm3base := hpm3base_192 initPM
  -- Main distribution: batchedMatmul g (transpose2d y) = dim-2 gather of the per-rank shards
  have hVsplit : batchedMatmul (initSM 828) (transpose2d (initSM 653)) =
      allGatherPrimDimN 2 4 0
        [batchedMatmul (initPM 2455) (transpose2d (initSM 653)),
         batchedMatmul (initPM 2458) (transpose2d (initSM 653)),
         batchedMatmul (initPM 2461) (transpose2d (initSM 653)),
         batchedMatmul (initPM 2464) (transpose2d (initSM 653))] := by
    have hsplit := fw_matmul_split_dim2_first_1_4_8_8_g192 (initSM 828) (transpose2d (initSM 653))
      h828_shape htY_shape
    rw [hg_chunk0, hg_chunk1, hg_chunk2, hg_chunk3] at hsplit
    exact hsplit
  -- the dim-2 gather of dX shards equals the SM dX
  have hZeq : allGatherPrimDimN 2 4 0
      [(denoteGraph pm_goal_192 initPM) 2453, (denoteGraph pm_goal_192 initPM) 2456,
       (denoteGraph pm_goal_192 initPM) 2459, (denoteGraph pm_goal_192 initPM) 2462]
      = batchedMatmul (initSM 828) (transpose2d (initSM 653)) := by
    rw [hbw0, hbw1, hbw2, hbw3, ← h653_eq, hVsplit]
  -- dX value and shape
  have hV_shape : (batchedMatmul (initSM 828) (transpose2d (initSM 653))).shape = [1, 4, 8, 8] :=
    batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ h828_shape htY_shape
  -- final shards are dim-1 chunks of dX
  have hpm0' : (denoteGraph pm_goal_192 initPM) 2358 =
      chunkPrimDimN 1 4 0 (batchedMatmul (initSM 828) (transpose2d (initSM 653))) := by
    rw [hpm0base]; simp only [allToAllPrimWithDims]; rw [hZeq]
  have hpm1' : (denoteGraph pm_goal_192 initPM) 2360 =
      chunkPrimDimN 1 4 1 (batchedMatmul (initSM 828) (transpose2d (initSM 653))) := by
    rw [hpm1base]; simp only [allToAllPrimWithDims]; rw [hZeq]
  have hpm2' : (denoteGraph pm_goal_192 initPM) 2362 =
      chunkPrimDimN 1 4 2 (batchedMatmul (initSM 828) (transpose2d (initSM 653))) := by
    rw [hpm2base]; simp only [allToAllPrimWithDims]; rw [hZeq]
  have hpm3' : (denoteGraph pm_goal_192 initPM) 2364 =
      chunkPrimDimN 1 4 3 (batchedMatmul (initSM 828) (transpose2d (initSM 653))) := by
    rw [hpm3base]; simp only [allToAllPrimWithDims]; rw [hZeq]
  have hchunkV : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r (batchedMatmul (initSM 828) (transpose2d (initSM 653)))).shape =
        [1, 1, 8, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 1 4 r _ _ hV_shape (by omega)]
    simp [List.set, List.getD]
  -- Discharge the three conjuncts
  simp only [goal_192, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes,
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
    exact allGatherPrimDimN_chunkPrimDimN_id_dim1_4_8_8 _ hV_shape

end TrainVerify.Denote.GeneratedGoals
