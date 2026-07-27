/- Goal_157 proof. The per-node lemmas live in Goal_157_<name>.lean; see the note
   in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_157_hbw0
import denote.gpt_ly4_regen.Goal_157_hbw1
import denote.gpt_ly4_regen.Goal_157_hbw2
import denote.gpt_ly4_regen.Goal_157_hbw3
import denote.gpt_ly4_regen.Goal_157_hpm0base
import denote.gpt_ly4_regen.Goal_157_hpm1base
import denote.gpt_ly4_regen.Goal_157_hpm2base
import denote.gpt_ly4_regen.Goal_157_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prove_goal_157_cut : goal_157_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- goal_163: tensor 786 (= g) is the dim-1 gather of shards 1895/1898/1901/1904
  have hInit786 : InitGoalHolds pm_goal_157.numRanks goal_163 initSM initPM := by
    apply hInitGoals
    simp only [goal_157_cut_initGoals, goal_157_prereqs]
    decide
  have h786_shape : (initSM 786).shape = [1, 4, 8, 8] := hInit786.1
  have hs786 := hInit786.2.1
  simp only [goal_163, List.map, List.cons.injEq, and_true] at hs786
  obtain ⟨h1895_shape, h1898_shape, h1901_shape, h1904_shape⟩ := hs786
  have h786_gather : initSM 786 = allGatherPrimDimN 1 4 0
      [initPM 1895, initPM 1898, initPM 1901, initPM 1904] := by
    have hrec := hInit786.2.2
    simp only [goal_163, pm_goal_157, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _ (by rw [h1895_shape]; decide)
  -- goal_40: tensor 618 (= y) is the dim-3 gather of shards 1853/1854/1855/1856
  have hInit618 : InitGoalHolds pm_goal_157.numRanks goal_40 initSM initPM := by
    apply hInitGoals
    simp only [goal_157_cut_initGoals, goal_157_prereqs]
    decide
  have h618_shape : (initSM 618).shape = [1, 4, 8, 8] := hInit618.1
  have hs618 := hInit618.2.1
  simp only [goal_40, List.map, List.cons.injEq, and_true] at hs618
  obtain ⟨h1853_shape, h1854_shape, h1855_shape, h1856_shape⟩ := hs618
  have h618_gather : initSM 618 = allGatherPrimDimN 3 4 0
      [initPM 1853, initPM 1854, initPM 1855, initPM 1856] := by
    have hrec := hInit618.2.2
    simp only [goal_40, pm_goal_157, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 3 4 0 _ _ _ (by rw [h1853_shape]; decide)
  -- Relate the g-shards to dim-1 chunks of 786
  have hg_chunk0 : chunkPrimDimN 1 4 0 (initSM 786) = initPM 1895 := by
    rw [h786_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h1895_shape h1898_shape h1901_shape h1904_shape 0 (by omega)
  have hg_chunk1 : chunkPrimDimN 1 4 1 (initSM 786) = initPM 1898 := by
    rw [h786_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h1895_shape h1898_shape h1901_shape h1904_shape 1 (by omega)
  have hg_chunk2 : chunkPrimDimN 1 4 2 (initSM 786) = initPM 1901 := by
    rw [h786_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h1895_shape h1898_shape h1901_shape h1904_shape 2 (by omega)
  have hg_chunk3 : chunkPrimDimN 1 4 3 (initSM 786) = initPM 1904 := by
    rw [h786_gather]
    simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h1895_shape h1898_shape h1901_shape h1904_shape 3 (by omega)
  -- The AllToAll of y-shards (dims 3→1) is the dim-1 chunk of 618
  have hy_chunk0 : allToAllPrimWithDims 4 0 [initPM 1853, initPM 1854, initPM 1855, initPM 1856] 3 1 =
      chunkPrimDimN 1 4 0 (initSM 618) := by
    simp only [allToAllPrimWithDims]; rw [← h618_gather]
  have hy_chunk1 : allToAllPrimWithDims 4 1 [initPM 1853, initPM 1854, initPM 1855, initPM 1856] 3 1 =
      chunkPrimDimN 1 4 1 (initSM 618) := by
    simp only [allToAllPrimWithDims]; rw [← h618_gather]
  have hy_chunk2 : allToAllPrimWithDims 4 2 [initPM 1853, initPM 1854, initPM 1855, initPM 1856] 3 1 =
      chunkPrimDimN 1 4 2 (initSM 618) := by
    simp only [allToAllPrimWithDims]; rw [← h618_gather]
  have hy_chunk3 : allToAllPrimWithDims 4 3 [initPM 1853, initPM 1854, initPM 1855, initPM 1856] 3 1 =
      chunkPrimDimN 1 4 3 (initSM 618) := by
    simp only [allToAllPrimWithDims]; rw [← h618_gather]
  -- SM store: 780 = dX = batchedMatmul g (transpose2d y)
  have hsm : (denoteGraph sm_goal_157 initSM) 780 =
      batchedMatmul (initSM 786) (transpose2d (initSM 618)) := by
    simp only [sm_goal_157, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_matmul_fst_out _ _ 0 786 613 618 780 785 (by decide), bw_matmul_fst_eq]
  -- PM BW_matmul .1 outputs, in terms of init shards
  have hbw0 := hbw0_157 initPM
  have hbw1 := hbw1_157 initPM
  have hbw2 := hbw2_157 initPM
  have hbw3 := hbw3_157 initPM
  -- Rewrite BW outputs as batchedMatmul of dim-1 chunks of 786 and 618
  have hbw0' : (denoteGraph pm_goal_157 initPM) 1893 =
      batchedMatmul (chunkPrimDimN 1 4 0 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 0 (initSM 618))) := by
    rw [hbw0, hy_chunk0, ← hg_chunk0]
  have hbw1' : (denoteGraph pm_goal_157 initPM) 1896 =
      batchedMatmul (chunkPrimDimN 1 4 1 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 1 (initSM 618))) := by
    rw [hbw1, hy_chunk1, ← hg_chunk1]
  have hbw2' : (denoteGraph pm_goal_157 initPM) 1899 =
      batchedMatmul (chunkPrimDimN 1 4 2 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 2 (initSM 618))) := by
    rw [hbw2, hy_chunk2, ← hg_chunk2]
  have hbw3' : (denoteGraph pm_goal_157 initPM) 1902 =
      batchedMatmul (chunkPrimDimN 1 4 3 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 3 (initSM 618))) := by
    rw [hbw3, hy_chunk3, ← hg_chunk3]
  -- Final AllToAll: gather BW outputs on dim 1, rechunk on dim 2
  have hpm0base := hpm0base_157 initPM
  have hpm1base := hpm1base_157 initPM
  have hpm2base := hpm2base_157 initPM
  have hpm3base := hpm3base_157 initPM
  -- Main distribution: batchedMatmul g yᵀ = gather_dim1 of the per-shard products
  have hVsplit : batchedMatmul (initSM 786) (transpose2d (initSM 618)) =
      allGatherPrimDimN 1 4 0
        [batchedMatmul (chunkPrimDimN 1 4 0 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 0 (initSM 618))),
         batchedMatmul (chunkPrimDimN 1 4 1 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 1 (initSM 618))),
         batchedMatmul (chunkPrimDimN 1 4 2 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 2 (initSM 618))),
         batchedMatmul (chunkPrimDimN 1 4 3 (initSM 786)) (transpose2d (chunkPrimDimN 1 4 3 (initSM 618)))] :=
    bw_matmul_fst_split_dim1_4_1_4_8_8 (initSM 786) (initSM 618) h786_shape h618_shape
  have hpm0' : (denoteGraph pm_goal_157 initPM) 1794 =
      chunkPrimDimN 2 4 0 (batchedMatmul (initSM 786) (transpose2d (initSM 618))) := by
    rw [hpm0base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  have hpm1' : (denoteGraph pm_goal_157 initPM) 1796 =
      chunkPrimDimN 2 4 1 (batchedMatmul (initSM 786) (transpose2d (initSM 618))) := by
    rw [hpm1base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  have hpm2' : (denoteGraph pm_goal_157 initPM) 1798 =
      chunkPrimDimN 2 4 2 (batchedMatmul (initSM 786) (transpose2d (initSM 618))) := by
    rw [hpm2base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  have hpm3' : (denoteGraph pm_goal_157 initPM) 1800 =
      chunkPrimDimN 2 4 3 (batchedMatmul (initSM 786) (transpose2d (initSM 618))) := by
    rw [hpm3base, hbw0', hbw1', hbw2', hbw3']
    simp only [allToAllPrimWithDims]
    rw [← hVsplit]
  -- Shapes
  have hV_shape : (batchedMatmul (initSM 786) (transpose2d (initSM 618))).shape = [1, 4, 8, 8] :=
    fw_matmul_shape_1_4_8_8 _ _ h786_shape (transpose2d_shape_1_4_8_8 _ h618_shape)
  have hchunkV : ∀ r, r < 4 →
      (chunkPrimDimN 2 4 r (batchedMatmul (initSM 786) (transpose2d (initSM 618)))).shape = [1, 4, 2, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ hV_shape (by omega)]
    simp [List.set, List.getD]
  -- Discharge the three conjuncts
  simp only [goal_157, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes,
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
