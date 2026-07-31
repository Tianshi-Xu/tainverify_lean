/- Goal_124 proof. The eight per-node lemmas (`hbw0..3`, `hpm0base..3base`)
   live in Goal_124_<name>.lean: under Lean v4.31 the kernel accumulates
   def-eq state across successive `simp only [pm_goal_124, denoteGraph, ...]`
   calls within one file (~3.5 GB/min, non-converging; measured 57 GB RSS and
   still climbing at 17 min). One module each gives them a fresh process.
   The proof body is otherwise the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_124_hbw0
import denote.gpt_ly4_regen.Goal_124_hbw1
import denote.gpt_ly4_regen.Goal_124_hbw2
import denote.gpt_ly4_regen.Goal_124_hbw3
import denote.gpt_ly4_regen.Goal_124_hpm0base
import denote.gpt_ly4_regen.Goal_124_hpm1base
import denote.gpt_ly4_regen.Goal_124_hpm2base
import denote.gpt_ly4_regen.Goal_124_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxHeartbeats 4000000 in
theorem prove_goal_124_cut : goal_124_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  have hInit : InitGoalHolds pm_goal_124.numRanks goal_127 initSM initPM := by
    apply hInitGoals
    decide
  have hgrad_shape : (initSM 743).shape = [1, 4, 8, 8] := hInit.1
  have htp_shapes := hInit.2.1
  simp only [goal_127, LineageGoal.tps, List.map] at htp_shapes
  have hg0 : (initPM 1346).shape = [1, 4, 2, 8] := by
    have := congrArg (List.getD · 0 []) htp_shapes; simp at this; exact this
  have hg1 : (initPM 1348).shape = [1, 4, 2, 8] := by
    have := congrArg (List.getD · 1 []) htp_shapes; simp at this; exact this
  have hg2 : (initPM 1350).shape = [1, 4, 2, 8] := by
    have := congrArg (List.getD · 2 []) htp_shapes; simp at this; exact this
  have hg3 : (initPM 1352).shape = [1, 4, 2, 8] := by
    have := congrArg (List.getD · 3 []) htp_shapes; simp at this; exact this
  have hrec_ag : initSM 743 = allGatherPrimDimN 2 4 0 [initPM 1346, initPM 1348, initPM 1350, initPM 1352] := by
    have hrec := hInit.2.2
    simp only [goal_127, LineageGoal.tps, LineageGoal.gatherDim, List.map] at hrec
    rw [hrec]
    exact reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [hg0]; decide)
  have hsm : (denoteGraph sm_goal_124 initSM) 740 = transposeAxes 2 3 (initSM 743) := by
    simp only [sm_goal_124, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_transposeAxes_out]
  have hbw0 := hbw0_124 initPM
  have hbw1 := hbw1_124 initPM
  have hbw2 := hbw2_124 initPM
  have hbw3 := hbw3_124 initPM
  have hpm0base := hpm0base_124 initPM
  have hpm1base := hpm1base_124 initPM
  have hpm2base := hpm2base_124 initPM
  have hpm3base := hpm3base_124 initPM
  have hpm0 : (denoteGraph pm_goal_124 initPM) 1298 =
      allToAllPrimWithDims 4 0 [transposeAxes 2 3 (initPM 1346), transposeAxes 2 3 (initPM 1348),
        transposeAxes 2 3 (initPM 1350), transposeAxes 2 3 (initPM 1352)] 3 1 := by
    rw [hpm0base]
    simp [hbw0, hbw1, hbw2, hbw3]
  have hpm1 : (denoteGraph pm_goal_124 initPM) 1300 =
      allToAllPrimWithDims 4 1 [transposeAxes 2 3 (initPM 1346), transposeAxes 2 3 (initPM 1348),
        transposeAxes 2 3 (initPM 1350), transposeAxes 2 3 (initPM 1352)] 3 1 := by
    rw [hpm1base]
    simp [hbw0, hbw1, hbw2, hbw3]
  have hpm2 : (denoteGraph pm_goal_124 initPM) 1302 =
      allToAllPrimWithDims 4 2 [transposeAxes 2 3 (initPM 1346), transposeAxes 2 3 (initPM 1348),
        transposeAxes 2 3 (initPM 1350), transposeAxes 2 3 (initPM 1352)] 3 1 := by
    rw [hpm2base]
    simp [hbw0, hbw1, hbw2, hbw3]
  have hpm3 : (denoteGraph pm_goal_124 initPM) 1304 =
      allToAllPrimWithDims 4 3 [transposeAxes 2 3 (initPM 1346), transposeAxes 2 3 (initPM 1348),
        transposeAxes 2 3 (initPM 1350), transposeAxes 2 3 (initPM 1352)] 3 1 := by
    rw [hpm3base]
    simp [hbw0, hbw1, hbw2, hbw3]
  have hchunk0 : chunkPrimDimN 2 4 0 (initSM 743) = initPM 1346 := by
    rw [hrec_ag]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _ hg0 hg1 hg2 hg3 0 (by omega)
  have hchunk1 : chunkPrimDimN 2 4 1 (initSM 743) = initPM 1348 := by
    rw [hrec_ag]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _ hg0 hg1 hg2 hg3 1 (by omega)
  have hchunk2 : chunkPrimDimN 2 4 2 (initSM 743) = initPM 1350 := by
    rw [hrec_ag]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _ hg0 hg1 hg2 hg3 2 (by omega)
  have hchunk3 : chunkPrimDimN 2 4 3 (initSM 743) = initPM 1352 := by
    rw [hrec_ag]
    simpa using chunk2_gather2_roundtrip_1_4_2_8 _ _ _ _ hg0 hg1 hg2 hg3 3 (by omega)
  have hbridge0 := fw_transpose23_split_dim2_4_1_4_8_8 (initSM 743) hgrad_shape
  have hbridge : transposeAxes 2 3 (initSM 743) = allGatherPrimDimN 3 4 0
      [transposeAxes 2 3 (initPM 1346), transposeAxes 2 3 (initPM 1348),
       transposeAxes 2 3 (initPM 1350), transposeAxes 2 3 (initPM 1352)] := by
    simpa [hchunk0, hchunk1, hchunk2, hchunk3] using hbridge0
  have halltoall : ∀ r, r < 4 →
      allToAllPrimWithDims 4 r [transposeAxes 2 3 (initPM 1346), transposeAxes 2 3 (initPM 1348),
        transposeAxes 2 3 (initPM 1350), transposeAxes 2 3 (initPM 1352)] 3 1 =
      chunkPrimDimN 1 4 r (transposeAxes 2 3 (initSM 743)) := by
    intro r _
    simp only [allToAllPrimWithDims]
    rw [← hbridge]
  have hpm0' : (denoteGraph pm_goal_124 initPM) 1298 = chunkPrimDimN 1 4 0 (transposeAxes 2 3 (initSM 743)) := by rw [hpm0, halltoall 0 (by omega)]
  have hpm1' : (denoteGraph pm_goal_124 initPM) 1300 = chunkPrimDimN 1 4 1 (transposeAxes 2 3 (initSM 743)) := by rw [hpm1, halltoall 1 (by omega)]
  have hpm2' : (denoteGraph pm_goal_124 initPM) 1302 = chunkPrimDimN 1 4 2 (transposeAxes 2 3 (initSM 743)) := by rw [hpm2, halltoall 2 (by omega)]
  have hpm3' : (denoteGraph pm_goal_124 initPM) 1304 = chunkPrimDimN 1 4 3 (transposeAxes 2 3 (initSM 743)) := by rw [hpm3, halltoall 3 (by omega)]
  have hts_shape : (transposeAxes 2 3 (initSM 743)).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hgrad_shape, listSwapAt, List.getD, List.set]
  have htp_shape : ∀ r, r < 4 → (chunkPrimDimN 1 4 r (transposeAxes 2 3 (initSM 743))).shape = [1, 1, 8, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 1 4 r _ _ hts_shape (by omega)]
    simp [List.set, List.getD]
  simp only [goal_124, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes,
    LineageGoal.gatherDim, List.map, Piece.tid]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]
    simp [transposeAxes, Tensor.mkShape, hgrad_shape, listSwapAt, List.getD, List.set]
  · rw [hpm0', hpm1', hpm2', hpm3']
    simp [htp_shape 0 (by omega), htp_shape 1 (by omega), htp_shape 2 (by omega), htp_shape 3 (by omega)]
  · rw [hsm]
    symm
    rw [hpm0', hpm1', hpm2', hpm3']
    -- `reconstructForGoal` (the `replicated` dispatch added later) wraps what the
    -- v4.27 proof saw directly as `reconstructWithDim`; peel it first.
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    simp only [reconstructWithDim_cons_cons_nonscalar (h := by rw [htp_shape 0 (by omega)]; decide)]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim1_4_8_8 _ hts_shape

end TrainVerify.Denote.GeneratedGoals
