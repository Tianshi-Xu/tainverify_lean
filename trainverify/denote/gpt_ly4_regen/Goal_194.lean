/- Goal_194 proof. The eight per-node lemmas live in Goal_194_<name>.lean; see
   the note in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_194_hbw0
import denote.gpt_ly4_regen.Goal_194_hbw1
import denote.gpt_ly4_regen.Goal_194_hbw2
import denote.gpt_ly4_regen.Goal_194_hbw3
import denote.gpt_ly4_regen.Goal_194_hpm0base
import denote.gpt_ly4_regen.Goal_194_hpm1base
import denote.gpt_ly4_regen.Goal_194_hpm2base
import denote.gpt_ly4_regen.Goal_194_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxHeartbeats 4000000 in
theorem prove_goal_194_cut : goal_194_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  have hInit : InitGoalHolds pm_goal_194.numRanks goal_197 initSM initPM := by
    apply hInitGoals
    decide
  have hgrad_shape : (initSM 827).shape = [1, 4, 8, 8] := hInit.1
  have htp_shapes := hInit.2.1
  simp only [goal_197, LineageGoal.tps, List.map] at htp_shapes
  have hg0 : (initPM 2430).shape = [1, 1, 8, 8] := by have := congrArg (List.getD · 0 []) htp_shapes; simp at this; exact this
  have hg1 : (initPM 2432).shape = [1, 1, 8, 8] := by have := congrArg (List.getD · 1 []) htp_shapes; simp at this; exact this
  have hg2 : (initPM 2434).shape = [1, 1, 8, 8] := by have := congrArg (List.getD · 2 []) htp_shapes; simp at this; exact this
  have hg3 : (initPM 2436).shape = [1, 1, 8, 8] := by have := congrArg (List.getD · 3 []) htp_shapes; simp at this; exact this
  have hrec_ag : initSM 827 = allGatherPrimDimN 1 4 0 [initPM 2430, initPM 2432, initPM 2434, initPM 2436] := by
    have hrec := hInit.2.2
    simp only [goal_197, LineageGoal.tps, LineageGoal.gatherDim, List.map] at hrec
    rw [hrec]
    exact reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _ (by rw [hg0]; decide)
  have hsm : (denoteGraph sm_goal_194 initSM) 824 = transposeAxes 2 3 (initSM 827) := by
    simp only [sm_goal_194, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_transposeAxes_out]
  have hbw0 := hbw0_194 initPM
  have hbw1 := hbw1_194 initPM
  have hbw2 := hbw2_194 initPM
  have hbw3 := hbw3_194 initPM
  have hpm0base := hpm0base_194 initPM
  have hpm1base := hpm1base_194 initPM
  have hpm2base := hpm2base_194 initPM
  have hpm3base := hpm3base_194 initPM
  have hpm0 : (denoteGraph pm_goal_194 initPM) 2382 = allToAllPrimWithDims 4 0 [transposeAxes 2 3 (initPM 2430), transposeAxes 2 3 (initPM 2432), transposeAxes 2 3 (initPM 2434), transposeAxes 2 3 (initPM 2436)] 1 3 := by rw [hpm0base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hpm1 : (denoteGraph pm_goal_194 initPM) 2384 = allToAllPrimWithDims 4 1 [transposeAxes 2 3 (initPM 2430), transposeAxes 2 3 (initPM 2432), transposeAxes 2 3 (initPM 2434), transposeAxes 2 3 (initPM 2436)] 1 3 := by rw [hpm1base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hpm2 : (denoteGraph pm_goal_194 initPM) 2386 = allToAllPrimWithDims 4 2 [transposeAxes 2 3 (initPM 2430), transposeAxes 2 3 (initPM 2432), transposeAxes 2 3 (initPM 2434), transposeAxes 2 3 (initPM 2436)] 1 3 := by rw [hpm2base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hpm3 : (denoteGraph pm_goal_194 initPM) 2388 = allToAllPrimWithDims 4 3 [transposeAxes 2 3 (initPM 2430), transposeAxes 2 3 (initPM 2432), transposeAxes 2 3 (initPM 2434), transposeAxes 2 3 (initPM 2436)] 1 3 := by rw [hpm3base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hchunk0 : chunkPrimDimN 1 4 0 (initSM 827) = initPM 2430 := by rw [hrec_ag]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ hg0 hg1 hg2 hg3 0 (by omega)
  have hchunk1 : chunkPrimDimN 1 4 1 (initSM 827) = initPM 2432 := by rw [hrec_ag]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ hg0 hg1 hg2 hg3 1 (by omega)
  have hchunk2 : chunkPrimDimN 1 4 2 (initSM 827) = initPM 2434 := by rw [hrec_ag]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ hg0 hg1 hg2 hg3 2 (by omega)
  have hchunk3 : chunkPrimDimN 1 4 3 (initSM 827) = initPM 2436 := by rw [hrec_ag]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ hg0 hg1 hg2 hg3 3 (by omega)
  have hbridge0 := fw_transpose23_split_dim1_4_1_4_8_8 (initSM 827) hgrad_shape
  have hbridge : transposeAxes 2 3 (initSM 827) = allGatherPrimDimN 1 4 0 [transposeAxes 2 3 (initPM 2430), transposeAxes 2 3 (initPM 2432), transposeAxes 2 3 (initPM 2434), transposeAxes 2 3 (initPM 2436)] := by
    simpa [hchunk0, hchunk1, hchunk2, hchunk3] using hbridge0
  have halltoall : ∀ r, r < 4 →
      allToAllPrimWithDims 4 r [transposeAxes 2 3 (initPM 2430), transposeAxes 2 3 (initPM 2432), transposeAxes 2 3 (initPM 2434), transposeAxes 2 3 (initPM 2436)] 1 3 =
      chunkPrimDimN 3 4 r (transposeAxes 2 3 (initSM 827)) := by
    intro r _
    simp only [allToAllPrimWithDims]
    rw [← hbridge]
  have hpm0' : (denoteGraph pm_goal_194 initPM) 2382 = chunkPrimDimN 3 4 0 (transposeAxes 2 3 (initSM 827)) := by rw [hpm0, halltoall 0 (by omega)]
  have hpm1' : (denoteGraph pm_goal_194 initPM) 2384 = chunkPrimDimN 3 4 1 (transposeAxes 2 3 (initSM 827)) := by rw [hpm1, halltoall 1 (by omega)]
  have hpm2' : (denoteGraph pm_goal_194 initPM) 2386 = chunkPrimDimN 3 4 2 (transposeAxes 2 3 (initSM 827)) := by rw [hpm2, halltoall 2 (by omega)]
  have hpm3' : (denoteGraph pm_goal_194 initPM) 2388 = chunkPrimDimN 3 4 3 (transposeAxes 2 3 (initSM 827)) := by rw [hpm3, halltoall 3 (by omega)]
  have hts_shape : (transposeAxes 2 3 (initSM 827)).shape = [1, 4, 8, 8] := by simp [transposeAxes, Tensor.mkShape, hgrad_shape, listSwapAt, List.getD, List.set]
  have htp_shape : ∀ r, r < 4 → (chunkPrimDimN 3 4 r (transposeAxes 2 3 (initSM 827))).shape = [1, 4, 8, 2] := by
    intro r hr
    rw [chunkPrimDimN_shape 3 4 r _ _ hts_shape (by omega)]
    simp [List.set, List.getD]
  simp only [goal_194, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes,
    LineageGoal.gatherDim, List.map, Piece.tid]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]
    simp [transposeAxes, Tensor.mkShape, hgrad_shape, listSwapAt, List.getD, List.set]
  · rw [hpm0', hpm1', hpm2', hpm3']
    simp [htp_shape 0 (by omega), htp_shape 1 (by omega), htp_shape 2 (by omega), htp_shape 3 (by omega)]
  · rw [hsm, hpm0', hpm1', hpm2', hpm3']
    symm
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    simp only [reconstructWithDim_cons_cons_nonscalar (h := by rw [htp_shape 0 (by omega)]; decide)]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim3_4_8_8 _ hts_shape

end TrainVerify.Denote.GeneratedGoals
