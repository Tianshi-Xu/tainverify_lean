/- Goal_234 proof. The per-node lemmas live in Goal_234_<name>.lean; see the note
   in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_234_hAA0
import denote.gpt_ly4_regen.Goal_234_hAA1
import denote.gpt_ly4_regen.Goal_234_hAA2
import denote.gpt_ly4_regen.Goal_234_hAA3
import denote.gpt_ly4_regen.Goal_234_hbw0
import denote.gpt_ly4_regen.Goal_234_hbw1
import denote.gpt_ly4_regen.Goal_234_hbw2
import denote.gpt_ly4_regen.Goal_234_hbw3
import denote.gpt_ly4_regen.Goal_234_hpm0base
import denote.gpt_ly4_regen.Goal_234_hpm1base
import denote.gpt_ly4_regen.Goal_234_hpm2base
import denote.gpt_ly4_regen.Goal_234_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prove_goal_234_cut : goal_234_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- Input 872 (the gradient g): goal_235, gather dim 1, shards [1,1,8,8].
  have hInit235 : InitGoalHolds pm_goal_234.numRanks goal_235 initSM initPM := by
    apply hInitGoals; decide
  have h872_shape : (initSM 872).shape = [1, 4, 8, 8] := hInit235.1
  have h235tp := hInit235.2.1
  simp only [goal_235, LineageGoal.tps, List.map] at h235tp
  have h3058 : (initPM 3058).shape = [1, 1, 8, 8] := by
    have := congrArg (List.getD · 0 []) h235tp; simpa using this
  have h3060 : (initPM 3060).shape = [1, 1, 8, 8] := by
    have := congrArg (List.getD · 1 []) h235tp; simpa using this
  have h3062 : (initPM 3062).shape = [1, 1, 8, 8] := by
    have := congrArg (List.getD · 2 []) h235tp; simpa using this
  have h3064 : (initPM 3064).shape = [1, 1, 8, 8] := by
    have := congrArg (List.getD · 3 []) h235tp; simpa using this
  have hrec872 : initSM 872 =
      allGatherPrimDimN 1 4 0 [initPM 3058, initPM 3060, initPM 3062, initPM 3064] := by
    have hrec := hInit235.2.2
    simp only [goal_235, LineageGoal.tps, LineageGoal.gatherDim, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _ (by rw [h3058]; decide)
  -- chunk roundtrip: initPM 3058+ = chunk_1_r (initSM 872)
  have hchunk872_0 : chunkPrimDimN 1 4 0 (initSM 872) = initPM 3058 := by
    rw [hrec872]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h3058 h3060 h3062 h3064 0 (by omega)
  have hchunk872_1 : chunkPrimDimN 1 4 1 (initSM 872) = initPM 3060 := by
    rw [hrec872]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h3058 h3060 h3062 h3064 1 (by omega)
  have hchunk872_2 : chunkPrimDimN 1 4 2 (initSM 872) = initPM 3062 := by
    rw [hrec872]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h3058 h3060 h3062 h3064 2 (by omega)
  have hchunk872_3 : chunkPrimDimN 1 4 3 (initSM 872) = initPM 3064 := by
    rw [hrec872]; simpa using chunk1_gather1_roundtrip_1_1_8_8 _ _ _ _ h3058 h3060 h3062 h3064 3 (by omega)
  -- Input 690 (softmax output y): goal_92, gather dim 2, shards [1,4,2,8].
  have hInit92 : InitGoalHolds pm_goal_234.numRanks goal_92 initSM initPM := by
    apply hInitGoals; decide
  have h690_shape : (initSM 690).shape = [1, 4, 8, 8] := hInit92.1
  have h92tp := hInit92.2.1
  simp only [goal_92, LineageGoal.tps, List.map] at h92tp
  have h3021 : (initPM 3021).shape = [1, 4, 2, 8] := by
    have := congrArg (List.getD · 0 []) h92tp; simpa using this
  have hrec690 : initSM 690 =
      allGatherPrimDimN 2 4 0 [initPM 3021, initPM 3022, initPM 3023, initPM 3024] := by
    have hrec := hInit92.2.2
    simp only [goal_92, LineageGoal.tps, LineageGoal.gatherDim, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [h3021]; decide)
  -- SM store
  have hsm : (denoteGraph sm_goal_234 initSM) 871 = bw_softmax (initSM 872) (initSM 690) := by
    simp only [sm_goal_234, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_softmax_out_g234]
  -- Layer 1: first AllToAll producing 3041..3044 from [3021..3024], idim 2 odim 1.
  have hAA0 := hAA0_234 initPM
  have hAA1 := hAA1_234 initPM
  have hAA2 := hAA2_234 initPM
  have hAA3 := hAA3_234 initPM
  -- 3041_r = chunk_1_r (initSM 690)
  have hY0 : (denoteGraph pm_goal_234 initPM) 3041 = chunkPrimDimN 1 4 0 (initSM 690) := by
    rw [hAA0, hrec690]; rfl
  have hY1 : (denoteGraph pm_goal_234 initPM) 3042 = chunkPrimDimN 1 4 1 (initSM 690) := by
    rw [hAA1, hrec690]; rfl
  have hY2 : (denoteGraph pm_goal_234 initPM) 3043 = chunkPrimDimN 1 4 2 (initSM 690) := by
    rw [hAA2, hrec690]; rfl
  have hY3 : (denoteGraph pm_goal_234 initPM) 3044 = chunkPrimDimN 1 4 3 (initSM 690) := by
    rw [hAA3, hrec690]; rfl
  -- Layer 2: BW_softmax producing 3057..3063.
  have hbw0 := hbw0_234 initPM
  have hbw1 := hbw1_234 initPM
  have hbw2 := hbw2_234 initPM
  have hbw3 := hbw3_234 initPM
  -- 3057_r = bw_softmax (chunk_1_r 872) (chunk_1_r 690)
  have hS0 : (denoteGraph pm_goal_234 initPM) 3057 =
      bw_softmax (chunkPrimDimN 1 4 0 (initSM 872)) (chunkPrimDimN 1 4 0 (initSM 690)) := by
    rw [hbw0, hY0, ← hchunk872_0]
  have hS1 : (denoteGraph pm_goal_234 initPM) 3059 =
      bw_softmax (chunkPrimDimN 1 4 1 (initSM 872)) (chunkPrimDimN 1 4 1 (initSM 690)) := by
    rw [hbw1, hY1, ← hchunk872_1]
  have hS2 : (denoteGraph pm_goal_234 initPM) 3061 =
      bw_softmax (chunkPrimDimN 1 4 2 (initSM 872)) (chunkPrimDimN 1 4 2 (initSM 690)) := by
    rw [hbw2, hY2, ← hchunk872_2]
  have hS3 : (denoteGraph pm_goal_234 initPM) 3063 =
      bw_softmax (chunkPrimDimN 1 4 3 (initSM 872)) (chunkPrimDimN 1 4 3 (initSM 690)) := by
    rw [hbw3, hY3, ← hchunk872_3]
  -- Layer 3: final AllToAll producing 3034..3040, idim 1 odim 2.
  have hpm0base := hpm0base_234 initPM
  have hpm1base := hpm1base_234 initPM
  have hpm2base := hpm2base_234 initPM
  have hpm3base := hpm3base_234 initPM
  -- distribution: gather of pieces = full bw_softmax
  have hSplit : allGatherPrimDimN 1 4 0
      [bw_softmax (chunkPrimDimN 1 4 0 (initSM 872)) (chunkPrimDimN 1 4 0 (initSM 690)),
       bw_softmax (chunkPrimDimN 1 4 1 (initSM 872)) (chunkPrimDimN 1 4 1 (initSM 690)),
       bw_softmax (chunkPrimDimN 1 4 2 (initSM 872)) (chunkPrimDimN 1 4 2 (initSM 690)),
       bw_softmax (chunkPrimDimN 1 4 3 (initSM 872)) (chunkPrimDimN 1 4 3 (initSM 690))]
      = bw_softmax (initSM 872) (initSM 690) :=
    (softmaxBwd_split_dim1_4_1_4_8_8_g234 (initSM 872) (initSM 690) h872_shape h690_shape).symm
  have hpm0 : (denoteGraph pm_goal_234 initPM) 3034 =
      chunkPrimDimN 2 4 0 (bw_softmax (initSM 872) (initSM 690)) := by
    rw [hpm0base, hS0, hS1, hS2, hS3]; unfold allToAllPrimWithDims; rw [hSplit]
  have hpm1 : (denoteGraph pm_goal_234 initPM) 3036 =
      chunkPrimDimN 2 4 1 (bw_softmax (initSM 872) (initSM 690)) := by
    rw [hpm1base, hS0, hS1, hS2, hS3]; unfold allToAllPrimWithDims; rw [hSplit]
  have hpm2 : (denoteGraph pm_goal_234 initPM) 3038 =
      chunkPrimDimN 2 4 2 (bw_softmax (initSM 872) (initSM 690)) := by
    rw [hpm2base, hS0, hS1, hS2, hS3]; unfold allToAllPrimWithDims; rw [hSplit]
  have hpm3 : (denoteGraph pm_goal_234 initPM) 3040 =
      chunkPrimDimN 2 4 3 (bw_softmax (initSM 872) (initSM 690)) := by
    rw [hpm3base, hS0, hS1, hS2, hS3]; unfold allToAllPrimWithDims; rw [hSplit]
  -- shapes
  have hbwshape : (bw_softmax (initSM 872) (initSM 690)).shape = [1, 4, 8, 8] :=
    bw_softmax_shape_d8_g234 (initSM 872) (initSM 690) 1 4 8 h690_shape
  have htp_shape : ∀ r, r < 4 →
      (chunkPrimDimN 2 4 r (bw_softmax (initSM 872) (initSM 690))).shape = [1, 4, 2, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ hbwshape (by omega)]
    simp [List.set, List.getD]
  simp only [goal_234, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes,
    LineageGoal.gatherDim, List.map, Piece.tid]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]; exact hbwshape
  · rw [hpm0, hpm1, hpm2, hpm3]
    simp [htp_shape 0 (by omega), htp_shape 1 (by omega), htp_shape 2 (by omega), htp_shape 3 (by omega)]
  · rw [hsm, hpm0, hpm1, hpm2, hpm3]
    symm
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    simp only [reconstructWithDim_cons_cons_nonscalar (h := by rw [htp_shape 0 (by omega)]; decide)]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim2_4_8_8 _ hbwshape

end TrainVerify.Denote.GeneratedGoals
