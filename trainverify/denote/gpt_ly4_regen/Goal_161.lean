/- Goal_161 proof. The per-node lemmas live in Goal_161_<name>.lean; see the note
   in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_161_b45_0
import denote.gpt_ly4_regen.Goal_161_b45_1
import denote.gpt_ly4_regen.Goal_161_b45_2
import denote.gpt_ly4_regen.Goal_161_b45_3
import denote.gpt_ly4_regen.Goal_161_b66_0
import denote.gpt_ly4_regen.Goal_161_b66_1
import denote.gpt_ly4_regen.Goal_161_b66_2
import denote.gpt_ly4_regen.Goal_161_b66_3
import denote.gpt_ly4_regen.Goal_161_b42_0
import denote.gpt_ly4_regen.Goal_161_b42_1
import denote.gpt_ly4_regen.Goal_161_b42_2
import denote.gpt_ly4_regen.Goal_161_b42_3

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prove_goal_161_cut : goal_161_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- prereq goal_43: 621 (= x) is the dim-2 gather of shards 1929..1932
  have hInit621 : InitGoalHolds pm_goal_161.numRanks goal_43 initSM initPM := by
    apply hInitGoals
    simp only [goal_161_cut_initGoals, goal_161_prereqs]
    decide
  have h621_shape : (initSM 621).shape = [1, 4, 8, 8] := hInit621.1
  have hs621 := hInit621.2.1
  simp only [goal_43, List.map] at hs621
  have h1929_shape : (initPM 1929).shape = [1, 4, 2, 8] := by
    have := congrArg (List.getD · 0 []) hs621; simp at this; exact this
  have h621_eq : initSM 621 = allGatherPrimDimN 2 4 0
      [initPM 1929, initPM 1930, initPM 1931, initPM 1932] := by
    have hrec := hInit621.2.2
    simp only [goal_43, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [h1929_shape]; decide)
  -- prereq goal_166: 789 (= g) is replicated
  have hInit789 : InitGoalHolds pm_goal_161.numRanks goal_166 initSM initPM := by
    apply hInitGoals
    simp only [goal_161_cut_initGoals, goal_161_prereqs]
    decide
  have h789_shape : (initSM 789).shape = [1, 4, 8, 8] := hInit789.1
  have h789_eq : initSM 789 = initPM 789 := by
    have hrec := hInit789.2.2
    simp only [goal_166, List.map] at hrec
    rw [hrec]; rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]; exact reconstructWithDim_singleton _ _ _ _
  have h789PM_shape : (initPM 789).shape = [1, 4, 8, 8] := by rw [← h789_eq]; exact h789_shape
  -- abbreviation for the full second-output gradient dW = xᵀ @ g
  set dW : Tensor := batchedMatmul (transpose2d (initSM 621)) (initPM 789) with hdW_def
  -- chunk shapes
  have hc : ∀ r, (chunkPrimDimN 3 4 r (initSM 621)).shape = [1, 4, 8, 2] := by
    intro r
    rw [chunkPrimDimN_shape 3 4 r _ _ h621_shape (by omega)]; simp [List.set, List.getD]
  have hdW_shape : dW.shape = [1, 4, 8, 8] :=
    batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_8 _ h621_shape) h789PM_shape
  have hchunk_dW : ∀ r, (chunkPrimDimN 3 4 r dW).shape = [1, 4, 8, 2] := by
    intro r
    rw [chunkPrimDimN_shape 3 4 r _ _ hdW_shape (by omega)]; simp [List.set, List.getD]
  -- init tids pass through unchanged (never written by any pm node)
  have e1929 : (denoteGraph pm_goal_161 initPM) 1929 = initPM 1929 := by
    simp only [pm_goal_161, denoteGraph, GraphDecl.nodes, List.foldl]
    repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  have e1930 : (denoteGraph pm_goal_161 initPM) 1930 = initPM 1930 := by
    simp only [pm_goal_161, denoteGraph, GraphDecl.nodes, List.foldl]
    repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  have e1931 : (denoteGraph pm_goal_161 initPM) 1931 = initPM 1931 := by
    simp only [pm_goal_161, denoteGraph, GraphDecl.nodes, List.foldl]
    repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  have e1932 : (denoteGraph pm_goal_161 initPM) 1932 = initPM 1932 := by
    simp only [pm_goal_161, denoteGraph, GraphDecl.nodes, List.foldl]
    repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  have e789 : (denoteGraph pm_goal_161 initPM) 789 = initPM 789 := by
    simp only [pm_goal_161, denoteGraph, GraphDecl.nodes, List.foldl]
    repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  -- First AllToAll outputs (1945..1948): redistribute x from dim-2 shards to dim-3 chunks
  have b45_0 := b45_0_161 initPM
  have b45_1 := b45_1_161 initPM
  have b45_2 := b45_2_161 initPM
  have b45_3 := b45_3_161 initPM
  have h45_0 : (denoteGraph pm_goal_161 initPM) 1945 = chunkPrimDimN 3 4 0 (initSM 621) := by
    rw [b45_0, e1929, e1930, e1931, e1932]; simp only [allToAllPrimWithDims]; rw [← h621_eq]
  have h45_1 : (denoteGraph pm_goal_161 initPM) 1946 = chunkPrimDimN 3 4 1 (initSM 621) := by
    rw [b45_1, e1929, e1930, e1931, e1932]; simp only [allToAllPrimWithDims]; rw [← h621_eq]
  have h45_2 : (denoteGraph pm_goal_161 initPM) 1947 = chunkPrimDimN 3 4 2 (initSM 621) := by
    rw [b45_2, e1929, e1930, e1931, e1932]; simp only [allToAllPrimWithDims]; rw [← h621_eq]
  have h45_3 : (denoteGraph pm_goal_161 initPM) 1948 = chunkPrimDimN 3 4 3 (initSM 621) := by
    rw [b45_3, e1929, e1930, e1931, e1932]; simp only [allToAllPrimWithDims]; rw [← h621_eq]
  -- Middle BW_matmul second outputs (1966,1968,1970,1972): dy_r = (chunk_r x)ᵀ @ g
  have b66_0 := b66_0_161 initPM
  have b66_1 := b66_1_161 initPM
  have b66_2 := b66_2_161 initPM
  have b66_3 := b66_3_161 initPM
  have h66_0 : (denoteGraph pm_goal_161 initPM) 1966 =
      batchedMatmul (transpose2d (chunkPrimDimN 3 4 0 (initSM 621))) (initPM 789) := by
    rw [b66_0]
    show batchedMatmul (transpose2d ((denoteGraph pm_goal_161 initPM) 1945))
      ((denoteGraph pm_goal_161 initPM) 789) = _
    rw [h45_0, e789]
  have h66_1 : (denoteGraph pm_goal_161 initPM) 1968 =
      batchedMatmul (transpose2d (chunkPrimDimN 3 4 1 (initSM 621))) (initPM 789) := by
    rw [b66_1]
    show batchedMatmul (transpose2d ((denoteGraph pm_goal_161 initPM) 1946))
      ((denoteGraph pm_goal_161 initPM) 789) = _
    rw [h45_1, e789]
  have h66_2 : (denoteGraph pm_goal_161 initPM) 1970 =
      batchedMatmul (transpose2d (chunkPrimDimN 3 4 2 (initSM 621))) (initPM 789) := by
    rw [b66_2]
    show batchedMatmul (transpose2d ((denoteGraph pm_goal_161 initPM) 1947))
      ((denoteGraph pm_goal_161 initPM) 789) = _
    rw [h45_2, e789]
  have h66_3 : (denoteGraph pm_goal_161 initPM) 1972 =
      batchedMatmul (transpose2d (chunkPrimDimN 3 4 3 (initSM 621))) (initPM 789) := by
    rw [b66_3]
    show batchedMatmul (transpose2d ((denoteGraph pm_goal_161 initPM) 1948))
      ((denoteGraph pm_goal_161 initPM) 789) = _
    rw [h45_3, e789]
  -- Bridge: gathering the per-rank dy outputs (dim 2) reconstructs the full dW
  have hgather_dW : allGatherPrimDimN 2 4 0
      [(denoteGraph pm_goal_161 initPM) 1966, (denoteGraph pm_goal_161 initPM) 1968,
       (denoteGraph pm_goal_161 initPM) 1970, (denoteGraph pm_goal_161 initPM) 1972] = dW := by
    rw [h66_0, h66_1, h66_2, h66_3]
    rw [← bw_matmul_snd_split_dX_1_4_8_8 (initPM 789)
        (chunkPrimDimN 3 4 0 (initSM 621)) (chunkPrimDimN 3 4 1 (initSM 621))
        (chunkPrimDimN 3 4 2 (initSM 621)) (chunkPrimDimN 3 4 3 (initSM 621))
        h789PM_shape (hc 0) (hc 1) (hc 2) (hc 3)]
    rw [allGatherPrimDimN_chunkPrimDimN_id_dim3_4_8_8 (initSM 621) h621_shape]
  -- Final AllToAll outputs (1842..1848): chunk dW along dim 3
  have b42_0 := b42_0_161 initPM
  have b42_1 := b42_1_161 initPM
  have b42_2 := b42_2_161 initPM
  have b42_3 := b42_3_161 initPM
  have h42_0 : (denoteGraph pm_goal_161 initPM) 1842 = chunkPrimDimN 3 4 0 dW := by
    rw [b42_0]; simp only [allToAllPrimWithDims]; rw [hgather_dW]
  have h42_1 : (denoteGraph pm_goal_161 initPM) 1844 = chunkPrimDimN 3 4 1 dW := by
    rw [b42_1]; simp only [allToAllPrimWithDims]; rw [hgather_dW]
  have h42_2 : (denoteGraph pm_goal_161 initPM) 1846 = chunkPrimDimN 3 4 2 dW := by
    rw [b42_2]; simp only [allToAllPrimWithDims]; rw [hgather_dW]
  have h42_3 : (denoteGraph pm_goal_161 initPM) 1848 = chunkPrimDimN 3 4 3 dW := by
    rw [b42_3]; simp only [allToAllPrimWithDims]; rw [hgather_dW]
  -- SM second output 784 = dW
  have hsm : (denoteGraph sm_goal_161 initSM) 784 = dW := by
    simp only [sm_goal_161, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_matmul_snd_out (hne := by decide)]
    show batchedMatmul (transpose2d (initSM 621)) (initSM 789) = dW
    rw [hdW_def, h789_eq]
  -- Discharge the three conjuncts
  simp only [goal_161, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm]; exact hdW_shape
  · rw [h42_0, h42_1, h42_2, h42_3]
    simp [hchunk_dW 0, hchunk_dW 1, hchunk_dW 2, hchunk_dW 3]
  · rw [hsm, h42_0, h42_1, h42_2, h42_3]
    -- The v4.27 proof restated the goal with `show ... = reconstructWithDim ...` to
    -- pin the numeric arguments. Since 8bd410b3 the goal is the `reconstructForGoal`
    -- wrapper, so peel first and keep the `show` to specialise the arguments.
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    show dW = reconstructWithDim 3 4 0
      [chunkPrimDimN 3 4 0 dW, chunkPrimDimN 3 4 1 dW, chunkPrimDimN 3 4 2 dW, chunkPrimDimN 3 4 3 dW]
    symm
    rw [reconstructWithDim_cons_cons_nonscalar 3 4 0 _ _ _ (by rw [hchunk_dW 0]; decide)]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim3_4_8_8 dW hdW_shape

end TrainVerify.Denote.GeneratedGoals
