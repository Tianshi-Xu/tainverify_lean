/- Goal_233 proof. The eight per-node lemmas live in Goal_233_<name>.lean; see
   the note in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_233_hbw0
import denote.gpt_ly4_regen.Goal_233_hbw1
import denote.gpt_ly4_regen.Goal_233_hbw2
import denote.gpt_ly4_regen.Goal_233_hbw3
import denote.gpt_ly4_regen.Goal_233_hpm0base
import denote.gpt_ly4_regen.Goal_233_hpm1base
import denote.gpt_ly4_regen.Goal_233_hpm2base
import denote.gpt_ly4_regen.Goal_233_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxHeartbeats 4000000 in
theorem prove_goal_233_cut : goal_233_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  have hInit : InitGoalHolds pm_goal_233.numRanks goal_234 initSM initPM := by apply hInitGoals; decide
  have hgrad_shape : (initSM 871).shape = [1, 4, 8, 8] := hInit.1
  have htp_shapes := hInit.2.1
  simp only [goal_234, LineageGoal.tps, List.map] at htp_shapes
  have hg0 : (initPM 3034).shape = [1, 4, 2, 8] := by have := congrArg (List.getD · 0 []) htp_shapes; simp at this; exact this
  have hg1 : (initPM 3036).shape = [1, 4, 2, 8] := by have := congrArg (List.getD · 1 []) htp_shapes; simp at this; exact this
  have hg2 : (initPM 3038).shape = [1, 4, 2, 8] := by have := congrArg (List.getD · 2 []) htp_shapes; simp at this; exact this
  have hg3 : (initPM 3040).shape = [1, 4, 2, 8] := by have := congrArg (List.getD · 3 []) htp_shapes; simp at this; exact this
  have hrec_ag : initSM 871 = allGatherPrimDimN 2 4 0 [initPM 3034, initPM 3036, initPM 3038, initPM 3040] := by
    have hrec := hInit.2.2
    simp only [goal_234, LineageGoal.tps, LineageGoal.gatherDim, List.map] at hrec
    rw [hrec]
    exact reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [hg0]; decide)
  have hsm : (denoteGraph sm_goal_233 initSM) 870 = bw_div ((2 : Nat) : Scalar) (initSM 871) := by
    simp only [sm_goal_233, denoteGraph, GraphDecl.nodes, List.foldl]
    rw [applyNode_bw_div_out_g233]
  have hbw0 := hbw0_233 initPM
  have hbw1 := hbw1_233 initPM
  have hbw2 := hbw2_233 initPM
  have hbw3 := hbw3_233 initPM
  have hpm0base := hpm0base_233 initPM
  have hpm1base := hpm1base_233 initPM
  have hpm2base := hpm2base_233 initPM
  have hpm3base := hpm3base_233 initPM
  have hpm0 : (denoteGraph pm_goal_233 initPM) 3010 = allToAllPrimWithDims 4 0 [bw_div ((2:Nat):Scalar) (initPM 3034), bw_div ((2:Nat):Scalar) (initPM 3036), bw_div ((2:Nat):Scalar) (initPM 3038), bw_div ((2:Nat):Scalar) (initPM 3040)] 2 1 := by rw [hpm0base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hpm1 : (denoteGraph pm_goal_233 initPM) 3012 = allToAllPrimWithDims 4 1 [bw_div ((2:Nat):Scalar) (initPM 3034), bw_div ((2:Nat):Scalar) (initPM 3036), bw_div ((2:Nat):Scalar) (initPM 3038), bw_div ((2:Nat):Scalar) (initPM 3040)] 2 1 := by rw [hpm1base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hpm2 : (denoteGraph pm_goal_233 initPM) 3014 = allToAllPrimWithDims 4 2 [bw_div ((2:Nat):Scalar) (initPM 3034), bw_div ((2:Nat):Scalar) (initPM 3036), bw_div ((2:Nat):Scalar) (initPM 3038), bw_div ((2:Nat):Scalar) (initPM 3040)] 2 1 := by rw [hpm2base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hpm3 : (denoteGraph pm_goal_233 initPM) 3016 = allToAllPrimWithDims 4 3 [bw_div ((2:Nat):Scalar) (initPM 3034), bw_div ((2:Nat):Scalar) (initPM 3036), bw_div ((2:Nat):Scalar) (initPM 3038), bw_div ((2:Nat):Scalar) (initPM 3040)] 2 1 := by rw [hpm3base]; simp [hbw0, hbw1, hbw2, hbw3]
  have hxs_shape234 : ∀ i (hi : i < ([initPM 3034, initPM 3036, initPM 3038, initPM 3040] : List Tensor).length),
      (([initPM 3034, initPM 3036, initPM 3038, initPM 3040] : List Tensor).get ⟨i, hi⟩).shape = [1, 4, 2, 8] := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl
    · exact hg0
    · exact hg1
    · exact hg2
    · exact hg3
  have hhead234 : (([initPM 3034, initPM 3036, initPM 3038, initPM 3040] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hg0
  have hcomm234 := bw_div_allGatherPrimDimN_eq_g233 ((2:Nat):Scalar) 2 4 [initPM 3034, initPM 3036, initPM 3038, initPM 3040] [1, 4, 2, 8] (by omega) (by rfl) hhead234 hxs_shape234
  have hbridge : bw_div ((2:Nat):Scalar) (initSM 871) = allGatherPrimDimN 2 4 0 [bw_div ((2:Nat):Scalar) (initPM 3034), bw_div ((2:Nat):Scalar) (initPM 3036), bw_div ((2:Nat):Scalar) (initPM 3038), bw_div ((2:Nat):Scalar) (initPM 3040)] := by
    rw [hrec_ag, hcomm234]; rfl
  have halltoall : ∀ r, r < 4 → allToAllPrimWithDims 4 r [bw_div ((2:Nat):Scalar) (initPM 3034), bw_div ((2:Nat):Scalar) (initPM 3036), bw_div ((2:Nat):Scalar) (initPM 3038), bw_div ((2:Nat):Scalar) (initPM 3040)] 2 1 = chunkPrimDimN 1 4 r (bw_div ((2:Nat):Scalar) (initSM 871)) := by
    intro r _
    simp only [allToAllPrimWithDims]
    rw [← hbridge]
  have hpm0' : (denoteGraph pm_goal_233 initPM) 3010 = chunkPrimDimN 1 4 0 (bw_div ((2:Nat):Scalar) (initSM 871)) := by rw [hpm0, halltoall 0 (by omega)]
  have hpm1' : (denoteGraph pm_goal_233 initPM) 3012 = chunkPrimDimN 1 4 1 (bw_div ((2:Nat):Scalar) (initSM 871)) := by rw [hpm1, halltoall 1 (by omega)]
  have hpm2' : (denoteGraph pm_goal_233 initPM) 3014 = chunkPrimDimN 1 4 2 (bw_div ((2:Nat):Scalar) (initSM 871)) := by rw [hpm2, halltoall 2 (by omega)]
  have hpm3' : (denoteGraph pm_goal_233 initPM) 3016 = chunkPrimDimN 1 4 3 (bw_div ((2:Nat):Scalar) (initSM 871)) := by rw [hpm3, halltoall 3 (by omega)]
  have hts_shape : (bw_div ((2:Nat):Scalar) (initSM 871)).shape = [1, 4, 8, 8] := by rw [bw_div_shape_g233, hgrad_shape]
  have htp_shape : ∀ r, r < 4 → (chunkPrimDimN 1 4 r (bw_div ((2:Nat):Scalar) (initSM 871))).shape = [1, 1, 8, 8] := by intro r hr; rw [chunkPrimDimN_shape 1 4 r _ _ hts_shape (by omega)]; simp [List.set, List.getD]
  simp only [goal_233, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes, LineageGoal.gatherDim, List.map, Piece.tid]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm, bw_div_shape_g233, hgrad_shape]
  · rw [hpm0', hpm1', hpm2', hpm3']
    simp only [List.map_cons, List.map_nil, htp_shape 0 (by omega), htp_shape 1 (by omega), htp_shape 2 (by omega), htp_shape 3 (by omega)]
  · rw [hsm, hpm0', hpm1', hpm2', hpm3']
    symm
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    simp only [reconstructWithDim_cons_cons_nonscalar (h := by rw [htp_shape 0 (by omega)]; decide)]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim1_4_8_8 _ hts_shape

end TrainVerify.Denote.GeneratedGoals
