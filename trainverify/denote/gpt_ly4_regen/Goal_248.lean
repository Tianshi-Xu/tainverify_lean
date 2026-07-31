/- Goal_248 proof. The per-node lemmas live in Goal_248_<name>.lean; see the note
   in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_248_hbw0
import denote.gpt_ly4_regen.Goal_248_hbw1
import denote.gpt_ly4_regen.Goal_248_hbw2
import denote.gpt_ly4_regen.Goal_248_hbw3
import denote.gpt_ly4_regen.Goal_248_hpm0base
import denote.gpt_ly4_regen.Goal_248_hpm1base
import denote.gpt_ly4_regen.Goal_248_hpm2base
import denote.gpt_ly4_regen.Goal_248_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prove_goal_248_cut : goal_248_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- abbreviations for the input AllToAll (X reshard) results
  set X0 := allToAllPrimWithDims 4 0 [initPM 3265, initPM 3266, initPM 3267, initPM 3268] 1 2 with hX0def
  set X1 := allToAllPrimWithDims 4 1 [initPM 3265, initPM 3266, initPM 3267, initPM 3268] 1 2 with hX1def
  set X2 := allToAllPrimWithDims 4 2 [initPM 3265, initPM 3266, initPM 3267, initPM 3268] 1 2 with hX2def
  set X3 := allToAllPrimWithDims 4 3 [initPM 3265, initPM 3266, initPM 3267, initPM 3268] 1 2 with hX3def
  -- goal_250: gradient g (tid 889) is replicated
  have hInit250 : InitGoalHolds pm_goal_248.numRanks goal_250 initSM initPM := by
    apply hInitGoals; simp only [goal_248_cut_initGoals, goal_248_prereqs]; decide
  have h889_shape : (initSM 889).shape = [1, 8, 32] := hInit250.1
  have h889_eq : initSM 889 = initPM 889 := by
    have hrec := hInit250.2.2
    simp only [goal_250, pm_goal_248, List.map] at hrec
    rw [hrec]; rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]; exact reconstructWithDim_singleton ..
  -- goal_102: input X (tid 704) is dim-1 gather of shards 3265..3268
  have hInit102 : InitGoalHolds pm_goal_248.numRanks goal_102 initSM initPM := by
    apply hInitGoals; simp only [goal_248_cut_initGoals, goal_248_prereqs]; decide
  have h704_shape : (initSM 704).shape = [1, 8, 128] := hInit102.1
  have hs102 := hInit102.2.1
  simp only [goal_102, List.map, List.cons.injEq, and_true] at hs102
  obtain ⟨h3265_shape, h3266_shape, h3267_shape, h3268_shape⟩ := hs102
  -- initGoal_705: weight W (tid 705) is dim-1 gather of shards 3289..3292
  have hInit705 : InitGoalHolds pm_goal_248.numRanks initGoal_705 initSM initPM := by
    apply hInitGoals; simp only [goal_248_cut_initGoals, goal_248_prereqs]; decide
  have h705_shape : (initSM 705).shape = [32, 128] := hInit705.1
  have hs705 := hInit705.2.1
  simp only [initGoal_705, List.map, List.cons.injEq, and_true] at hs705
  obtain ⟨h3289_shape, h3290_shape, h3291_shape, h3292_shape⟩ := hs705
  have h705_gather : initSM 705 = allGatherPrimDimN 1 4 0
      [initPM 3289, initPM 3290, initPM 3291, initPM 3292] := by
    have hrec := hInit705.2.2
    simp only [initGoal_705, pm_goal_248, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _ (by rw [h3289_shape]; decide)
  -- shapes of the per-rank X reshards
  have hX0_shape : X0.shape = [1, 8, 32] := by
    rw [hX0def, allToAllPrimWithDims_shape 4 0 _ 1 2 [1,2,128] (by simp [h3265_shape]) (by omega)]
    simp [List.set, List.getD]
  have hX1_shape : X1.shape = [1, 8, 32] := by
    rw [hX1def, allToAllPrimWithDims_shape 4 1 _ 1 2 [1,2,128] (by simp [h3265_shape]) (by omega)]
    simp [List.set, List.getD]
  have hX2_shape : X2.shape = [1, 8, 32] := by
    rw [hX2def, allToAllPrimWithDims_shape 4 2 _ 1 2 [1,2,128] (by simp [h3265_shape]) (by omega)]
    simp [List.set, List.getD]
  have hX3_shape : X3.shape = [1, 8, 32] := by
    rw [hX3def, allToAllPrimWithDims_shape 4 3 _ 1 2 [1,2,128] (by simp [h3265_shape]) (by omega)]
    simp [List.set, List.getD]
  -- SM store: 887 = dX
  have hsm : (denoteGraph sm_goal_248 initSM) 887 =
      (bw_linear (initSM 889) (initSM 704) (initSM 705)).1 := by
    simp only [sm_goal_248, denoteGraph, List.foldl]
    rw [applyNode_bw_linear_fst_out _ _ 0 889 704 705 887 888 (by decide)]
  -- full SM dX shape
  have hDshape : (bw_linear (initSM 889) (initSM 704) (initSM 705)).1.shape = [1, 8, 128] :=
    bw_linear_3d_fst_shape 1 8 32 128 _ _ _ h889_shape h704_shape h705_shape
  -- Key distribution: dX is the dim-2 all-gather of the per-rank dX shards
  have hkey : (bw_linear (initSM 889) (initSM 704) (initSM 705)).1 =
      allGatherPrimDimN 2 4 0
        [(bw_linear (initSM 889) X0 (initPM 3289)).1,
         (bw_linear (initSM 889) X1 (initPM 3290)).1,
         (bw_linear (initSM 889) X2 (initPM 3291)).1,
         (bw_linear (initSM 889) X3 (initPM 3292)).1] := by
    rw [h705_gather]
    exact bw_linear_dx_isplit_dim2_4_1_8_128_g248 (initSM 889) (initSM 704)
      X0 X1 X2 X3 (initPM 3289) (initPM 3290) (initPM 3291) (initPM 3292)
      h889_shape h704_shape hX0_shape hX1_shape hX2_shape hX3_shape
      h3289_shape h3290_shape h3291_shape h3292_shape
  -- PM per-rank BW dX outputs
  have hbw0 := hbw0_248 initPM
  have hbw1 := hbw1_248 initPM
  have hbw2 := hbw2_248 initPM
  have hbw3 := hbw3_248 initPM
  -- PM final AllToAll outputs (base form)
  have hpm0base := hpm0base_248 initPM
  have hpm1base := hpm1base_248 initPM
  have hpm2base := hpm2base_248 initPM
  have hpm3base := hpm3base_248 initPM
  -- the outer AllToAll (params 2 1) unfolds to a dim-1 chunk of a dim-2 all-gather
  have hunfold : ∀ (rank : Nat) (L : List Tensor),
      allToAllPrimWithDims 4 rank L 2 1 = chunkPrimDimN 1 4 rank (allGatherPrimDimN 2 4 0 L) :=
    fun _ _ => rfl
  -- each PM final output is a dim-1 chunk of the full SM dX
  have hpm0 : (denoteGraph pm_goal_248 initPM) 3278 =
      chunkPrimDimN 1 4 0 (bw_linear (initSM 889) (initSM 704) (initSM 705)).1 := by
    rw [hpm0base, hbw0, hbw1, hbw2, hbw3, hunfold, ← h889_eq, ← hkey]
  have hpm1 : (denoteGraph pm_goal_248 initPM) 3280 =
      chunkPrimDimN 1 4 1 (bw_linear (initSM 889) (initSM 704) (initSM 705)).1 := by
    rw [hpm1base, hbw0, hbw1, hbw2, hbw3, hunfold, ← h889_eq, ← hkey]
  have hpm2 : (denoteGraph pm_goal_248 initPM) 3282 =
      chunkPrimDimN 1 4 2 (bw_linear (initSM 889) (initSM 704) (initSM 705)).1 := by
    rw [hpm2base, hbw0, hbw1, hbw2, hbw3, hunfold, ← h889_eq, ← hkey]
  have hpm3 : (denoteGraph pm_goal_248 initPM) 3284 =
      chunkPrimDimN 1 4 3 (bw_linear (initSM 889) (initSM 704) (initSM 705)).1 := by
    rw [hpm3base, hbw0, hbw1, hbw2, hbw3, hunfold, ← h889_eq, ← hkey]
  -- chunk shapes
  have hchunkD : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r (bw_linear (initSM 889) (initSM 704) (initSM 705)).1).shape = [1, 2, 128] := by
    intro r hr
    rw [chunkPrimDimN_shape 1 4 r _ _ hDshape (by omega)]
    simp [List.set, List.getD]
  -- discharge the three conjuncts
  simp only [goal_248, List.map]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm_goal_248 initSM 887).shape = _
    rw [hsm]; exact hDshape
  · show [(denoteGraph pm_goal_248 initPM 3278).shape,
          (denoteGraph pm_goal_248 initPM 3280).shape,
          (denoteGraph pm_goal_248 initPM 3282).shape,
          (denoteGraph pm_goal_248 initPM 3284).shape] = _
    rw [hpm0, hpm1, hpm2, hpm3,
        hchunkD 0 (by omega), hchunkD 1 (by omega), hchunkD 2 (by omega), hchunkD 3 (by omega)]
  · rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    rw [hsm, hpm0, hpm1, hpm2, hpm3]
    symm
    rw [reconstructWithDim_cons_cons_nonscalar 1 pm_goal_248.numRanks 0 _ _ _
        (by rw [hchunkD 0 (by omega)]; decide)]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim1_4_128 _ hDshape

end TrainVerify.Denote.GeneratedGoals
