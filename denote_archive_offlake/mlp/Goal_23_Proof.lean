/- Manual proof for Goal 23 (split file). -/
import denote.mlp.Goal_23
import denote.mlp.Common

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.Common
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.ManualProofs

set_option linter.flexible false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

/-!
## Goal 23

Outline:
- Unfold `goal_23_stmt_cut`.
- Use `goal_23_cut_initGoals` to obtain intermediate consistency for tid=24.
- Unfold `denoteGraph` for `sm_goal_23` and `pm_goal_23`.
- Use `BW_linear` lemma to show shard reconstruction equals SM output for tid=23.

Goal 23 proves that SM tid23 (dW from bw_linear) equals the reconstruction of PM tid47,49,51,53.
Key insight: dW = gradOut.T @ x, and since x is chunked, the dW outputs are also chunked.
-/

-- SM computes tid23 = (bw_linear tid24 tid20 tid16).2
lemma sm23_tid23 (initSM : Store) :
    (denoteGraph sm_goal_23 initSM) 23 = (bw_linear (initSM 24) (initSM 20) (initSM 16)).2 := by
  simp [sm_goal_23, denoteGraph, List.foldl, applyNode, evalOp, storeSet]

-- pm_goal_23 nodes = chunk_prefix ++ bw_linear_suffix (from Goal_BW_Common)
lemma pm23_split (initPM : Store) :
    denoteGraph pm_goal_23 initPM =
      denoteGraph { pm_goal_23 with nodes := bw_linear_suffix }
        (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM) := by
  simpa [pm_goal_23, chunk_prefix, bw_linear_suffix] using
    (denoteGraph_nodes_append pm_goal_23 chunk_prefix bw_linear_suffix initPM)

theorem goal_23_proof : goal_23_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  dsimp [goal_23_stmt_cut, CoarseLineageHoldsWithInit, goal_23]
  -- Extract initGoals using shared lemmas
  have hInit16 : InitGoalHolds pm_goal_23.numRanks initGoal_16 initSM initPM := by
    have : initGoal_16 ∈ goal_23_cut_initGoals := by simp [goal_23_cut_initGoals, initGoals]
    exact hInitGoals initGoal_16 this
  have hInit20 : InitGoalHolds pm_goal_23.numRanks initGoal_20 initSM initPM := by
    have : initGoal_20 ∈ goal_23_cut_initGoals := by simp [goal_23_cut_initGoals, initGoals]
    exact hInitGoals initGoal_20 this
  have hInit24 : InitGoalHolds pm_goal_23.numRanks intermediateGoal_24 initSM initPM := by
    have : intermediateGoal_24 ∈ goal_23_cut_initGoals := by
      simp [goal_23_cut_initGoals, goal_23_prereqs]
    exact hInitGoals intermediateGoal_24 this
  -- Use shared extraction lemmas (replacing ~30 lines of boilerplate per file)
  have hrec16' := initGoal_16_rec_allGather pm_goal_23.numRanks initSM initPM hInit16
  have hrec20 := initGoal_20_eq pm_goal_23.numRanks initSM initPM hInit20
  have h24eq := intermediateGoal_24_eq pm_goal_23.numRanks initSM initPM hInit24
  have hws_shapes := initGoal_16_ws_shapes pm_goal_23.numRanks initSM initPM hInit16
  have hshape30 := initGoal_16_shape_30 pm_goal_23.numRanks initSM initPM hInit16
  have hnon30 := initGoal_16_non_scalar pm_goal_23.numRanks initSM initPM hInit16
  -- SM tid23
  have hsm23 := sm23_tid23 initSM
  -- PM structure using shared lemmas from Goal_BW_Common
  have hpmSplit := pm23_split initPM
  -- PM tids 26..29 via shared chunk_prefix lemmas
  have hpm26 : (denoteGraph pm_goal_23 initPM) 26 = chunkPrim pm_goal_23.numRanks 0 (initPM 20) := by
    have hpres := bw_linear_suffix_preserves_26 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit] using (by simpa using hpres.trans (chunk_prefix_tid26 pm_goal_23 initPM).symm)
  have hpm27 : (denoteGraph pm_goal_23 initPM) 27 = chunkPrim pm_goal_23.numRanks 1 (initPM 20) := by
    have hpres := bw_linear_suffix_preserves_27 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit] using (by simpa using hpres.trans (chunk_prefix_tid27 pm_goal_23 initPM).symm)
  have hpm28 : (denoteGraph pm_goal_23 initPM) 28 = chunkPrim pm_goal_23.numRanks 2 (initPM 20) := by
    have hpres := bw_linear_suffix_preserves_28 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit] using (by simpa using hpres.trans (chunk_prefix_tid28 pm_goal_23 initPM).symm)
  have hpm29 : (denoteGraph pm_goal_23 initPM) 29 = chunkPrim pm_goal_23.numRanks 3 (initPM 20) := by
    have hpres := bw_linear_suffix_preserves_29 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit] using (by simpa using hpres.trans (chunk_prefix_tid29 pm_goal_23 initPM).symm)
  -- PM tid47,49,51,53 via shared bw_linear_suffix lemmas
  have hpm47 : (denoteGraph pm_goal_23 initPM) 47 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 26) (initPM 30)).2 := by
    have h := bw_linear_suffix_tid47 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit,
      chunk_prefix_preserves_24 pm_goal_23 initPM,
      chunk_prefix_tid26 pm_goal_23 initPM,
      chunk_prefix_preserves_30 pm_goal_23 initPM] using h
  have hpm49 : (denoteGraph pm_goal_23 initPM) 49 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 27) (initPM 31)).2 := by
    have h := bw_linear_suffix_tid49 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit,
      chunk_prefix_preserves_24 pm_goal_23 initPM,
      chunk_prefix_tid27 pm_goal_23 initPM,
      chunk_prefix_preserves_31 pm_goal_23 initPM] using h
  have hpm51 : (denoteGraph pm_goal_23 initPM) 51 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 28) (initPM 32)).2 := by
    have h := bw_linear_suffix_tid51 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit,
      chunk_prefix_preserves_24 pm_goal_23 initPM,
      chunk_prefix_tid28 pm_goal_23 initPM,
      chunk_prefix_preserves_32 pm_goal_23 initPM] using h
  have hpm53 : (denoteGraph pm_goal_23 initPM) 53 =
      (bw_linear (initPM 24) (denoteGraph pm_goal_23 initPM 29) (initPM 33)).2 := by
    have h := bw_linear_suffix_tid53 pm_goal_23
      (denoteGraph { pm_goal_23 with nodes := chunk_prefix } initPM)
    simpa [hpmSplit,
      chunk_prefix_preserves_24 pm_goal_23 initPM,
      chunk_prefix_tid29 pm_goal_23 initPM,
      chunk_prefix_preserves_33 pm_goal_23 initPM] using h
  -- Shape info using shared lemmas
  have hx20 : (initPM 20).shape = [128, 128] := by
    exact hPmInit 20 [128, 128] (by simp [pm_goal_23InitEnv, pm_goal_23InitShapes, shapeEnvOfList])
  have h24shape : (initPM 24).shape = [128, 128] := by
    exact hPmInit 24 [128, 128] (by simp [pm_goal_23InitEnv, pm_goal_23InitShapes, shapeEnvOfList])
  -- dW shape is [o, shard] = [128, 32] for each rank
  have hshape47 : (denoteGraph pm_goal_23 initPM 47).shape = [128, 32] := by
    rw [hpm47, hpm26]
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 0 (initPM 20)) (initPM 30) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, chunkPrim_shape_128_4 _ _ 0 hx20 rfl⟩ hshape30
  have hnon47 : (denoteGraph pm_goal_23 initPM 47).shape ≠ [1] := by
    intro h; rw [hshape47] at h; cases h
  -- reconstruct = allGather for non-scalar
  have hrec23 := reconstruct_4_nonscalar pm_goal_23.numRanks
    (denoteGraph pm_goal_23 initPM 47) (denoteGraph pm_goal_23 initPM 49)
    (denoteGraph pm_goal_23 initPM 51) (denoteGraph pm_goal_23 initPM 53) hnon47
  -- Additional shard shapes
  have hshape49 : (denoteGraph pm_goal_23 initPM 49).shape = [128, 32] := by
    rw [hpm49, hpm27]
    have h31 := initGoal_16_shape_31 pm_goal_23.numRanks initSM initPM hInit16
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 1 (initPM 20)) (initPM 31) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, chunkPrim_shape_128_4 _ _ 1 hx20 rfl⟩ h31
  have hshape51 : (denoteGraph pm_goal_23 initPM 51).shape = [128, 32] := by
    rw [hpm51, hpm28]
    have h32 := initGoal_16_shape_32 pm_goal_23.numRanks initSM initPM hInit16
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 2 (initPM 20)) (initPM 32) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, chunkPrim_shape_128_4 _ _ 2 hx20 rfl⟩ h32
  have hshape53 : (denoteGraph pm_goal_23 initPM 53).shape = [128, 32] := by
    rw [hpm53, hpm29]
    have h33 := initGoal_16_shape_33 pm_goal_23.numRanks initSM initPM hInit16
    exact bw_linear_snd_shape' (initPM 24) (chunkPrim pm_goal_23.numRanks 3 (initPM 20)) (initPM 33) 128 32
      ⟨128, 128, h24shape⟩ ⟨128, 32, chunkPrim_shape_128_4 _ _ 3 hx20 rfl⟩ h33
  -- SM shape
  have hsm23_shape : (denoteGraph sm_goal_23 initSM 23).shape = [128, 128] := by
    rw [hsm23]
    have hsm16 := hSmInit 16 [128, 128] (by simp [sm_goal_23InitEnv, sm_goal_23InitShapes, shapeEnvOfList])
    have hsm20 := hSmInit 20 [128, 128] (by simp [sm_goal_23InitEnv, sm_goal_23InitShapes, shapeEnvOfList])
    have hsm24 := hSmInit 24 [128, 128] (by simp [sm_goal_23InitEnv, sm_goal_23InitShapes, shapeEnvOfList])
    exact bw_linear_snd_shape 128 128 128 (initSM 24) (initSM 20) (initSM 16) hsm24 hsm20 hsm16
  refine ⟨hsm23_shape, ?shapes, ?values⟩
  case shapes =>
    simp only [hshape47, hshape49, hshape51, hshape53]
  case values =>
    -- Rewrite SM side
    rw [hsm23, h24eq, hrec20, hrec16']
    -- Rewrite PM side
    rw [hrec23]
    -- Apply bw_linear_snd allGather lemma
    have hbw := bw_linear_snd_allGather_eq_allGather_bw_linear_chunk
      (numParts := pm_goal_23.numRanks) (b := 128) (i := 128) (o := 128) (shard := 32)
      (g := initPM 24) (x := initPM 20)
      (ws := [initPM 30, initPM 31, initPM 32, initPM 33])
      (hg := h24shape) (hx := hx20)
      (hi := numRanks_4_128_eq_mul_32 pm_goal_23.numRanks rfl)
      (hws_len := by simp [pm_goal_23]) (hws_shapes := hws_shapes)
      (hparts := by simp [pm_goal_23]) (hshard := by decide)
    -- Connect PM outputs to the RHS of hbw
    have hpm_list :
        [denoteGraph pm_goal_23 initPM 47, denoteGraph pm_goal_23 initPM 49,
         denoteGraph pm_goal_23 initPM 51, denoteGraph pm_goal_23 initPM 53] =
        (List.ofFn (fun r : Fin pm_goal_23.numRanks =>
          (bw_linear (initPM 24)
            (chunkPrim pm_goal_23.numRanks r.val (initPM 20))
            ([initPM 30, initPM 31, initPM 32, initPM 33].get ⟨r.val, by
              simp only [List.length_cons, List.length_nil]; exact r.isLt⟩)).2)) := by
      rw [show (denoteGraph pm_goal_23 initPM 47) = _ from by rw [hpm47, hpm26],
          show (denoteGraph pm_goal_23 initPM 49) = _ from by rw [hpm49, hpm27],
          show (denoteGraph pm_goal_23 initPM 51) = _ from by rw [hpm51, hpm28],
          show (denoteGraph pm_goal_23 initPM 53) = _ from by rw [hpm53, hpm29]]
      rfl
    rw [hpm_list, ← hbw]

end TrainVerify.Denote.ManualProofs
