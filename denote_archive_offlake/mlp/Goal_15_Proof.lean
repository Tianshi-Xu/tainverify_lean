/- Manual proof for Goal 15 (split file). -/
import denote.mlp.GeneratedData
import denote.mlp.Common
import denote.mlp.Goal_15

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.Common
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.ManualProofs

/-!
## Goal 15

Outline:
- Unfold `goal_15_stmt_cut`.
- Unfold `denoteGraph` for `sm_goal_15` and `pm_goal_15`.
- Use `InitGoalsHold` for `initGoals` to relate SM input tensor 16 with PM shards 30..33.
- Use `AllReducePrim` + `ChunkPrim` + `FW_sum` reconstruction lemmas to show equality.
-/

theorem goal_15_proof : goal_15_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  dsimp [goal_15_stmt_cut, CoarseLineageHoldsWithInit, goal_15]
  -- Extract init alignments using shared lemmas
  have hInit16 : InitGoalHolds pm_goal_15.numRanks initGoal_16 initSM initPM := by
    have : initGoal_16 ∈ initGoals := by simp [initGoals]
    exact hInitGoals initGoal_16 this
  have hInit20 : InitGoalHolds pm_goal_15.numRanks initGoal_20 initSM initPM := by
    have : initGoal_20 ∈ initGoals := by simp [initGoals]
    exact hInitGoals initGoal_20 this
  -- Use shared lemmas for reconstruction
  have hrec16' := initGoal_16_rec_allGather pm_goal_15.numRanks initSM initPM hInit16
  have hrec20 := initGoal_20_eq pm_goal_15.numRanks initSM initPM hInit20
  have hws_shapes := initGoal_16_ws_shapes pm_goal_15.numRanks initSM initPM hInit16
  have hshape30 := initGoal_16_shape_30 pm_goal_15.numRanks initSM initPM hInit16
  -- SM store at tid15
  have hsm : (denoteGraph sm_goal_15 initSM) 15 = fw_sum (fw_linear (initSM 20) (initSM 16)) := by
    simp [sm_goal_15, denoteGraph, applyNode_fw_linear_out, applyNode_fw_sum_out]
  -- PM store at tid17: allReduce over per-rank fw_linear on chunked input
  have hpm17 : (denoteGraph pm_goal_15 initPM) 17 =
      allReducePrim pm_goal_15.numRanks 0
        [ fw_linear (chunkPrim pm_goal_15.numRanks 0 (initPM 20)) (initPM 30),
          fw_linear (chunkPrim pm_goal_15.numRanks 1 (initPM 20)) (initPM 31),
          fw_linear (chunkPrim pm_goal_15.numRanks 2 (initPM 20)) (initPM 32),
          fw_linear (chunkPrim pm_goal_15.numRanks 3 (initPM 20)) (initPM 33) ] := by
    simp [pm_goal_15, denoteGraph, List.foldl, applyNode, evalOp, storeSet]
  -- PM store at tid15: allReduce over fw_sum of chunked tid17
  have hpm15 : (denoteGraph pm_goal_15 initPM) 15 =
      allReducePrim pm_goal_15.numRanks 0
        [ fw_sum (chunkPrim pm_goal_15.numRanks 0 (denoteGraph pm_goal_15 initPM 17)),
          fw_sum (chunkPrim pm_goal_15.numRanks 1 (denoteGraph pm_goal_15 initPM 17)),
          fw_sum (chunkPrim pm_goal_15.numRanks 2 (denoteGraph pm_goal_15 initPM 17)),
          fw_sum (chunkPrim pm_goal_15.numRanks 3 (denoteGraph pm_goal_15 initPM 17)) ] := by
    simp [pm_goal_15, denoteGraph, List.foldl, applyNode, evalOp, storeSet]
  -- Relate fw_linear with allReduce of chunked fw_linear
  have hlin : fw_linear (initSM 20) (initSM 16) =
      allReducePrim pm_goal_15.numRanks 0
        (List.ofFn (fun r : Fin pm_goal_15.numRanks =>
          fw_linear (chunkPrim pm_goal_15.numRanks r.val (initPM 20))
            ([initPM 30, initPM 31, initPM 32, initPM 33].get ⟨r.val, by
              simpa [pm_goal_15] using r.isLt⟩))) := by
    have hx : (initSM 20).shape = [128, 128] :=
      initGoal_20_sm_shape pm_goal_15.numRanks initSM initPM hInit20
    have hws_len : ([initPM 30, initPM 31, initPM 32, initPM 33] : List Tensor).length = pm_goal_15.numRanks := by
      simp [pm_goal_15]
    have hparts : 0 < pm_goal_15.numRanks := by simp [pm_goal_15]
    have hshard : 0 < 32 := by decide
    have hlin' := fw_linear_allGather_eq_allReduce_fw_linear_chunk
      (numParts := pm_goal_15.numRanks) (b := 128) (i := 128) (o := 128) (shard := 32)
      (x := initSM 20) (ws := [initPM 30, initPM 31, initPM 32, initPM 33])
      (hx := hx) (hi := by decide) (hws_len := hws_len) (hws_shapes := hws_shapes)
      (hparts := hparts) (hshard := hshard)
    simpa [hrec16', hrec20] using hlin'
  -- Conclude shapes and value equality
  refine And.intro ?shapeSM ?rest
  · rw [hsm]; exact fw_sum_shape _
  · refine And.intro ?shapePM ?eqval
    · -- tps shapes: singleton pm tid15 has shape [1]
      rw [hpm15]
      have hhead :
          ([ fw_sum (chunkPrim pm_goal_15.numRanks 0 (denoteGraph pm_goal_15 initPM 17)),
             fw_sum (chunkPrim pm_goal_15.numRanks 1 (denoteGraph pm_goal_15 initPM 17)),
             fw_sum (chunkPrim pm_goal_15.numRanks 2 (denoteGraph pm_goal_15 initPM 17)),
             fw_sum (chunkPrim pm_goal_15.numRanks 3 (denoteGraph pm_goal_15 initPM 17)) ].head?) =
            some (fw_sum (chunkPrim pm_goal_15.numRanks 0 (denoteGraph pm_goal_15 initPM 17))) := by
        rfl
      have hshape : (allReducePrim pm_goal_15.numRanks 0
          [ fw_sum (chunkPrim pm_goal_15.numRanks 0 (denoteGraph pm_goal_15 initPM 17)),
            fw_sum (chunkPrim pm_goal_15.numRanks 1 (denoteGraph pm_goal_15 initPM 17)),
            fw_sum (chunkPrim pm_goal_15.numRanks 2 (denoteGraph pm_goal_15 initPM 17)),
            fw_sum (chunkPrim pm_goal_15.numRanks 3 (denoteGraph pm_goal_15 initPM 17)) ]).shape =
          (fw_sum (chunkPrim pm_goal_15.numRanks 0 (denoteGraph pm_goal_15 initPM 17))).shape :=
        allReducePrim_shape _ _ _ _ hhead
      simp [hshape, fw_sum_shape]
    · -- value equality: show SM=PM at tid=15
      have hpm15' : (denoteGraph pm_goal_15 initPM) 15 =
          fw_sum (denoteGraph pm_goal_15 initPM 17) := by
        have hparts : 0 < pm_goal_15.numRanks := by simp [pm_goal_15]
        have hshape26 : (chunkPrim pm_goal_15.numRanks 0 (initPM 20)).shape = [128, 32] := by
          have hx20 : (initPM 20).shape = [128, 128] := by
            simpa [initGoal_20, hrec20] using hInit20.1
          have hparts' : 0 < pm_goal_15.numRanks := by simp [pm_goal_15]
          simpa [pm_goal_15] using (chunkPrim_shape' pm_goal_15.numRanks 0 128 32 (initPM 20)
            (by simpa [pm_goal_15] using hx20) hparts')
        have hshape17 : ((denoteGraph pm_goal_15 initPM) 17).shape = [128, 128] := by
          have hhead :
              ([ fw_linear (chunkPrim pm_goal_15.numRanks 0 (initPM 20)) (initPM 30),
                 fw_linear (chunkPrim pm_goal_15.numRanks 1 (initPM 20)) (initPM 31),
                 fw_linear (chunkPrim pm_goal_15.numRanks 2 (initPM 20)) (initPM 32),
                 fw_linear (chunkPrim pm_goal_15.numRanks 3 (initPM 20)) (initPM 33) ].head?) =
                some (fw_linear (chunkPrim pm_goal_15.numRanks 0 (initPM 20)) (initPM 30)) := by
            rfl
          have hshape_fw : (fw_linear (chunkPrim pm_goal_15.numRanks 0 (initPM 20)) (initPM 30)).shape = [128, 128] :=
            fw_linear_shape 128 32 128 (chunkPrim pm_goal_15.numRanks 0 (initPM 20)) (initPM 30)
              hshape26 (by simpa using hshape30)
          have hshape_ar := allReducePrim_shape pm_goal_15.numRanks 0
            [ fw_linear (chunkPrim pm_goal_15.numRanks 0 (initPM 20)) (initPM 30),
              fw_linear (chunkPrim pm_goal_15.numRanks 1 (initPM 20)) (initPM 31),
              fw_linear (chunkPrim pm_goal_15.numRanks 2 (initPM 20)) (initPM 32),
              fw_linear (chunkPrim pm_goal_15.numRanks 3 (initPM 20)) (initPM 33) ]
            (fw_linear (chunkPrim pm_goal_15.numRanks 0 (initPM 20)) (initPM 30)) hhead
          simpa [hpm17, hshape_fw] using hshape_ar
        have hshape17' : (denoteGraph pm_goal_15 initPM 17).shape = [128, pm_goal_15.numRanks * 32] := by
          simpa [pm_goal_15] using hshape17
        have hsum := fw_sum_eq_allReduce_fw_sum_chunkPrim
          (numParts := pm_goal_15.numRanks) (b := 128) (shard := 32)
          (x := denoteGraph pm_goal_15 initPM 17) (hshape := by
            simpa [pm_goal_15] using hshape17') (hparts := hparts)
        simpa [hpm15, pm_goal_15, List.ofFn] using hsum.symm
      -- Use hlin and hpm17 to align tid17
      have h17 : fw_linear (initSM 20) (initSM 16) = denoteGraph pm_goal_15 initPM 17 := by
        simpa [hpm17, hlin, hrec20, pm_goal_15, List.ofFn] using hlin
      simp [reconstruct, hsm, hpm15', h17]

end TrainVerify.Denote.ManualProofs
