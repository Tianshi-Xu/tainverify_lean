/-
Auto-generated proof template for the denotational spec.

- This file is meant to be edited by humans.
- It is generated only when --emit-spec-template is passed.
- Proofs are left as `sorry` stubs initially.
-/
import trainverify.denote.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedSpec

/-!
## Shape gate

These are computable checks (proved by native_decide in GeneratedData).
-/
theorem sm_shape_ok : smShapeCheck.isOk := by
  simpa using smShapeCheck_ok

theorem pm_shape_ok : pmShapeCheck.isOk := by
  simpa using pmShapeCheck_ok

theorem prove_goal_15 : goal_15_stmt := by
  classical
  -- Shape gate (computable, proved in GeneratedData via native_decide):
  have _hSm : smShapeCheck.isOk := sm_shape_ok
  have _hPm : pmShapeCheck.isOk := pm_shape_ok

  -- Expand the statement into concrete obligations.
  unfold goal_15_stmt CoarseLineageHoldsWithInit
  intro initSM initPM hSmInitShapes hPmInitShapes hInitGoals

  -- Extract the init-goal alignments we need (inputs and weights).
  -- Avoid `simp [initGoals]` here: it triggers large `DecidableEq` reductions on `LineageGoal`.
  have hmem16 : initGoal_16 ∈ initGoals := by
    unfold initGoals
    exact List.mem_cons_self _ _
  have hmem20 : initGoal_20 ∈ initGoals := by
    unfold initGoals
    -- `initGoal_20` is in the tail.
    exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)

  have hInit20 : InitGoalHolds pm.numRanks initGoal_20 initSM initPM :=
    hInitGoals initGoal_20 hmem20
  have hInit16 : InitGoalHolds pm.numRanks initGoal_16 initSM initPM :=
    hInitGoals initGoal_16 hmem16

  have hxEq : initSM 20 = initPM 20 := by
    rcases hInit20 with ⟨_hshTs, _hshTps, hval⟩
    simpa [initGoal_20, reconstruct] using hval

  have hwEq : initSM 16 = reconstruct pm.numRanks 0
      [initPM 34, initPM 35, initPM 36, initPM 37, initPM 38, initPM 39, initPM 40, initPM 41] := by
    rcases hInit16 with ⟨_hshTs, _hshTps, hval⟩
    simpa [initGoal_16] using hval

  -- Main proof (performance note):
  -- Do NOT do `simp [denoteGraph, applyNode, storeSet, ...]` on the whole goal: it unfolds
  -- the entire graph and kernel definitions, producing a giant term and heartbeats timeout.
  --
  -- Next step is to prove the goal by *tracing only the relevant tids* using the existing
  -- store-preservation lemmas (e.g. `applyNode_eq_of_not_mem_outs`,
  -- `denoteGraph_tid_eq_of_forall_not_mem_outs`, and the generated
  -- `pm_tid_90..97_eq_prefix_goal_15`), then discharge the remaining pure algebraic equality
  -- using `List.foldl_add_eq_sum` and `Finset.sum_range_mul_eq_sum_sum`.
  --
  -- Keeping this proof fast and readable requires adding a few targeted lemmas about:
  -- (1) `fw_sum (chunkPrim ...)` summing to a slice of the parent tensor,
  -- (2) `fw_sum (allReducePrim ...)` distributing over the fold.
  -- I'll add those next and then finish this theorem without global simp.
  
  -- TODO: finish (value-level equivalence).
  sorry

  -- Common next steps (uncomment as needed):
  -- simp [InitGoalsHold, InitGoalHolds] at hInitGoals
  -- simp [denoteGraph_nodes_cons, denoteGraph_nodes_nil]
  -- simp [valAt_of_fin]
  -- simp [applyNode, storeSet]  -- or use storeSet_eq_of_find?_some/none


theorem prove_goal_21 : goal_21_stmt := by
  classical
  -- Shape gate (computable, proved in GeneratedData via native_decide):
  have _hSm : smShapeCheck.isOk := sm_shape_ok
  have _hPm : pmShapeCheck.isOk := pm_shape_ok

  -- Expand the statement into concrete obligations.
  unfold goal_21_stmt CoarseLineageHoldsWithInit
  intro initSM initPM hSmInitShapes hPmInitShapes hInitGoals

  -- Common next steps (uncomment as needed):
  -- simp [InitGoalsHold, InitGoalHolds] at hInitGoals
  -- simp [denoteGraph_nodes_cons, denoteGraph_nodes_nil]
  -- simp [valAt_of_fin]
  -- simp [applyNode, storeSet]  -- or use storeSet_eq_of_find?_some/none
  sorry

theorem prove_goal_23 : goal_23_stmt := by
  classical
  -- Shape gate (computable, proved in GeneratedData via native_decide):
  have _hSm : smShapeCheck.isOk := sm_shape_ok
  have _hPm : pmShapeCheck.isOk := pm_shape_ok

  -- Expand the statement into concrete obligations.
  unfold goal_23_stmt CoarseLineageHoldsWithInit
  intro initSM initPM hSmInitShapes hPmInitShapes hInitGoals

  -- Common next steps (uncomment as needed):
  -- simp [InitGoalsHold, InitGoalHolds] at hInitGoals
  -- simp [denoteGraph_nodes_cons, denoteGraph_nodes_nil]
  -- simp [valAt_of_fin]
  -- simp [applyNode, storeSet]  -- or use storeSet_eq_of_find?_some/none
  sorry

theorem prove_all_goals : all_goals_stmt := by
  -- After proving each prove_goal_*, you can finish by cases on membership in goals.
  sorry

end TrainVerify.Denote.GeneratedSpec
