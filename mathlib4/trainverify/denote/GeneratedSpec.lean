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
