/- Goal 3 -> Goal 1 finite input-shape/init bridge for the L12--L23 ancestry. -/
import denote.yoco_goals.Goal3L0L11RoutingCertificate

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

/-- The finite Goal-1 leaf environments consumed by the ancestry proof.  These
are lists of input TID/shape pairs, not claims about computed graph values. -/
def goal1AncestryRequiredSmShapes : List (Tid × Shape) := sm_goal_1InitShapes

def goal1AncestryRequiredPmShapes : List (Tid × Shape) := pm_goal_1InitShapes

/-- Input-only shape and init facts needed to run the Goal-1 ancestry inside the
Goal-3 closure.  The fields deliberately expose only the finite Goal-1 leaf
environments plus the generated init-goal family. -/
structure Goal1AncestryShapeInitFacts (initSM initPM : Store) : Prop where
  sm_shapes : StoreShapesHold initSM
    (shapeEnvOfList goal1AncestryRequiredSmShapes)
  pm_shapes : StoreShapesHold initPM
    (shapeEnvOfList goal1AncestryRequiredPmShapes)
  init_goals : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM

/-- Every SM leaf shape used by Goal-1 ancestry is present, with the same shape,
in Goal 3's generated full input environment. -/
theorem goal1_ancestry_sm_shapes_covered_by_goal3 :
    ∀ p ∈ goal1AncestryRequiredSmShapes,
      shapeEnvOfList smInitShapes p.1 = some p.2 := by
  native_decide

/-- Every PM leaf shape used by Goal-1 ancestry is present, with the same shape,
in Goal 3's generated full input environment. -/
theorem goal1_ancestry_pm_shapes_covered_by_goal3 :
    ∀ p ∈ goal1AncestryRequiredPmShapes,
      shapeEnvOfList pmInitShapes p.1 = some p.2 := by
  native_decide

/-- Goal 3 and Goal 1 use the same finite generated init-goal family and rank
count.  This certificate is kept separate from the shape coverage facts. -/
theorem goal3_goal1_ancestry_init_scope :
    pm.numRanks = pm_goal_1.numRanks ∧ initGoals = goal_1_full_initGoals := by
  native_decide

/-- Restrict Goal 3's full input shape/init assumptions to exactly the finite
leaf environments expected by Goal-1's L12--L23 ancestry.  No tensor value and
no computed-store relation is introduced by this bridge. -/
theorem goal3_to_goal1_ancestry_shape_init
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Goal1AncestryShapeInitFacts initSM initPM := by
  refine {
    sm_shapes := ?_
    pm_shapes := ?_
    init_goals := ?_
  }
  · exact storeShapesHold_weaken goal1_ancestry_sm_shapes_covered_by_goal3 hSM
  · exact storeShapesHold_weaken goal1_ancestry_pm_shapes_covered_by_goal3 hPM
  · rw [← goal3_goal1_ancestry_init_scope.1,
      ← goal3_goal1_ancestry_init_scope.2]
    exact hInit

#print axioms goal1_ancestry_sm_shapes_covered_by_goal3
#print axioms goal1_ancestry_pm_shapes_covered_by_goal3
#print axioms goal3_goal1_ancestry_init_scope
#print axioms goal3_to_goal1_ancestry_shape_init

end
end TrainVerify.Denote.GeneratedPatterns
