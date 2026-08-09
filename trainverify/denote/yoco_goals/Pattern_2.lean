/- Pattern 2: canonical full faithful Goal-2 theorem. -/
import denote.yoco_goals.Goal2FaithfulFull

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote.GeneratedGoals

def pattern_2_goalIds : List Nat := [2]

inductive pattern_2_target : Prop → Prop
  | goal_2 : pattern_2_target goal_2_stmt_full

def pattern_2_stmt : Prop :=
  ∀ {target : Prop}, pattern_2_target target → target

/-- Public Pattern-2 entry point.  Unlike the retired slice proof, this exports
exactly the generated full faithful theorem and reconstructs every computed
boundary from the external/init contract. -/
theorem prove_pattern_2 : pattern_2_stmt := by
  intro _ hpat
  cases hpat
  exact canonical_goal_2_external

#print axioms prove_pattern_2

end TrainVerify.Denote.GeneratedPatterns
