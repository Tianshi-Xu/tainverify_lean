/- Public faithful theorem for the complete Goal 1 statement. -/
import denote.yoco_goals.Goal1ExternalFinalComposition

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote.GeneratedGoals

/-- Goal 1 under the production faithful distributed evaluator. -/
theorem prove_goal_1_stmt_full : goal_1_stmt_full :=
  canonical_goal_1_external

/-- Public Pattern-1 entry point.  This name formerly exposed the local
plain-denotation pattern contract; it now exposes exactly `goal_1_stmt_full`. -/
theorem prove_pattern_1 : goal_1_stmt_full :=
  canonical_goal_1_external

#print axioms prove_goal_1_stmt_full
#print axioms prove_pattern_1

end TrainVerify.Denote.GeneratedPatterns
