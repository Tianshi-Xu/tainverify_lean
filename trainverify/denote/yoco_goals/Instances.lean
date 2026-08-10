/- Honest public pattern instances.

   All five goals expose their ancestry-closed faithful full statements.

   The legacy Pattern-3 cut development is intentionally absent from this
   import graph.  Its ring theorem remains isolated under an explicit legacy
   name; this aggregate imports `Goal3PublicFaithful`, whose theorem has exactly
   type `goal_3_stmt_full`. -/
import denote.yoco_goals.Goal1PublicFaithful
import denote.yoco_goals.Pattern_2
import denote.yoco_goals.Goal3PublicFaithful
import denote.yoco_goals.Goal4PublicFaithful
import denote.yoco_goals.Pattern_5

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.GeneratedPatternInstances

/-- Goal 1's public production theorem, with the exact generated full type. -/
theorem prove_goal_1_from_pattern_1 : goal_1_stmt_full :=
  prove_pattern_1

/-- Goal 2's public production theorem, with the exact generated full type. -/
theorem prove_goal_2_from_pattern_2 : goal_2_stmt_full :=
  prove_pattern_2 pattern_2_target.goal_2

/-- Goal 3's public production theorem.  This resolves the old same-name clash
by importing only the faithful public entry point, never legacy `Pattern_3`. -/
theorem prove_goal_3_from_pattern_3 : goal_3_stmt_full :=
  prove_pattern_3

/-- Goal 4's public production theorem, with the exact faithful full type. -/
theorem prove_goal_4_from_pattern_4 : goal_4_stmt_full :=
  Goal4PublicFaithful.prove_pattern_4

/-- Goal 5's graph is already ancestry-closed; its compatibility cut name is
not used by this public aggregate. -/
theorem prove_goal_5_from_pattern_5 : goal_5_stmt_full :=
  prove_pattern_5 pattern_5_target.goal_5

#print axioms prove_goal_1_from_pattern_1
#print axioms prove_goal_2_from_pattern_2
#print axioms prove_goal_3_from_pattern_3
#print axioms prove_goal_4_from_pattern_4
#print axioms prove_goal_5_from_pattern_5

end TrainVerify.Denote.GeneratedPatternInstances
