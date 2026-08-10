/- Production snapshot aggregate.  Public proofs are materialized at the
   canonical Pattern_N module paths by the sealed proof registry. -/
import denote.yoco_goals.Pattern_1
import denote.yoco_goals.Pattern_2
import denote.yoco_goals.Pattern_3
import denote.yoco_goals.Pattern_4
import denote.yoco_goals.Pattern_5

open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.GeneratedPatternInstances

theorem prove_goal_1_from_pattern_1 : goal_1_stmt_full := prove_pattern_1
theorem prove_goal_2_from_pattern_2 : goal_2_stmt_full :=
  prove_pattern_2 pattern_2_target.goal_2
theorem prove_goal_3_from_pattern_3 : goal_3_stmt_full := prove_pattern_3
theorem prove_goal_4_from_pattern_4 : goal_4_stmt_full :=
  Goal4PublicFaithful.prove_pattern_4
theorem prove_goal_5_from_pattern_5 : goal_5_stmt_full :=
  prove_pattern_5 pattern_5_target.goal_5

end TrainVerify.Denote.GeneratedPatternInstances