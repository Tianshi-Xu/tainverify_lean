/- Auto-generated pattern instances.
   These theorems instantiate reusable Pattern_N proofs to concrete goals.
   They intentionally avoid importing Goal_N cut-proof files; the all-goals
   theorem is meant to depend on reusable pattern proofs only.
-/
import denote.yoco3b_goals.Pattern_1
import denote.yoco3b_goals.Pattern_2
import denote.yoco3b_goals.Pattern_3
import denote.yoco3b_goals.Pattern_4
import denote.yoco3b_goals.Pattern_5

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.GeneratedPatternInstances

theorem prove_goal_1_from_pattern_1 : goal_1_stmt := by
  exact prove_pattern_1 pattern_1_target.goal_1

theorem prove_goal_2_from_pattern_2 : goal_2_stmt := by
  exact prove_pattern_2 pattern_2_target.goal_2

theorem prove_goal_3_from_pattern_3 : goal_3_stmt := by
  exact prove_pattern_3 pattern_3_target.goal_3

theorem prove_goal_4_from_pattern_4 : goal_4_stmt := by
  exact prove_pattern_4 pattern_4_target.goal_4

theorem prove_goal_5_from_pattern_5 : goal_5_stmt := by
  exact prove_pattern_5 pattern_5_target.goal_5

end TrainVerify.Denote.GeneratedPatternInstances

