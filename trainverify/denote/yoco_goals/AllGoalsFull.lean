/- Public statement authority for the five exact YOCO-MoE-A0.4B targets.
   The separately generated whole-model `Main` theorem proves this proposition. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.Goal_2
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.Goal_4
import denote.yoco_goals.Goal_5

namespace TrainVerify.Denote.GeneratedGoals

/-- The selected public obligation is exactly the conjunction of the five
ancestry-closed target statements. -/
def all_goals_stmt_full : Prop :=
  goal_1_stmt_full ∧
  goal_2_stmt_full ∧
  goal_3_stmt_full ∧
  goal_4_stmt_full ∧
  goal_5_stmt_full

end TrainVerify.Denote.GeneratedGoals
