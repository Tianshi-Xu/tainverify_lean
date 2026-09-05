import denote.yoco3b_heldout.Goal_1
import denote.yoco3b_heldout.Goal_2
import denote.yoco3b_heldout.Goal_3
import denote.yoco3b_heldout.Goal_4
import denote.yoco3b_heldout.Goal_5

namespace TrainVerify.Denote.GeneratedYOCO3BHeldout

/-- Exact public statement authority for the five pinned caller-facing YOCO-3B
    statements.  The generated whole-model `Main` theorem proves this proposition. -/
def all_goals_stmt_full : Prop :=
  TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal1.goal_1_stmt_full ∧
  TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal2.goal_2_stmt_full ∧
  TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal3.goal_3_stmt_full ∧
  TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal4.goal_4_stmt_full ∧
  TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal5.goal_5_stmt_full

end TrainVerify.Denote.GeneratedYOCO3BHeldout
