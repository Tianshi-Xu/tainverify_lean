import denote.GeneratedYOCO3B

open TrainVerify.Denote

namespace TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal3

def goal_3_full_initGoals : List LineageGoal := Generated.initGoals

/-- Exact caller-facing full statement; this early embedding target needs no extra value contract. -/
def goal_3_stmt_full : Prop :=
  CoarseLineageHoldsWithInit
    Generated.sm Generated.pm Generated.goal_3
    Generated.smInitEnv Generated.pmInitEnv goal_3_full_initGoals

end TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal3
