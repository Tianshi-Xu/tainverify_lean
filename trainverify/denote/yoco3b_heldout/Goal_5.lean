import denote.GeneratedYOCO3B

open TrainVerify.Denote

namespace TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal5

def goal_5_full_initGoals : List LineageGoal := Generated.initGoals

/-- Exact caller-facing full statement; this early RMS target needs no extra value contract. -/
def goal_5_stmt_full : Prop :=
  CoarseLineageHoldsWithInit
    Generated.sm Generated.pm Generated.goal_5
    Generated.smInitEnv Generated.pmInitEnv goal_5_full_initGoals

end TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal5
