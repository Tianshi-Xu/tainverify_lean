import denote.GeneratedYOCO3B

open TrainVerify.Denote

namespace TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal4

def goal_4_full_initGoals : List LineageGoal := Generated.initGoals

/-- Exact caller-facing full statement; this early float target needs no extra value contract. -/
def goal_4_stmt_full : Prop :=
  CoarseLineageHoldsWithInit
    Generated.sm Generated.pm Generated.goal_4
    Generated.smInitEnv Generated.pmInitEnv goal_4_full_initGoals

end TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal4
