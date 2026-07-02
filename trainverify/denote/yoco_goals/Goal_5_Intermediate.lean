/- goal_5_intermediate — needed by downstream goals that list goal_5 in their prereqs.
   Uses the already-hand-proven `prove_goal_5 : goal_5_stmt` from Pattern_5.lean.
-/
import denote.yoco_goals.Pattern_5

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedGoals

open TrainVerify.Denote TrainVerify.Denote.Generated

theorem goal_5_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_5 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_5_stmt := TrainVerify.Denote.GeneratedPatterns.prove_goal_5
  have := hfull initSM initPM hSM hPM hInit
  unfold InitGoalHolds
  simp only [goal_5]
  exact this

end TrainVerify.Denote.GeneratedGoals
