/- goal_5_intermediate — needed by downstream goals that list goal_5 in their prereqs.
   Uses Pattern_5's `prove_goal_5 : goal_5_stmt_cut` + `goal_5_cut_to_full` bridge.
-/
import denote.yoco_goals.Pattern_5
import denote.yoco_goals.Goal_5_CutToFull

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedGoals

open TrainVerify.Denote TrainVerify.Denote.Generated

theorem goal_5_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_5 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hcut : goal_5_stmt_cut := TrainVerify.Denote.GeneratedPatterns.prove_goal_5
  have hfull : goal_5_stmt := goal_5_cut_to_full hcut
  have := hfull initSM initPM hSM hPM hInit
  unfold InitGoalHolds
  simp only [goal_5]
  exact this

end TrainVerify.Denote.GeneratedGoals
