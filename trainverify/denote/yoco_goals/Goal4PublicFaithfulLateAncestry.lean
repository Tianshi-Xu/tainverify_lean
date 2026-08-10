/- Assemble Goal 4 late routing ancestry from per-layer faithful checkpoints. -/
import denote.yoco_goals.Goal4PublicFaithfulL23Checkpoint

set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

theorem goal4_late_ancestry_of_external
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) :
    Goal4RoutingLateAncestry initSM initPM := by
  have mid := goal4_l23_checkpoint_of_external initSM initPM hSM hPM hInit hContract
  exact {
    l12 := mid.base.base.base.base.base.base.base.base.base.base.base.base.base.l12
    l13 := mid.base.base.base.base.base.base.base.base.base.base.base.l13
    l14 := mid.base.base.base.base.base.base.base.base.base.base.base.l14
    l15 := mid.base.base.base.base.base.base.base.base.base.base.l15
    l16 := mid.base.base.base.base.base.base.base.base.base.l16
    l17 := mid.base.base.base.base.base.base.base.base.l17
    l18 := mid.base.base.base.base.base.base.base.l18
    l19 := mid.base.base.base.base.base.base.l19
    l20 := mid.base.base.base.base.base.l20
    l21 := mid.base.base.base.base.l21
    l22 := mid.base.base.l22
    l23 := mid.l23
  }
end TrainVerify.Denote.GeneratedPatterns
