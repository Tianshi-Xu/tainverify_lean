/- L5 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL5OrdinaryAttention
import denote.yoco_goals.L5OrdinaryMoEComposition
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

theorem l5_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8574)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8575)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5265)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8739)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l5o_residual5232_rel_from_boundary5210 initSM initPM hInit hBoundary
  exact l5_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l5_ordinary_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
