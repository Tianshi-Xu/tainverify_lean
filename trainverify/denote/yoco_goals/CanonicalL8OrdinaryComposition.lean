/- L8 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL8OrdinaryAttention
import denote.yoco_goals.L8OrdinaryMoEComposition

set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

/-- Reconstruct L8 attention and MoE internally from its sole faithful incoming boundary. -/
theorem l8_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5375)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9066)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9067)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9231)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l8o_residual5397_rel_from_boundary5375
    initSM initPM hInit hBoundary
  exact l8_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l8_ordinary_faithful_composition

end TrainVerify.Denote.GeneratedPatterns
