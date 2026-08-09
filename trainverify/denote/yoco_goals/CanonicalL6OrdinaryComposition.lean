/- L6 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL6OrdinaryAttention
import denote.yoco_goals.L6OrdinaryMoEComposition

set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

/-- Reconstruct L6 attention and MoE internally from its sole faithful incoming boundary. -/
theorem l6_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5265)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8739)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8902)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8903)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l6o_residual5287_rel_from_boundary5265
    initSM initPM hInit hBoundary
  exact l6_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l6_ordinary_faithful_composition

end TrainVerify.Denote.GeneratedPatterns
