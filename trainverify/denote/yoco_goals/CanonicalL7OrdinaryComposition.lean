/- L7 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL7OrdinaryAttention
import denote.yoco_goals.L7OrdinaryMoEComposition

set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

/-- Reconstruct L7 attention and MoE internally from its sole faithful incoming boundary. -/
theorem l7_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8902)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8903)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5375)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9066)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9067)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l7o_residual5342_rel_from_boundary5320
    initSM initPM hInit hBoundary
  exact l7_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l7_ordinary_faithful_composition

end TrainVerify.Denote.GeneratedPatterns
