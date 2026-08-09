/- L9 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL9OrdinaryAttention
import denote.yoco_goals.L9OrdinaryMoEComposition

set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

/-- From the sole incoming faithful ordinary boundary, reconstruct L9 attention
and the complete MoE residual tail internally. -/
theorem l9_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9231)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5485)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9394)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9395)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l9o_residual5452_rel_from_boundary5430
    initSM initPM hInit hBoundary
  exact l9_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l9_ordinary_faithful_composition

end TrainVerify.Denote.GeneratedPatterns
