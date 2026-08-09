/- L3 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL3OrdinaryAttention
import denote.yoco_goals.L3OrdinaryMoEComposition
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

theorem l3_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8247)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8410)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8411)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l3o_residual5122_rel_from_boundary5100 initSM initPM hInit hBoundary
  exact l3_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l3_ordinary_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
