/- L2 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL2OrdinaryAttention
import denote.yoco_goals.L2OrdinaryMoEComposition
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

theorem l2_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5045)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8082)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8083)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8247)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l2o_residual5067_rel_from_boundary5045 initSM initPM hInit hBoundary
  exact l2_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l2_ordinary_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
