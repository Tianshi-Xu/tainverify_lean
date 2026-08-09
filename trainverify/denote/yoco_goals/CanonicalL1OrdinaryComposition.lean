/- L1 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL1OrdinaryAttention
import denote.yoco_goals.L1OrdinaryMoEComposition
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

theorem l1_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7918)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7919)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5045)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8082)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8083)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l1o_residual5012_rel_from_boundary4990 initSM initPM hInit hBoundary
  exact l1_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l1_ordinary_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
