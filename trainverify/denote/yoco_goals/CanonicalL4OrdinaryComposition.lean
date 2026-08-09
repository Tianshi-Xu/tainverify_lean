/- L4 faithful ordinary full-layer composition. -/
import denote.yoco_goals.CanonicalL4OrdinaryAttention
import denote.yoco_goals.L4OrdinaryMoEComposition
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

theorem l4_ordinary_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8410)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8411)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8574)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8575)
      [4096, 1024] [2048, 1024] := by
  have hAttention := l4o_residual5177_rel_from_boundary5155 initSM initPM hInit hBoundary
  exact l4_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms l4_ordinary_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
