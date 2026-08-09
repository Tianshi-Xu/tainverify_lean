/- Goal 1 external-input through complete L0 faithful ordinary composition. -/
import denote.yoco_goals.CanonicalL0OrdinaryAttention
import denote.yoco_goals.L0OrdinaryMoEComposition
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

theorem goal1_external_l0_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7918)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7919)
      [4096, 1024] [2048, 1024] := by
  have hAttention := canonical_l0_residual4957_rel initSM initPM hSM hPM hInit
  exact l0_ordinary_moe_composition initSM initPM hSM hPM hInit hAttention

#print axioms goal1_external_l0_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
