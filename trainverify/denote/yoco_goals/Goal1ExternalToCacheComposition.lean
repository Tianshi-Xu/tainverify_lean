/- Goal 1 external-input ancestry through the shared K/V cache source. -/
import denote.yoco_goals.CanonicalGoal1ExternalL0Composition
import denote.yoco_goals.Goal1L1L11CacheComposition

set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

/-- Full faithful ordinary ancestry from independent external/init contracts to
the pre-shuffle shared K/V cache source. No computed relation is exposed to the
caller. -/
theorem goal1_external_to_cache_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024] := by
  have hL0 := goal1_external_l0_faithful_composition initSM initPM hSM hPM hInit
  exact goal1_l1_l11_cache_faithful_composition initSM initPM hSM hPM hInit hL0

#print axioms goal1_external_to_cache_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
