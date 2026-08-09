/- Goal 1 faithful ordinary backbone from L1 through L11 and the cache block. -/
import denote.yoco_goals.CanonicalL1OrdinaryComposition
import denote.yoco_goals.CanonicalL2OrdinaryComposition
import denote.yoco_goals.CanonicalL3OrdinaryComposition
import denote.yoco_goals.CanonicalL4OrdinaryComposition
import denote.yoco_goals.CanonicalL5OrdinaryComposition
import denote.yoco_goals.CanonicalL6OrdinaryComposition
import denote.yoco_goals.CanonicalL7OrdinaryComposition
import denote.yoco_goals.CanonicalL8OrdinaryComposition
import denote.yoco_goals.CanonicalL9OrdinaryComposition
import denote.yoco_goals.L10OrdinaryMoEComposition
import denote.yoco_goals.CanonicalL11OrdinaryAttention
import denote.yoco_goals.CanonicalKVCacheOrdinaryComposition

set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

/-- Compose every faithful ordinary layer after L0 through the shared K/V cache
source. The only computed input is the output boundary of the separately closed
external-through-L0 theorem. -/
theorem goal1_l1_l11_cache_faithful_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hBoundary4990 : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7918)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7919)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024] := by
  have hL1 := l1_ordinary_faithful_composition initSM initPM hSM hPM hInit hBoundary4990
  have hL2 := l2_ordinary_faithful_composition initSM initPM hSM hPM hInit hL1
  have hL3 := l3_ordinary_faithful_composition initSM initPM hSM hPM hInit hL2
  have hL4 := l4_ordinary_faithful_composition initSM initPM hSM hPM hInit hL3
  have hL5 := l5_ordinary_faithful_composition initSM initPM hSM hPM hInit hL4
  have hL6 := l6_ordinary_faithful_composition initSM initPM hSM hPM hInit hL5
  have hL7 := l7_ordinary_faithful_composition initSM initPM hSM hPM hInit hL6
  have hL8 := l8_ordinary_faithful_composition initSM initPM hSM hPM hInit hL7
  have hL9 := l9_ordinary_faithful_composition initSM initPM hSM hPM hInit hL8
  have hL10 := l10_ordinary_faithful_composition initSM initPM hSM hPM hInit hL9
  have hL11 := l11o_residual5562_rel_from_boundary5540 initSM initPM hInit hL10
  exact canonical_kv_cache_ordinary_composition initSM initPM hSM hPM hInit hL11

#print axioms goal1_l1_l11_cache_faithful_composition
end TrainVerify.Denote.GeneratedPatterns
