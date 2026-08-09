/- Goal 4 L12--L23: ancestry-derived faithful unshuffle certificate. -/
import denote.yoco_goals.CanonicalGoal4L12Routing
import denote.yoco_goals.CanonicalGoal4L13Routing
import denote.yoco_goals.CanonicalGoal4L14Routing
import denote.yoco_goals.CanonicalGoal4L15Routing
import denote.yoco_goals.CanonicalGoal4L16Routing
import denote.yoco_goals.CanonicalGoal4L17Routing
import denote.yoco_goals.CanonicalGoal4L18Routing
import denote.yoco_goals.CanonicalGoal4L19Routing
import denote.yoco_goals.CanonicalGoal4L20Routing
import denote.yoco_goals.CanonicalGoal4L21Routing
import denote.yoco_goals.CanonicalGoal4L22Routing
import denote.yoco_goals.CanonicalGoal4L23Routing

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

noncomputable section

/-- The twelve pre-unshuffle gate-score relations reconstructed by Goal 4
ancestry.  This package is internal proof plumbing, not an external-input
contract: the public closure must construct it from graph ancestry. -/
structure Goal4RoutingLateAncestry (initSM initPM : Store) : Prop where
  l12 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5628)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9833)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5656) [4096, 64] [2048, 64]
  l13 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5682)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9987)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5710) [4096, 64] [2048, 64]
  l14 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5736)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10141)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5764) [4096, 64] [2048, 64]
  l15 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5790)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10295)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5818) [4096, 64] [2048, 64]
  l16 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5844)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10449)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5872) [4096, 64] [2048, 64]
  l17 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5898)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10603)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5926) [4096, 64] [2048, 64]
  l18 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5952)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10757)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5980) [4096, 64] [2048, 64]
  l19 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6006)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10911)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 6034) [4096, 64] [2048, 64]
  l20 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6060)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11065)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 6088) [4096, 64] [2048, 64]
  l21 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6114)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11219)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 6142) [4096, 64] [2048, 64]
  l22 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6168)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11373)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 6196) [4096, 64] [2048, 64]
  l23 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6222)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11527)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 6250) [4096, 64] [2048, 64]

/-- The twelve ordinary post-unshuffle routing relations consumed by the real
Goal 4 routing stack. -/
structure Goal4RoutingLateCertificate (initSM initPM : Store) : Prop where
  l12 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5657)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9910)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9911) [4096, 64] [2048, 64]
  l13 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5711)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10064)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10065) [4096, 64] [2048, 64]
  l14 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5765)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10218)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10219) [4096, 64] [2048, 64]
  l15 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5819)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10372)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10373) [4096, 64] [2048, 64]
  l16 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5873)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10526)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10527) [4096, 64] [2048, 64]
  l17 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5927)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10680)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10681) [4096, 64] [2048, 64]
  l18 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5981)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10834)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10835) [4096, 64] [2048, 64]
  l19 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6035)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10988)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10989) [4096, 64] [2048, 64]
  l20 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6089)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11142)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11143) [4096, 64] [2048, 64]
  l21 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6143)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11296)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11297) [4096, 64] [2048, 64]
  l22 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6197)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11450)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11451) [4096, 64] [2048, 64]
  l23 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6251)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11604)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11605) [4096, 64] [2048, 64]

/-- Close all twelve faithful unshuffle boundaries.  Packed-cu witnesses are
projected from the genuine Goal-4 external contract; no decoded-cu equality or
post-unshuffle relation is supplied by the external caller. -/
theorem goal4_faithful_routing_l12_l23_certificate
    (initSM initPM : Store)
    (hContract : Goal4ExternalInputContract initSM initPM)
    (hAncestry : Goal4RoutingLateAncestry initSM initPM) :
    Goal4RoutingLateCertificate initSM initPM := by
  rcases hContract with
    ⟨_hSmValues, _hPmValues, hp12, hp13, hp14, hp15, hp16, hp17,
      hp18, hp19, hp20, hp21, hp22, hp23⟩
  exact {
    l12 := canonical_goal4_l12_routing_unshuffle initSM initPM hAncestry.l12 hp12
    l13 := canonical_goal4_l13_routing_unshuffle initSM initPM hAncestry.l13 hp13
    l14 := canonical_goal4_l14_routing_unshuffle initSM initPM hAncestry.l14 hp14
    l15 := canonical_goal4_l15_routing_unshuffle initSM initPM hAncestry.l15 hp15
    l16 := canonical_goal4_l16_routing_unshuffle initSM initPM hAncestry.l16 hp16
    l17 := canonical_goal4_l17_routing_unshuffle initSM initPM hAncestry.l17 hp17
    l18 := canonical_goal4_l18_routing_unshuffle initSM initPM hAncestry.l18 hp18
    l19 := canonical_goal4_l19_routing_unshuffle initSM initPM hAncestry.l19 hp19
    l20 := canonical_goal4_l20_routing_unshuffle initSM initPM hAncestry.l20 hp20
    l21 := canonical_goal4_l21_routing_unshuffle initSM initPM hAncestry.l21 hp21
    l22 := canonical_goal4_l22_routing_unshuffle initSM initPM hAncestry.l22 hp22
    l23 := canonical_goal4_l23_routing_unshuffle initSM initPM hAncestry.l23 hp23
  }

#print axioms goal4_faithful_routing_l12_l23_certificate

end
end TrainVerify.Denote.GeneratedPatterns
