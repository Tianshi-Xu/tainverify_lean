/- Goal 3 L12-L23: convert ancestry-derived zigzag routing maps through the
   generated faithful unshuffle nodes into the ordinary relations consumed by
   the final routing stack. -/
import denote.yoco_goals.CanonicalGoal3L12Routing
import denote.yoco_goals.CanonicalGoal3L13Routing
import denote.yoco_goals.CanonicalGoal3L14Routing
import denote.yoco_goals.CanonicalGoal3L15Routing
import denote.yoco_goals.CanonicalGoal3L16Routing
import denote.yoco_goals.CanonicalGoal3L17Routing
import denote.yoco_goals.CanonicalGoal3L18Routing
import denote.yoco_goals.CanonicalGoal3L19Routing
import denote.yoco_goals.CanonicalGoal3L20Routing
import denote.yoco_goals.CanonicalGoal3L21Routing
import denote.yoco_goals.CanonicalGoal3L22Routing
import denote.yoco_goals.CanonicalGoal3L23Routing

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-- The exact post-shuffle routing facts exported by Goal 3 ancestry.  Keeping
this as one record makes the late certificate independent of how the ancestry
proof is assembled. -/
structure Goal3RoutingLateAncestry (initSM initPM : Store) : Prop where
  l12 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5627)
    (denoteGraphDistributedFaithful pm initPM 9830)
    (denoteGraphDistributedFaithful pm initPM 9831)
    (denoteGraphDistributedFaithful pm initPM 5654) [4096, 64] [2048, 64]
  l13 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5681)
    (denoteGraphDistributedFaithful pm initPM 9984)
    (denoteGraphDistributedFaithful pm initPM 9985)
    (denoteGraphDistributedFaithful pm initPM 5708) [4096, 64] [2048, 64]
  l14 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5735)
    (denoteGraphDistributedFaithful pm initPM 10138)
    (denoteGraphDistributedFaithful pm initPM 10139)
    (denoteGraphDistributedFaithful pm initPM 5762) [4096, 64] [2048, 64]
  l15 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5789)
    (denoteGraphDistributedFaithful pm initPM 10292)
    (denoteGraphDistributedFaithful pm initPM 10293)
    (denoteGraphDistributedFaithful pm initPM 5816) [4096, 64] [2048, 64]
  l16 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5843)
    (denoteGraphDistributedFaithful pm initPM 10446)
    (denoteGraphDistributedFaithful pm initPM 10447)
    (denoteGraphDistributedFaithful pm initPM 5870) [4096, 64] [2048, 64]
  l17 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5897)
    (denoteGraphDistributedFaithful pm initPM 10600)
    (denoteGraphDistributedFaithful pm initPM 10601)
    (denoteGraphDistributedFaithful pm initPM 5924) [4096, 64] [2048, 64]
  l18 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5951)
    (denoteGraphDistributedFaithful pm initPM 10754)
    (denoteGraphDistributedFaithful pm initPM 10755)
    (denoteGraphDistributedFaithful pm initPM 5978) [4096, 64] [2048, 64]
  l19 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 6005)
    (denoteGraphDistributedFaithful pm initPM 10908)
    (denoteGraphDistributedFaithful pm initPM 10909)
    (denoteGraphDistributedFaithful pm initPM 6032) [4096, 64] [2048, 64]
  l20 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 6059)
    (denoteGraphDistributedFaithful pm initPM 11062)
    (denoteGraphDistributedFaithful pm initPM 11063)
    (denoteGraphDistributedFaithful pm initPM 6086) [4096, 64] [2048, 64]
  l21 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 6113)
    (denoteGraphDistributedFaithful pm initPM 11216)
    (denoteGraphDistributedFaithful pm initPM 11217)
    (denoteGraphDistributedFaithful pm initPM 6140) [4096, 64] [2048, 64]
  l22 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 6167)
    (denoteGraphDistributedFaithful pm initPM 11370)
    (denoteGraphDistributedFaithful pm initPM 11371)
    (denoteGraphDistributedFaithful pm initPM 6194) [4096, 64] [2048, 64]
  l23 : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 6221)
    (denoteGraphDistributedFaithful pm initPM 11524)
    (denoteGraphDistributedFaithful pm initPM 11525)
    (denoteGraphDistributedFaithful pm initPM 6248) [4096, 64] [2048, 64]

/-- The twelve ordinary routing relations needed by Goal 3's generated stack. -/
structure Goal3RoutingLateCertificate (initSM initPM : Store) : Prop where
  l12 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5655)
    (denoteGraphDistributedFaithful pm initPM 9908)
    (denoteGraphDistributedFaithful pm initPM 9909) [4096, 64] [2048, 64]
  l13 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5709)
    (denoteGraphDistributedFaithful pm initPM 10062)
    (denoteGraphDistributedFaithful pm initPM 10063) [4096, 64] [2048, 64]
  l14 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5763)
    (denoteGraphDistributedFaithful pm initPM 10216)
    (denoteGraphDistributedFaithful pm initPM 10217) [4096, 64] [2048, 64]
  l15 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5817)
    (denoteGraphDistributedFaithful pm initPM 10370)
    (denoteGraphDistributedFaithful pm initPM 10371) [4096, 64] [2048, 64]
  l16 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5871)
    (denoteGraphDistributedFaithful pm initPM 10524)
    (denoteGraphDistributedFaithful pm initPM 10525) [4096, 64] [2048, 64]
  l17 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5925)
    (denoteGraphDistributedFaithful pm initPM 10678)
    (denoteGraphDistributedFaithful pm initPM 10679) [4096, 64] [2048, 64]
  l18 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5979)
    (denoteGraphDistributedFaithful pm initPM 10832)
    (denoteGraphDistributedFaithful pm initPM 10833) [4096, 64] [2048, 64]
  l19 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 6033)
    (denoteGraphDistributedFaithful pm initPM 10986)
    (denoteGraphDistributedFaithful pm initPM 10987) [4096, 64] [2048, 64]
  l20 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 6087)
    (denoteGraphDistributedFaithful pm initPM 11140)
    (denoteGraphDistributedFaithful pm initPM 11141) [4096, 64] [2048, 64]
  l21 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 6141)
    (denoteGraphDistributedFaithful pm initPM 11294)
    (denoteGraphDistributedFaithful pm initPM 11295) [4096, 64] [2048, 64]
  l22 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 6195)
    (denoteGraphDistributedFaithful pm initPM 11448)
    (denoteGraphDistributedFaithful pm initPM 11449) [4096, 64] [2048, 64]
  l23 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 6249)
    (denoteGraphDistributedFaithful pm initPM 11602)
    (denoteGraphDistributedFaithful pm initPM 11603) [4096, 64] [2048, 64]

private theorem goal3_late_packed_of_contract (initSM initPM : Store)
    (hContract : Goal3FullExternalInputs initSM initPM)
    (tid : Tid)
    (htid : tid ∈ [5654, 5708, 5762, 5816, 5870, 5924,
      5978, 6032, 6086, 6140, 6194, 6248]) :
    PackedCuSeqlensWF (initPM tid) 4096 2 := by
  have hc : ∃ c ∈ pmInputValueClasses, tid ∈ c.tids ∧ (6248 : Tid) ∈ c.tids := by
    unfold pmInputValueClasses
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨{ source := "getitem:root=4441:key=cu_seqlens_q", tids :=
      [4947, 5002, 5057, 5112, 5167, 5222, 5277, 5332, 5387, 5442, 5497,
       5552, 5602, 5610, 5654, 5656, 5664, 5708, 5710, 5718, 5762, 5764,
       5772, 5816, 5818, 5826, 5870, 5872, 5880, 5924, 5926, 5934, 5978,
       5980, 5988, 6032, 6034, 6042, 6086, 6088, 6096, 6140, 6142, 6150,
       6194, 6196, 6204, 6248, 6250, 6252] }, by decide, ?_, by decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htid ⊢
    rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide
  rcases hc with ⟨c, hc, htidc, hbasec⟩
  have heq : initPM tid = initPM 6248 :=
    hContract.2.1.eq_of_mem hc htidc hbasec
  rw [heq]
  exact hContract.2.2

/-- Faithful-unshuffle routing certificate for Goal 3's late (L12-L23) band.
All packed-cu facts come from the external input contract/value ancestry; the
only routing input is the package produced by graph ancestry, never a caller
assertion about an already-unshuffled computed value. -/
theorem goal3_faithful_routing_l12_l23_certificate
    (initSM initPM : Store)
    (hContract : Goal3FullExternalInputs initSM initPM)
    (hAncestry : Goal3RoutingLateAncestry initSM initPM) :
    Goal3RoutingLateCertificate initSM initPM := by
  have hp12 := goal3_late_packed_of_contract initSM initPM hContract 5654 (by decide)
  have hp13 := goal3_late_packed_of_contract initSM initPM hContract 5708 (by decide)
  have hp14 := goal3_late_packed_of_contract initSM initPM hContract 5762 (by decide)
  have hp15 := goal3_late_packed_of_contract initSM initPM hContract 5816 (by decide)
  have hp16 := goal3_late_packed_of_contract initSM initPM hContract 5870 (by decide)
  have hp17 := goal3_late_packed_of_contract initSM initPM hContract 5924 (by decide)
  have hp18 := goal3_late_packed_of_contract initSM initPM hContract 5978 (by decide)
  have hp19 := goal3_late_packed_of_contract initSM initPM hContract 6032 (by decide)
  have hp20 := goal3_late_packed_of_contract initSM initPM hContract 6086 (by decide)
  have hp21 := goal3_late_packed_of_contract initSM initPM hContract 6140 (by decide)
  have hp22 := goal3_late_packed_of_contract initSM initPM hContract 6194 (by decide)
  have hp23 := goal3_late_packed_of_contract initSM initPM hContract 6248 (by decide)
  exact {
    l12 := canonical_goal3_l12_routing_unshuffle initSM initPM hAncestry.l12 hp12
    l13 := canonical_goal3_l13_routing_unshuffle initSM initPM hAncestry.l13 hp13
    l14 := canonical_goal3_l14_routing_unshuffle initSM initPM hAncestry.l14 hp14
    l15 := canonical_goal3_l15_routing_unshuffle initSM initPM hAncestry.l15 hp15
    l16 := canonical_goal3_l16_routing_unshuffle initSM initPM hAncestry.l16 hp16
    l17 := canonical_goal3_l17_routing_unshuffle initSM initPM hAncestry.l17 hp17
    l18 := canonical_goal3_l18_routing_unshuffle initSM initPM hAncestry.l18 hp18
    l19 := canonical_goal3_l19_routing_unshuffle initSM initPM hAncestry.l19 hp19
    l20 := canonical_goal3_l20_routing_unshuffle initSM initPM hAncestry.l20 hp20
    l21 := canonical_goal3_l21_routing_unshuffle initSM initPM hAncestry.l21 hp21
    l22 := canonical_goal3_l22_routing_unshuffle initSM initPM hAncestry.l22 hp22
    l23 := canonical_goal3_l23_routing_unshuffle initSM initPM hAncestry.l23 hp23
  }

#print axioms goal3_faithful_routing_l12_l23_certificate

end
end TrainVerify.Denote.GeneratedPatterns
