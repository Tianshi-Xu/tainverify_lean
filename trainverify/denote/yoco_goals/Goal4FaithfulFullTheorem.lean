/- Goal 4: combine the 24 faithful routing relations and close the real target. -/
import denote.yoco_goals.Goal4L0L11GateScoreCertificate
import denote.yoco_goals.Goal4FaithfulRoutingLate

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private theorem goal4_routing_stack_of_certificates (initSM initPM : Store)
    (early : Goal4L0L11GateScoreCertificate initSM initPM)
    (late : Goal4RoutingLateCertificate initSM initPM) :
    Goal4RoutingStackRel initSM initPM := by
  refine {
    full_values := ?_
    full_shapes := ?_
    rank0_shapes := ?_
    rank1_shapes := ?_
  }
  · unfold goal4SmRoutingTids goal4PmRouting0Tids goal4PmRouting1Tids
    simp only [List.map, List.zipWith]
    rw [early.l0.full_value, early.l1.full_value, early.l2.full_value,
      early.l3.full_value, early.l4.full_value, early.l5.full_value,
      early.l6.full_value, early.l7.full_value, early.l8.full_value,
      early.l9.full_value, early.l10.full_value, early.l11.full_value,
      late.l12.full_value, late.l13.full_value, late.l14.full_value,
      late.l15.full_value, late.l16.full_value, late.l17.full_value,
      late.l18.full_value, late.l19.full_value, late.l20.full_value,
      late.l21.full_value, late.l22.full_value, late.l23.full_value]
  · intro t ht
    rcases List.mem_map.mp ht with ⟨tid, htid, rfl⟩
    unfold goal4SmRoutingTids at htid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
    rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    next => exact early.l0.full_shape
    next => exact early.l1.full_shape
    next => exact early.l2.full_shape
    next => exact early.l3.full_shape
    next => exact early.l4.full_shape
    next => exact early.l5.full_shape
    next => exact early.l6.full_shape
    next => exact early.l7.full_shape
    next => exact early.l8.full_shape
    next => exact early.l9.full_shape
    next => exact early.l10.full_shape
    next => exact early.l11.full_shape
    next => exact late.l12.full_shape
    next => exact late.l13.full_shape
    next => exact late.l14.full_shape
    next => exact late.l15.full_shape
    next => exact late.l16.full_shape
    next => exact late.l17.full_shape
    next => exact late.l18.full_shape
    next => exact late.l19.full_shape
    next => exact late.l20.full_shape
    next => exact late.l21.full_shape
    next => exact late.l22.full_shape
    next => exact late.l23.full_shape
  · intro t ht
    rcases List.mem_map.mp ht with ⟨tid, htid, rfl⟩
    unfold goal4PmRouting0Tids at htid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
    rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    next => exact early.l0.rank0_shape
    next => exact early.l1.rank0_shape
    next => exact early.l2.rank0_shape
    next => exact early.l3.rank0_shape
    next => exact early.l4.rank0_shape
    next => exact early.l5.rank0_shape
    next => exact early.l6.rank0_shape
    next => exact early.l7.rank0_shape
    next => exact early.l8.rank0_shape
    next => exact early.l9.rank0_shape
    next => exact early.l10.rank0_shape
    next => exact early.l11.rank0_shape
    next => exact late.l12.rank0_shape
    next => exact late.l13.rank0_shape
    next => exact late.l14.rank0_shape
    next => exact late.l15.rank0_shape
    next => exact late.l16.rank0_shape
    next => exact late.l17.rank0_shape
    next => exact late.l18.rank0_shape
    next => exact late.l19.rank0_shape
    next => exact late.l20.rank0_shape
    next => exact late.l21.rank0_shape
    next => exact late.l22.rank0_shape
    next => exact late.l23.rank0_shape
  · intro t ht
    rcases List.mem_map.mp ht with ⟨tid, htid, rfl⟩
    unfold goal4PmRouting1Tids at htid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
    rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    next => exact early.l0.rank1_shape
    next => exact early.l1.rank1_shape
    next => exact early.l2.rank1_shape
    next => exact early.l3.rank1_shape
    next => exact early.l4.rank1_shape
    next => exact early.l5.rank1_shape
    next => exact early.l6.rank1_shape
    next => exact early.l7.rank1_shape
    next => exact early.l8.rank1_shape
    next => exact early.l9.rank1_shape
    next => exact early.l10.rank1_shape
    next => exact early.l11.rank1_shape
    next => exact late.l12.rank1_shape
    next => exact late.l13.rank1_shape
    next => exact late.l14.rank1_shape
    next => exact late.l15.rank1_shape
    next => exact late.l16.rank1_shape
    next => exact late.l17.rank1_shape
    next => exact late.l18.rank1_shape
    next => exact late.l19.rank1_shape
    next => exact late.l20.rank1_shape
    next => exact late.l21.rank1_shape
    next => exact late.l22.rank1_shape
    next => exact late.l23.rank1_shape

/-- Exact Goal-4 closure once the internally computed late ancestry is supplied. -/
theorem canonical_goal_4_from_late_ancestry
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM)
    (hAncestry : Goal4RoutingLateAncestry initSM initPM) :
    InitGoalHolds pm_goal_4.numRanks goal_4
      (denoteGraphDistributedFaithful sm_goal_4 initSM)
      (denoteGraphDistributedFaithful pm_goal_4 initPM) := by
  have early := goal4_l0_l11_gate_score_certificate
    initSM initPM hSM hPM hInit hContract
  have late := goal4_faithful_routing_l12_l23_certificate
    initSM initPM hContract hAncestry
  exact goal4_faithful_4929_from_routing_stack initSM initPM
    (goal4_routing_stack_of_certificates initSM initPM early late)

#print axioms goal4_faithful_4929_from_routing_stack
#print axioms canonical_goal_4_from_late_ancestry

end
end TrainVerify.Denote.GeneratedPatterns
