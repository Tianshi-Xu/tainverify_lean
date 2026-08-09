/- Goal 3: faithful 24-layer routing stack and the real TID-4928 theorem. -/
import denote.yoco_goals.Goal3L0L11RoutingCertificate
import denote.yoco_goals.Goal3FaithfulRoutingLate

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def goal3SmRoutingTids : List Tid :=
  [4964, 5019, 5074, 5129, 5184, 5239, 5294, 5349, 5404, 5459, 5514, 5569,
   5655, 5709, 5763, 5817, 5871, 5925, 5979, 6033, 6087, 6141, 6195, 6249]

private def goal3PmRouting0Tids : List Tid :=
  [7844, 8008, 8172, 8336, 8500, 8664, 8828, 8992, 9156, 9320, 9484, 9648,
   9908, 10062, 10216, 10370, 10524, 10678, 10832, 10986, 11140, 11294, 11448, 11602]

private def goal3PmRouting1Tids : List Tid :=
  [7845, 8009, 8173, 8337, 8501, 8665, 8829, 8993, 9157, 9321, 9485, 9649,
   9909, 10063, 10217, 10371, 10525, 10679, 10833, 10987, 11141, 11295, 11449, 11603]

/-- The 24 ordinary routing relations in the list-oriented form consumed by the
real generated stack.  This is internal proof plumbing, not a caller contract. -/
structure Goal3RoutingStackRel (initSM initPM : Store) : Prop where
  full_values :
    goal3SmRoutingTids.map (denoteGraphDistributedFaithful sm initSM) =
      List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b])
        (goal3PmRouting0Tids.map (denoteGraphDistributedFaithful pm initPM))
        (goal3PmRouting1Tids.map (denoteGraphDistributedFaithful pm initPM))
  full_shapes : ∀ t ∈ goal3SmRoutingTids.map
      (denoteGraphDistributedFaithful sm initSM), t.shape = [4096, 64]
  rank0_shapes : ∀ t ∈ goal3PmRouting0Tids.map
      (denoteGraphDistributedFaithful pm initPM), t.shape = [2048, 64]
  rank1_shapes : ∀ t ∈ goal3PmRouting1Tids.map
      (denoteGraphDistributedFaithful pm initPM), t.shape = [2048, 64]

private def goal3SmStack : NodeDecl :=
  { rank := 0, op := "OpName.FW_stack", ins := goal3SmRoutingTids, outs := [4928] }
private def goal3PmStack0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_stack", ins := goal3PmRouting0Tids, outs := [11608] }
private def goal3PmStack1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_stack", ins := goal3PmRouting1Tids, outs := [11609] }
private def goal3PmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11608, 11609],
    outs := [4928], params := [1] }

private theorem goal3_tail_nodes :
    sm.nodes[939]'(by native_decide) = goal3SmStack ∧
    pm.nodes[2055]'(by native_decide) = goal3PmStack0 ∧
    pm.nodes[2057]'(by native_decide) = goal3PmStack1 ∧
    pm.nodes[2061]'(by native_decide) = goal3PmGather := by
  native_decide

private theorem goal3_sm_nodes_nonempty : ∀ n ∈ sm.nodes, n.outs ≠ [] := by
  native_decide
private theorem goal3_pm_nodes_nonempty : ∀ n ∈ pm.nodes, n.outs ≠ [] := by
  native_decide

private theorem goal3_sm_routing_not_written (tid : Tid)
    (h : tid ∈ goal3SmRoutingTids) :
    ∀ n ∈ sm.nodes.drop 939, tid ∉ n.outs := by
  unfold goal3SmRoutingTids at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> native_decide +revert

private theorem goal3_pm_routing0_not_written (tid : Tid)
    (h : tid ∈ goal3PmRouting0Tids) :
    ∀ n ∈ pm.nodes.drop 2055, tid ∉ n.outs := by
  unfold goal3PmRouting0Tids at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> native_decide +revert

private theorem goal3_pm_routing1_not_written (tid : Tid)
    (h : tid ∈ goal3PmRouting1Tids) :
    ∀ n ∈ pm.nodes.drop 2057, tid ∉ n.outs := by
  unfold goal3PmRouting1Tids at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> native_decide +revert

private theorem goal3_sm_stack_faithful (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 4928 =
      fw_stack (goal3SmRoutingTids.map
        (denoteGraphDistributedFaithful sm initSM)) := by
  let pre := (sm.nodes.take 939).foldl (applyNodeDistributedFaithful sm) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm initSM 939
    goal3SmStack 4928 (by native_decide) goal3_tail_nodes.1
    (fun n hn => goal3_sm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
  have happly : applyNodeDistributedFaithful sm pre goal3SmStack 4928 =
      fw_stack (goal3SmRoutingTids.map pre) := by
    unfold goal3SmStack
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
    exact applyNode_fw_stack_out sm pre 0 goal3SmRoutingTids 4928 []
  have hmap : goal3SmRoutingTids.map pre = goal3SmRoutingTids.map
      (denoteGraphDistributedFaithful sm initSM) := by
    apply List.map_congr_left
    intro tid htid
    exact denoteGraphDistributedFaithful_prefix_read sm initSM 939 tid
      (fun n hn => goal3_sm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (goal3_sm_routing_not_written tid htid)
  rw [hcore, happly, hmap]

private theorem goal3_pm_stack0_faithful (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11608 =
      fw_stack (goal3PmRouting0Tids.map
        (denoteGraphDistributedFaithful pm initPM)) := by
  let pre := (pm.nodes.take 2055).foldl (applyNodeDistributedFaithful pm) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm initPM 2055
    goal3PmStack0 11608 (by native_decide) goal3_tail_nodes.2.1
    (fun n hn => goal3_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
  have happly : applyNodeDistributedFaithful pm pre goal3PmStack0 11608 =
      fw_stack (goal3PmRouting0Tids.map pre) := by
    unfold goal3PmStack0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
    exact applyNode_fw_stack_out pm pre 0 goal3PmRouting0Tids 11608 []
  have hmap : goal3PmRouting0Tids.map pre = goal3PmRouting0Tids.map
      (denoteGraphDistributedFaithful pm initPM) := by
    apply List.map_congr_left
    intro tid htid
    exact denoteGraphDistributedFaithful_prefix_read pm initPM 2055 tid
      (fun n hn => goal3_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (goal3_pm_routing0_not_written tid htid)
  rw [hcore, happly, hmap]

private theorem goal3_pm_stack1_faithful (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11609 =
      fw_stack (goal3PmRouting1Tids.map
        (denoteGraphDistributedFaithful pm initPM)) := by
  let pre := (pm.nodes.take 2057).foldl (applyNodeDistributedFaithful pm) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm initPM 2057
    goal3PmStack1 11609 (by native_decide) goal3_tail_nodes.2.2.1
    (fun n hn => goal3_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
  have happly : applyNodeDistributedFaithful pm pre goal3PmStack1 11609 =
      fw_stack (goal3PmRouting1Tids.map pre) := by
    unfold goal3PmStack1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
    exact applyNode_fw_stack_out pm pre 1 goal3PmRouting1Tids 11609 []
  have hmap : goal3PmRouting1Tids.map pre = goal3PmRouting1Tids.map
      (denoteGraphDistributedFaithful pm initPM) := by
    apply List.map_congr_left
    intro tid htid
    exact denoteGraphDistributedFaithful_prefix_read pm initPM 2057 tid
      (fun n hn => goal3_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (goal3_pm_routing1_not_written tid htid)
  rw [hcore, happly, hmap]

/-- The complete generated tail at TID 4928. -/
theorem goal3_faithful_4928_from_routing_stack (initSM initPM : Store)
    (h : Goal3RoutingStackRel initSM initPM) :
    InitGoalHolds pm.numRanks goal_3
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  let as := goal3PmRouting0Tids.map (denoteGraphDistributedFaithful pm initPM)
  let bs := goal3PmRouting1Tids.map (denoteGraphDistributedFaithful pm initPM)
  have hlen : as.length = bs.length := by
    simp [as, bs, goal3PmRouting0Tids, goal3PmRouting1Tids]
  have hne : as ≠ [] := by simp [as, goal3PmRouting0Tids]
  have hcommute := stack_allGather_commute_generic_2048_64 as bs hlen hne
    h.rank0_shapes h.rank1_shapes
  have hsm := goal3_sm_stack_faithful initSM
  have hp0 := goal3_pm_stack0_faithful initPM
  have hp1 := goal3_pm_stack1_faithful initPM
  have hpm := goal_3_pm4928_faithful initPM
  have hvalue : denoteGraphDistributedFaithful sm initSM 4928 =
      denoteGraphDistributedFaithful pm initPM 4928 := by
    calc
      denoteGraphDistributedFaithful sm initSM 4928 =
          fw_stack (goal3SmRoutingTids.map
            (denoteGraphDistributedFaithful sm initSM)) := hsm
      _ = fw_stack (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b])
            as bs) := congrArg fw_stack h.full_values
      _ = allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs] := hcommute
      _ = allGatherPrimDimN 1 2 0
            [denoteGraphDistributedFaithful pm initPM 11608,
             denoteGraphDistributedFaithful pm initPM 11609] := by rw [hp0, hp1]
      _ = denoteGraphDistributedFaithful pm initPM 4928 := hpm.symm
  have hsmShape : (denoteGraphDistributedFaithful sm initSM 4928).shape =
      [24, 4096, 64] := by
    rw [hsm]
    have hhead : ((goal3SmRoutingTids.map
        (denoteGraphDistributedFaithful sm initSM)).head?.map
        (fun t => t.shape)).getD [] = [4096, 64] := by
      exact h.full_shapes (denoteGraphDistributedFaithful sm initSM 4964) (by
        simp [goal3SmRoutingTids])
    rw [fw_stack_shape _ [4096, 64] hhead]
    rfl
  have hpmShape : (denoteGraphDistributedFaithful pm initPM 4928).shape =
      [24, 4096, 64] := by rw [← hvalue]; exact hsmShape
  unfold InitGoalHolds
  refine ⟨hsmShape, ?_, ?_⟩
  · exact congrArg (fun s => [s]) hpmShape
  · unfold reconstructForGoal
    simp only [goal_3, List.map, reconstructWithDim]
    exact hvalue

private theorem goal3_routing_stack_of_certificates (initSM initPM : Store)
    (early : Goal3L0L11RoutingCertificate initSM initPM)
    (late : Goal3RoutingLateCertificate initSM initPM) :
    Goal3RoutingStackRel initSM initPM := by
  refine {
    full_values := ?_
    full_shapes := ?_
    rank0_shapes := ?_
    rank1_shapes := ?_
  }
  · unfold goal3SmRoutingTids goal3PmRouting0Tids goal3PmRouting1Tids
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
    unfold goal3SmRoutingTids at ht
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
    unfold goal3PmRouting0Tids at ht
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
    unfold goal3PmRouting1Tids at ht
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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

/-- Exact closure once the internally-computed late ancestry package is in hand. -/
theorem canonical_goal_3_from_late_ancestry
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hContract : Goal3FullExternalInputs initSM initPM)
    (hAncestry : Goal3RoutingLateAncestry initSM initPM) :
    InitGoalHolds pm.numRanks goal_3
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have early := goal3_l0_l11_routing_certificate initSM initPM hSM hPM hInit hContract
  have late := goal3_faithful_routing_l12_l23_certificate initSM initPM hContract hAncestry
  exact goal3_faithful_4928_from_routing_stack initSM initPM
    (goal3_routing_stack_of_certificates initSM initPM early late)

#print axioms goal3_faithful_4928_from_routing_stack
#print axioms canonical_goal_3_from_late_ancestry

end
end TrainVerify.Denote.GeneratedPatterns
