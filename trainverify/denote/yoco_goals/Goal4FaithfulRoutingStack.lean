/- Goal 4: faithful 24-layer routing stack and the real TID-4929 tail. -/
import denote.yoco_goals.CanonicalGoal4L0Routing
import denote.yoco_goals.CanonicalGoal4L1Routing
import denote.yoco_goals.CanonicalGoal4L2Routing
import denote.yoco_goals.CanonicalGoal4L3Routing
import denote.yoco_goals.CanonicalGoal4L4Routing
import denote.yoco_goals.CanonicalGoal4L5Routing
import denote.yoco_goals.CanonicalGoal4L6Routing
import denote.yoco_goals.CanonicalGoal4L7Routing
import denote.yoco_goals.CanonicalGoal4L8Routing
import denote.yoco_goals.CanonicalGoal4L9Routing
import denote.yoco_goals.CanonicalGoal4L10Routing
import denote.yoco_goals.CanonicalGoal4L11Routing
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
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def goal4SmRoutingTids : List Tid :=
  [4965, 5020, 5075, 5130, 5185, 5240, 5295, 5350, 5405, 5460, 5515, 5570,
   5657, 5711, 5765, 5819, 5873, 5927, 5981, 6035, 6089, 6143, 6197, 6251]

private def goal4PmRouting0Tids : List Tid :=
  [7846, 8010, 8174, 8338, 8502, 8666, 8830, 8994, 9158, 9322, 9486, 9650,
   9910, 10064, 10218, 10372, 10526, 10680, 10834, 10988, 11142, 11296, 11450, 11604]

private def goal4PmRouting1Tids : List Tid :=
  [7847, 8011, 8175, 8339, 8503, 8667, 8831, 8995, 9159, 9323, 9487, 9651,
   9911, 10065, 10219, 10373, 10527, 10681, 10835, 10989, 11143, 11297, 11451, 11605]

/-- The exact information exported by the 24 routing-layer proofs and consumed
by the final stack.  It is deliberately not part of `goal_4_stmt_full`; the
closure theorem must construct it from ancestry internally. -/
structure Goal4RoutingStackRel (initSM initPM : Store) : Prop where
  full_values :
    goal4SmRoutingTids.map (denoteGraphDistributedFaithful sm_goal_4 initSM) =
      List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b])
        (goal4PmRouting0Tids.map (denoteGraphDistributedFaithful pm_goal_4 initPM))
        (goal4PmRouting1Tids.map (denoteGraphDistributedFaithful pm_goal_4 initPM))
  full_shapes : ∀ t ∈ goal4SmRoutingTids.map
      (denoteGraphDistributedFaithful sm_goal_4 initSM), t.shape = [4096, 64]
  rank0_shapes : ∀ t ∈ goal4PmRouting0Tids.map
      (denoteGraphDistributedFaithful pm_goal_4 initPM), t.shape = [2048, 64]
  rank1_shapes : ∀ t ∈ goal4PmRouting1Tids.map
      (denoteGraphDistributedFaithful pm_goal_4 initPM), t.shape = [2048, 64]

private def goal4SmStack : NodeDecl :=
  { rank := 0, op := "OpName.FW_stack", ins := goal4SmRoutingTids, outs := [4929] }
private def goal4PmStack0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_stack", ins := goal4PmRouting0Tids, outs := [11660] }
private def goal4PmStack1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_stack", ins := goal4PmRouting1Tids, outs := [11661] }
private def goal4PmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11660, 11661],
    outs := [4929], params := [1] }

private theorem goal4_tail_nodes :
    sm_goal_4.nodes[915]'(by native_decide) = goal4SmStack ∧
    pm_goal_4.nodes[2000]'(by native_decide) = goal4PmStack0 ∧
    pm_goal_4.nodes[2001]'(by native_decide) = goal4PmStack1 ∧
    pm_goal_4.nodes[2002]'(by native_decide) = goal4PmGather := by
  native_decide

private theorem goal4_sm_nodes_nonempty : ∀ n ∈ sm_goal_4.nodes, n.outs ≠ [] := by
  native_decide
private theorem goal4_pm_nodes_nonempty : ∀ n ∈ pm_goal_4.nodes, n.outs ≠ [] := by
  native_decide

private theorem goal4_sm_routing_not_written (tid : Tid)
    (h : tid ∈ goal4SmRoutingTids) :
    ∀ n ∈ sm_goal_4.nodes.drop 915, tid ∉ n.outs := by
  unfold goal4SmRoutingTids at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> native_decide +revert

private theorem goal4_pm_routing0_not_written (tid : Tid)
    (h : tid ∈ goal4PmRouting0Tids) :
    ∀ n ∈ pm_goal_4.nodes.drop 2000, tid ∉ n.outs := by
  unfold goal4PmRouting0Tids at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> native_decide +revert

private theorem goal4_pm_routing1_not_written (tid : Tid)
    (h : tid ∈ goal4PmRouting1Tids) :
    ∀ n ∈ pm_goal_4.nodes.drop 2001, tid ∉ n.outs := by
  unfold goal4PmRouting1Tids at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> native_decide +revert

private theorem goal4_sm_stack_faithful (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 4929 =
      fw_stack (goal4SmRoutingTids.map
        (denoteGraphDistributedFaithful sm_goal_4 initSM)) := by
  let pre := (sm_goal_4.nodes.take 915).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 915
    goal4SmStack 4929 (by native_decide) goal4_tail_nodes.1
    (fun n hn => goal4_sm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
  have happly : applyNodeDistributedFaithful sm_goal_4 pre goal4SmStack 4929 =
      fw_stack (goal4SmRoutingTids.map pre) := by
    unfold goal4SmStack
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
    exact applyNode_fw_stack_out sm_goal_4 pre 0 goal4SmRoutingTids 4929 []
  have hmap : goal4SmRoutingTids.map pre = goal4SmRoutingTids.map
      (denoteGraphDistributedFaithful sm_goal_4 initSM) := by
    apply List.map_congr_left
    intro tid htid
    exact denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 915 tid
      (fun n hn => goal4_sm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (goal4_sm_routing_not_written tid htid)
  rw [hcore, happly, hmap]

private theorem goal4_pm_stack0_faithful (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11660 =
      fw_stack (goal4PmRouting0Tids.map
        (denoteGraphDistributedFaithful pm_goal_4 initPM)) := by
  let pre := (pm_goal_4.nodes.take 2000).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 2000
    goal4PmStack0 11660 (by native_decide) goal4_tail_nodes.2.1
    (fun n hn => goal4_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
  have happly : applyNodeDistributedFaithful pm_goal_4 pre goal4PmStack0 11660 =
      fw_stack (goal4PmRouting0Tids.map pre) := by
    unfold goal4PmStack0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
    exact applyNode_fw_stack_out pm_goal_4 pre 0 goal4PmRouting0Tids 11660 []
  have hmap : goal4PmRouting0Tids.map pre = goal4PmRouting0Tids.map
      (denoteGraphDistributedFaithful pm_goal_4 initPM) := by
    apply List.map_congr_left
    intro tid htid
    exact denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 2000 tid
      (fun n hn => goal4_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (goal4_pm_routing0_not_written tid htid)
  rw [hcore, happly, hmap]

private theorem goal4_pm_stack1_faithful (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11661 =
      fw_stack (goal4PmRouting1Tids.map
        (denoteGraphDistributedFaithful pm_goal_4 initPM)) := by
  let pre := (pm_goal_4.nodes.take 2001).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 2001
    goal4PmStack1 11661 (by native_decide) goal4_tail_nodes.2.2.1
    (fun n hn => goal4_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
  have happly : applyNodeDistributedFaithful pm_goal_4 pre goal4PmStack1 11661 =
      fw_stack (goal4PmRouting1Tids.map pre) := by
    unfold goal4PmStack1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
    exact applyNode_fw_stack_out pm_goal_4 pre 1 goal4PmRouting1Tids 11661 []
  have hmap : goal4PmRouting1Tids.map pre = goal4PmRouting1Tids.map
      (denoteGraphDistributedFaithful pm_goal_4 initPM) := by
    apply List.map_congr_left
    intro tid htid
    exact denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 2001 tid
      (fun n hn => goal4_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (goal4_pm_routing1_not_written tid htid)
  rw [hcore, happly, hmap]

private theorem goal4_pm4929_faithful (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 4929 =
      allGatherPrimDimN 1 2 0
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11660,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11661] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_4 initPM 2002 goal4PmGather
    11660 11661 4929 (fun a b => allGatherPrimDimN 1 2 0 [a, b])
    (by native_decide) goal4_tail_nodes.2.2.2 ?_
    (fun n hn => goal4_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
    (fun n hn => goal4_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide) (by native_decide)
  intro s
  unfold goal4PmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    _ _ _ (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm_goal_4 s 0 [11660, 11661] 4929 1

/-- The complete graph tail: a 24-way ordinary routing relation implies the
actual generated SM stack equals the generated PM rank stacks gathered on dim 1. -/
theorem goal4_faithful_4929_from_routing_stack (initSM initPM : Store)
    (h : Goal4RoutingStackRel initSM initPM) :
    InitGoalHolds pm_goal_4.numRanks goal_4
      (denoteGraphDistributedFaithful sm_goal_4 initSM)
      (denoteGraphDistributedFaithful pm_goal_4 initPM) := by
  let as := goal4PmRouting0Tids.map
    (denoteGraphDistributedFaithful pm_goal_4 initPM)
  let bs := goal4PmRouting1Tids.map
    (denoteGraphDistributedFaithful pm_goal_4 initPM)
  have hlen : as.length = bs.length := by
    simp [as, bs, goal4PmRouting0Tids, goal4PmRouting1Tids]
  have hne : as ≠ [] := by
    simp [as, goal4PmRouting0Tids]
  have hcommute := stack_allGather_commute_generic_2048_64 as bs hlen hne
    h.rank0_shapes h.rank1_shapes
  have hsm := goal4_sm_stack_faithful initSM
  have hp0 := goal4_pm_stack0_faithful initPM
  have hp1 := goal4_pm_stack1_faithful initPM
  have hpm := goal4_pm4929_faithful initPM
  have hvalue : denoteGraphDistributedFaithful sm_goal_4 initSM 4929 =
      denoteGraphDistributedFaithful pm_goal_4 initPM 4929 := by
    calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 4929 =
          fw_stack (goal4SmRoutingTids.map
            (denoteGraphDistributedFaithful sm_goal_4 initSM)) := hsm
      _ = fw_stack (List.zipWith (fun a b => allGatherPrimDimN 0 2 0 [a, b])
            as bs) := congrArg fw_stack h.full_values
      _ = allGatherPrimDimN 1 2 0 [fw_stack as, fw_stack bs] := hcommute
      _ = allGatherPrimDimN 1 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 11660,
             denoteGraphDistributedFaithful pm_goal_4 initPM 11661] := by
        rw [hp0, hp1]
      _ = denoteGraphDistributedFaithful pm_goal_4 initPM 4929 := hpm.symm
  have hsmShape : (denoteGraphDistributedFaithful sm_goal_4 initSM 4929).shape =
      [24, 4096, 64] := by
    rw [hsm]
    have hhead : ((goal4SmRoutingTids.map
        (denoteGraphDistributedFaithful sm_goal_4 initSM)).head?.map
        (fun t => t.shape)).getD [] = [4096, 64] := by
      exact h.full_shapes
        (denoteGraphDistributedFaithful sm_goal_4 initSM 4965) (by
          simp [goal4SmRoutingTids])
    rw [fw_stack_shape _ [4096, 64] hhead]
    rfl
  have hpmShape : (denoteGraphDistributedFaithful pm_goal_4 initPM 4929).shape =
      [24, 4096, 64] := by rw [← hvalue]; exact hsmShape
  unfold InitGoalHolds
  refine ⟨hsmShape, ?_, ?_⟩
  · exact congrArg (fun s => [s]) hpmShape
  · unfold reconstructForGoal
    simp only [goal_4, List.map, reconstructWithDim]
    exact hvalue

end
end TrainVerify.Denote.GeneratedPatterns
