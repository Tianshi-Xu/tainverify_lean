import denote.yoco_goals.Goal_1

/-!
# Generated PM to Goal 1 faithful bridge before shuffle

`Generated.pm` and `pm_goal_1` have different full node lists and replica-group
lists.  Their first 1043 nodes nevertheless agree, and every graph-sensitive
replica group used by that prefix (sliding-window attention and full-expert MoE)
resolves to the same ordered buddy list.  This file transports values whose last
writer is in that prefix from the ordinary distributed evaluator on `pm` to the
faithful distributed evaluator on `pm_goal_1`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def preShufflePMTids : List Tid :=
  [9394, 9395, 9468, 9469, 9558, 9559, 9632, 9633, 9722, 9723]

set_option maxRecDepth 1000000 in
private theorem pre_shuffle_pm_facts :
    pm.numRanks = pm_goal_1.numRanks ∧
    pm.nodes.take 1043 = pm_goal_1.nodes.take 1043 ∧
    (∀ n ∈ pm.nodes.take 1043,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag") ∧
    (∀ n ∈ pm.nodes.take 1043,
      (n.op = "OpName.FW_all2all_moe_gmm" ∨
        n.op = "OpName.FW_attn_sliding_window") →
      pm.replicaBuddies n = pm_goal_1.replicaBuddies n) ∧
    (∀ tid ∈ preShufflePMTids,
      (∀ n ∈ pm.nodes.drop 1043, n.outs ≠ []) ∧
      (∀ n ∈ pm.nodes.drop 1043, tid ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes.drop 1043, n.outs ≠ []) ∧
      (∀ n ∈ pm_goal_1.nodes.drop 1043, tid ∉ n.outs)) := by
  native_decide

/-- One prefix step agrees across the two concrete graphs.  The MoE branch uses
`replicaBuddies`; the sliding-window branch uses the same metadata through
`ringAttnBuddies`; the remaining branch depends only on `numRanks`. -/
private theorem pre_shuffle_pm_step_eq (s : Store) (n : NodeDecl)
    (hn : n ∈ pm.nodes.take 1043) :
    applyNodeDistributed pm s n = applyNodeDistributedFaithful pm_goal_1 s n := by
  rcases pre_shuffle_pm_facts with ⟨hranks, _, hops, hbuddies, _⟩
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    pm_goal_1 s n (hops n hn).1 (hops n hn).2.1 (hops n hn).2.2]
  unfold applyNodeDistributed
  by_cases hmoe : n.op = "OpName.FW_all2all_moe_gmm"
  · rw [if_pos hmoe, if_pos hmoe]
    unfold applyNodeFullExpertMoE_value
    rw [hbuddies n hn (Or.inl hmoe)]
  · rw [if_neg hmoe, if_neg hmoe]
    unfold applyNodeRingAttn
    rw [if_neg (hops n hn).2.2, if_neg (hops n hn).2.2]
    by_cases hwindow : n.op = "OpName.FW_attn_sliding_window"
    · rw [if_pos hwindow, if_pos hwindow]
      unfold applyNodeRingAttn_sliding_window ringAttnBuddies
      rw [hbuddies n hn (Or.inr hwindow)]
    · rw [if_neg hwindow, if_neg hwindow]
      rw [applyNode_congr_numRanks pm pm_goal_1 hranks]

private theorem foldl_eq_of_steps
    (f g : Store → NodeDecl → Store) (nodes : List NodeDecl) (init : Store)
    (hstep : ∀ n ∈ nodes, ∀ s, f s n = g s n) :
    nodes.foldl f init = nodes.foldl g init := by
  induction nodes generalizing init with
  | nil => rfl
  | cons n rest ih =>
      rw [List.foldl_cons, List.foldl_cons, hstep n List.mem_cons_self init]
      apply ih
      intro m hm s
      exact hstep m (List.mem_cons_of_mem n hm) s

private theorem pre_shuffle_pm_fold_eq (init : Store) :
    (pm.nodes.take 1043).foldl (applyNodeDistributed pm) init =
      (pm_goal_1.nodes.take 1043).foldl
        (applyNodeDistributedFaithful pm_goal_1) init := by
  have hnodes := pre_shuffle_pm_facts.2.1
  rw [← hnodes]
  let pre := pm.nodes.take 1043
  have hstep : ∀ n ∈ pre, ∀ s,
      applyNodeDistributed pm s n = applyNodeDistributedFaithful pm_goal_1 s n := by
    intro n hn s
    exact pre_shuffle_pm_step_eq s n hn
  change pre.foldl (applyNodeDistributed pm) init =
    pre.foldl (applyNodeDistributedFaithful pm_goal_1) init
  exact foldl_eq_of_steps _ _ pre init hstep

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- General Generated-to-Goal1 value bridge for the audited pre-shuffle TIDs. -/
theorem generated_pm_to_goal_1_faithful_pre_shuffle (init : Store) (tid : Tid)
    (htid : tid ∈ preShufflePMTids) :
    denoteGraphDistributed pm init tid =
      denoteGraphDistributedFaithful pm_goal_1 init tid := by
  rcases pre_shuffle_pm_facts.2.2.2.2 tid htid with ⟨pnil, pwrite, gnil, gwrite⟩
  rw [denoteGraphDistributed_eq_prefix pm init tid 1043 pnil pwrite,
    denoteGraphDistributedFaithful_eq_prefix pm_goal_1 init tid 1043 gnil gwrite,
    pre_shuffle_pm_fold_eq init]

/-- Layer-9 ordinary rank-0 boundary. -/
theorem generated_pm_9394_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9394 =
      denoteGraphDistributedFaithful pm_goal_1 init 9394 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9394 (by decide)

/-- Layer-9 ordinary rank-1 boundary. -/
theorem generated_pm_9395_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9395 =
      denoteGraphDistributedFaithful pm_goal_1 init 9395 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9395 (by decide)

/-- Layer-10 ordinary rank-0 boundary. -/
theorem generated_pm_9468_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9468 =
      denoteGraphDistributedFaithful pm_goal_1 init 9468 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9468 (by decide)

/-- Layer-10 ordinary rank-1 boundary. -/
theorem generated_pm_9469_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9469 =
      denoteGraphDistributedFaithful pm_goal_1 init 9469 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9469 (by decide)

/-- Layer-10 MoE-exit ordinary rank-0 boundary. -/
theorem generated_pm_9558_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9558 =
      denoteGraphDistributedFaithful pm_goal_1 init 9558 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9558 (by decide)

/-- Layer-10 MoE-exit ordinary rank-1 boundary. -/
theorem generated_pm_9559_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9559 =
      denoteGraphDistributedFaithful pm_goal_1 init 9559 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9559 (by decide)

/-- Layer-11 ordinary rank-0 boundary. -/
theorem generated_pm_9632_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9632 =
      denoteGraphDistributedFaithful pm_goal_1 init 9632 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9632 (by decide)

/-- Layer-11 ordinary rank-1 boundary. -/
theorem generated_pm_9633_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9633 =
      denoteGraphDistributedFaithful pm_goal_1 init 9633 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9633 (by decide)

/-- Layer-11 MoE-exit ordinary rank-0 boundary. -/
theorem generated_pm_9722_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9722 =
      denoteGraphDistributedFaithful pm_goal_1 init 9722 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9722 (by decide)

/-- Layer-11 MoE-exit ordinary rank-1 boundary. -/
theorem generated_pm_9723_to_goal_1_faithful (init : Store) :
    denoteGraphDistributed pm init 9723 =
      denoteGraphDistributedFaithful pm_goal_1 init 9723 :=
  generated_pm_to_goal_1_faithful_pre_shuffle init 9723 (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
