/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRN4683

/-!
# Shard agreement for the QKV fan-out

A replicated `LineageGoal` pins only its rank-0 shard, but the PM node writing a
downstream tid last belongs to rank 1. The two are equal — not because the goal
says so, but because both are outputs of the same `FW_multiref` off `4683`.
These lemmas discharge that once, for the three QKV branches.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def qkvPm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [14620, 14624, 14628],
    params := [3] }

private def qkvPm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem qkv_pn0 : pm.nodes[33]'(by native_decide) = qkvPm0 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem qkv_pn1 : pm.nodes[34]'(by native_decide) = qkvPm1 := by
  native_decide

-- Both PM shards of the replicated fan-out `7392` reduce to `4683`. The goal
-- statement pins only rank 0; the graph is what relates the two.
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem pm_7392_shards_agree (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 14620 =
      denoteGraphDistributedFaithful pm initPM 14632 := by
  have r0 : denoteGraphDistributedFaithful pm initPM 14620 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 33 qkvPm0 4683 14620
      (fun x => x) (by native_decide) qkv_pn0 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold qkvPm0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4683 [14620, 14624, 14628] 3 rfl 14620 (by decide)
  have r1 : denoteGraphDistributedFaithful pm initPM 14632 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 34 qkvPm1 4683 14632
      (fun x => x) (by native_decide) qkv_pn1 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold qkvPm1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4683 [14632, 14636, 14640] 3 rfl 14632 (by decide)
  rw [r0, ← r1]

-- Both PM shards of the replicated fan-out `7396` reduce to `4683`. The goal
-- statement pins only rank 0; the graph is what relates the two.
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem pm_7396_shards_agree (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 14624 =
      denoteGraphDistributedFaithful pm initPM 14636 := by
  have r0 : denoteGraphDistributedFaithful pm initPM 14624 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 33 qkvPm0 4683 14624
      (fun x => x) (by native_decide) qkv_pn0 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold qkvPm0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4683 [14620, 14624, 14628] 3 rfl 14624 (by decide)
  have r1 : denoteGraphDistributedFaithful pm initPM 14636 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 34 qkvPm1 4683 14636
      (fun x => x) (by native_decide) qkv_pn1 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold qkvPm1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4683 [14632, 14636, 14640] 3 rfl 14636 (by decide)
  rw [r0, ← r1]

-- Both PM shards of the replicated fan-out `7400` reduce to `4683`. The goal
-- statement pins only rank 0; the graph is what relates the two.
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem pm_7400_shards_agree (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 14628 =
      denoteGraphDistributedFaithful pm initPM 14640 := by
  have r0 : denoteGraphDistributedFaithful pm initPM 14628 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 33 qkvPm0 4683 14628
      (fun x => x) (by native_decide) qkv_pn0 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold qkvPm0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4683 [14620, 14624, 14628] 3 rfl 14628 (by decide)
  have r1 : denoteGraphDistributedFaithful pm initPM 14640 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 34 qkvPm1 4683 14640
      (fun x => x) (by native_decide) qkv_pn1 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold qkvPm1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4683 [14632, 14636, 14640] 3 rfl 14640 (by decide)
  rw [r0, ← r1]

end

end TrainVerify.Denote.GeneratedPatterns
