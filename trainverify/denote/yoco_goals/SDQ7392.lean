/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRN4683

/-!
# The QKV fan-out

`7392` / `7396` / `7400` are the three outputs of the arity-3 `FW_multiref` off
the normalised `4683`, feeding the Q, K and V projections. All replicated.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def m3Sm7392 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400],
    params := [3] }

private def m3Pm14620 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [14620, 14624, 14628],
    params := [3] }

private def m3Pm14632 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem m3_sn7392 : sm.nodes[4]'(by native_decide) = m3Sm7392 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem m3_pn14620 : pm.nodes[33]'(by native_decide) = m3Pm14620 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem m3_pn14632 : pm.nodes[34]'(by native_decide) = m3Pm14632 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7392_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7392
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4683_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4683 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hval
    exact hval
  have hs : (denoteGraphDistributedFaithful sm initSM 4683).shape = [4096, 1024] :=
    hparent.1
  have rSM : denoteGraphDistributedFaithful sm initSM 7392 =
      denoteGraphDistributedFaithful sm initSM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 4 m3Sm7392 4683 7392
      (fun x => x) (by native_decide) m3_sn7392 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold m3Sm7392
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4683 [7392, 7396, 7400] 3 rfl 7392 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14620 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 33 m3Pm14620 4683 14620
      (fun x => x) (by native_decide) m3_pn14620 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold m3Pm14620
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4683 [14620, 14624, 14628] 3 rfl 14620 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14632 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 34 m3Pm14632 4683 14632
      (fun x => x) (by native_decide) m3_pn14632 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold m3Pm14632
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4683 [14632, 14636, 14640] 3 rfl 14632 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7392, List.map]
  refine ⟨by rw [rSM]; exact hs, ?_, ?_⟩
  · rw [rPM0, rPM1, ← hv, hs]
  · rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons, rSM, rPM0, hv]

end

end TrainVerify.Denote.GeneratedPatterns
