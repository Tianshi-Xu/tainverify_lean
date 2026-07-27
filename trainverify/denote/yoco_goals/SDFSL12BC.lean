/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer12BC_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer12BC_0`

`FW_multiref` forwards each rank's shard unchanged, and the goal reconstructs
exactly as its parent does, so all three components of `InitGoalHolds` transfer
after rewriting the tids. No `hWF` and no reasoning about `reconstructWithDim`
itself.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def fnSm8011 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn8011 : sm.nodes[470]'(by native_decide) = fnSm8011 := by
  native_decide

private def fnPm13257 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn13257 : pm.nodes[1001]'(by native_decide) = fnPm13257 := by
  native_decide

private def fnPm13258 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn13258 : pm.nodes[1002]'(by native_decide) = fnPm13258 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8011_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8011
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5330_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 8011 =
      denoteGraphDistributedFaithful sm initSM 5330 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 470 fnSm8011 5330 8011
      (fun x => x) (by native_decide) fn_sn8011 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm8011
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5330 [8007, 8011] 2 rfl 8011 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 13257 =
      denoteGraphDistributedFaithful pm initPM 9625 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1001 fnPm13257 9625 13257
      (fun x => x) (by native_decide) fn_pn13257 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm13257
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9625 [14597, 13257] 2 rfl 13257 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 13258 =
      denoteGraphDistributedFaithful pm initPM 9626 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1002 fnPm13258 9626 13258
      (fun x => x) (by native_decide) fn_pn13258 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm13258
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9626 [14599, 13258] 2 rfl 13258 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_8011, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5330, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 8011 =
      reconstructForGoal intermediateGoal_8011 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 13257,
         denoteGraphDistributedFaithful pm initPM 13258]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5330, intermediateGoal_8011, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
