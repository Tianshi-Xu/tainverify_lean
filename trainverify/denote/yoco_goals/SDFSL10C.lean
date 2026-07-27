/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer10C_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer10C_0`

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

private def fnSm7903 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7903 : sm.nodes[392]'(by native_decide) = fnSm7903 := by
  native_decide

private def fnPm15533 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15533 : pm.nodes[845]'(by native_decide) = fnPm15533 := by
  native_decide

private def fnPm15541 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15541 : pm.nodes[846]'(by native_decide) = fnPm15541 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7903_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7903
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5222_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7903 =
      denoteGraphDistributedFaithful sm initSM 5222 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 392 fnSm7903 5222 7903
      (fun x => x) (by native_decide) fn_sn7903 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7903
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5222 [7903, 7907] 2 rfl 7903 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15533 =
      denoteGraphDistributedFaithful pm initPM 9253 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 845 fnPm15533 9253 15533
      (fun x => x) (by native_decide) fn_pn15533 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15533
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9253 [15533, 15537] 2 rfl 15533 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15541 =
      denoteGraphDistributedFaithful pm initPM 9254 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 846 fnPm15541 9254 15541
      (fun x => x) (by native_decide) fn_pn15541 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15541
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9254 [15541, 15545] 2 rfl 15541 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7903, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5222, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7903 =
      reconstructForGoal intermediateGoal_7903 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15533,
         denoteGraphDistributedFaithful pm initPM 15541]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5222, intermediateGoal_7903, List.map] using h3'

private def fnSm7916 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7916 : sm.nodes[394]'(by native_decide) = fnSm7916 := by
  native_decide

private def fnPm15554 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15554 : pm.nodes[849]'(by native_decide) = fnPm15554 := by
  native_decide

private def fnPm15567 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15567 : pm.nodes[850]'(by native_decide) = fnPm15567 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7916_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7916
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5224_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7916 =
      denoteGraphDistributedFaithful sm initSM 5224 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 394 fnSm7916 5224 7916
      (fun x => x) (by native_decide) fn_sn7916 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7916
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5224 [7912, 7916, 7920] 3 rfl 7916 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15554 =
      denoteGraphDistributedFaithful pm initPM 9257 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 849 fnPm15554 9257 15554
      (fun x => x) (by native_decide) fn_pn15554 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15554
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9257 [15550, 15554, 15558] 3 rfl 15554 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15567 =
      denoteGraphDistributedFaithful pm initPM 9258 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 850 fnPm15567 9258 15567
      (fun x => x) (by native_decide) fn_pn15567 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15567
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9258 [15563, 15567, 15571] 3 rfl 15567 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7916, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5224, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7916 =
      reconstructForGoal intermediateGoal_7916 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15554,
         denoteGraphDistributedFaithful pm initPM 15567]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5224, intermediateGoal_7916, List.map] using h3'

private def fnSm7920 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7920 : sm.nodes[394]'(by native_decide) = fnSm7920 := by
  native_decide

private def fnPm15558 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15558 : pm.nodes[849]'(by native_decide) = fnPm15558 := by
  native_decide

private def fnPm15571 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15571 : pm.nodes[850]'(by native_decide) = fnPm15571 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7920_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7920
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5224_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7920 =
      denoteGraphDistributedFaithful sm initSM 5224 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 394 fnSm7920 5224 7920
      (fun x => x) (by native_decide) fn_sn7920 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7920
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5224 [7912, 7916, 7920] 3 rfl 7920 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15558 =
      denoteGraphDistributedFaithful pm initPM 9257 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 849 fnPm15558 9257 15558
      (fun x => x) (by native_decide) fn_pn15558 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15558
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9257 [15550, 15554, 15558] 3 rfl 15558 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15571 =
      denoteGraphDistributedFaithful pm initPM 9258 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 850 fnPm15571 9258 15571
      (fun x => x) (by native_decide) fn_pn15571 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15571
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9258 [15563, 15567, 15571] 3 rfl 15571 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7920, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5224, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7920 =
      reconstructForGoal intermediateGoal_7920 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15558,
         denoteGraphDistributedFaithful pm initPM 15571]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5224, intermediateGoal_7920, List.map] using h3'

private def fnSm7912 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7912 : sm.nodes[394]'(by native_decide) = fnSm7912 := by
  native_decide

private def fnPm15550 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15550 : pm.nodes[849]'(by native_decide) = fnPm15550 := by
  native_decide

private def fnPm15563 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15563 : pm.nodes[850]'(by native_decide) = fnPm15563 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7912_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7912
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5224_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7912 =
      denoteGraphDistributedFaithful sm initSM 5224 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 394 fnSm7912 5224 7912
      (fun x => x) (by native_decide) fn_sn7912 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7912
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5224 [7912, 7916, 7920] 3 rfl 7912 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15550 =
      denoteGraphDistributedFaithful pm initPM 9257 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 849 fnPm15550 9257 15550
      (fun x => x) (by native_decide) fn_pn15550 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15550
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9257 [15550, 15554, 15558] 3 rfl 15550 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15563 =
      denoteGraphDistributedFaithful pm initPM 9258 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 850 fnPm15563 9258 15563
      (fun x => x) (by native_decide) fn_pn15563 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15563
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9258 [15563, 15567, 15571] 3 rfl 15563 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7912, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5224, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7912 =
      reconstructForGoal intermediateGoal_7912 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15550,
         denoteGraphDistributedFaithful pm initPM 15563]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5224, intermediateGoal_7912, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
