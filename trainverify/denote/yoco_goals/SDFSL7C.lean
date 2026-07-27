/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer7C_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer7C_0`

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

private def fnSm7803 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7803 : sm.nodes[314]'(by native_decide) = fnSm7803 := by
  native_decide

private def fnPm15329 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15329 : pm.nodes[689]'(by native_decide) = fnPm15329 := by
  native_decide

private def fnPm15337 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15337 : pm.nodes[690]'(by native_decide) = fnPm15337 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7803_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7803
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5114_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7803 =
      denoteGraphDistributedFaithful sm initSM 5114 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 314 fnSm7803 5114 7803
      (fun x => x) (by native_decide) fn_sn7803 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7803
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5114 [7799, 7803] 2 rfl 7803 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15329 =
      denoteGraphDistributedFaithful pm initPM 8881 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 689 fnPm15329 8881 15329
      (fun x => x) (by native_decide) fn_pn15329 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15329
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8881 [15325, 15329] 2 rfl 15329 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15337 =
      denoteGraphDistributedFaithful pm initPM 8882 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 690 fnPm15337 8882 15337
      (fun x => x) (by native_decide) fn_pn15337 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15337
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8882 [15333, 15337] 2 rfl 15337 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7803, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5114, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7803 =
      reconstructForGoal intermediateGoal_7803 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15329,
         denoteGraphDistributedFaithful pm initPM 15337]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5114, intermediateGoal_7803, List.map] using h3'

private def fnSm7787 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7787 : sm.nodes[291]'(by native_decide) = fnSm7787 := by
  native_decide

private def fnPm15290 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15290 : pm.nodes[643]'(by native_decide) = fnPm15290 := by
  native_decide

private def fnPm15313 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15313 : pm.nodes[644]'(by native_decide) = fnPm15313 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7787_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7787
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5083_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7787 =
      denoteGraphDistributedFaithful sm initSM 5083 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 291 fnSm7787 5083 7787
      (fun x => x) (by native_decide) fn_sn7787 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7787
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5083 [7779, 7783, 7787, 7791, 7795] 5 rfl 7787 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15290 =
      denoteGraphDistributedFaithful pm initPM 8773 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 643 fnPm15290 8773 15290
      (fun x => x) (by native_decide) fn_pn15290 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15290
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8773 [15282, 15286, 15290, 15294, 15298] 5 rfl 15290 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15313 =
      denoteGraphDistributedFaithful pm initPM 8774 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 644 fnPm15313 8774 15313
      (fun x => x) (by native_decide) fn_pn15313 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15313
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8774 [15305, 15309, 15313, 15317, 15321] 5 rfl 15313 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7787, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5083, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7787 =
      reconstructForGoal intermediateGoal_7787 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15290,
         denoteGraphDistributedFaithful pm initPM 15313]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5083, intermediateGoal_7787, List.map] using h3'

private def fnSm7791 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7791 : sm.nodes[291]'(by native_decide) = fnSm7791 := by
  native_decide

private def fnPm15294 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15294 : pm.nodes[643]'(by native_decide) = fnPm15294 := by
  native_decide

private def fnPm15317 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15317 : pm.nodes[644]'(by native_decide) = fnPm15317 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7791_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7791
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5083_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7791 =
      denoteGraphDistributedFaithful sm initSM 5083 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 291 fnSm7791 5083 7791
      (fun x => x) (by native_decide) fn_sn7791 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7791
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5083 [7779, 7783, 7787, 7791, 7795] 5 rfl 7791 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15294 =
      denoteGraphDistributedFaithful pm initPM 8773 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 643 fnPm15294 8773 15294
      (fun x => x) (by native_decide) fn_pn15294 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15294
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8773 [15282, 15286, 15290, 15294, 15298] 5 rfl 15294 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15317 =
      denoteGraphDistributedFaithful pm initPM 8774 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 644 fnPm15317 8774 15317
      (fun x => x) (by native_decide) fn_pn15317 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15317
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8774 [15305, 15309, 15313, 15317, 15321] 5 rfl 15317 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7791, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5083, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7791 =
      reconstructForGoal intermediateGoal_7791 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15294,
         denoteGraphDistributedFaithful pm initPM 15317]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5083, intermediateGoal_7791, List.map] using h3'

private def fnSm7756 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7756 : sm.nodes[277]'(by native_decide) = fnSm7756 := by
  native_decide

private def fnPm15238 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15238 : pm.nodes[615]'(by native_decide) = fnPm15238 := by
  native_decide

private def fnPm15251 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15251 : pm.nodes[616]'(by native_decide) = fnPm15251 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7756_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7756
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5062_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7756 =
      denoteGraphDistributedFaithful sm initSM 5062 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 277 fnSm7756 5062 7756
      (fun x => x) (by native_decide) fn_sn7756 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7756
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5062 [7756, 7760, 7764] 3 rfl 7756 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15238 =
      denoteGraphDistributedFaithful pm initPM 8699 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 615 fnPm15238 8699 15238
      (fun x => x) (by native_decide) fn_pn15238 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15238
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8699 [15238, 15242, 15246] 3 rfl 15238 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15251 =
      denoteGraphDistributedFaithful pm initPM 8700 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 616 fnPm15251 8700 15251
      (fun x => x) (by native_decide) fn_pn15251 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15251
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8700 [15251, 15255, 15259] 3 rfl 15251 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7756, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5062, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7756 =
      reconstructForGoal intermediateGoal_7756 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15238,
         denoteGraphDistributedFaithful pm initPM 15251]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5062, intermediateGoal_7756, List.map] using h3'

private def fnSm7760 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7760 : sm.nodes[277]'(by native_decide) = fnSm7760 := by
  native_decide

private def fnPm15242 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15242 : pm.nodes[615]'(by native_decide) = fnPm15242 := by
  native_decide

private def fnPm15255 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15255 : pm.nodes[616]'(by native_decide) = fnPm15255 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7760_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7760
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5062_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7760 =
      denoteGraphDistributedFaithful sm initSM 5062 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 277 fnSm7760 5062 7760
      (fun x => x) (by native_decide) fn_sn7760 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7760
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5062 [7756, 7760, 7764] 3 rfl 7760 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15242 =
      denoteGraphDistributedFaithful pm initPM 8699 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 615 fnPm15242 8699 15242
      (fun x => x) (by native_decide) fn_pn15242 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15242
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8699 [15238, 15242, 15246] 3 rfl 15242 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15255 =
      denoteGraphDistributedFaithful pm initPM 8700 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 616 fnPm15255 8700 15255
      (fun x => x) (by native_decide) fn_pn15255 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15255
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8700 [15251, 15255, 15259] 3 rfl 15255 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7760, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5062, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7760 =
      reconstructForGoal intermediateGoal_7760 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15242,
         denoteGraphDistributedFaithful pm initPM 15255]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5062, intermediateGoal_7760, List.map] using h3'

private def fnSm7779 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7779 : sm.nodes[291]'(by native_decide) = fnSm7779 := by
  native_decide

private def fnPm15282 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15282 : pm.nodes[643]'(by native_decide) = fnPm15282 := by
  native_decide

private def fnPm15305 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15305 : pm.nodes[644]'(by native_decide) = fnPm15305 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7779_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7779
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5083_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7779 =
      denoteGraphDistributedFaithful sm initSM 5083 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 291 fnSm7779 5083 7779
      (fun x => x) (by native_decide) fn_sn7779 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7779
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5083 [7779, 7783, 7787, 7791, 7795] 5 rfl 7779 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15282 =
      denoteGraphDistributedFaithful pm initPM 8773 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 643 fnPm15282 8773 15282
      (fun x => x) (by native_decide) fn_pn15282 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15282
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8773 [15282, 15286, 15290, 15294, 15298] 5 rfl 15282 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15305 =
      denoteGraphDistributedFaithful pm initPM 8774 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 644 fnPm15305 8774 15305
      (fun x => x) (by native_decide) fn_pn15305 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15305
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8774 [15305, 15309, 15313, 15317, 15321] 5 rfl 15305 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7779, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5083, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7779 =
      reconstructForGoal intermediateGoal_7779 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15282,
         denoteGraphDistributedFaithful pm initPM 15305]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5083, intermediateGoal_7779, List.map] using h3'

private def fnSm7795 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7795 : sm.nodes[291]'(by native_decide) = fnSm7795 := by
  native_decide

private def fnPm15298 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15298 : pm.nodes[643]'(by native_decide) = fnPm15298 := by
  native_decide

private def fnPm15321 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15321 : pm.nodes[644]'(by native_decide) = fnPm15321 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7795_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7795
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5083_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7795 =
      denoteGraphDistributedFaithful sm initSM 5083 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 291 fnSm7795 5083 7795
      (fun x => x) (by native_decide) fn_sn7795 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7795
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5083 [7779, 7783, 7787, 7791, 7795] 5 rfl 7795 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15298 =
      denoteGraphDistributedFaithful pm initPM 8773 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 643 fnPm15298 8773 15298
      (fun x => x) (by native_decide) fn_pn15298 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15298
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8773 [15282, 15286, 15290, 15294, 15298] 5 rfl 15298 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15321 =
      denoteGraphDistributedFaithful pm initPM 8774 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 644 fnPm15321 8774 15321
      (fun x => x) (by native_decide) fn_pn15321 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15321
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8774 [15305, 15309, 15313, 15317, 15321] 5 rfl 15321 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7795, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5083, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7795 =
      reconstructForGoal intermediateGoal_7795 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15298,
         denoteGraphDistributedFaithful pm initPM 15321]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5083, intermediateGoal_7795, List.map] using h3'

private def fnSm7768 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5081], outs := [7768, 7772],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7768 : sm.nodes[289]'(by native_decide) = fnSm7768 := by
  native_decide

private def fnPm15263 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8769], outs := [15263, 15267],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15263 : pm.nodes[639]'(by native_decide) = fnPm15263 := by
  native_decide

private def fnPm15271 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8770], outs := [15271, 15275],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15271 : pm.nodes[640]'(by native_decide) = fnPm15271 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7768_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7768
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5081_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7768 =
      denoteGraphDistributedFaithful sm initSM 5081 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 289 fnSm7768 5081 7768
      (fun x => x) (by native_decide) fn_sn7768 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7768
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5081 [7768, 7772] 2 rfl 7768 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15263 =
      denoteGraphDistributedFaithful pm initPM 8769 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 639 fnPm15263 8769 15263
      (fun x => x) (by native_decide) fn_pn15263 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15263
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8769 [15263, 15267] 2 rfl 15263 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15271 =
      denoteGraphDistributedFaithful pm initPM 8770 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 640 fnPm15271 8770 15271
      (fun x => x) (by native_decide) fn_pn15271 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15271
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8770 [15271, 15275] 2 rfl 15271 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7768, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5081, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7768 =
      reconstructForGoal intermediateGoal_7768 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15263,
         denoteGraphDistributedFaithful pm initPM 15271]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5081, intermediateGoal_7768, List.map] using h3'

private def fnSm7764 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7764 : sm.nodes[277]'(by native_decide) = fnSm7764 := by
  native_decide

private def fnPm15246 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15246 : pm.nodes[615]'(by native_decide) = fnPm15246 := by
  native_decide

private def fnPm15259 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15259 : pm.nodes[616]'(by native_decide) = fnPm15259 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7764_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7764
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5062_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7764 =
      denoteGraphDistributedFaithful sm initSM 5062 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 277 fnSm7764 5062 7764
      (fun x => x) (by native_decide) fn_sn7764 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7764
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5062 [7756, 7760, 7764] 3 rfl 7764 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15246 =
      denoteGraphDistributedFaithful pm initPM 8699 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 615 fnPm15246 8699 15246
      (fun x => x) (by native_decide) fn_pn15246 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15246
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8699 [15238, 15242, 15246] 3 rfl 15246 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15259 =
      denoteGraphDistributedFaithful pm initPM 8700 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 616 fnPm15259 8700 15259
      (fun x => x) (by native_decide) fn_pn15259 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15259
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8700 [15251, 15255, 15259] 3 rfl 15259 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7764, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5062, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7764 =
      reconstructForGoal intermediateGoal_7764 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15246,
         denoteGraphDistributedFaithful pm initPM 15259]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5062, intermediateGoal_7764, List.map] using h3'

private def fnSm7799 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7799 : sm.nodes[314]'(by native_decide) = fnSm7799 := by
  native_decide

private def fnPm15325 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15325 : pm.nodes[689]'(by native_decide) = fnPm15325 := by
  native_decide

private def fnPm15333 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15333 : pm.nodes[690]'(by native_decide) = fnPm15333 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7799_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7799
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5114_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7799 =
      denoteGraphDistributedFaithful sm initSM 5114 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 314 fnSm7799 5114 7799
      (fun x => x) (by native_decide) fn_sn7799 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7799
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5114 [7799, 7803] 2 rfl 7799 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15325 =
      denoteGraphDistributedFaithful pm initPM 8881 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 689 fnPm15325 8881 15325
      (fun x => x) (by native_decide) fn_pn15325 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15325
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8881 [15325, 15329] 2 rfl 15325 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15333 =
      denoteGraphDistributedFaithful pm initPM 8882 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 690 fnPm15333 8882 15333
      (fun x => x) (by native_decide) fn_pn15333 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15333
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8882 [15333, 15337] 2 rfl 15333 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7799, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5114, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7799 =
      reconstructForGoal intermediateGoal_7799 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15325,
         denoteGraphDistributedFaithful pm initPM 15333]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5114, intermediateGoal_7799, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
