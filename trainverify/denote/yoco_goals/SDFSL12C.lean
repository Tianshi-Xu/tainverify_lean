/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer12C_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer12C_0`

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

private def fnSm7999 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7999 : sm.nodes[447]'(by native_decide) = fnSm7999 := by
  native_decide

private def fnPm15710 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15710 : pm.nodes[955]'(by native_decide) = fnPm15710 := by
  native_decide

private def fnPm15733 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15733 : pm.nodes[956]'(by native_decide) = fnPm15733 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7999_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7999
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5299_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7999 =
      denoteGraphDistributedFaithful sm initSM 5299 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 447 fnSm7999 5299 7999
      (fun x => x) (by native_decide) fn_sn7999 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7999
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5299 [7987, 7991, 7995, 7999, 8003] 5 rfl 7999 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15710 =
      denoteGraphDistributedFaithful pm initPM 9517 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 955 fnPm15710 9517 15710
      (fun x => x) (by native_decide) fn_pn15710 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15710
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9517 [15698, 15702, 15706, 15710, 15714] 5 rfl 15710 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15733 =
      denoteGraphDistributedFaithful pm initPM 9518 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 956 fnPm15733 9518 15733
      (fun x => x) (by native_decide) fn_pn15733 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15733
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9518 [15721, 15725, 15729, 15733, 15737] 5 rfl 15733 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7999, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5299, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7999 =
      reconstructForGoal intermediateGoal_7999 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15710,
         denoteGraphDistributedFaithful pm initPM 15733]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5299, intermediateGoal_7999, List.map] using h3'

private def fnSm7976 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7976 : sm.nodes[445]'(by native_decide) = fnSm7976 := by
  native_decide

private def fnPm15679 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15679 : pm.nodes[951]'(by native_decide) = fnPm15679 := by
  native_decide

private def fnPm15687 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15687 : pm.nodes[952]'(by native_decide) = fnPm15687 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7976_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7976
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5297_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7976 =
      denoteGraphDistributedFaithful sm initSM 5297 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 445 fnSm7976 5297 7976
      (fun x => x) (by native_decide) fn_sn7976 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7976
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5297 [7976, 7980] 2 rfl 7976 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15679 =
      denoteGraphDistributedFaithful pm initPM 9513 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 951 fnPm15679 9513 15679
      (fun x => x) (by native_decide) fn_pn15679 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15679
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9513 [15679, 15683] 2 rfl 15679 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15687 =
      denoteGraphDistributedFaithful pm initPM 9514 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 952 fnPm15687 9514 15687
      (fun x => x) (by native_decide) fn_pn15687 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15687
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9514 [15687, 15691] 2 rfl 15687 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7976, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5297, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7976 =
      reconstructForGoal intermediateGoal_7976 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15679,
         denoteGraphDistributedFaithful pm initPM 15687]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5297, intermediateGoal_7976, List.map] using h3'

private def fnSm8003 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn8003 : sm.nodes[447]'(by native_decide) = fnSm8003 := by
  native_decide

private def fnPm15714 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15714 : pm.nodes[955]'(by native_decide) = fnPm15714 := by
  native_decide

private def fnPm15737 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15737 : pm.nodes[956]'(by native_decide) = fnPm15737 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8003_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8003
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5299_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 8003 =
      denoteGraphDistributedFaithful sm initSM 5299 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 447 fnSm8003 5299 8003
      (fun x => x) (by native_decide) fn_sn8003 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm8003
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5299 [7987, 7991, 7995, 7999, 8003] 5 rfl 8003 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15714 =
      denoteGraphDistributedFaithful pm initPM 9517 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 955 fnPm15714 9517 15714
      (fun x => x) (by native_decide) fn_pn15714 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15714
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9517 [15698, 15702, 15706, 15710, 15714] 5 rfl 15714 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15737 =
      denoteGraphDistributedFaithful pm initPM 9518 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 956 fnPm15737 9518 15737
      (fun x => x) (by native_decide) fn_pn15737 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15737
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9518 [15721, 15725, 15729, 15733, 15737] 5 rfl 15737 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_8003, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5299, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 8003 =
      reconstructForGoal intermediateGoal_8003 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15714,
         denoteGraphDistributedFaithful pm initPM 15737]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5299, intermediateGoal_8003, List.map] using h3'

private def fnSm7964 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7964 : sm.nodes[433]'(by native_decide) = fnSm7964 := by
  native_decide

private def fnPm15654 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15654 : pm.nodes[927]'(by native_decide) = fnPm15654 := by
  native_decide

private def fnPm15667 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15667 : pm.nodes[928]'(by native_decide) = fnPm15667 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7964_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7964
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5278_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7964 =
      denoteGraphDistributedFaithful sm initSM 5278 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 433 fnSm7964 5278 7964
      (fun x => x) (by native_decide) fn_sn7964 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7964
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5278 [7964, 7968, 7972] 3 rfl 7964 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15654 =
      denoteGraphDistributedFaithful pm initPM 9443 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 927 fnPm15654 9443 15654
      (fun x => x) (by native_decide) fn_pn15654 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15654
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9443 [15654, 15658, 15662] 3 rfl 15654 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15667 =
      denoteGraphDistributedFaithful pm initPM 9444 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 928 fnPm15667 9444 15667
      (fun x => x) (by native_decide) fn_pn15667 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15667
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9444 [15667, 15671, 15675] 3 rfl 15667 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7964, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5278, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7964 =
      reconstructForGoal intermediateGoal_7964 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15654,
         denoteGraphDistributedFaithful pm initPM 15667]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5278, intermediateGoal_7964, List.map] using h3'

private def fnSm7968 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7968 : sm.nodes[433]'(by native_decide) = fnSm7968 := by
  native_decide

private def fnPm15658 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15658 : pm.nodes[927]'(by native_decide) = fnPm15658 := by
  native_decide

private def fnPm15671 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15671 : pm.nodes[928]'(by native_decide) = fnPm15671 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7968_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7968
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5278_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7968 =
      denoteGraphDistributedFaithful sm initSM 5278 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 433 fnSm7968 5278 7968
      (fun x => x) (by native_decide) fn_sn7968 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7968
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5278 [7964, 7968, 7972] 3 rfl 7968 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15658 =
      denoteGraphDistributedFaithful pm initPM 9443 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 927 fnPm15658 9443 15658
      (fun x => x) (by native_decide) fn_pn15658 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15658
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9443 [15654, 15658, 15662] 3 rfl 15658 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15671 =
      denoteGraphDistributedFaithful pm initPM 9444 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 928 fnPm15671 9444 15671
      (fun x => x) (by native_decide) fn_pn15671 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15671
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9444 [15667, 15671, 15675] 3 rfl 15671 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7968, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5278, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7968 =
      reconstructForGoal intermediateGoal_7968 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15658,
         denoteGraphDistributedFaithful pm initPM 15671]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5278, intermediateGoal_7968, List.map] using h3'

private def fnSm7972 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7972 : sm.nodes[433]'(by native_decide) = fnSm7972 := by
  native_decide

private def fnPm15662 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15662 : pm.nodes[927]'(by native_decide) = fnPm15662 := by
  native_decide

private def fnPm15675 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15675 : pm.nodes[928]'(by native_decide) = fnPm15675 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7972_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7972
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5278_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7972 =
      denoteGraphDistributedFaithful sm initSM 5278 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 433 fnSm7972 5278 7972
      (fun x => x) (by native_decide) fn_sn7972 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7972
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5278 [7964, 7968, 7972] 3 rfl 7972 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15662 =
      denoteGraphDistributedFaithful pm initPM 9443 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 927 fnPm15662 9443 15662
      (fun x => x) (by native_decide) fn_pn15662 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15662
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9443 [15654, 15658, 15662] 3 rfl 15662 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15675 =
      denoteGraphDistributedFaithful pm initPM 9444 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 928 fnPm15675 9444 15675
      (fun x => x) (by native_decide) fn_pn15675 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15675
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9444 [15667, 15671, 15675] 3 rfl 15675 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7972, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5278, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7972 =
      reconstructForGoal intermediateGoal_7972 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15662,
         denoteGraphDistributedFaithful pm initPM 15675]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5278, intermediateGoal_7972, List.map] using h3'

private def fnSm7995 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7995 : sm.nodes[447]'(by native_decide) = fnSm7995 := by
  native_decide

private def fnPm15706 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15706 : pm.nodes[955]'(by native_decide) = fnPm15706 := by
  native_decide

private def fnPm15729 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15729 : pm.nodes[956]'(by native_decide) = fnPm15729 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7995_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7995
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5299_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7995 =
      denoteGraphDistributedFaithful sm initSM 5299 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 447 fnSm7995 5299 7995
      (fun x => x) (by native_decide) fn_sn7995 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7995
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5299 [7987, 7991, 7995, 7999, 8003] 5 rfl 7995 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15706 =
      denoteGraphDistributedFaithful pm initPM 9517 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 955 fnPm15706 9517 15706
      (fun x => x) (by native_decide) fn_pn15706 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15706
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9517 [15698, 15702, 15706, 15710, 15714] 5 rfl 15706 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15729 =
      denoteGraphDistributedFaithful pm initPM 9518 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 956 fnPm15729 9518 15729
      (fun x => x) (by native_decide) fn_pn15729 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15729
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9518 [15721, 15725, 15729, 15733, 15737] 5 rfl 15729 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7995, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5299, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7995 =
      reconstructForGoal intermediateGoal_7995 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15706,
         denoteGraphDistributedFaithful pm initPM 15729]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5299, intermediateGoal_7995, List.map] using h3'

private def fnSm7987 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7987 : sm.nodes[447]'(by native_decide) = fnSm7987 := by
  native_decide

private def fnPm15698 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15698 : pm.nodes[955]'(by native_decide) = fnPm15698 := by
  native_decide

private def fnPm15721 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15721 : pm.nodes[956]'(by native_decide) = fnPm15721 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7987_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7987
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5299_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7987 =
      denoteGraphDistributedFaithful sm initSM 5299 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 447 fnSm7987 5299 7987
      (fun x => x) (by native_decide) fn_sn7987 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7987
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5299 [7987, 7991, 7995, 7999, 8003] 5 rfl 7987 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15698 =
      denoteGraphDistributedFaithful pm initPM 9517 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 955 fnPm15698 9517 15698
      (fun x => x) (by native_decide) fn_pn15698 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15698
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9517 [15698, 15702, 15706, 15710, 15714] 5 rfl 15698 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15721 =
      denoteGraphDistributedFaithful pm initPM 9518 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 956 fnPm15721 9518 15721
      (fun x => x) (by native_decide) fn_pn15721 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15721
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9518 [15721, 15725, 15729, 15733, 15737] 5 rfl 15721 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7987, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5299, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7987 =
      reconstructForGoal intermediateGoal_7987 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15698,
         denoteGraphDistributedFaithful pm initPM 15721]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5299, intermediateGoal_7987, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
