/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer9C_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer9C_0`

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

private def fnSm7899 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7899 : sm.nodes[369]'(by native_decide) = fnSm7899 := by
  native_decide

private def fnPm15506 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15506 : pm.nodes[799]'(by native_decide) = fnPm15506 := by
  native_decide

private def fnPm15529 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15529 : pm.nodes[800]'(by native_decide) = fnPm15529 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7899_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7899
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5191_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7899 =
      denoteGraphDistributedFaithful sm initSM 5191 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 369 fnSm7899 5191 7899
      (fun x => x) (by native_decide) fn_sn7899 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7899
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5191 [7883, 7887, 7891, 7895, 7899] 5 rfl 7899 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15506 =
      denoteGraphDistributedFaithful pm initPM 9145 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 799 fnPm15506 9145 15506
      (fun x => x) (by native_decide) fn_pn15506 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15506
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9145 [15490, 15494, 15498, 15502, 15506] 5 rfl 15506 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15529 =
      denoteGraphDistributedFaithful pm initPM 9146 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 800 fnPm15529 9146 15529
      (fun x => x) (by native_decide) fn_pn15529 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15529
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9146 [15513, 15517, 15521, 15525, 15529] 5 rfl 15529 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7899, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5191, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7899 =
      reconstructForGoal intermediateGoal_7899 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15506,
         denoteGraphDistributedFaithful pm initPM 15529]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5191, intermediateGoal_7899, List.map] using h3'

private def fnSm7860 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7860 : sm.nodes[355]'(by native_decide) = fnSm7860 := by
  native_decide

private def fnPm15446 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15446 : pm.nodes[771]'(by native_decide) = fnPm15446 := by
  native_decide

private def fnPm15459 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15459 : pm.nodes[772]'(by native_decide) = fnPm15459 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7860_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7860
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5170_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7860 =
      denoteGraphDistributedFaithful sm initSM 5170 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 355 fnSm7860 5170 7860
      (fun x => x) (by native_decide) fn_sn7860 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7860
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5170 [7860, 7864, 7868] 3 rfl 7860 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15446 =
      denoteGraphDistributedFaithful pm initPM 9071 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 771 fnPm15446 9071 15446
      (fun x => x) (by native_decide) fn_pn15446 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15446
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9071 [15446, 15450, 15454] 3 rfl 15446 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15459 =
      denoteGraphDistributedFaithful pm initPM 9072 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 772 fnPm15459 9072 15459
      (fun x => x) (by native_decide) fn_pn15459 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15459
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9072 [15459, 15463, 15467] 3 rfl 15459 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7860, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5170, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7860 =
      reconstructForGoal intermediateGoal_7860 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15446,
         denoteGraphDistributedFaithful pm initPM 15459]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5170, intermediateGoal_7860, List.map] using h3'

private def fnSm7868 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7868 : sm.nodes[355]'(by native_decide) = fnSm7868 := by
  native_decide

private def fnPm15454 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15454 : pm.nodes[771]'(by native_decide) = fnPm15454 := by
  native_decide

private def fnPm15467 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15467 : pm.nodes[772]'(by native_decide) = fnPm15467 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7868_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7868
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5170_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7868 =
      denoteGraphDistributedFaithful sm initSM 5170 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 355 fnSm7868 5170 7868
      (fun x => x) (by native_decide) fn_sn7868 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7868
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5170 [7860, 7864, 7868] 3 rfl 7868 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15454 =
      denoteGraphDistributedFaithful pm initPM 9071 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 771 fnPm15454 9071 15454
      (fun x => x) (by native_decide) fn_pn15454 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15454
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9071 [15446, 15450, 15454] 3 rfl 15454 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15467 =
      denoteGraphDistributedFaithful pm initPM 9072 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 772 fnPm15467 9072 15467
      (fun x => x) (by native_decide) fn_pn15467 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15467
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9072 [15459, 15463, 15467] 3 rfl 15467 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7868, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5170, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7868 =
      reconstructForGoal intermediateGoal_7868 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15454,
         denoteGraphDistributedFaithful pm initPM 15467]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5170, intermediateGoal_7868, List.map] using h3'

private def fnSm7895 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7895 : sm.nodes[369]'(by native_decide) = fnSm7895 := by
  native_decide

private def fnPm15502 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15502 : pm.nodes[799]'(by native_decide) = fnPm15502 := by
  native_decide

private def fnPm15525 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15525 : pm.nodes[800]'(by native_decide) = fnPm15525 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7895_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7895
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5191_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7895 =
      denoteGraphDistributedFaithful sm initSM 5191 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 369 fnSm7895 5191 7895
      (fun x => x) (by native_decide) fn_sn7895 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7895
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5191 [7883, 7887, 7891, 7895, 7899] 5 rfl 7895 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15502 =
      denoteGraphDistributedFaithful pm initPM 9145 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 799 fnPm15502 9145 15502
      (fun x => x) (by native_decide) fn_pn15502 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15502
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9145 [15490, 15494, 15498, 15502, 15506] 5 rfl 15502 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15525 =
      denoteGraphDistributedFaithful pm initPM 9146 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 800 fnPm15525 9146 15525
      (fun x => x) (by native_decide) fn_pn15525 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15525
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9146 [15513, 15517, 15521, 15525, 15529] 5 rfl 15525 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7895, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5191, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7895 =
      reconstructForGoal intermediateGoal_7895 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15502,
         denoteGraphDistributedFaithful pm initPM 15525]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5191, intermediateGoal_7895, List.map] using h3'

private def fnSm7851 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7851 : sm.nodes[353]'(by native_decide) = fnSm7851 := by
  native_decide

private def fnPm15429 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15429 : pm.nodes[767]'(by native_decide) = fnPm15429 := by
  native_decide

private def fnPm15437 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15437 : pm.nodes[768]'(by native_decide) = fnPm15437 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7851_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7851
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5168_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7851 =
      denoteGraphDistributedFaithful sm initSM 5168 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 353 fnSm7851 5168 7851
      (fun x => x) (by native_decide) fn_sn7851 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7851
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5168 [7851, 7855] 2 rfl 7851 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15429 =
      denoteGraphDistributedFaithful pm initPM 9067 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 767 fnPm15429 9067 15429
      (fun x => x) (by native_decide) fn_pn15429 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15429
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9067 [15429, 15433] 2 rfl 15429 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15437 =
      denoteGraphDistributedFaithful pm initPM 9068 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 768 fnPm15437 9068 15437
      (fun x => x) (by native_decide) fn_pn15437 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15437
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9068 [15437, 15441] 2 rfl 15437 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7851, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5168, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7851 =
      reconstructForGoal intermediateGoal_7851 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15429,
         denoteGraphDistributedFaithful pm initPM 15437]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5168, intermediateGoal_7851, List.map] using h3'

private def fnSm7872 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5189], outs := [7872, 7876],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7872 : sm.nodes[367]'(by native_decide) = fnSm7872 := by
  native_decide

private def fnPm15471 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9141], outs := [15471, 15475],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15471 : pm.nodes[795]'(by native_decide) = fnPm15471 := by
  native_decide

private def fnPm15479 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9142], outs := [15479, 15483],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15479 : pm.nodes[796]'(by native_decide) = fnPm15479 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7872_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7872
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5189_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7872 =
      denoteGraphDistributedFaithful sm initSM 5189 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 367 fnSm7872 5189 7872
      (fun x => x) (by native_decide) fn_sn7872 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7872
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5189 [7872, 7876] 2 rfl 7872 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15471 =
      denoteGraphDistributedFaithful pm initPM 9141 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 795 fnPm15471 9141 15471
      (fun x => x) (by native_decide) fn_pn15471 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15471
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9141 [15471, 15475] 2 rfl 15471 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15479 =
      denoteGraphDistributedFaithful pm initPM 9142 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 796 fnPm15479 9142 15479
      (fun x => x) (by native_decide) fn_pn15479 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15479
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9142 [15479, 15483] 2 rfl 15479 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7872, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5189, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7872 =
      reconstructForGoal intermediateGoal_7872 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15471,
         denoteGraphDistributedFaithful pm initPM 15479]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5189, intermediateGoal_7872, List.map] using h3'

private def fnSm7883 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7883 : sm.nodes[369]'(by native_decide) = fnSm7883 := by
  native_decide

private def fnPm15490 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15490 : pm.nodes[799]'(by native_decide) = fnPm15490 := by
  native_decide

private def fnPm15513 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15513 : pm.nodes[800]'(by native_decide) = fnPm15513 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7883_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7883
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5191_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7883 =
      denoteGraphDistributedFaithful sm initSM 5191 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 369 fnSm7883 5191 7883
      (fun x => x) (by native_decide) fn_sn7883 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7883
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5191 [7883, 7887, 7891, 7895, 7899] 5 rfl 7883 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15490 =
      denoteGraphDistributedFaithful pm initPM 9145 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 799 fnPm15490 9145 15490
      (fun x => x) (by native_decide) fn_pn15490 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15490
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9145 [15490, 15494, 15498, 15502, 15506] 5 rfl 15490 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15513 =
      denoteGraphDistributedFaithful pm initPM 9146 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 800 fnPm15513 9146 15513
      (fun x => x) (by native_decide) fn_pn15513 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15513
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9146 [15513, 15517, 15521, 15525, 15529] 5 rfl 15513 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7883, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5191, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7883 =
      reconstructForGoal intermediateGoal_7883 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15490,
         denoteGraphDistributedFaithful pm initPM 15513]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5191, intermediateGoal_7883, List.map] using h3'

private def fnSm7891 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7891 : sm.nodes[369]'(by native_decide) = fnSm7891 := by
  native_decide

private def fnPm15498 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15498 : pm.nodes[799]'(by native_decide) = fnPm15498 := by
  native_decide

private def fnPm15521 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15521 : pm.nodes[800]'(by native_decide) = fnPm15521 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7891_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7891
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5191_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7891 =
      denoteGraphDistributedFaithful sm initSM 5191 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 369 fnSm7891 5191 7891
      (fun x => x) (by native_decide) fn_sn7891 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7891
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5191 [7883, 7887, 7891, 7895, 7899] 5 rfl 7891 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15498 =
      denoteGraphDistributedFaithful pm initPM 9145 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 799 fnPm15498 9145 15498
      (fun x => x) (by native_decide) fn_pn15498 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15498
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9145 [15490, 15494, 15498, 15502, 15506] 5 rfl 15498 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15521 =
      denoteGraphDistributedFaithful pm initPM 9146 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 800 fnPm15521 9146 15521
      (fun x => x) (by native_decide) fn_pn15521 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15521
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9146 [15513, 15517, 15521, 15525, 15529] 5 rfl 15521 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7891, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5191, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7891 =
      reconstructForGoal intermediateGoal_7891 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15498,
         denoteGraphDistributedFaithful pm initPM 15521]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5191, intermediateGoal_7891, List.map] using h3'

private def fnSm7864 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7864 : sm.nodes[355]'(by native_decide) = fnSm7864 := by
  native_decide

private def fnPm15450 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15450 : pm.nodes[771]'(by native_decide) = fnPm15450 := by
  native_decide

private def fnPm15463 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15463 : pm.nodes[772]'(by native_decide) = fnPm15463 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7864_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7864
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5170_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7864 =
      denoteGraphDistributedFaithful sm initSM 5170 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 355 fnSm7864 5170 7864
      (fun x => x) (by native_decide) fn_sn7864 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7864
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5170 [7860, 7864, 7868] 3 rfl 7864 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15450 =
      denoteGraphDistributedFaithful pm initPM 9071 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 771 fnPm15450 9071 15450
      (fun x => x) (by native_decide) fn_pn15450 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15450
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9071 [15446, 15450, 15454] 3 rfl 15450 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15463 =
      denoteGraphDistributedFaithful pm initPM 9072 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 772 fnPm15463 9072 15463
      (fun x => x) (by native_decide) fn_pn15463 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15463
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9072 [15459, 15463, 15467] 3 rfl 15463 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7864, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5170, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7864 =
      reconstructForGoal intermediateGoal_7864 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15450,
         denoteGraphDistributedFaithful pm initPM 15463]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5170, intermediateGoal_7864, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
