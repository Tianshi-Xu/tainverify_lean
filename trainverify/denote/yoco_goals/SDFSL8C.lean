/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer8C_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer8C_0`

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

private def fnSm7808 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7808 : sm.nodes[316]'(by native_decide) = fnSm7808 := by
  native_decide

private def fnPm15342 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15342 : pm.nodes[693]'(by native_decide) = fnPm15342 := by
  native_decide

private def fnPm15355 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15355 : pm.nodes[694]'(by native_decide) = fnPm15355 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7808_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7808
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5116_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7808 =
      denoteGraphDistributedFaithful sm initSM 5116 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 316 fnSm7808 5116 7808
      (fun x => x) (by native_decide) fn_sn7808 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7808
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5116 [7808, 7812, 7816] 3 rfl 7808 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15342 =
      denoteGraphDistributedFaithful pm initPM 8885 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 693 fnPm15342 8885 15342
      (fun x => x) (by native_decide) fn_pn15342 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15342
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8885 [15342, 15346, 15350] 3 rfl 15342 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15355 =
      denoteGraphDistributedFaithful pm initPM 8886 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 694 fnPm15355 8886 15355
      (fun x => x) (by native_decide) fn_pn15355 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15355
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8886 [15355, 15359, 15363] 3 rfl 15355 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7808, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5116, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7808 =
      reconstructForGoal intermediateGoal_7808 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15342,
         denoteGraphDistributedFaithful pm initPM 15355]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5116, intermediateGoal_7808, List.map] using h3'

private def fnSm7847 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7847 : sm.nodes[330]'(by native_decide) = fnSm7847 := by
  native_decide

private def fnPm15402 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15402 : pm.nodes[721]'(by native_decide) = fnPm15402 := by
  native_decide

private def fnPm15425 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15425 : pm.nodes[722]'(by native_decide) = fnPm15425 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7847_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7847
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5137_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7847 =
      denoteGraphDistributedFaithful sm initSM 5137 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 330 fnSm7847 5137 7847
      (fun x => x) (by native_decide) fn_sn7847 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7847
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5137 [7831, 7835, 7839, 7843, 7847] 5 rfl 7847 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15402 =
      denoteGraphDistributedFaithful pm initPM 8959 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 721 fnPm15402 8959 15402
      (fun x => x) (by native_decide) fn_pn15402 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15402
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8959 [15386, 15390, 15394, 15398, 15402] 5 rfl 15402 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15425 =
      denoteGraphDistributedFaithful pm initPM 8960 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 722 fnPm15425 8960 15425
      (fun x => x) (by native_decide) fn_pn15425 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15425
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8960 [15409, 15413, 15417, 15421, 15425] 5 rfl 15425 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7847, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5137, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7847 =
      reconstructForGoal intermediateGoal_7847 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15402,
         denoteGraphDistributedFaithful pm initPM 15425]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5137, intermediateGoal_7847, List.map] using h3'

private def fnSm7831 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7831 : sm.nodes[330]'(by native_decide) = fnSm7831 := by
  native_decide

private def fnPm15386 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15386 : pm.nodes[721]'(by native_decide) = fnPm15386 := by
  native_decide

private def fnPm15409 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15409 : pm.nodes[722]'(by native_decide) = fnPm15409 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7831_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7831
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5137_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7831 =
      denoteGraphDistributedFaithful sm initSM 5137 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 330 fnSm7831 5137 7831
      (fun x => x) (by native_decide) fn_sn7831 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7831
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5137 [7831, 7835, 7839, 7843, 7847] 5 rfl 7831 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15386 =
      denoteGraphDistributedFaithful pm initPM 8959 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 721 fnPm15386 8959 15386
      (fun x => x) (by native_decide) fn_pn15386 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15386
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8959 [15386, 15390, 15394, 15398, 15402] 5 rfl 15386 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15409 =
      denoteGraphDistributedFaithful pm initPM 8960 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 722 fnPm15409 8960 15409
      (fun x => x) (by native_decide) fn_pn15409 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15409
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8960 [15409, 15413, 15417, 15421, 15425] 5 rfl 15409 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7831, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5137, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7831 =
      reconstructForGoal intermediateGoal_7831 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15386,
         denoteGraphDistributedFaithful pm initPM 15409]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5137, intermediateGoal_7831, List.map] using h3'

private def fnSm7820 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7820 : sm.nodes[328]'(by native_decide) = fnSm7820 := by
  native_decide

private def fnPm15367 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15367 : pm.nodes[717]'(by native_decide) = fnPm15367 := by
  native_decide

private def fnPm15375 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15375 : pm.nodes[718]'(by native_decide) = fnPm15375 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7820_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7820
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5135_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7820 =
      denoteGraphDistributedFaithful sm initSM 5135 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 328 fnSm7820 5135 7820
      (fun x => x) (by native_decide) fn_sn7820 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7820
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5135 [7820, 7824] 2 rfl 7820 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15367 =
      denoteGraphDistributedFaithful pm initPM 8955 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 717 fnPm15367 8955 15367
      (fun x => x) (by native_decide) fn_pn15367 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15367
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8955 [15367, 15371] 2 rfl 15367 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15375 =
      denoteGraphDistributedFaithful pm initPM 8956 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 718 fnPm15375 8956 15375
      (fun x => x) (by native_decide) fn_pn15375 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15375
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8956 [15375, 15379] 2 rfl 15375 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7820, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5135, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7820 =
      reconstructForGoal intermediateGoal_7820 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15367,
         denoteGraphDistributedFaithful pm initPM 15375]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5135, intermediateGoal_7820, List.map] using h3'

private def fnSm7843 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7843 : sm.nodes[330]'(by native_decide) = fnSm7843 := by
  native_decide

private def fnPm15398 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15398 : pm.nodes[721]'(by native_decide) = fnPm15398 := by
  native_decide

private def fnPm15421 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15421 : pm.nodes[722]'(by native_decide) = fnPm15421 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7843_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7843
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5137_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7843 =
      denoteGraphDistributedFaithful sm initSM 5137 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 330 fnSm7843 5137 7843
      (fun x => x) (by native_decide) fn_sn7843 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7843
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5137 [7831, 7835, 7839, 7843, 7847] 5 rfl 7843 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15398 =
      denoteGraphDistributedFaithful pm initPM 8959 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 721 fnPm15398 8959 15398
      (fun x => x) (by native_decide) fn_pn15398 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15398
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8959 [15386, 15390, 15394, 15398, 15402] 5 rfl 15398 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15421 =
      denoteGraphDistributedFaithful pm initPM 8960 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 722 fnPm15421 8960 15421
      (fun x => x) (by native_decide) fn_pn15421 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15421
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8960 [15409, 15413, 15417, 15421, 15425] 5 rfl 15421 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7843, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5137, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7843 =
      reconstructForGoal intermediateGoal_7843 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15398,
         denoteGraphDistributedFaithful pm initPM 15421]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5137, intermediateGoal_7843, List.map] using h3'

private def fnSm7812 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7812 : sm.nodes[316]'(by native_decide) = fnSm7812 := by
  native_decide

private def fnPm15346 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15346 : pm.nodes[693]'(by native_decide) = fnPm15346 := by
  native_decide

private def fnPm15359 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15359 : pm.nodes[694]'(by native_decide) = fnPm15359 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7812_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7812
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5116_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7812 =
      denoteGraphDistributedFaithful sm initSM 5116 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 316 fnSm7812 5116 7812
      (fun x => x) (by native_decide) fn_sn7812 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7812
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5116 [7808, 7812, 7816] 3 rfl 7812 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15346 =
      denoteGraphDistributedFaithful pm initPM 8885 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 693 fnPm15346 8885 15346
      (fun x => x) (by native_decide) fn_pn15346 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15346
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8885 [15342, 15346, 15350] 3 rfl 15346 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15359 =
      denoteGraphDistributedFaithful pm initPM 8886 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 694 fnPm15359 8886 15359
      (fun x => x) (by native_decide) fn_pn15359 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15359
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8886 [15355, 15359, 15363] 3 rfl 15359 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7812, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5116, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7812 =
      reconstructForGoal intermediateGoal_7812 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15346,
         denoteGraphDistributedFaithful pm initPM 15359]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5116, intermediateGoal_7812, List.map] using h3'

private def fnSm7816 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7816 : sm.nodes[316]'(by native_decide) = fnSm7816 := by
  native_decide

private def fnPm15350 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15350 : pm.nodes[693]'(by native_decide) = fnPm15350 := by
  native_decide

private def fnPm15363 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15363 : pm.nodes[694]'(by native_decide) = fnPm15363 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7816_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7816
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5116_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7816 =
      denoteGraphDistributedFaithful sm initSM 5116 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 316 fnSm7816 5116 7816
      (fun x => x) (by native_decide) fn_sn7816 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7816
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5116 [7808, 7812, 7816] 3 rfl 7816 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15350 =
      denoteGraphDistributedFaithful pm initPM 8885 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 693 fnPm15350 8885 15350
      (fun x => x) (by native_decide) fn_pn15350 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15350
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8885 [15342, 15346, 15350] 3 rfl 15350 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15363 =
      denoteGraphDistributedFaithful pm initPM 8886 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 694 fnPm15363 8886 15363
      (fun x => x) (by native_decide) fn_pn15363 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15363
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8886 [15355, 15359, 15363] 3 rfl 15363 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7816, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5116, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7816 =
      reconstructForGoal intermediateGoal_7816 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15350,
         denoteGraphDistributedFaithful pm initPM 15363]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5116, intermediateGoal_7816, List.map] using h3'

private def fnSm7839 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7839 : sm.nodes[330]'(by native_decide) = fnSm7839 := by
  native_decide

private def fnPm15394 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15394 : pm.nodes[721]'(by native_decide) = fnPm15394 := by
  native_decide

private def fnPm15417 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15417 : pm.nodes[722]'(by native_decide) = fnPm15417 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7839_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7839
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5137_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7839 =
      denoteGraphDistributedFaithful sm initSM 5137 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 330 fnSm7839 5137 7839
      (fun x => x) (by native_decide) fn_sn7839 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7839
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5137 [7831, 7835, 7839, 7843, 7847] 5 rfl 7839 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15394 =
      denoteGraphDistributedFaithful pm initPM 8959 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 721 fnPm15394 8959 15394
      (fun x => x) (by native_decide) fn_pn15394 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15394
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8959 [15386, 15390, 15394, 15398, 15402] 5 rfl 15394 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15417 =
      denoteGraphDistributedFaithful pm initPM 8960 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 722 fnPm15417 8960 15417
      (fun x => x) (by native_decide) fn_pn15417 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15417
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8960 [15409, 15413, 15417, 15421, 15425] 5 rfl 15417 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7839, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5137, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7839 =
      reconstructForGoal intermediateGoal_7839 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15394,
         denoteGraphDistributedFaithful pm initPM 15417]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5137, intermediateGoal_7839, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
