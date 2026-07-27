/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer2M_1

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer2M_1`

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

private def fnSm7560 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7560 : sm.nodes[133]'(by native_decide) = fnSm7560 := by
  native_decide

private def fnPm14847 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14847 : pm.nodes[327]'(by native_decide) = fnPm14847 := by
  native_decide

private def fnPm14855 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14855 : pm.nodes[328]'(by native_decide) = fnPm14855 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7560_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7560
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4865_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7560 =
      denoteGraphDistributedFaithful sm initSM 4865 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 133 fnSm7560 4865 7560
      (fun x => x) (by native_decide) fn_sn7560 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7560
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4865 [7560, 7564] 2 rfl 7560 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14847 =
      denoteGraphDistributedFaithful pm initPM 8025 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 327 fnPm14847 8025 14847
      (fun x => x) (by native_decide) fn_pn14847 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14847
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8025 [14847, 14851] 2 rfl 14847 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14855 =
      denoteGraphDistributedFaithful pm initPM 8026 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 328 fnPm14855 8026 14855
      (fun x => x) (by native_decide) fn_pn14855 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14855
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8026 [14855, 14859] 2 rfl 14855 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7560, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4865, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7560 =
      reconstructForGoal intermediateGoal_7560 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14847,
         denoteGraphDistributedFaithful pm initPM 14855]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4865, intermediateGoal_7560, List.map] using h3'

private def fnSm7587 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7587 : sm.nodes[135]'(by native_decide) = fnSm7587 := by
  native_decide

private def fnPm14882 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14882 : pm.nodes[331]'(by native_decide) = fnPm14882 := by
  native_decide

private def fnPm14905 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14905 : pm.nodes[332]'(by native_decide) = fnPm14905 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7587_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7587
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4867_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7587 =
      denoteGraphDistributedFaithful sm initSM 4867 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 135 fnSm7587 4867 7587
      (fun x => x) (by native_decide) fn_sn7587 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7587
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4867 [7571, 7575, 7579, 7583, 7587] 5 rfl 7587 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14882 =
      denoteGraphDistributedFaithful pm initPM 8029 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 331 fnPm14882 8029 14882
      (fun x => x) (by native_decide) fn_pn14882 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14882
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8029 [14866, 14870, 14874, 14878, 14882] 5 rfl 14882 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14905 =
      denoteGraphDistributedFaithful pm initPM 8030 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 332 fnPm14905 8030 14905
      (fun x => x) (by native_decide) fn_pn14905 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14905
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8030 [14889, 14893, 14897, 14901, 14905] 5 rfl 14905 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7587, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4867, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7587 =
      reconstructForGoal intermediateGoal_7587 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14882,
         denoteGraphDistributedFaithful pm initPM 14905]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4867, intermediateGoal_7587, List.map] using h3'

private def fnSm7579 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7579 : sm.nodes[135]'(by native_decide) = fnSm7579 := by
  native_decide

private def fnPm14874 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14874 : pm.nodes[331]'(by native_decide) = fnPm14874 := by
  native_decide

private def fnPm14897 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14897 : pm.nodes[332]'(by native_decide) = fnPm14897 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7579_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7579
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4867_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7579 =
      denoteGraphDistributedFaithful sm initSM 4867 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 135 fnSm7579 4867 7579
      (fun x => x) (by native_decide) fn_sn7579 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7579
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4867 [7571, 7575, 7579, 7583, 7587] 5 rfl 7579 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14874 =
      denoteGraphDistributedFaithful pm initPM 8029 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 331 fnPm14874 8029 14874
      (fun x => x) (by native_decide) fn_pn14874 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14874
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8029 [14866, 14870, 14874, 14878, 14882] 5 rfl 14874 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14897 =
      denoteGraphDistributedFaithful pm initPM 8030 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 332 fnPm14897 8030 14897
      (fun x => x) (by native_decide) fn_pn14897 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14897
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8030 [14889, 14893, 14897, 14901, 14905] 5 rfl 14897 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7579, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4867, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7579 =
      reconstructForGoal intermediateGoal_7579 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14874,
         denoteGraphDistributedFaithful pm initPM 14897]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4867, intermediateGoal_7579, List.map] using h3'

private def fnSm7608 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7608 : sm.nodes[160]'(by native_decide) = fnSm7608 := by
  native_decide

private def fnPm14934 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14934 : pm.nodes[381]'(by native_decide) = fnPm14934 := by
  native_decide

private def fnPm14947 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14947 : pm.nodes[382]'(by native_decide) = fnPm14947 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7608_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7608
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4900_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7608 =
      denoteGraphDistributedFaithful sm initSM 4900 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 160 fnSm7608 4900 7608
      (fun x => x) (by native_decide) fn_sn7608 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7608
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4900 [7600, 7604, 7608] 3 rfl 7608 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14934 =
      denoteGraphDistributedFaithful pm initPM 8141 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 381 fnPm14934 8141 14934
      (fun x => x) (by native_decide) fn_pn14934 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14934
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8141 [14926, 14930, 14934] 3 rfl 14934 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14947 =
      denoteGraphDistributedFaithful pm initPM 8142 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 382 fnPm14947 8142 14947
      (fun x => x) (by native_decide) fn_pn14947 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14947
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8142 [14939, 14943, 14947] 3 rfl 14947 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7608, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4900, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7608 =
      reconstructForGoal intermediateGoal_7608 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14934,
         denoteGraphDistributedFaithful pm initPM 14947]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4900, intermediateGoal_7608, List.map] using h3'

private def fnSm7604 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7604 : sm.nodes[160]'(by native_decide) = fnSm7604 := by
  native_decide

private def fnPm14930 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14930 : pm.nodes[381]'(by native_decide) = fnPm14930 := by
  native_decide

private def fnPm14943 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14943 : pm.nodes[382]'(by native_decide) = fnPm14943 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7604_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7604
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4900_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7604 =
      denoteGraphDistributedFaithful sm initSM 4900 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 160 fnSm7604 4900 7604
      (fun x => x) (by native_decide) fn_sn7604 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7604
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4900 [7600, 7604, 7608] 3 rfl 7604 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14930 =
      denoteGraphDistributedFaithful pm initPM 8141 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 381 fnPm14930 8141 14930
      (fun x => x) (by native_decide) fn_pn14930 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14930
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8141 [14926, 14930, 14934] 3 rfl 14930 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14943 =
      denoteGraphDistributedFaithful pm initPM 8142 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 382 fnPm14943 8142 14943
      (fun x => x) (by native_decide) fn_pn14943 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14943
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8142 [14939, 14943, 14947] 3 rfl 14943 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7604, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4900, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7604 =
      reconstructForGoal intermediateGoal_7604 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14930,
         denoteGraphDistributedFaithful pm initPM 14943]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4900, intermediateGoal_7604, List.map] using h3'

private def fnSm7600 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7600 : sm.nodes[160]'(by native_decide) = fnSm7600 := by
  native_decide

private def fnPm14926 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14926 : pm.nodes[381]'(by native_decide) = fnPm14926 := by
  native_decide

private def fnPm14939 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14939 : pm.nodes[382]'(by native_decide) = fnPm14939 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7600_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7600
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4900_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7600 =
      denoteGraphDistributedFaithful sm initSM 4900 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 160 fnSm7600 4900 7600
      (fun x => x) (by native_decide) fn_sn7600 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7600
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4900 [7600, 7604, 7608] 3 rfl 7600 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14926 =
      denoteGraphDistributedFaithful pm initPM 8141 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 381 fnPm14926 8141 14926
      (fun x => x) (by native_decide) fn_pn14926 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14926
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8141 [14926, 14930, 14934] 3 rfl 14926 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14939 =
      denoteGraphDistributedFaithful pm initPM 8142 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 382 fnPm14939 8142 14939
      (fun x => x) (by native_decide) fn_pn14939 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14939
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8142 [14939, 14943, 14947] 3 rfl 14939 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7600, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4900, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7600 =
      reconstructForGoal intermediateGoal_7600 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14926,
         denoteGraphDistributedFaithful pm initPM 14939]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4900, intermediateGoal_7600, List.map] using h3'

private def fnSm7635 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7635 : sm.nodes[174]'(by native_decide) = fnSm7635 := by
  native_decide

private def fnPm14982 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14982 : pm.nodes[409]'(by native_decide) = fnPm14982 := by
  native_decide

private def fnPm15005 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15005 : pm.nodes[410]'(by native_decide) = fnPm15005 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7635_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7635
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4921_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7635 =
      denoteGraphDistributedFaithful sm initSM 4921 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 174 fnSm7635 4921 7635
      (fun x => x) (by native_decide) fn_sn7635 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7635
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4921 [7623, 7627, 7631, 7635, 7639] 5 rfl 7635 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14982 =
      denoteGraphDistributedFaithful pm initPM 8215 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 409 fnPm14982 8215 14982
      (fun x => x) (by native_decide) fn_pn14982 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14982
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8215 [14970, 14974, 14978, 14982, 14986] 5 rfl 14982 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15005 =
      denoteGraphDistributedFaithful pm initPM 8216 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 410 fnPm15005 8216 15005
      (fun x => x) (by native_decide) fn_pn15005 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15005
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8216 [14993, 14997, 15001, 15005, 15009] 5 rfl 15005 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7635, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4921, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7635 =
      reconstructForGoal intermediateGoal_7635 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14982,
         denoteGraphDistributedFaithful pm initPM 15005]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4921, intermediateGoal_7635, List.map] using h3'

private def fnSm7591 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7591 : sm.nodes[158]'(by native_decide) = fnSm7591 := by
  native_decide

private def fnPm14909 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14909 : pm.nodes[377]'(by native_decide) = fnPm14909 := by
  native_decide

private def fnPm14917 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14917 : pm.nodes[378]'(by native_decide) = fnPm14917 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7591_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7591
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4898_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7591 =
      denoteGraphDistributedFaithful sm initSM 4898 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 158 fnSm7591 4898 7591
      (fun x => x) (by native_decide) fn_sn7591 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7591
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4898 [7591, 7595] 2 rfl 7591 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14909 =
      denoteGraphDistributedFaithful pm initPM 8137 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 377 fnPm14909 8137 14909
      (fun x => x) (by native_decide) fn_pn14909 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14909
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8137 [14909, 14913] 2 rfl 14909 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14917 =
      denoteGraphDistributedFaithful pm initPM 8138 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 378 fnPm14917 8138 14917
      (fun x => x) (by native_decide) fn_pn14917 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14917
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8138 [14917, 14921] 2 rfl 14917 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7591, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4898, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7591 =
      reconstructForGoal intermediateGoal_7591 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14909,
         denoteGraphDistributedFaithful pm initPM 14917]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4898, intermediateGoal_7591, List.map] using h3'

private def fnSm7612 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7612 : sm.nodes[172]'(by native_decide) = fnSm7612 := by
  native_decide

private def fnPm14951 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14951 : pm.nodes[405]'(by native_decide) = fnPm14951 := by
  native_decide

private def fnPm14959 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14959 : pm.nodes[406]'(by native_decide) = fnPm14959 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7612_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7612
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4919_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7612 =
      denoteGraphDistributedFaithful sm initSM 4919 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 172 fnSm7612 4919 7612
      (fun x => x) (by native_decide) fn_sn7612 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7612
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4919 [7612, 7616] 2 rfl 7612 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14951 =
      denoteGraphDistributedFaithful pm initPM 8211 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 405 fnPm14951 8211 14951
      (fun x => x) (by native_decide) fn_pn14951 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14951
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8211 [14951, 14955] 2 rfl 14951 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14959 =
      denoteGraphDistributedFaithful pm initPM 8212 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 406 fnPm14959 8212 14959
      (fun x => x) (by native_decide) fn_pn14959 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14959
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8212 [14959, 14963] 2 rfl 14959 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7612, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4919, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7612 =
      reconstructForGoal intermediateGoal_7612 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14951,
         denoteGraphDistributedFaithful pm initPM 14959]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4919, intermediateGoal_7612, List.map] using h3'

private def fnSm7639 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7639 : sm.nodes[174]'(by native_decide) = fnSm7639 := by
  native_decide

private def fnPm14986 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14986 : pm.nodes[409]'(by native_decide) = fnPm14986 := by
  native_decide

private def fnPm15009 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15009 : pm.nodes[410]'(by native_decide) = fnPm15009 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7639_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7639
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4921_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7639 =
      denoteGraphDistributedFaithful sm initSM 4921 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 174 fnSm7639 4921 7639
      (fun x => x) (by native_decide) fn_sn7639 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7639
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4921 [7623, 7627, 7631, 7635, 7639] 5 rfl 7639 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14986 =
      denoteGraphDistributedFaithful pm initPM 8215 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 409 fnPm14986 8215 14986
      (fun x => x) (by native_decide) fn_pn14986 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14986
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8215 [14970, 14974, 14978, 14982, 14986] 5 rfl 14986 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15009 =
      denoteGraphDistributedFaithful pm initPM 8216 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 410 fnPm15009 8216 15009
      (fun x => x) (by native_decide) fn_pn15009 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15009
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8216 [14993, 14997, 15001, 15005, 15009] 5 rfl 15009 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7639, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4921, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7639 =
      reconstructForGoal intermediateGoal_7639 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14986,
         denoteGraphDistributedFaithful pm initPM 15009]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4921, intermediateGoal_7639, List.map] using h3'

private def fnSm7571 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7571 : sm.nodes[135]'(by native_decide) = fnSm7571 := by
  native_decide

private def fnPm14866 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14866 : pm.nodes[331]'(by native_decide) = fnPm14866 := by
  native_decide

private def fnPm14889 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14889 : pm.nodes[332]'(by native_decide) = fnPm14889 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7571_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7571
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4867_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7571 =
      denoteGraphDistributedFaithful sm initSM 4867 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 135 fnSm7571 4867 7571
      (fun x => x) (by native_decide) fn_sn7571 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7571
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4867 [7571, 7575, 7579, 7583, 7587] 5 rfl 7571 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14866 =
      denoteGraphDistributedFaithful pm initPM 8029 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 331 fnPm14866 8029 14866
      (fun x => x) (by native_decide) fn_pn14866 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14866
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8029 [14866, 14870, 14874, 14878, 14882] 5 rfl 14866 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14889 =
      denoteGraphDistributedFaithful pm initPM 8030 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 332 fnPm14889 8030 14889
      (fun x => x) (by native_decide) fn_pn14889 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14889
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8030 [14889, 14893, 14897, 14901, 14905] 5 rfl 14889 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7571, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4867, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7571 =
      reconstructForGoal intermediateGoal_7571 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14866,
         denoteGraphDistributedFaithful pm initPM 14889]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4867, intermediateGoal_7571, List.map] using h3'

private def fnSm7623 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7623 : sm.nodes[174]'(by native_decide) = fnSm7623 := by
  native_decide

private def fnPm14970 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14970 : pm.nodes[409]'(by native_decide) = fnPm14970 := by
  native_decide

private def fnPm14993 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14993 : pm.nodes[410]'(by native_decide) = fnPm14993 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7623_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7623
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4921_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7623 =
      denoteGraphDistributedFaithful sm initSM 4921 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 174 fnSm7623 4921 7623
      (fun x => x) (by native_decide) fn_sn7623 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7623
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4921 [7623, 7627, 7631, 7635, 7639] 5 rfl 7623 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14970 =
      denoteGraphDistributedFaithful pm initPM 8215 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 409 fnPm14970 8215 14970
      (fun x => x) (by native_decide) fn_pn14970 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14970
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8215 [14970, 14974, 14978, 14982, 14986] 5 rfl 14970 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14993 =
      denoteGraphDistributedFaithful pm initPM 8216 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 410 fnPm14993 8216 14993
      (fun x => x) (by native_decide) fn_pn14993 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14993
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8216 [14993, 14997, 15001, 15005, 15009] 5 rfl 14993 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7623, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4921, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7623 =
      reconstructForGoal intermediateGoal_7623 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14970,
         denoteGraphDistributedFaithful pm initPM 14993]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4921, intermediateGoal_7623, List.map] using h3'

private def fnSm7583 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7583 : sm.nodes[135]'(by native_decide) = fnSm7583 := by
  native_decide

private def fnPm14878 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14878 : pm.nodes[331]'(by native_decide) = fnPm14878 := by
  native_decide

private def fnPm14901 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14901 : pm.nodes[332]'(by native_decide) = fnPm14901 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7583_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7583
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4867_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7583 =
      denoteGraphDistributedFaithful sm initSM 4867 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 135 fnSm7583 4867 7583
      (fun x => x) (by native_decide) fn_sn7583 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7583
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4867 [7571, 7575, 7579, 7583, 7587] 5 rfl 7583 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14878 =
      denoteGraphDistributedFaithful pm initPM 8029 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 331 fnPm14878 8029 14878
      (fun x => x) (by native_decide) fn_pn14878 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14878
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8029 [14866, 14870, 14874, 14878, 14882] 5 rfl 14878 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14901 =
      denoteGraphDistributedFaithful pm initPM 8030 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 332 fnPm14901 8030 14901
      (fun x => x) (by native_decide) fn_pn14901 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14901
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8030 [14889, 14893, 14897, 14901, 14905] 5 rfl 14901 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7583, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4867, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7583 =
      reconstructForGoal intermediateGoal_7583 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14878,
         denoteGraphDistributedFaithful pm initPM 14901]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4867, intermediateGoal_7583, List.map] using h3'

private def fnSm7631 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7631 : sm.nodes[174]'(by native_decide) = fnSm7631 := by
  native_decide

private def fnPm14978 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14978 : pm.nodes[409]'(by native_decide) = fnPm14978 := by
  native_decide

private def fnPm15001 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15001 : pm.nodes[410]'(by native_decide) = fnPm15001 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7631_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7631
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4921_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7631 =
      denoteGraphDistributedFaithful sm initSM 4921 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 174 fnSm7631 4921 7631
      (fun x => x) (by native_decide) fn_sn7631 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7631
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4921 [7623, 7627, 7631, 7635, 7639] 5 rfl 7631 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14978 =
      denoteGraphDistributedFaithful pm initPM 8215 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 409 fnPm14978 8215 14978
      (fun x => x) (by native_decide) fn_pn14978 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14978
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8215 [14970, 14974, 14978, 14982, 14986] 5 rfl 14978 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15001 =
      denoteGraphDistributedFaithful pm initPM 8216 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 410 fnPm15001 8216 15001
      (fun x => x) (by native_decide) fn_pn15001 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15001
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8216 [14993, 14997, 15001, 15005, 15009] 5 rfl 15001 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7631, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4921, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7631 =
      reconstructForGoal intermediateGoal_7631 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14978,
         denoteGraphDistributedFaithful pm initPM 15001]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4921, intermediateGoal_7631, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
