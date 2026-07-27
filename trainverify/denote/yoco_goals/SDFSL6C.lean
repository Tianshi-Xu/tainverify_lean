/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer6C_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer6C_0`

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

private def fnSm7704 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7704 : sm.nodes[238]'(by native_decide) = fnSm7704 := by
  native_decide

private def fnPm15134 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15134 : pm.nodes[537]'(by native_decide) = fnPm15134 := by
  native_decide

private def fnPm15147 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15147 : pm.nodes[538]'(by native_decide) = fnPm15147 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7704_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7704
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5008_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7704 =
      denoteGraphDistributedFaithful sm initSM 5008 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 238 fnSm7704 5008 7704
      (fun x => x) (by native_decide) fn_sn7704 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7704
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5008 [7704, 7708, 7712] 3 rfl 7704 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15134 =
      denoteGraphDistributedFaithful pm initPM 8513 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 537 fnPm15134 8513 15134
      (fun x => x) (by native_decide) fn_pn15134 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15134
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8513 [15134, 15138, 15142] 3 rfl 15134 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15147 =
      denoteGraphDistributedFaithful pm initPM 8514 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 538 fnPm15147 8514 15147
      (fun x => x) (by native_decide) fn_pn15147 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15147
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8514 [15147, 15151, 15155] 3 rfl 15147 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7704, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5008, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7704 =
      reconstructForGoal intermediateGoal_7704 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15134,
         denoteGraphDistributedFaithful pm initPM 15147]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5008, intermediateGoal_7704, List.map] using h3'

private def fnSm7735 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7735 : sm.nodes[252]'(by native_decide) = fnSm7735 := by
  native_decide

private def fnPm15186 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15186 : pm.nodes[565]'(by native_decide) = fnPm15186 := by
  native_decide

private def fnPm15209 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15209 : pm.nodes[566]'(by native_decide) = fnPm15209 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7735_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7735
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5029_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7735 =
      denoteGraphDistributedFaithful sm initSM 5029 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 252 fnSm7735 5029 7735
      (fun x => x) (by native_decide) fn_sn7735 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7735
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5029 [7727, 7731, 7735, 7739, 7743] 5 rfl 7735 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15186 =
      denoteGraphDistributedFaithful pm initPM 8587 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 565 fnPm15186 8587 15186
      (fun x => x) (by native_decide) fn_pn15186 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15186
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8587 [15178, 15182, 15186, 15190, 15194] 5 rfl 15186 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15209 =
      denoteGraphDistributedFaithful pm initPM 8588 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 566 fnPm15209 8588 15209
      (fun x => x) (by native_decide) fn_pn15209 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15209
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8588 [15201, 15205, 15209, 15213, 15217] 5 rfl 15209 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7735, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5029, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7735 =
      reconstructForGoal intermediateGoal_7735 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15186,
         denoteGraphDistributedFaithful pm initPM 15209]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5029, intermediateGoal_7735, List.map] using h3'

private def fnSm7743 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7743 : sm.nodes[252]'(by native_decide) = fnSm7743 := by
  native_decide

private def fnPm15194 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15194 : pm.nodes[565]'(by native_decide) = fnPm15194 := by
  native_decide

private def fnPm15217 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15217 : pm.nodes[566]'(by native_decide) = fnPm15217 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7743_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7743
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5029_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7743 =
      denoteGraphDistributedFaithful sm initSM 5029 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 252 fnSm7743 5029 7743
      (fun x => x) (by native_decide) fn_sn7743 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7743
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5029 [7727, 7731, 7735, 7739, 7743] 5 rfl 7743 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15194 =
      denoteGraphDistributedFaithful pm initPM 8587 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 565 fnPm15194 8587 15194
      (fun x => x) (by native_decide) fn_pn15194 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15194
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8587 [15178, 15182, 15186, 15190, 15194] 5 rfl 15194 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15217 =
      denoteGraphDistributedFaithful pm initPM 8588 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 566 fnPm15217 8588 15217
      (fun x => x) (by native_decide) fn_pn15217 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15217
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8588 [15201, 15205, 15209, 15213, 15217] 5 rfl 15217 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7743, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5029, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7743 =
      reconstructForGoal intermediateGoal_7743 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15194,
         denoteGraphDistributedFaithful pm initPM 15217]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5029, intermediateGoal_7743, List.map] using h3'

private def fnSm7716 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5027], outs := [7716, 7720],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7716 : sm.nodes[250]'(by native_decide) = fnSm7716 := by
  native_decide

private def fnPm15159 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8583], outs := [15159, 15163],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15159 : pm.nodes[561]'(by native_decide) = fnPm15159 := by
  native_decide

private def fnPm15167 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8584], outs := [15167, 15171],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15167 : pm.nodes[562]'(by native_decide) = fnPm15167 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7716_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7716
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5027_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7716 =
      denoteGraphDistributedFaithful sm initSM 5027 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 250 fnSm7716 5027 7716
      (fun x => x) (by native_decide) fn_sn7716 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7716
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5027 [7716, 7720] 2 rfl 7716 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15159 =
      denoteGraphDistributedFaithful pm initPM 8583 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 561 fnPm15159 8583 15159
      (fun x => x) (by native_decide) fn_pn15159 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15159
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8583 [15159, 15163] 2 rfl 15159 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15167 =
      denoteGraphDistributedFaithful pm initPM 8584 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 562 fnPm15167 8584 15167
      (fun x => x) (by native_decide) fn_pn15167 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15167
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8584 [15167, 15171] 2 rfl 15167 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7716, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5027, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7716 =
      reconstructForGoal intermediateGoal_7716 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15159,
         denoteGraphDistributedFaithful pm initPM 15167]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5027, intermediateGoal_7716, List.map] using h3'

private def fnSm7739 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7739 : sm.nodes[252]'(by native_decide) = fnSm7739 := by
  native_decide

private def fnPm15190 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15190 : pm.nodes[565]'(by native_decide) = fnPm15190 := by
  native_decide

private def fnPm15213 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15213 : pm.nodes[566]'(by native_decide) = fnPm15213 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7739_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7739
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5029_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7739 =
      denoteGraphDistributedFaithful sm initSM 5029 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 252 fnSm7739 5029 7739
      (fun x => x) (by native_decide) fn_sn7739 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7739
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5029 [7727, 7731, 7735, 7739, 7743] 5 rfl 7739 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15190 =
      denoteGraphDistributedFaithful pm initPM 8587 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 565 fnPm15190 8587 15190
      (fun x => x) (by native_decide) fn_pn15190 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15190
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8587 [15178, 15182, 15186, 15190, 15194] 5 rfl 15190 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15213 =
      denoteGraphDistributedFaithful pm initPM 8588 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 566 fnPm15213 8588 15213
      (fun x => x) (by native_decide) fn_pn15213 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15213
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8588 [15201, 15205, 15209, 15213, 15217] 5 rfl 15213 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7739, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5029, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7739 =
      reconstructForGoal intermediateGoal_7739 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15190,
         denoteGraphDistributedFaithful pm initPM 15213]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5029, intermediateGoal_7739, List.map] using h3'

private def fnSm7708 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7708 : sm.nodes[238]'(by native_decide) = fnSm7708 := by
  native_decide

private def fnPm15138 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15138 : pm.nodes[537]'(by native_decide) = fnPm15138 := by
  native_decide

private def fnPm15151 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15151 : pm.nodes[538]'(by native_decide) = fnPm15151 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7708_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7708
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5008_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7708 =
      denoteGraphDistributedFaithful sm initSM 5008 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 238 fnSm7708 5008 7708
      (fun x => x) (by native_decide) fn_sn7708 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7708
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5008 [7704, 7708, 7712] 3 rfl 7708 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15138 =
      denoteGraphDistributedFaithful pm initPM 8513 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 537 fnPm15138 8513 15138
      (fun x => x) (by native_decide) fn_pn15138 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15138
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8513 [15134, 15138, 15142] 3 rfl 15138 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15151 =
      denoteGraphDistributedFaithful pm initPM 8514 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 538 fnPm15151 8514 15151
      (fun x => x) (by native_decide) fn_pn15151 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15151
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8514 [15147, 15151, 15155] 3 rfl 15151 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7708, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5008, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7708 =
      reconstructForGoal intermediateGoal_7708 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15138,
         denoteGraphDistributedFaithful pm initPM 15151]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5008, intermediateGoal_7708, List.map] using h3'

private def fnSm7727 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7727 : sm.nodes[252]'(by native_decide) = fnSm7727 := by
  native_decide

private def fnPm15178 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15178 : pm.nodes[565]'(by native_decide) = fnPm15178 := by
  native_decide

private def fnPm15201 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15201 : pm.nodes[566]'(by native_decide) = fnPm15201 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7727_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7727
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5029_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7727 =
      denoteGraphDistributedFaithful sm initSM 5029 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 252 fnSm7727 5029 7727
      (fun x => x) (by native_decide) fn_sn7727 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7727
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5029 [7727, 7731, 7735, 7739, 7743] 5 rfl 7727 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15178 =
      denoteGraphDistributedFaithful pm initPM 8587 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 565 fnPm15178 8587 15178
      (fun x => x) (by native_decide) fn_pn15178 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15178
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8587 [15178, 15182, 15186, 15190, 15194] 5 rfl 15178 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15201 =
      denoteGraphDistributedFaithful pm initPM 8588 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 566 fnPm15201 8588 15201
      (fun x => x) (by native_decide) fn_pn15201 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15201
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8588 [15201, 15205, 15209, 15213, 15217] 5 rfl 15201 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7727, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5029, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7727 =
      reconstructForGoal intermediateGoal_7727 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15178,
         denoteGraphDistributedFaithful pm initPM 15201]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5029, intermediateGoal_7727, List.map] using h3'

private def fnSm7712 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7712 : sm.nodes[238]'(by native_decide) = fnSm7712 := by
  native_decide

private def fnPm15142 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15142 : pm.nodes[537]'(by native_decide) = fnPm15142 := by
  native_decide

private def fnPm15155 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15155 : pm.nodes[538]'(by native_decide) = fnPm15155 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7712_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7712
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5008_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7712 =
      denoteGraphDistributedFaithful sm initSM 5008 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 238 fnSm7712 5008 7712
      (fun x => x) (by native_decide) fn_sn7712 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7712
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5008 [7704, 7708, 7712] 3 rfl 7712 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15142 =
      denoteGraphDistributedFaithful pm initPM 8513 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 537 fnPm15142 8513 15142
      (fun x => x) (by native_decide) fn_pn15142 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15142
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8513 [15134, 15138, 15142] 3 rfl 15142 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15155 =
      denoteGraphDistributedFaithful pm initPM 8514 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 538 fnPm15155 8514 15155
      (fun x => x) (by native_decide) fn_pn15155 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15155
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8514 [15147, 15151, 15155] 3 rfl 15155 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7712, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5008, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7712 =
      reconstructForGoal intermediateGoal_7712 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15142,
         denoteGraphDistributedFaithful pm initPM 15155]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5008, intermediateGoal_7712, List.map] using h3'

private def fnSm7695 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7695 : sm.nodes[236]'(by native_decide) = fnSm7695 := by
  native_decide

private def fnPm15117 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15117 : pm.nodes[533]'(by native_decide) = fnPm15117 := by
  native_decide

private def fnPm15125 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15125 : pm.nodes[534]'(by native_decide) = fnPm15125 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7695_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7695
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5006_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7695 =
      denoteGraphDistributedFaithful sm initSM 5006 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 236 fnSm7695 5006 7695
      (fun x => x) (by native_decide) fn_sn7695 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7695
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5006 [7695, 7699] 2 rfl 7695 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15117 =
      denoteGraphDistributedFaithful pm initPM 8509 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 533 fnPm15117 8509 15117
      (fun x => x) (by native_decide) fn_pn15117 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15117
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8509 [15117, 15121] 2 rfl 15117 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15125 =
      denoteGraphDistributedFaithful pm initPM 8510 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 534 fnPm15125 8510 15125
      (fun x => x) (by native_decide) fn_pn15125 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15125
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8510 [15125, 15129] 2 rfl 15125 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7695, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5006, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7695 =
      reconstructForGoal intermediateGoal_7695 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15117,
         denoteGraphDistributedFaithful pm initPM 15125]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5006, intermediateGoal_7695, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
