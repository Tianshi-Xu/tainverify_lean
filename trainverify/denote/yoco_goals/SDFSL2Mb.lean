/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer2M_2

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer2M_2`

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

private def fnSm7691 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7691 : sm.nodes[213]'(by native_decide) = fnSm7691 := by
  native_decide

private def fnPm15090 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15090 : pm.nodes[487]'(by native_decide) = fnPm15090 := by
  native_decide

private def fnPm15113 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15113 : pm.nodes[488]'(by native_decide) = fnPm15113 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7691_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7691
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4975_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7691 =
      denoteGraphDistributedFaithful sm initSM 4975 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 213 fnSm7691 4975 7691
      (fun x => x) (by native_decide) fn_sn7691 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7691
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4975 [7675, 7679, 7683, 7687, 7691] 5 rfl 7691 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15090 =
      denoteGraphDistributedFaithful pm initPM 8401 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 487 fnPm15090 8401 15090
      (fun x => x) (by native_decide) fn_pn15090 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15090
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8401 [15074, 15078, 15082, 15086, 15090] 5 rfl 15090 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15113 =
      denoteGraphDistributedFaithful pm initPM 8402 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 488 fnPm15113 8402 15113
      (fun x => x) (by native_decide) fn_pn15113 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15113
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8402 [15097, 15101, 15105, 15109, 15113] 5 rfl 15113 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7691, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4975, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7691 =
      reconstructForGoal intermediateGoal_7691 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15090,
         denoteGraphDistributedFaithful pm initPM 15113]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4975, intermediateGoal_7691, List.map] using h3'

private def fnSm7687 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7687 : sm.nodes[213]'(by native_decide) = fnSm7687 := by
  native_decide

private def fnPm15086 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15086 : pm.nodes[487]'(by native_decide) = fnPm15086 := by
  native_decide

private def fnPm15109 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15109 : pm.nodes[488]'(by native_decide) = fnPm15109 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7687_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7687
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4975_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7687 =
      denoteGraphDistributedFaithful sm initSM 4975 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 213 fnSm7687 4975 7687
      (fun x => x) (by native_decide) fn_sn7687 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7687
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4975 [7675, 7679, 7683, 7687, 7691] 5 rfl 7687 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15086 =
      denoteGraphDistributedFaithful pm initPM 8401 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 487 fnPm15086 8401 15086
      (fun x => x) (by native_decide) fn_pn15086 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15086
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8401 [15074, 15078, 15082, 15086, 15090] 5 rfl 15086 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15109 =
      denoteGraphDistributedFaithful pm initPM 8402 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 488 fnPm15109 8402 15109
      (fun x => x) (by native_decide) fn_pn15109 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15109
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8402 [15097, 15101, 15105, 15109, 15113] 5 rfl 15109 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7687, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4975, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7687 =
      reconstructForGoal intermediateGoal_7687 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15086,
         denoteGraphDistributedFaithful pm initPM 15109]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4975, intermediateGoal_7687, List.map] using h3'

private def fnSm7643 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7643 : sm.nodes[197]'(by native_decide) = fnSm7643 := by
  native_decide

private def fnPm15013 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15013 : pm.nodes[455]'(by native_decide) = fnPm15013 := by
  native_decide

private def fnPm15021 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15021 : pm.nodes[456]'(by native_decide) = fnPm15021 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7643_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7643
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4952_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7643 =
      denoteGraphDistributedFaithful sm initSM 4952 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 197 fnSm7643 4952 7643
      (fun x => x) (by native_decide) fn_sn7643 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7643
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4952 [7643, 7647] 2 rfl 7643 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15013 =
      denoteGraphDistributedFaithful pm initPM 8323 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 455 fnPm15013 8323 15013
      (fun x => x) (by native_decide) fn_pn15013 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15013
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8323 [15013, 15017] 2 rfl 15013 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15021 =
      denoteGraphDistributedFaithful pm initPM 8324 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 456 fnPm15021 8324 15021
      (fun x => x) (by native_decide) fn_pn15021 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15021
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8324 [15021, 15025] 2 rfl 15021 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7643, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4952, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7643 =
      reconstructForGoal intermediateGoal_7643 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15013,
         denoteGraphDistributedFaithful pm initPM 15021]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4952, intermediateGoal_7643, List.map] using h3'

private def fnSm7675 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7675 : sm.nodes[213]'(by native_decide) = fnSm7675 := by
  native_decide

private def fnPm15074 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15074 : pm.nodes[487]'(by native_decide) = fnPm15074 := by
  native_decide

private def fnPm15097 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15097 : pm.nodes[488]'(by native_decide) = fnPm15097 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7675_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7675
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4975_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7675 =
      denoteGraphDistributedFaithful sm initSM 4975 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 213 fnSm7675 4975 7675
      (fun x => x) (by native_decide) fn_sn7675 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7675
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4975 [7675, 7679, 7683, 7687, 7691] 5 rfl 7675 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15074 =
      denoteGraphDistributedFaithful pm initPM 8401 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 487 fnPm15074 8401 15074
      (fun x => x) (by native_decide) fn_pn15074 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15074
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8401 [15074, 15078, 15082, 15086, 15090] 5 rfl 15074 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15097 =
      denoteGraphDistributedFaithful pm initPM 8402 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 488 fnPm15097 8402 15097
      (fun x => x) (by native_decide) fn_pn15097 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15097
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8402 [15097, 15101, 15105, 15109, 15113] 5 rfl 15097 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7675, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4975, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7675 =
      reconstructForGoal intermediateGoal_7675 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15074,
         denoteGraphDistributedFaithful pm initPM 15097]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4975, intermediateGoal_7675, List.map] using h3'

private def fnSm7652 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7652 : sm.nodes[199]'(by native_decide) = fnSm7652 := by
  native_decide

private def fnPm15030 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15030 : pm.nodes[459]'(by native_decide) = fnPm15030 := by
  native_decide

private def fnPm15043 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15043 : pm.nodes[460]'(by native_decide) = fnPm15043 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7652_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7652
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4954_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7652 =
      denoteGraphDistributedFaithful sm initSM 4954 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 199 fnSm7652 4954 7652
      (fun x => x) (by native_decide) fn_sn7652 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7652
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4954 [7652, 7656, 7660] 3 rfl 7652 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15030 =
      denoteGraphDistributedFaithful pm initPM 8327 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 459 fnPm15030 8327 15030
      (fun x => x) (by native_decide) fn_pn15030 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15030
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8327 [15030, 15034, 15038] 3 rfl 15030 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15043 =
      denoteGraphDistributedFaithful pm initPM 8328 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 460 fnPm15043 8328 15043
      (fun x => x) (by native_decide) fn_pn15043 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15043
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8328 [15043, 15047, 15051] 3 rfl 15043 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7652, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4954, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7652 =
      reconstructForGoal intermediateGoal_7652 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15030,
         denoteGraphDistributedFaithful pm initPM 15043]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4954, intermediateGoal_7652, List.map] using h3'

private def fnSm7664 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4973], outs := [7664, 7668],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7664 : sm.nodes[211]'(by native_decide) = fnSm7664 := by
  native_decide

private def fnPm15055 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8397], outs := [15055, 15059],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15055 : pm.nodes[483]'(by native_decide) = fnPm15055 := by
  native_decide

private def fnPm15063 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8398], outs := [15063, 15067],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15063 : pm.nodes[484]'(by native_decide) = fnPm15063 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7664_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7664
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4973_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7664 =
      denoteGraphDistributedFaithful sm initSM 4973 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 211 fnSm7664 4973 7664
      (fun x => x) (by native_decide) fn_sn7664 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7664
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4973 [7664, 7668] 2 rfl 7664 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15055 =
      denoteGraphDistributedFaithful pm initPM 8397 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 483 fnPm15055 8397 15055
      (fun x => x) (by native_decide) fn_pn15055 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15055
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8397 [15055, 15059] 2 rfl 15055 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15063 =
      denoteGraphDistributedFaithful pm initPM 8398 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 484 fnPm15063 8398 15063
      (fun x => x) (by native_decide) fn_pn15063 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15063
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8398 [15063, 15067] 2 rfl 15063 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7664, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4973, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7664 =
      reconstructForGoal intermediateGoal_7664 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15055,
         denoteGraphDistributedFaithful pm initPM 15063]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4973, intermediateGoal_7664, List.map] using h3'

private def fnSm7683 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7683 : sm.nodes[213]'(by native_decide) = fnSm7683 := by
  native_decide

private def fnPm15082 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15082 : pm.nodes[487]'(by native_decide) = fnPm15082 := by
  native_decide

private def fnPm15105 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15105 : pm.nodes[488]'(by native_decide) = fnPm15105 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7683_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7683
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4975_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7683 =
      denoteGraphDistributedFaithful sm initSM 4975 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 213 fnSm7683 4975 7683
      (fun x => x) (by native_decide) fn_sn7683 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7683
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4975 [7675, 7679, 7683, 7687, 7691] 5 rfl 7683 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15082 =
      denoteGraphDistributedFaithful pm initPM 8401 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 487 fnPm15082 8401 15082
      (fun x => x) (by native_decide) fn_pn15082 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15082
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8401 [15074, 15078, 15082, 15086, 15090] 5 rfl 15082 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15105 =
      denoteGraphDistributedFaithful pm initPM 8402 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 488 fnPm15105 8402 15105
      (fun x => x) (by native_decide) fn_pn15105 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15105
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8402 [15097, 15101, 15105, 15109, 15113] 5 rfl 15105 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7683, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4975, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7683 =
      reconstructForGoal intermediateGoal_7683 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15082,
         denoteGraphDistributedFaithful pm initPM 15105]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4975, intermediateGoal_7683, List.map] using h3'

private def fnSm7656 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7656 : sm.nodes[199]'(by native_decide) = fnSm7656 := by
  native_decide

private def fnPm15034 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15034 : pm.nodes[459]'(by native_decide) = fnPm15034 := by
  native_decide

private def fnPm15047 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15047 : pm.nodes[460]'(by native_decide) = fnPm15047 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7656_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7656
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4954_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7656 =
      denoteGraphDistributedFaithful sm initSM 4954 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 199 fnSm7656 4954 7656
      (fun x => x) (by native_decide) fn_sn7656 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7656
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4954 [7652, 7656, 7660] 3 rfl 7656 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15034 =
      denoteGraphDistributedFaithful pm initPM 8327 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 459 fnPm15034 8327 15034
      (fun x => x) (by native_decide) fn_pn15034 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15034
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8327 [15030, 15034, 15038] 3 rfl 15034 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15047 =
      denoteGraphDistributedFaithful pm initPM 8328 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 460 fnPm15047 8328 15047
      (fun x => x) (by native_decide) fn_pn15047 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15047
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8328 [15043, 15047, 15051] 3 rfl 15047 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7656, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4954, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7656 =
      reconstructForGoal intermediateGoal_7656 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15034,
         denoteGraphDistributedFaithful pm initPM 15047]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4954, intermediateGoal_7656, List.map] using h3'

private def fnSm7660 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7660 : sm.nodes[199]'(by native_decide) = fnSm7660 := by
  native_decide

private def fnPm15038 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15038 : pm.nodes[459]'(by native_decide) = fnPm15038 := by
  native_decide

private def fnPm15051 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15051 : pm.nodes[460]'(by native_decide) = fnPm15051 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7660_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7660
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4954_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7660 =
      denoteGraphDistributedFaithful sm initSM 4954 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 199 fnSm7660 4954 7660
      (fun x => x) (by native_decide) fn_sn7660 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7660
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4954 [7652, 7656, 7660] 3 rfl 7660 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15038 =
      denoteGraphDistributedFaithful pm initPM 8327 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 459 fnPm15038 8327 15038
      (fun x => x) (by native_decide) fn_pn15038 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15038
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8327 [15030, 15034, 15038] 3 rfl 15038 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15051 =
      denoteGraphDistributedFaithful pm initPM 8328 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 460 fnPm15051 8328 15051
      (fun x => x) (by native_decide) fn_pn15051 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15051
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8328 [15043, 15047, 15051] 3 rfl 15051 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7660, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4954, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7660 =
      reconstructForGoal intermediateGoal_7660 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15038,
         denoteGraphDistributedFaithful pm initPM 15051]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4954, intermediateGoal_7660, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
