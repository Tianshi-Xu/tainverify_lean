/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer11C_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer11C_0`

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

private def fnSm7924 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5243], outs := [7924, 7928],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7924 : sm.nodes[406]'(by native_decide) = fnSm7924 := by
  native_decide

private def fnPm15575 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9327], outs := [15575, 15579],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15575 : pm.nodes[873]'(by native_decide) = fnPm15575 := by
  native_decide

private def fnPm15583 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9328], outs := [15583, 15587],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15583 : pm.nodes[874]'(by native_decide) = fnPm15583 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7924_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7924
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5243_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7924 =
      denoteGraphDistributedFaithful sm initSM 5243 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 406 fnSm7924 5243 7924
      (fun x => x) (by native_decide) fn_sn7924 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7924
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5243 [7924, 7928] 2 rfl 7924 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15575 =
      denoteGraphDistributedFaithful pm initPM 9327 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 873 fnPm15575 9327 15575
      (fun x => x) (by native_decide) fn_pn15575 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15575
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9327 [15575, 15579] 2 rfl 15575 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15583 =
      denoteGraphDistributedFaithful pm initPM 9328 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 874 fnPm15583 9328 15583
      (fun x => x) (by native_decide) fn_pn15583 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15583
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9328 [15583, 15587] 2 rfl 15583 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7924, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5243, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7924 =
      reconstructForGoal intermediateGoal_7924 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15575,
         denoteGraphDistributedFaithful pm initPM 15583]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5243, intermediateGoal_7924, List.map] using h3'

private def fnSm7951 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7951 : sm.nodes[408]'(by native_decide) = fnSm7951 := by
  native_decide

private def fnPm15610 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15610 : pm.nodes[877]'(by native_decide) = fnPm15610 := by
  native_decide

private def fnPm15633 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15633 : pm.nodes[878]'(by native_decide) = fnPm15633 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7951_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7951
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5245_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7951 =
      denoteGraphDistributedFaithful sm initSM 5245 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 408 fnSm7951 5245 7951
      (fun x => x) (by native_decide) fn_sn7951 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7951
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5245 [7935, 7939, 7943, 7947, 7951] 5 rfl 7951 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15610 =
      denoteGraphDistributedFaithful pm initPM 9331 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 877 fnPm15610 9331 15610
      (fun x => x) (by native_decide) fn_pn15610 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15610
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9331 [15594, 15598, 15602, 15606, 15610] 5 rfl 15610 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15633 =
      denoteGraphDistributedFaithful pm initPM 9332 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 878 fnPm15633 9332 15633
      (fun x => x) (by native_decide) fn_pn15633 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15633
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9332 [15617, 15621, 15625, 15629, 15633] 5 rfl 15633 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7951, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5245, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7951 =
      reconstructForGoal intermediateGoal_7951 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15610,
         denoteGraphDistributedFaithful pm initPM 15633]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5245, intermediateGoal_7951, List.map] using h3'

private def fnSm7943 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7943 : sm.nodes[408]'(by native_decide) = fnSm7943 := by
  native_decide

private def fnPm15602 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15602 : pm.nodes[877]'(by native_decide) = fnPm15602 := by
  native_decide

private def fnPm15625 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15625 : pm.nodes[878]'(by native_decide) = fnPm15625 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7943_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7943
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5245_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7943 =
      denoteGraphDistributedFaithful sm initSM 5245 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 408 fnSm7943 5245 7943
      (fun x => x) (by native_decide) fn_sn7943 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7943
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5245 [7935, 7939, 7943, 7947, 7951] 5 rfl 7943 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15602 =
      denoteGraphDistributedFaithful pm initPM 9331 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 877 fnPm15602 9331 15602
      (fun x => x) (by native_decide) fn_pn15602 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15602
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9331 [15594, 15598, 15602, 15606, 15610] 5 rfl 15602 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15625 =
      denoteGraphDistributedFaithful pm initPM 9332 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 878 fnPm15625 9332 15625
      (fun x => x) (by native_decide) fn_pn15625 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15625
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9332 [15617, 15621, 15625, 15629, 15633] 5 rfl 15625 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7943, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5245, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7943 =
      reconstructForGoal intermediateGoal_7943 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15602,
         denoteGraphDistributedFaithful pm initPM 15625]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5245, intermediateGoal_7943, List.map] using h3'

private def fnSm7935 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7935 : sm.nodes[408]'(by native_decide) = fnSm7935 := by
  native_decide

private def fnPm15594 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15594 : pm.nodes[877]'(by native_decide) = fnPm15594 := by
  native_decide

private def fnPm15617 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15617 : pm.nodes[878]'(by native_decide) = fnPm15617 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7935_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7935
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5245_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7935 =
      denoteGraphDistributedFaithful sm initSM 5245 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 408 fnSm7935 5245 7935
      (fun x => x) (by native_decide) fn_sn7935 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7935
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5245 [7935, 7939, 7943, 7947, 7951] 5 rfl 7935 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15594 =
      denoteGraphDistributedFaithful pm initPM 9331 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 877 fnPm15594 9331 15594
      (fun x => x) (by native_decide) fn_pn15594 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15594
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9331 [15594, 15598, 15602, 15606, 15610] 5 rfl 15594 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15617 =
      denoteGraphDistributedFaithful pm initPM 9332 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 878 fnPm15617 9332 15617
      (fun x => x) (by native_decide) fn_pn15617 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15617
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9332 [15617, 15621, 15625, 15629, 15633] 5 rfl 15617 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7935, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5245, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7935 =
      reconstructForGoal intermediateGoal_7935 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15594,
         denoteGraphDistributedFaithful pm initPM 15617]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5245, intermediateGoal_7935, List.map] using h3'

private def fnSm7947 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7947 : sm.nodes[408]'(by native_decide) = fnSm7947 := by
  native_decide

private def fnPm15606 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15606 : pm.nodes[877]'(by native_decide) = fnPm15606 := by
  native_decide

private def fnPm15629 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15629 : pm.nodes[878]'(by native_decide) = fnPm15629 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7947_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7947
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5245_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7947 =
      denoteGraphDistributedFaithful sm initSM 5245 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 408 fnSm7947 5245 7947
      (fun x => x) (by native_decide) fn_sn7947 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7947
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5245 [7935, 7939, 7943, 7947, 7951] 5 rfl 7947 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15606 =
      denoteGraphDistributedFaithful pm initPM 9331 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 877 fnPm15606 9331 15606
      (fun x => x) (by native_decide) fn_pn15606 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15606
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9331 [15594, 15598, 15602, 15606, 15610] 5 rfl 15606 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15629 =
      denoteGraphDistributedFaithful pm initPM 9332 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 878 fnPm15629 9332 15629
      (fun x => x) (by native_decide) fn_pn15629 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15629
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9332 [15617, 15621, 15625, 15629, 15633] 5 rfl 15629 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7947, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5245, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7947 =
      reconstructForGoal intermediateGoal_7947 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15606,
         denoteGraphDistributedFaithful pm initPM 15629]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5245, intermediateGoal_7947, List.map] using h3'

private def fnSm7955 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7955 : sm.nodes[431]'(by native_decide) = fnSm7955 := by
  native_decide

private def fnPm15637 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15637 : pm.nodes[923]'(by native_decide) = fnPm15637 := by
  native_decide

private def fnPm15645 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn15645 : pm.nodes[924]'(by native_decide) = fnPm15645 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7955_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7955
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5276_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7955 =
      denoteGraphDistributedFaithful sm initSM 5276 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 431 fnSm7955 5276 7955
      (fun x => x) (by native_decide) fn_sn7955 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7955
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5276 [7955, 7959] 2 rfl 7955 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15637 =
      denoteGraphDistributedFaithful pm initPM 9439 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 923 fnPm15637 9439 15637
      (fun x => x) (by native_decide) fn_pn15637 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15637
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9439 [15637, 15641] 2 rfl 15637 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15645 =
      denoteGraphDistributedFaithful pm initPM 9440 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 924 fnPm15645 9440 15645
      (fun x => x) (by native_decide) fn_pn15645 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15645
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9440 [15645, 15649] 2 rfl 15645 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7955, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5276, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7955 =
      reconstructForGoal intermediateGoal_7955 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15637,
         denoteGraphDistributedFaithful pm initPM 15645]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5276, intermediateGoal_7955, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
