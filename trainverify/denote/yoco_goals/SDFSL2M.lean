/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer2M_0

/-!
# Two-shard fan-out goals from parents proved in `SDTLayer2M_0`

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

private def fnSm7527 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7527 : sm.nodes[96]'(by native_decide) = fnSm7527 := by
  native_decide

private def fnPm14770 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14770 : pm.nodes[253]'(by native_decide) = fnPm14770 := by
  native_decide

private def fnPm14793 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14793 : pm.nodes[254]'(by native_decide) = fnPm14793 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7527_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7527
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4813_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7527 =
      denoteGraphDistributedFaithful sm initSM 4813 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 96 fnSm7527 4813 7527
      (fun x => x) (by native_decide) fn_sn7527 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7527
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4813 [7519, 7523, 7527, 7531, 7535] 5 rfl 7527 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14770 =
      denoteGraphDistributedFaithful pm initPM 7843 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 253 fnPm14770 7843 14770
      (fun x => x) (by native_decide) fn_pn14770 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14770
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7843 [14762, 14766, 14770, 14774, 14778] 5 rfl 14770 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14793 =
      denoteGraphDistributedFaithful pm initPM 7844 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 254 fnPm14793 7844 14793
      (fun x => x) (by native_decide) fn_pn14793 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14793
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7844 [14785, 14789, 14793, 14797, 14801] 5 rfl 14793 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7527, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4813, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7527 =
      reconstructForGoal intermediateGoal_7527 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14770,
         denoteGraphDistributedFaithful pm initPM 14793]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4813, intermediateGoal_7527, List.map] using h3'

private def fnSm7535 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7535 : sm.nodes[96]'(by native_decide) = fnSm7535 := by
  native_decide

private def fnPm14778 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14778 : pm.nodes[253]'(by native_decide) = fnPm14778 := by
  native_decide

private def fnPm14801 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14801 : pm.nodes[254]'(by native_decide) = fnPm14801 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7535_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7535
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4813_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7535 =
      denoteGraphDistributedFaithful sm initSM 4813 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 96 fnSm7535 4813 7535
      (fun x => x) (by native_decide) fn_sn7535 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7535
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4813 [7519, 7523, 7527, 7531, 7535] 5 rfl 7535 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14778 =
      denoteGraphDistributedFaithful pm initPM 7843 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 253 fnPm14778 7843 14778
      (fun x => x) (by native_decide) fn_pn14778 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14778
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7843 [14762, 14766, 14770, 14774, 14778] 5 rfl 14778 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14801 =
      denoteGraphDistributedFaithful pm initPM 7844 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 254 fnPm14801 7844 14801
      (fun x => x) (by native_decide) fn_pn14801 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14801
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7844 [14785, 14789, 14793, 14797, 14801] 5 rfl 14801 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7535, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4813, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7535 =
      reconstructForGoal intermediateGoal_7535 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14778,
         denoteGraphDistributedFaithful pm initPM 14801]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4813, intermediateGoal_7535, List.map] using h3'

private def fnSm7504 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7504 : sm.nodes[82]'(by native_decide) = fnSm7504 := by
  native_decide

private def fnPm14726 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14726 : pm.nodes[225]'(by native_decide) = fnPm14726 := by
  native_decide

private def fnPm14739 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14739 : pm.nodes[226]'(by native_decide) = fnPm14739 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7504_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7504
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4792_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7504 =
      denoteGraphDistributedFaithful sm initSM 4792 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 82 fnSm7504 4792 7504
      (fun x => x) (by native_decide) fn_sn7504 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7504
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4792 [7496, 7500, 7504] 3 rfl 7504 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14726 =
      denoteGraphDistributedFaithful pm initPM 7769 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 225 fnPm14726 7769 14726
      (fun x => x) (by native_decide) fn_pn14726 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14726
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7769 [14718, 14722, 14726] 3 rfl 14726 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14739 =
      denoteGraphDistributedFaithful pm initPM 7770 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 226 fnPm14739 7770 14739
      (fun x => x) (by native_decide) fn_pn14739 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14739
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7770 [14731, 14735, 14739] 3 rfl 14739 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7504, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4792, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7504 =
      reconstructForGoal intermediateGoal_7504 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14726,
         denoteGraphDistributedFaithful pm initPM 14739]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4792, intermediateGoal_7504, List.map] using h3'

private def fnSm7487 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4790], outs := [7487, 7491],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7487 : sm.nodes[80]'(by native_decide) = fnSm7487 := by
  native_decide

private def fnPm14701 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7765], outs := [14701, 14705],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14701 : pm.nodes[221]'(by native_decide) = fnPm14701 := by
  native_decide

private def fnPm14709 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7766], outs := [14709, 14713],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14709 : pm.nodes[222]'(by native_decide) = fnPm14709 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7487_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7487
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4790_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7487 =
      denoteGraphDistributedFaithful sm initSM 4790 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 80 fnSm7487 4790 7487
      (fun x => x) (by native_decide) fn_sn7487 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7487
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4790 [7487, 7491] 2 rfl 7487 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14701 =
      denoteGraphDistributedFaithful pm initPM 7765 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 221 fnPm14701 7765 14701
      (fun x => x) (by native_decide) fn_pn14701 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14701
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7765 [14701, 14705] 2 rfl 14701 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14709 =
      denoteGraphDistributedFaithful pm initPM 7766 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 222 fnPm14709 7766 14709
      (fun x => x) (by native_decide) fn_pn14709 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14709
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7766 [14709, 14713] 2 rfl 14709 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7487, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4790, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7487 =
      reconstructForGoal intermediateGoal_7487 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14701,
         denoteGraphDistributedFaithful pm initPM 14709]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4790, intermediateGoal_7487, List.map] using h3'

private def fnSm7548 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7548 : sm.nodes[121]'(by native_decide) = fnSm7548 := by
  native_decide

private def fnPm14822 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14822 : pm.nodes[303]'(by native_decide) = fnPm14822 := by
  native_decide

private def fnPm14835 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14835 : pm.nodes[304]'(by native_decide) = fnPm14835 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7548_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7548
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4846_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7548 =
      denoteGraphDistributedFaithful sm initSM 4846 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 121 fnSm7548 4846 7548
      (fun x => x) (by native_decide) fn_sn7548 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7548
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4846 [7548, 7552, 7556] 3 rfl 7548 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14822 =
      denoteGraphDistributedFaithful pm initPM 7955 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 303 fnPm14822 7955 14822
      (fun x => x) (by native_decide) fn_pn14822 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14822
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7955 [14822, 14826, 14830] 3 rfl 14822 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14835 =
      denoteGraphDistributedFaithful pm initPM 7956 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 304 fnPm14835 7956 14835
      (fun x => x) (by native_decide) fn_pn14835 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14835
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7956 [14835, 14839, 14843] 3 rfl 14835 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7548, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4846, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7548 =
      reconstructForGoal intermediateGoal_7548 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14822,
         denoteGraphDistributedFaithful pm initPM 14835]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4846, intermediateGoal_7548, List.map] using h3'

private def fnSm7500 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7500 : sm.nodes[82]'(by native_decide) = fnSm7500 := by
  native_decide

private def fnPm14722 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14722 : pm.nodes[225]'(by native_decide) = fnPm14722 := by
  native_decide

private def fnPm14735 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14735 : pm.nodes[226]'(by native_decide) = fnPm14735 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7500_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7500
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4792_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7500 =
      denoteGraphDistributedFaithful sm initSM 4792 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 82 fnSm7500 4792 7500
      (fun x => x) (by native_decide) fn_sn7500 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7500
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4792 [7496, 7500, 7504] 3 rfl 7500 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14722 =
      denoteGraphDistributedFaithful pm initPM 7769 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 225 fnPm14722 7769 14722
      (fun x => x) (by native_decide) fn_pn14722 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14722
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7769 [14718, 14722, 14726] 3 rfl 14722 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14735 =
      denoteGraphDistributedFaithful pm initPM 7770 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 226 fnPm14735 7770 14735
      (fun x => x) (by native_decide) fn_pn14735 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14735
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7770 [14731, 14735, 14739] 3 rfl 14735 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7500, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4792, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7500 =
      reconstructForGoal intermediateGoal_7500 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14722,
         denoteGraphDistributedFaithful pm initPM 14735]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4792, intermediateGoal_7500, List.map] using h3'

private def fnSm7552 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7552 : sm.nodes[121]'(by native_decide) = fnSm7552 := by
  native_decide

private def fnPm14826 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14826 : pm.nodes[303]'(by native_decide) = fnPm14826 := by
  native_decide

private def fnPm14839 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14839 : pm.nodes[304]'(by native_decide) = fnPm14839 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7552_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7552
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4846_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7552 =
      denoteGraphDistributedFaithful sm initSM 4846 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 121 fnSm7552 4846 7552
      (fun x => x) (by native_decide) fn_sn7552 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7552
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4846 [7548, 7552, 7556] 3 rfl 7552 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14826 =
      denoteGraphDistributedFaithful pm initPM 7955 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 303 fnPm14826 7955 14826
      (fun x => x) (by native_decide) fn_pn14826 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14826
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7955 [14822, 14826, 14830] 3 rfl 14826 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14839 =
      denoteGraphDistributedFaithful pm initPM 7956 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 304 fnPm14839 7956 14839
      (fun x => x) (by native_decide) fn_pn14839 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14839
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7956 [14835, 14839, 14843] 3 rfl 14839 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7552, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4846, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7552 =
      reconstructForGoal intermediateGoal_7552 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14826,
         denoteGraphDistributedFaithful pm initPM 14839]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4846, intermediateGoal_7552, List.map] using h3'

private def fnSm7539 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7539 : sm.nodes[119]'(by native_decide) = fnSm7539 := by
  native_decide

private def fnPm14805 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14805 : pm.nodes[299]'(by native_decide) = fnPm14805 := by
  native_decide

private def fnPm14813 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14813 : pm.nodes[300]'(by native_decide) = fnPm14813 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7539_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7539
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4844_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7539 =
      denoteGraphDistributedFaithful sm initSM 4844 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 119 fnSm7539 4844 7539
      (fun x => x) (by native_decide) fn_sn7539 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7539
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4844 [7539, 7543] 2 rfl 7539 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14805 =
      denoteGraphDistributedFaithful pm initPM 7951 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 299 fnPm14805 7951 14805
      (fun x => x) (by native_decide) fn_pn14805 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14805
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7951 [14805, 14809] 2 rfl 14805 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14813 =
      denoteGraphDistributedFaithful pm initPM 7952 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 300 fnPm14813 7952 14813
      (fun x => x) (by native_decide) fn_pn14813 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14813
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7952 [14813, 14817] 2 rfl 14813 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7539, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4844, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7539 =
      reconstructForGoal intermediateGoal_7539 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14805,
         denoteGraphDistributedFaithful pm initPM 14813]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4844, intermediateGoal_7539, List.map] using h3'

private def fnSm7531 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7531 : sm.nodes[96]'(by native_decide) = fnSm7531 := by
  native_decide

private def fnPm14774 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14774 : pm.nodes[253]'(by native_decide) = fnPm14774 := by
  native_decide

private def fnPm14797 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14797 : pm.nodes[254]'(by native_decide) = fnPm14797 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7531_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7531
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4813_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7531 =
      denoteGraphDistributedFaithful sm initSM 4813 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 96 fnSm7531 4813 7531
      (fun x => x) (by native_decide) fn_sn7531 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7531
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4813 [7519, 7523, 7527, 7531, 7535] 5 rfl 7531 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14774 =
      denoteGraphDistributedFaithful pm initPM 7843 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 253 fnPm14774 7843 14774
      (fun x => x) (by native_decide) fn_pn14774 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14774
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7843 [14762, 14766, 14770, 14774, 14778] 5 rfl 14774 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14797 =
      denoteGraphDistributedFaithful pm initPM 7844 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 254 fnPm14797 7844 14797
      (fun x => x) (by native_decide) fn_pn14797 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14797
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7844 [14785, 14789, 14793, 14797, 14801] 5 rfl 14797 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7531, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4813, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7531 =
      reconstructForGoal intermediateGoal_7531 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14774,
         denoteGraphDistributedFaithful pm initPM 14797]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4813, intermediateGoal_7531, List.map] using h3'

private def fnSm7519 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7519 : sm.nodes[96]'(by native_decide) = fnSm7519 := by
  native_decide

private def fnPm14762 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14762 : pm.nodes[253]'(by native_decide) = fnPm14762 := by
  native_decide

private def fnPm14785 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14785 : pm.nodes[254]'(by native_decide) = fnPm14785 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7519_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7519
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4813_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7519 =
      denoteGraphDistributedFaithful sm initSM 4813 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 96 fnSm7519 4813 7519
      (fun x => x) (by native_decide) fn_sn7519 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7519
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4813 [7519, 7523, 7527, 7531, 7535] 5 rfl 7519 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14762 =
      denoteGraphDistributedFaithful pm initPM 7843 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 253 fnPm14762 7843 14762
      (fun x => x) (by native_decide) fn_pn14762 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14762
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7843 [14762, 14766, 14770, 14774, 14778] 5 rfl 14762 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14785 =
      denoteGraphDistributedFaithful pm initPM 7844 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 254 fnPm14785 7844 14785
      (fun x => x) (by native_decide) fn_pn14785 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14785
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7844 [14785, 14789, 14793, 14797, 14801] 5 rfl 14785 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7519, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4813, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7519 =
      reconstructForGoal intermediateGoal_7519 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14762,
         denoteGraphDistributedFaithful pm initPM 14785]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4813, intermediateGoal_7519, List.map] using h3'

private def fnSm7556 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7556 : sm.nodes[121]'(by native_decide) = fnSm7556 := by
  native_decide

private def fnPm14830 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14830 : pm.nodes[303]'(by native_decide) = fnPm14830 := by
  native_decide

private def fnPm14843 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14843 : pm.nodes[304]'(by native_decide) = fnPm14843 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7556_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7556
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4846_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7556 =
      denoteGraphDistributedFaithful sm initSM 4846 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 121 fnSm7556 4846 7556
      (fun x => x) (by native_decide) fn_sn7556 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7556
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4846 [7548, 7552, 7556] 3 rfl 7556 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14830 =
      denoteGraphDistributedFaithful pm initPM 7955 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 303 fnPm14830 7955 14830
      (fun x => x) (by native_decide) fn_pn14830 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14830
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7955 [14822, 14826, 14830] 3 rfl 14830 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14843 =
      denoteGraphDistributedFaithful pm initPM 7956 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 304 fnPm14843 7956 14843
      (fun x => x) (by native_decide) fn_pn14843 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14843
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7956 [14835, 14839, 14843] 3 rfl 14843 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7556, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4846, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7556 =
      reconstructForGoal intermediateGoal_7556 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14830,
         denoteGraphDistributedFaithful pm initPM 14843]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4846, intermediateGoal_7556, List.map] using h3'

private def fnSm7496 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7496 : sm.nodes[82]'(by native_decide) = fnSm7496 := by
  native_decide

private def fnPm14718 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14718 : pm.nodes[225]'(by native_decide) = fnPm14718 := by
  native_decide

private def fnPm14731 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14731 : pm.nodes[226]'(by native_decide) = fnPm14731 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7496_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7496
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4792_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7496 =
      denoteGraphDistributedFaithful sm initSM 4792 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 82 fnSm7496 4792 7496
      (fun x => x) (by native_decide) fn_sn7496 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7496
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4792 [7496, 7500, 7504] 3 rfl 7496 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14718 =
      denoteGraphDistributedFaithful pm initPM 7769 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 225 fnPm14718 7769 14718
      (fun x => x) (by native_decide) fn_pn14718 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14718
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7769 [14718, 14722, 14726] 3 rfl 14718 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14731 =
      denoteGraphDistributedFaithful pm initPM 7770 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 226 fnPm14731 7770 14731
      (fun x => x) (by native_decide) fn_pn14731 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14731
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7770 [14731, 14735, 14739] 3 rfl 14731 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7496, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4792, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7496 =
      reconstructForGoal intermediateGoal_7496 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14718,
         denoteGraphDistributedFaithful pm initPM 14731]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4792, intermediateGoal_7496, List.map] using h3'

private def fnSm7508 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7508 : sm.nodes[94]'(by native_decide) = fnSm7508 := by
  native_decide

private def fnPm14743 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14743 : pm.nodes[249]'(by native_decide) = fnPm14743 := by
  native_decide

private def fnPm14751 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_pn14751 : pm.nodes[250]'(by native_decide) = fnPm14751 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7508_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7508
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4811_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7508 =
      denoteGraphDistributedFaithful sm initSM 4811 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 94 fnSm7508 4811 7508
      (fun x => x) (by native_decide) fn_sn7508 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7508
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4811 [7508, 7512] 2 rfl 7508 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14743 =
      denoteGraphDistributedFaithful pm initPM 7839 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 249 fnPm14743 7839 14743
      (fun x => x) (by native_decide) fn_pn14743 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14743
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 7839 [14743, 14747] 2 rfl 14743 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14751 =
      denoteGraphDistributedFaithful pm initPM 7840 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 250 fnPm14751 7840 14751
      (fun x => x) (by native_decide) fn_pn14751 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm14751
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 7840 [14751, 14755] 2 rfl 14751 (by decide)
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7508, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_4811, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7508 =
      reconstructForGoal intermediateGoal_7508 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14743,
         denoteGraphDistributedFaithful pm initPM 14751]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_4811, intermediateGoal_7508, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
