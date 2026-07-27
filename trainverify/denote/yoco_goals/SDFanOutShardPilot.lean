/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer6C_0

/-!
# Two-shard fan-out goals, reduced from their faithful parents

The replicated case is handled in `SDFanOutRep`. This is the other shape: the
parent goal is a genuine two-shard gather, and the multiref simply forwards each
rank's shard. Both sides reduce with `applyNode_fw_multiref_at`, and the
reconstruction is the parent's, unchanged — so the goal follows without touching
`reconstructWithDim` at all.

`7747` fixes the template: SM node 275 forwards `5060`, PM nodes 611/612 forward
that goal's two shards `8695` / `8696`.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def fnSm7747 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751],
    params := [2] }

private def fnPm15221 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225],
    params := [2] }

private def fnPm15229 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fn_sn7747 : sm.nodes[275]'(by native_decide) = fnSm7747 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem fn_pn15221 : pm.nodes[611]'(by native_decide) = fnPm15221 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem fn_pn15229 : pm.nodes[612]'(by native_decide) = fnPm15229 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7747_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7747
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5060_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7747 =
      denoteGraphDistributedFaithful sm initSM 5060 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 275 fnSm7747 5060 7747
      (fun x => x) (by native_decide) fn_sn7747 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnSm7747
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5060 [7747, 7751] 2 rfl 7747 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15221 =
      denoteGraphDistributedFaithful pm initPM 8695 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 611 fnPm15221 8695 15221
      (fun x => x) (by native_decide) fn_pn15221 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15221
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 8695 [15221, 15225] 2 rfl 15221 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15229 =
      denoteGraphDistributedFaithful pm initPM 8696 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 612 fnPm15229 8696 15229
      (fun x => x) (by native_decide) fn_pn15229 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold fnPm15229
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 8696 [15229, 15233] 2 rfl 15229 (by decide)
  -- The goal's reconstruction is the parent's with each tid rewritten, so the
  -- parent's three components transfer directly.
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7747, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5060, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7747 =
      reconstructForGoal intermediateGoal_7747 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15221,
         denoteGraphDistributedFaithful pm initPM 15229]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5060, intermediateGoal_7747, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
