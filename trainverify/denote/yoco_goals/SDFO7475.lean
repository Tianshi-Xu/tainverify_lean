/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDRingTransport
import denote.yoco_goals.SDTLayer1TDC_0
import denote.yoco_goals.ResidualMoEReconstruction
import denote.yoco_goals.IntermediateReconstruction

/-!
# Single-shard fan-out goals

The remaining `FW_multiref` goals whose lineage goal names one tensor rather than
two. Both PM ranks write the same tid here, so each reduction anchors on the
*last* writer — the earlier rank's write is overwritten before the denotation is
read.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def f1Sm7475 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483],
    params := [5] }

private def f1Pm11905 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem f1_sn7475 : sm.nodes[57]'(by native_decide) = f1Sm7475 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem f1_pn11905 : pm.nodes[166]'(by native_decide) = f1Pm11905 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7475_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7475
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4759_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4759 =
      denoteGraphDistributedFaithful pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4759).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4759] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7475 =
      denoteGraphDistributedFaithful sm initSM 4759 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 57 f1Sm7475 4759 7475
      (fun x => x) (by native_decide) f1_sn7475 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold f1Sm7475
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4759 [7467, 7471, 7475, 7479, 7483] 5 rfl 7475 (by decide)
  -- Both PM ranks write `11905`; anchor on the last writer.
  have rPM : denoteGraphDistributedFaithful pm initPM 11905 =
      denoteGraphDistributedFaithful pm initPM 4759 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 166 f1Pm11905 4759 11905
      (fun x => x) (by native_decide) f1_pn11905 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold f1Pm11905
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4759 [11903, 11904, 11905, 11906, 11907] 5 rfl 11905 (by decide)
  have hval : denoteGraphDistributedFaithful sm initSM 7475 =
      denoteGraphDistributedFaithful pm initPM 11905 := by
    rw [rSM, rPM, hv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 7475).shape = [4096, 1024] := by
    rw [rSM]; exact hs
  -- Spelled out instead of `wrap_1tp_gen`: that helper finishes with
  -- `simp only [List.map, reconstructWithDim]`, and normalising
  -- `reconstructWithDim` is what made this file take an hour to compile.
  unfold InitGoalHolds
  simp only [intermediateGoal_7475, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
