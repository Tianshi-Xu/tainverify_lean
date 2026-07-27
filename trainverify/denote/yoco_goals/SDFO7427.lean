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

private def f1Sm7427 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431],
    params := [5] }

private def f1Pm11878 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := [11875, 11876, 11877, 11878, 11879],
    params := [5] }

set_option maxRecDepth 1000000 in
private theorem f1_sn7427 : sm.nodes[18]'(by native_decide) = f1Sm7427 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem f1_pn11878 : pm.nodes[69]'(by native_decide) = f1Pm11878 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7427_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7427
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4705_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4705 =
      denoteGraphDistributedFaithful pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4705).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4705] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7427 =
      denoteGraphDistributedFaithful sm initSM 4705 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 18 f1Sm7427 4705 7427
      (fun x => x) (by native_decide) f1_sn7427 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold f1Sm7427
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4705 [7415, 7419, 7423, 7427, 7431] 5 rfl 7427 (by decide)
  -- Both PM ranks write `11878`; anchor on the last writer.
  have rPM : denoteGraphDistributedFaithful pm initPM 11878 =
      denoteGraphDistributedFaithful pm initPM 4705 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 69 f1Pm11878 4705 11878
      (fun x => x) (by native_decide) f1_pn11878 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold f1Pm11878
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4705 [11875, 11876, 11877, 11878, 11879] 5 rfl 11878 (by decide)
  have hval : denoteGraphDistributedFaithful sm initSM 7427 =
      denoteGraphDistributedFaithful pm initPM 11878 := by
    rw [rSM, rPM, hv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 7427).shape = [4096, 1024] := by
    rw [rSM]; exact hs
  -- Spelled out instead of `wrap_1tp_gen`: that helper finishes with
  -- `simp only [List.map, reconstructWithDim]`, and normalising
  -- `reconstructWithDim` is what made this file take an hour to compile.
  unfold InitGoalHolds
  simp only [intermediateGoal_7427, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
