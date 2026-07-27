/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDMP4780

/-!
# Chain-head view

`4781` is a `FW_view` over the projection `4780`; both PM ranks run the same node
on the same tid. `fw_view` builds with `Tensor.mkShape targetShape`, so the shape
falls out of the definition.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def vwSm4781 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781],
    params := [4096, 512] }

private def vwPm4781 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [4780], outs := [4781],
    params := [4096, 512] }

set_option maxRecDepth 1000000 in
private theorem vw_sn4781 : sm.nodes[69]'(by native_decide) = vwSm4781 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem vw_pn4781 : pm.nodes[192]'(by native_decide) = vwPm4781 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4781_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4781
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4780_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4780 =
      denoteGraphDistributedFaithful pm initPM 4780 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hval
    exact hval
  have rSM : denoteGraphDistributedFaithful sm initSM 4781 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm initSM 4780) := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 69 vwSm4781 4780 4781
      (fw_view [4096, 512]) (by native_decide) vw_sn4781 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold vwSm4781
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_view_out sm st 0 4096 [512] 4780 4781
  have rPM : denoteGraphDistributedFaithful pm initPM 4781 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful pm initPM 4780) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 192 vwPm4781 4780 4781
      (fw_view [4096, 512]) (by native_decide) vw_pn4781 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold vwPm4781
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_view_out pm st 1 4096 [512] 4780 4781
  have hval : denoteGraphDistributedFaithful sm initSM 4781 =
      denoteGraphDistributedFaithful pm initPM 4781 := by
    rw [rSM, rPM, hv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4781).shape = [4096, 512] := by
    rw [rSM]; unfold fw_view; simp [Tensor.mkShape]
  unfold InitGoalHolds
  simp only [intermediateGoal_4781, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
