/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDFO7479
import denote.yoco_goals.SDFO7483
import denote.yoco_goals.IntermediateReconstruction

/-!
# Chain-head reshapes

`4774` and `4778` reshape the fan-out outputs `7479` / `7483` that landed in the
single-shard batch. `FW_reshape` with explicit params reduces to
`fw_view targetShape`, whose shape is the target by construction — no separate
shape lemma needed.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def rsSm4774 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7479], outs := [4774],
    params := [4096, 1024] }

private def rsPm4774 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11906], outs := [4774],
    params := [4096, 1024] }

set_option maxRecDepth 1000000 in
private theorem rs_sn4774 : sm.nodes[60]'(by native_decide) = rsSm4774 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rs_pn4774 : pm.nodes[175]'(by native_decide) = rsPm4774 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4774_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4774
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_7479_faithful initSM initPM hSM hPM hInit
  -- Not via `oneTp_valeq`: that helper ends with
  -- `simp only [List.map, reconstructWithDim] at hval`, and normalising
  -- `reconstructWithDim` here costs the whole heartbeat budget (measured: the
  -- rest of this proof is 4s, this step alone blows 16M).
  have hv : denoteGraphDistributedFaithful sm initSM 7479 =
      denoteGraphDistributedFaithful pm initPM 11906 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hval
    exact hval
  have rSM : denoteGraphDistributedFaithful sm initSM 4774 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 7479) := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 60 rsSm4774 7479 4774
      (fw_view [4096, 1024]) (by native_decide) rs_sn4774 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold rsSm4774
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_reshape_out sm st 0 7479 4774 [4096, 1024]
  have rPM : denoteGraphDistributedFaithful pm initPM 4774 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful pm initPM 11906) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 175 rsPm4774 11906 4774
      (fw_view [4096, 1024]) (by native_decide) rs_pn4774 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold rsPm4774
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_reshape_out pm st 1 11906 4774 [4096, 1024]
  have hval : denoteGraphDistributedFaithful sm initSM 4774 =
      denoteGraphDistributedFaithful pm initPM 4774 := by
    rw [rSM, rPM, hv]
  -- `fw_view` builds its tensor with `Tensor.mkShape targetShape`, so the shape
  -- is the target by construction. State that as a standalone step: asking
  -- `rfl` for it at the end makes the elaborator normalise the whole chain.
  have hviewshape : ∀ x : Tensor, (fw_view [4096, 1024] x).shape = [4096, 1024] := by
    intro x; unfold fw_view; simp [Tensor.mkShape]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4774).shape = [4096, 1024] := by
    rw [rSM]; exact hviewshape _
  unfold InitGoalHolds
  simp only [intermediateGoal_4774, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
