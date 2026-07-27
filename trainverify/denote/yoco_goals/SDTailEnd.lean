/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDTail4731

/-!
# Closing the MoE branch

`4732` reshapes to the shape it already has (`fw_view_self`); `4733` multiplies
that by the gate from `4719`. Both PM ranks read the same tids here, so these
are ordinary single-shard reductions.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def tlSm4732 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] }

private def tlP14732 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] }

private def tlSm4733 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733], params := [] }

private def tlP14733 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733], params := [] }

set_option maxRecDepth 1000000 in
private theorem tl_sn4732 : sm.nodes[36]'(by native_decide) = tlSm4732 := by native_decide

set_option maxRecDepth 1000000 in
private theorem tl_pn4732 : pm.nodes[115]'(by native_decide) = tlP14732 := by native_decide

set_option maxRecDepth 1000000 in
private theorem tl_sn4733 : sm.nodes[37]'(by native_decide) = tlSm4733 := by native_decide

set_option maxRecDepth 1000000 in
private theorem tl_pn4733 : pm.nodes[117]'(by native_decide) = tlP14733 := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4732_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4732
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hx := recon_intermediateGoal_4731_faithful initSM initPM hSM hPM hInit
  have hxv : denoteGraphDistributedFaithful sm initSM 4731 =
      denoteGraphDistributedFaithful pm initPM 4731 := by
    have h := hx.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hxs : (denoteGraphDistributedFaithful sm initSM 4731).shape = [4096, 1024] := hx.1
  have rSM : denoteGraphDistributedFaithful sm initSM 4732 =
      denoteGraphDistributedFaithful sm initSM 4731 := by
    have h : denoteGraphDistributedFaithful sm initSM 4732 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 4731) := by
      refine denoteGraphDistributedFaithful_reduce1 sm initSM 36 tlSm4732 4731 4732
        (fw_view [4096, 1024]) (by native_decide) tl_sn4732 ?_
        (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
        (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      intro st
      unfold tlSm4732
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide)]
      exact applyNode_fw_view_out sm st 0 4096 [1024] 4731 4732
    rw [h, fw_view_self _ _ hxs]
  have rPM : denoteGraphDistributedFaithful pm initPM 4732 =
      denoteGraphDistributedFaithful pm initPM 4731 := by
    have h : denoteGraphDistributedFaithful pm initPM 4732 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful pm initPM 4731) := by
      refine denoteGraphDistributedFaithful_reduce1 pm initPM 115 tlP14732 4731 4732
        (fw_view [4096, 1024]) (by native_decide) tl_pn4732 ?_
        (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
        (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      intro st
      unfold tlP14732
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide)]
      exact applyNode_fw_view_out pm st 1 4096 [1024] 4731 4732
    rw [h, fw_view_self _ _ (by rw [← hxv]; exact hxs)]
  have hval : denoteGraphDistributedFaithful sm initSM 4732 =
      denoteGraphDistributedFaithful pm initPM 4732 := by
    rw [rSM, rPM, hxv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4732).shape = [4096, 1024] := by
    rw [rSM]; exact hxs
  unfold InitGoalHolds
  simp only [intermediateGoal_4732, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4733_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4733
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hg := recon_intermediateGoal_4719_faithful initSM initPM hSM hPM hInit
  have hv := recon_intermediateGoal_4732_faithful initSM initPM hSM hPM hInit
  have hgv : denoteGraphDistributedFaithful sm initSM 4719 =
      denoteGraphDistributedFaithful pm initPM 4719 := by
    have h := hg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hvv : denoteGraphDistributedFaithful sm initSM 4732 =
      denoteGraphDistributedFaithful pm initPM 4732 := by
    have h := hv.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hvs : (denoteGraphDistributedFaithful sm initSM 4732).shape = [4096, 1024] := hv.1
  have rSM : denoteGraphDistributedFaithful sm initSM 4733 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 4719)
        (denoteGraphDistributedFaithful sm initSM 4732) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 37 tlSm4733 4719 4732 4733
      elemwiseMul (by native_decide) tl_sn4733 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold tlSm4733
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mul_out sm st 0 4719 4732 4733
  have rPM : denoteGraphDistributedFaithful pm initPM 4733 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 4719)
        (denoteGraphDistributedFaithful pm initPM 4732) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 117 tlP14733 4719 4732 4733
      elemwiseMul (by native_decide) tl_pn4733 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold tlP14733
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mul_out pm st 1 4719 4732 4733
  have hval : denoteGraphDistributedFaithful sm initSM 4733 =
      denoteGraphDistributedFaithful pm initPM 4733 := by
    rw [rSM, rPM, hgv, hvv]
  -- `elemwiseMul` takes the broadcast shape of both operands, so the gate's
  -- shape is needed too.
  have hgs : (denoteGraphDistributedFaithful sm initSM 4719).shape = [4096, 1] := hg.1
  have hshape : (denoteGraphDistributedFaithful sm initSM 4733).shape = [4096, 1024] := by
    rw [rSM]
    unfold elemwiseMul
    simp only [Tensor.mkShape]
    unfold outShape2
    rw [hgs, hvs]
    simp [List.replicate, List.zipWith, Nat.max_def]
  unfold InitGoalHolds
  simp only [intermediateGoal_4733, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
