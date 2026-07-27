/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ViewSelf
import denote.yoco_goals.SDGather4729
import denote.yoco_goals.SDChainCompute

/-!
# The tail of the MoE branch

After `4729` the two PM ranks go back to reading the same tids, so these three
are ordinary single-shard reductions. `4732` reshapes to the shape it already
has, so `fw_view_self` applies again.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def tlSm4731 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731], params := [] }

private def tlP04731 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731], params := [] }

private def tlP14731 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731], params := [] }

set_option maxRecDepth 1000000 in
private theorem tl_sn4731 : sm.nodes[35]'(by native_decide) = tlSm4731 := by native_decide

set_option maxRecDepth 1000000 in
private theorem tl_pn4731 : pm.nodes[113]'(by native_decide) = tlP14731 := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4731_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4731
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hx := recon_intermediateGoal_4729_faithful initSM initPM hSM hPM hInit
  have hxv : denoteGraphDistributedFaithful sm initSM 4729 =
      denoteGraphDistributedFaithful pm initPM 4729 := by
    have h := hx.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hxs : (denoteGraphDistributedFaithful sm initSM 4729).shape = [4096, 512] := hx.1
  have hwg := hInit initGoal_4730 (by native_decide)
  have hws : denoteGraphDistributedFaithful sm initSM 4730 = initSM 4730 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4730
      layer1_sm_nodes_nonempty (by native_decide)
  have hwp : denoteGraphDistributedFaithful pm initPM 4730 = initPM 4730 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4730
      layer1_pm_nodes_nonempty (by native_decide)
  have hwv : denoteGraphDistributedFaithful sm initSM 4730 =
      denoteGraphDistributedFaithful pm initPM 4730 := by
    rw [hws, hwp]
    have h := hwg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hwsh : (denoteGraphDistributedFaithful sm initSM 4730).shape = [1024, 512] := by
    rw [hws]; exact hwg.1
  have rSM : denoteGraphDistributedFaithful sm initSM 4731 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 4729)
        (denoteGraphDistributedFaithful sm initSM 4730) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 35 tlSm4731 4729 4730 4731
      fw_linear (by native_decide) tl_sn4731 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold tlSm4731
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mix_precision_linear_out sm st 0 4729 4730 4731 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4731 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 4729)
        (denoteGraphDistributedFaithful pm initPM 4730) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 113 tlP14731 4729 4730 4731
      fw_linear (by native_decide) tl_pn4731 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold tlP14731
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mix_precision_linear_out pm st 1 4729 4730 4731 []
  have hval : denoteGraphDistributedFaithful sm initSM 4731 =
      denoteGraphDistributedFaithful pm initPM 4731 := by
    rw [rSM, rPM, hxv, hwv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4731).shape = [4096, 1024] := by
    rw [rSM]
    unfold fw_linear
    simp [Tensor.mkShape, hxs, hwsh]
  unfold InitGoalHolds
  simp only [intermediateGoal_4731, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩


end

end TrainVerify.Denote.GeneratedPatterns
