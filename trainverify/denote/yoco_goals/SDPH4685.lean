/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDQKVShards
import denote.yoco_goals.SDQ7392
import denote.yoco_goals.SDQ7396
import denote.yoco_goals.SDQ7400

/-!
# The QKV projections

`4685` / `4687` / `4689` are the per-head projections of the three fan-out
branches. Each parent goal is replicated, so its reconstruction pins rank 0 while
the PM node reads rank 1 — `pm_*_shards_agree` closes that gap.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def phSm4685 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684],
    outs := [4685], params := [] }

private def phPm4685 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684],
    outs := [4685], params := [] }

set_option maxRecDepth 1000000 in
private theorem ph_sn4685 : sm.nodes[5]'(by native_decide) = phSm4685 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem ph_pn4685 : pm.nodes[38]'(by native_decide) = phPm4685 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4685_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4685
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_7392_faithful initSM initPM hSM hPM hInit
  -- The goal pins rank 0 (`14620`); the PM node reads rank 1 (`14632`).
  -- `pm_7392_shards_agree` bridges them.
  have hv : denoteGraphDistributedFaithful sm initSM 7392 =
      denoteGraphDistributedFaithful pm initPM 14632 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl)] at hval
    simp only [intermediateGoal_7392, List.map, List.headD_cons] at hval
    rw [hval]
    exact pm_7392_shards_agree initPM
  have hxs : (denoteGraphDistributedFaithful sm initSM 7392).shape = [4096, 1024] :=
    hparent.1
  have hwg := hInit initGoal_4684 (by native_decide)
  have hwsm : denoteGraphDistributedFaithful sm initSM 4684 = initSM 4684 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4684
      layer1_sm_nodes_nonempty (by native_decide)
  have hwpm : denoteGraphDistributedFaithful pm initPM 4684 = initPM 4684 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4684
      layer1_pm_nodes_nonempty (by native_decide)
  have hw : denoteGraphDistributedFaithful sm initSM 4684 =
      denoteGraphDistributedFaithful pm initPM 4684 := by
    rw [hwsm, hwpm]
    have := hwg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at this
    exact this
  have hws : (denoteGraphDistributedFaithful sm initSM 4684).shape = [16, 64, 1024] := by
    rw [hwsm]; exact hwg.1
  have rSM : denoteGraphDistributedFaithful sm initSM 4685 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 7392)
        (denoteGraphDistributedFaithful sm initSM 4684) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 5 phSm4685 7392 4684 4685
      fw_per_head_linear (by native_decide) ph_sn4685 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold phSm4685
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_per_head_mix_precision_linear_out sm st 0 7392 4684 4685 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4685 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 14632)
        (denoteGraphDistributedFaithful pm initPM 4684) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 38 phPm4685 14632 4684 4685
      fw_per_head_linear (by native_decide) ph_pn4685 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold phPm4685
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_per_head_mix_precision_linear_out pm st 1 14632 4684 4685 []
  have hval : denoteGraphDistributedFaithful sm initSM 4685 =
      denoteGraphDistributedFaithful pm initPM 4685 := by
    rw [rSM, rPM, hv, hw]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4685).shape = [4096, 16, 64] := by
    rw [rSM]
    exact fw_per_head_linear_shape _ _ 16 64 1024 [4096] (by rw [hxs]; rfl) hws
  unfold InitGoalHolds
  simp only [intermediateGoal_4685, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
