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

private def phSm4689 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7400, 4688],
    outs := [4689], params := [] }

private def phPm4689 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14640, 4688],
    outs := [4689], params := [] }

set_option maxRecDepth 1000000 in
private theorem ph_sn4689 : sm.nodes[7]'(by native_decide) = phSm4689 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem ph_pn4689 : pm.nodes[40]'(by native_decide) = phPm4689 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4689_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4689
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_7400_faithful initSM initPM hSM hPM hInit
  -- The goal pins rank 0 (`14628`); the PM node reads rank 1 (`14640`).
  -- `pm_7400_shards_agree` bridges them.
  have hv : denoteGraphDistributedFaithful sm initSM 7400 =
      denoteGraphDistributedFaithful pm initPM 14640 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl)] at hval
    simp only [intermediateGoal_7400, List.map, List.headD_cons] at hval
    rw [hval]
    exact pm_7400_shards_agree initPM
  have hxs : (denoteGraphDistributedFaithful sm initSM 7400).shape = [4096, 1024] :=
    hparent.1
  have hwg := hInit initGoal_4688 (by native_decide)
  have hwsm : denoteGraphDistributedFaithful sm initSM 4688 = initSM 4688 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4688
      layer1_sm_nodes_nonempty (by native_decide)
  have hwpm : denoteGraphDistributedFaithful pm initPM 4688 = initPM 4688 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4688
      layer1_pm_nodes_nonempty (by native_decide)
  have hw : denoteGraphDistributedFaithful sm initSM 4688 =
      denoteGraphDistributedFaithful pm initPM 4688 := by
    rw [hwsm, hwpm]
    have := hwg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at this
    exact this
  have hws : (denoteGraphDistributedFaithful sm initSM 4688).shape = [4, 64, 1024] := by
    rw [hwsm]; exact hwg.1
  have rSM : denoteGraphDistributedFaithful sm initSM 4689 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 7400)
        (denoteGraphDistributedFaithful sm initSM 4688) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 7 phSm4689 7400 4688 4689
      fw_per_head_linear (by native_decide) ph_sn4689 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold phSm4689
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_per_head_mix_precision_linear_out sm st 0 7400 4688 4689 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4689 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 14640)
        (denoteGraphDistributedFaithful pm initPM 4688) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 40 phPm4689 14640 4688 4689
      fw_per_head_linear (by native_decide) ph_pn4689 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold phPm4689
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_per_head_mix_precision_linear_out pm st 1 14640 4688 4689 []
  have hval : denoteGraphDistributedFaithful sm initSM 4689 =
      denoteGraphDistributedFaithful pm initPM 4689 := by
    rw [rSM, rPM, hv, hw]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4689).shape = [4096, 4, 64] := by
    rw [rSM]
    exact fw_per_head_linear_shape _ _ 4 64 1024 [4096] (by rw [hxs]; rfl) hws
  unfold InitGoalHolds
  simp only [intermediateGoal_4689, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
