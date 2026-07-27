/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDMW7383

/-!
# The chain-head RMS norm

`4683` normalises `7383`. There is a subtlety: `intermediateGoal_7383` is
*replicated*, so its reconstruction pins only the rank-0 shard `14603`, while the
PM node that actually writes `4683` last is rank 1, reading `14611`.

The goal statement does not relate the two shards — but the graph does. Both are
outputs of the same `FW_multiref` fan-out of `4681`, so each reduces to `4681`
and they are equal. No extra hypothesis needed.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def rnPm14603 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [14603, 14607],
    params := [2] }

private def rnPm14611 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615],
    params := [2] }

private def rnSm4683 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683],
    params := [] }

private def rnPm4683 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683],
    params := [] }

set_option maxRecDepth 1000000 in
private theorem rn_pn14603 : pm.nodes[29]'(by native_decide) = rnPm14603 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rn_pn14611 : pm.nodes[30]'(by native_decide) = rnPm14611 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rn_sn4683 : sm.nodes[3]'(by native_decide) = rnSm4683 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rn_pn4683 : pm.nodes[32]'(by native_decide) = rnPm4683 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4683_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4683
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_7383_faithful initSM initPM hSM hPM hInit
  -- Both PM shards of the replicated fan-out reduce to `4681`.
  have r603 : denoteGraphDistributedFaithful pm initPM 14603 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 29 rnPm14603 4681 14603
      (fun x => x) (by native_decide) rn_pn14603 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold rnPm14603
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4681 [14603, 14607] 2 rfl 14603 (by decide)
  have r611 : denoteGraphDistributedFaithful pm initPM 14611 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 30 rnPm14611 4681 14611
      (fun x => x) (by native_decide) rn_pn14611 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold rnPm14611
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4681 [14611, 14615] 2 rfl 14611 (by decide)
  -- The goal pins the rank-0 shard; compose to reach rank 1.
  have hv : denoteGraphDistributedFaithful sm initSM 7383 =
      denoteGraphDistributedFaithful pm initPM 14611 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl)] at hval
    simp only [intermediateGoal_7383, List.map, List.headD_cons] at hval
    rw [hval, r603, ← r611]
  have hxs : (denoteGraphDistributedFaithful sm initSM 7383).shape = [4096, 1024] :=
    hparent.1
  have hwg := hInit initGoal_4682 (by native_decide)
  have hwsm : denoteGraphDistributedFaithful sm initSM 4682 = initSM 4682 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4682
      layer1_sm_nodes_nonempty (by native_decide)
  have hwpm : denoteGraphDistributedFaithful pm initPM 4682 = initPM 4682 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4682
      layer1_pm_nodes_nonempty (by native_decide)
  have hw : denoteGraphDistributedFaithful sm initSM 4682 =
      denoteGraphDistributedFaithful pm initPM 4682 := by
    rw [hwsm, hwpm]
    have := hwg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at this
    exact this
  have rSM : denoteGraphDistributedFaithful sm initSM 4683 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 7383)
        (denoteGraphDistributedFaithful sm initSM 4682) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 3 rnSm4683 7383 4682 4683
      fw_rms_norm (by native_decide) rn_sn4683 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold rnSm4683
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_rms_norm_out sm st 0 7383 4682 4683 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4683 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 14611)
        (denoteGraphDistributedFaithful pm initPM 4682) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 32 rnPm4683 14611 4682 4683
      fw_rms_norm (by native_decide) rn_pn4683 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold rnPm4683
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_rms_norm_out pm st 1 14611 4682 4683 []
  have hval : denoteGraphDistributedFaithful sm initSM 4683 =
      denoteGraphDistributedFaithful pm initPM 4683 := by
    rw [rSM, rPM, hv, hw]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4683).shape = [4096, 1024] := by
    rw [rSM, fw_rms_norm_shape]; exact hxs
  unfold InitGoalHolds
  simp only [intermediateGoal_4683, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
