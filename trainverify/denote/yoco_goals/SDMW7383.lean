/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDChainCompute
import denote.yoco_goals.SDRingTransport

/-!
# Replicated fan-outs off the chain head

`7383` / `7387` come off `4681` (the float after the embedding), `7404` off
`4703`. All three are replicated two-tp goals, so the reconstruction is the
rank-0 head.

Both `oneTp_valeq` and `wrap_1tp_gen` are avoided here: each ends by normalising
`reconstructWithDim`, which on this graph costs the whole heartbeat budget.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def mwSm7383 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_sn7383 : sm.nodes[2]'(by native_decide) = mwSm7383 := by
  native_decide

private def mwPm14603 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [14603, 14607],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_pn14603 : pm.nodes[29]'(by native_decide) = mwPm14603 := by
  native_decide

private def mwPm14611 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_pn14611 : pm.nodes[30]'(by native_decide) = mwPm14611 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7383_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7383
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4681_faithful initSM initPM hSM hPM hInit
  -- Take the parent's components directly; `oneTp_valeq` would normalise
  -- `reconstructWithDim` and cost the entire heartbeat budget.
  have hv : denoteGraphDistributedFaithful sm initSM 4681 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hval
    exact hval
  have hs : (denoteGraphDistributedFaithful sm initSM 4681).shape = [4096, 1024] := hparent.1
  have rSM : denoteGraphDistributedFaithful sm initSM 7383 =
      denoteGraphDistributedFaithful sm initSM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 2 mwSm7383 4681 7383
      (fun x => x) (by native_decide) mw_sn7383 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwSm7383
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4681 [7383, 7387] 2 rfl 7383 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14603 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 29 mwPm14603 4681 14603
      (fun x => x) (by native_decide) mw_pn14603 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwPm14603
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4681 [14603, 14607] 2 rfl 14603 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14611 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 30 mwPm14611 4681 14611
      (fun x => x) (by native_decide) mw_pn14611 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwPm14611
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4681 [14611, 14615] 2 rfl 14611 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7383, List.map]
  refine ⟨by rw [rSM]; exact hs, ?_, ?_⟩
  · rw [rPM0, rPM1, ← hv, hs]
  · rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons, rSM, rPM0, hv]

end

end TrainVerify.Denote.GeneratedPatterns
