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

private def mwSm7387 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_sn7387 : sm.nodes[2]'(by native_decide) = mwSm7387 := by
  native_decide

private def mwPm14607 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [14603, 14607],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_pn14607 : pm.nodes[29]'(by native_decide) = mwPm14607 := by
  native_decide

private def mwPm14615 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_pn14615 : pm.nodes[30]'(by native_decide) = mwPm14615 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7387_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7387
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
  have rSM : denoteGraphDistributedFaithful sm initSM 7387 =
      denoteGraphDistributedFaithful sm initSM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 2 mwSm7387 4681 7387
      (fun x => x) (by native_decide) mw_sn7387 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwSm7387
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4681 [7383, 7387] 2 rfl 7387 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14607 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 29 mwPm14607 4681 14607
      (fun x => x) (by native_decide) mw_pn14607 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwPm14607
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4681 [14603, 14607] 2 rfl 14607 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14615 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 30 mwPm14615 4681 14615
      (fun x => x) (by native_decide) mw_pn14615 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwPm14615
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4681 [14611, 14615] 2 rfl 14615 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7387, List.map]
  refine ⟨by rw [rSM]; exact hs, ?_, ?_⟩
  · rw [rPM0, rPM1, ← hv, hs]
  · rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons, rSM, rPM0, hv]

end

end TrainVerify.Denote.GeneratedPatterns
