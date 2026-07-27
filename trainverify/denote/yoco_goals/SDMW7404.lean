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

private def mwSm7404 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_sn7404 : sm.nodes[16]'(by native_decide) = mwSm7404 := by
  native_decide

private def mwPm14644 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [14644, 14648],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_pn14644 : pm.nodes[64]'(by native_decide) = mwPm14644 := by
  native_decide

private def mwPm14652 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem mw_pn14652 : pm.nodes[65]'(by native_decide) = mwPm14652 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7404_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7404
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4703_faithful initSM initPM hSM hPM hInit
  -- Take the parent's components directly; `oneTp_valeq` would normalise
  -- `reconstructWithDim` and cost the entire heartbeat budget.
  have hv : denoteGraphDistributedFaithful sm initSM 4703 =
      denoteGraphDistributedFaithful pm initPM 4703 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hval
    exact hval
  have hs : (denoteGraphDistributedFaithful sm initSM 4703).shape = [4096, 1024] := hparent.1
  have rSM : denoteGraphDistributedFaithful sm initSM 7404 =
      denoteGraphDistributedFaithful sm initSM 4703 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 16 mwSm7404 4703 7404
      (fun x => x) (by native_decide) mw_sn7404 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwSm7404
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4703 [7404, 7408] 2 rfl 7404 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14644 =
      denoteGraphDistributedFaithful pm initPM 4703 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 64 mwPm14644 4703 14644
      (fun x => x) (by native_decide) mw_pn14644 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwPm14644
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4703 [14644, 14648] 2 rfl 14644 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14652 =
      denoteGraphDistributedFaithful pm initPM 4703 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 65 mwPm14652 4703 14652
      (fun x => x) (by native_decide) mw_pn14652 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mwPm14652
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4703 [14652, 14656] 2 rfl 14652 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7404, List.map]
  refine ⟨by rw [rSM]; exact hs, ?_, ?_⟩
  · rw [rPM0, rPM1, ← hv, hs]
  · rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons, rSM, rPM0, hv]

end

end TrainVerify.Denote.GeneratedPatterns
