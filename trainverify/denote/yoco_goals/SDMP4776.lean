/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRS4774
import denote.yoco_goals.SDRS4778

/-!
# Chain-head projections

`4776` / `4780` are `FW_mix_precision_linear` over the reshapes `4774` / `4778`
and the init weights `4775` / `4779`. Both PM ranks run the same node on the same
tids, so the goals reduce to equalities.

The weight equality comes straight out of `hInit`: neither graph writes an init
tid, so both denotations are the initial store. `recon_weight` would do this too
but ends by normalising `reconstructWithDim`, which is ruinous here.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def mpSm4776 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775],
    outs := [4776], params := [] }

private def mpPm4776 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775],
    outs := [4776], params := [] }

set_option maxRecDepth 1000000 in
private theorem mp_sn4776 : sm.nodes[64]'(by native_decide) = mpSm4776 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem mp_pn4776 : pm.nodes[182]'(by native_decide) = mpPm4776 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4776_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4776
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4774_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4774 =
      denoteGraphDistributedFaithful pm initPM 4774 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hval
    exact hval
  have hxs : (denoteGraphDistributedFaithful sm initSM 4774).shape = [4096, 1024] := hparent.1
  -- Weight `4775` is an init tid neither graph writes, so both denotations are
  -- the initial store and `hInit` gives the equality directly. Going through
  -- `recon_weight` would normalise `reconstructWithDim` and blow the budget.
  have hwg := hInit initGoal_4775 (by native_decide)
  have hwsm : denoteGraphDistributedFaithful sm initSM 4775 = initSM 4775 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4775
      layer1_sm_nodes_nonempty (by native_decide)
  have hwpm : denoteGraphDistributedFaithful pm initPM 4775 = initPM 4775 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4775
      layer1_pm_nodes_nonempty (by native_decide)
  have hw : denoteGraphDistributedFaithful sm initSM 4775 =
      denoteGraphDistributedFaithful pm initPM 4775 := by
    rw [hwsm, hwpm]
    have := hwg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at this
    exact this
  have hws : (denoteGraphDistributedFaithful sm initSM 4775).shape = [512, 1024] := by
    rw [hwsm]; exact hwg.1
  have rSM : denoteGraphDistributedFaithful sm initSM 4776 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 4774)
        (denoteGraphDistributedFaithful sm initSM 4775) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 64 mpSm4776 4774 4775 4776
      fw_linear (by native_decide) mp_sn4776 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold mpSm4776
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mix_precision_linear_out sm st 0 4774 4775 4776 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4776 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 4774)
        (denoteGraphDistributedFaithful pm initPM 4775) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 182 mpPm4776 4774 4775 4776
      fw_linear (by native_decide) mp_pn4776 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold mpPm4776
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mix_precision_linear_out pm st 1 4774 4775 4776 []
  have hval : denoteGraphDistributedFaithful sm initSM 4776 =
      denoteGraphDistributedFaithful pm initPM 4776 := by
    rw [rSM, rPM, hv, hw]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4776).shape = [4096, 512] := by
    rw [rSM]
    unfold fw_linear
    rw [hxs, hws]
    simp [Tensor.mkShape]
  unfold InitGoalHolds
  simp only [intermediateGoal_4776, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
