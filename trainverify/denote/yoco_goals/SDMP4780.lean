/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
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

private def mpSm4780 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779],
    outs := [4780], params := [] }

private def mpPm4780 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779],
    outs := [4780], params := [] }

set_option maxRecDepth 1000000 in
private theorem mp_sn4780 : sm.nodes[65]'(by native_decide) = mpSm4780 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem mp_pn4780 : pm.nodes[184]'(by native_decide) = mpPm4780 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4780_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4780
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4778_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4778 =
      denoteGraphDistributedFaithful pm initPM 4778 := by
    have hval := hparent.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hval
    exact hval
  have hxs : (denoteGraphDistributedFaithful sm initSM 4778).shape = [4096, 1024] := hparent.1
  -- Weight `4779` is an init tid neither graph writes, so both denotations are
  -- the initial store and `hInit` gives the equality directly. Going through
  -- `recon_weight` would normalise `reconstructWithDim` and blow the budget.
  have hwg := hInit initGoal_4779 (by native_decide)
  have hwsm : denoteGraphDistributedFaithful sm initSM 4779 = initSM 4779 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4779
      layer1_sm_nodes_nonempty (by native_decide)
  have hwpm : denoteGraphDistributedFaithful pm initPM 4779 = initPM 4779 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4779
      layer1_pm_nodes_nonempty (by native_decide)
  have hw : denoteGraphDistributedFaithful sm initSM 4779 =
      denoteGraphDistributedFaithful pm initPM 4779 := by
    rw [hwsm, hwpm]
    have := hwg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at this
    exact this
  have hws : (denoteGraphDistributedFaithful sm initSM 4779).shape = [512, 1024] := by
    rw [hwsm]; exact hwg.1
  have rSM : denoteGraphDistributedFaithful sm initSM 4780 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 4778)
        (denoteGraphDistributedFaithful sm initSM 4779) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 65 mpSm4780 4778 4779 4780
      fw_linear (by native_decide) mp_sn4780 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold mpSm4780
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mix_precision_linear_out sm st 0 4778 4779 4780 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4780 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 4778)
        (denoteGraphDistributedFaithful pm initPM 4779) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 184 mpPm4780 4778 4779 4780
      fw_linear (by native_decide) mp_pn4780 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold mpPm4780
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_mix_precision_linear_out pm st 1 4778 4779 4780 []
  have hval : denoteGraphDistributedFaithful sm initSM 4780 =
      denoteGraphDistributedFaithful pm initPM 4780 := by
    rw [rSM, rPM, hv, hw]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4780).shape = [4096, 512] := by
    rw [rSM]
    unfold fw_linear
    rw [hxs, hws]
    simp [Tensor.mkShape]
  unfold InitGoalHolds
  simp only [intermediateGoal_4780, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
