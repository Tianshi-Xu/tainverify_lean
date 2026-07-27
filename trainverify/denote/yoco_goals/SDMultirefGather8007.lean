/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDTLayer12BC_0

/-!
# A fan-out on an already-split tensor

`8007` is the first output of a `FW_multiref`. Its parent `5330` is already
two-shard, so each PM rank fans out its own shard and the goal's own
`AllGatherPrim` puts them back together — the same gather the parent goal
already uses, so the two line up directly.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def mgSm : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011],
    params := [2] }

private def mgP0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257],
    params := [2] }

private def mgP1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258],
    params := [2] }

private def mgGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917],
    params := [0] }

set_option maxRecDepth 1000000 in
private theorem mg_sn : sm.nodes[470]'(by native_decide) = mgSm := by native_decide

set_option maxRecDepth 1000000 in
private theorem mg_p0 : pm.nodes[1001]'(by native_decide) = mgP0 := by native_decide

set_option maxRecDepth 1000000 in
private theorem mg_p1 : pm.nodes[1002]'(by native_decide) = mgP1 := by native_decide

set_option maxRecDepth 1000000 in
private theorem mg_g : pm.nodes[1004]'(by native_decide) = mgGather := by native_decide

set_option maxRecDepth 1000000 in
private theorem mg_rep5330 : intermediateGoal_5330.replicated = false := by native_decide

set_option maxRecDepth 1000000 in
private theorem mg_rep8007 : intermediateGoal_8007.replicated = false := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8007_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8007
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hp := recon_intermediateGoal_5330_faithful initSM initPM hSM hPM hInit
  have hps : (denoteGraphDistributedFaithful sm initSM 5330).shape = [4096, 1024] := hp.1
  have hpshards := hp.2.1
  -- Keep the parent's value fact in `reconstructForGoal` form; normalising
  -- `reconstructWithDim` by hand is what blows the heartbeat budget.
  have hpval := hp.2.2
  -- SM: first output of the fan-out.
  have rSM : denoteGraphDistributedFaithful sm initSM 8007 =
      denoteGraphDistributedFaithful sm initSM 5330 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 470 mgSm 5330 8007
      (fun x => x) (by native_decide) mg_sn ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mgSm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5330 [8007, 8011] 2 rfl 8007 (by decide)
  -- PM: each rank fans out its own shard.
  have rP0 : denoteGraphDistributedFaithful pm initPM 14597 =
      denoteGraphDistributedFaithful pm initPM 9625 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1001 mgP0 9625 14597
      (fun x => x) (by native_decide) mg_p0 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mgP0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 9625 [14597, 13257] 2 rfl 14597 (by decide)
  have rP1 : denoteGraphDistributedFaithful pm initPM 14599 =
      denoteGraphDistributedFaithful pm initPM 9626 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1002 mgP1 9626 14599
      (fun x => x) (by native_decide) mg_p1 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mgP1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 9626 [14599, 13258] 2 rfl 14599 (by decide)
  have rG : denoteGraphDistributedFaithful pm initPM 11917 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm initPM 14597,
         denoteGraphDistributedFaithful pm initPM 14599] := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 1004 mgGather 14597 14599 11917
      (fun a b => allGatherPrimDimN 0 2 0 [a, b]) (by native_decide) mg_g ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold mgGather
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_allGatherPrimDimN_out pm st 0 [14597, 14599] 11917 0
  have hshape : (denoteGraphDistributedFaithful sm initSM 8007).shape = [4096, 1024] := by
    rw [rSM]; exact hps
  -- Convert the parent's fact FIRST, then chain equalities with `calc`.
  -- Rewriting `rG/rP0/rP1` into the goal and only then matching against
  -- `hpval` forces Lean to unify two large `reconstructWithDim` terms.
  rw [reconstructForGoal_of_not_replicated _ _ _ mg_rep5330] at hpval
  -- The parent's shards are [2048, 1024], so the non-scalar branch applies.
  have hshard0 : (denoteGraphDistributedFaithful pm initPM 9625).shape = [2048, 1024] := by
    have h := hp.2.1
    simp only [intermediateGoal_5330, List.map] at h
    exact (List.cons.inj h).1
  have hshard0_ne : (denoteGraphDistributedFaithful pm initPM 9625).shape ≠ [1] := by
    rw [hshard0]; decide
  have hval : denoteGraphDistributedFaithful pm initPM 11917 =
      denoteGraphDistributedFaithful sm initSM 5330 := by
    calc denoteGraphDistributedFaithful pm initPM 11917
        = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm initPM 14597,
             denoteGraphDistributedFaithful pm initPM 14599] := rG
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm initPM 9625,
             denoteGraphDistributedFaithful pm initPM 9626] := by rw [rP0, rP1]
      _ = reconstructWithDim 0 2 0
            [denoteGraphDistributedFaithful pm initPM 9625,
             denoteGraphDistributedFaithful pm initPM 9626] :=
          (reconstructWithDim_cons_cons_nonscalar 0 2 0 _ _ [] hshard0_ne).symm
      _ = denoteGraphDistributedFaithful sm initSM 5330 := hpval.symm
  refine ⟨hshape, ?_, ?_⟩
  · -- The PM tensor equals the SM one, so its shape list follows from `hps`.
    show [(denoteGraphDistributedFaithful pm initPM 11917).shape] = _
    rw [hval]
    exact congrArg (fun sh => [sh]) hps
  · show denoteGraphDistributedFaithful sm initSM 8007 =
      reconstructForGoal intermediateGoal_8007 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 11917]
    rw [reconstructForGoal_of_not_replicated _ _ _ mg_rep8007, rSM,
      reconstructWithDim_singleton, hval]

end

end TrainVerify.Denote.GeneratedPatterns
