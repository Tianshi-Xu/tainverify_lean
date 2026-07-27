/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ChunkGatherDim0
import denote.MultirefGeneral
import denote.yoco_goals.SDTLayer1TDC_0

/-!
# A fan-out that is then split

`7460` is the second output of a `FW_multiref`. On the PM side the fan-out
happens first (into `11890`) and each rank then takes a `ChunkPrim` shard of it,
so reconstructing the goal needs the dim-0 round trip.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def mcSm : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460],
    params := [2] }

private def mcPm : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890],
    params := [2] }

private def mcC0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [11890], outs := [12011], params := [0] }

private def mcC1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [11890], outs := [12012], params := [0] }

set_option maxRecDepth 1000000 in
private theorem mc_sn : sm.nodes[55]'(by native_decide) = mcSm := by native_decide

set_option maxRecDepth 1000000 in
private theorem mc_pn : pm.nodes[160]'(by native_decide) = mcPm := by native_decide

set_option maxRecDepth 1000000 in
private theorem mc_c0 : pm.nodes[162]'(by native_decide) = mcC0 := by native_decide

set_option maxRecDepth 1000000 in
private theorem mc_c1 : pm.nodes[164]'(by native_decide) = mcC1 := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7460_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7460
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hp := recon_intermediateGoal_4757_faithful initSM initPM hSM hPM hInit
  have hpv : denoteGraphDistributedFaithful sm initSM 4757 =
      denoteGraphDistributedFaithful pm initPM 4757 := by
    have h := hp.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hps : (denoteGraphDistributedFaithful sm initSM 4757).shape = [4096, 1024] := hp.1
  -- SM: second output of the fan-out.
  have rSM : denoteGraphDistributedFaithful sm initSM 7460 =
      denoteGraphDistributedFaithful sm initSM 4757 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 55 mcSm 4757 7460
      (fun x => x) (by native_decide) mc_sn ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mcSm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4757 [7456, 7460] 2 rfl 7460 (by decide)
  -- PM: fan out, then each rank chunks it.
  have rMid : denoteGraphDistributedFaithful pm initPM 11890 =
      denoteGraphDistributedFaithful pm initPM 4757 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 160 mcPm 4757 11890
      (fun x => x) (by native_decide) mc_pn ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mcPm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4757 [11889, 11890] 2 rfl 11890 (by decide)
  have rC0 : denoteGraphDistributedFaithful pm initPM 12011 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm initPM 11890) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 162 mcC0 11890 12011
      (chunkPrimDimN 0 2 0) (by native_decide) mc_c0 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mcC0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm st 0 11890 12011 0
  have rC1 : denoteGraphDistributedFaithful pm initPM 12012 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm initPM 11890) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 164 mcC1 11890 12012
      (chunkPrimDimN 0 2 1) (by native_decide) mc_c1 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold mcC1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm st 1 11890 12012 0
  have hmid : denoteGraphDistributedFaithful pm initPM 11890 =
      denoteGraphDistributedFaithful sm initSM 7460 := by
    rw [rMid, rSM, hpv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 7460).shape = [4096, 1024] := by
    rw [rSM]; exact hps
  have hchsh : ∀ r, (chunkPrimDimN 0 2 r
      (denoteGraphDistributedFaithful sm initSM 7460)).shape = [2048, 1024] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r _ _ hshape (by omega)]
    simp [List.set, List.getD]
  unfold InitGoalHolds
  simp only [intermediateGoal_7460, List.map]
  refine ⟨hshape, ?_, ?_⟩
  · rw [rC0, rC1, hmid, hchsh 0, hchsh 1]
  · rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    simp only [reconstructWithDim, List.map, List.head?, Option.map, Option.getD]
    rw [rC0, rC1, hmid, hchsh 0]
    rw [if_neg (by decide : ¬ ([2048, 1024] : List Nat) = [1])]
    exact (allGatherPrimDimN_chunkPrimDimN_id_dim0_2 _ 4096 1024 hshape
      (by omega) (by omega) (by omega)).symm

end

end TrainVerify.Denote.GeneratedPatterns
