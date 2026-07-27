/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.SwigluChunkCommute
import denote.yoco_goals.SDRingTransport

/-!
# The MoE-branch swiglu

`4728` is the first goal in this campaign whose PM side genuinely *splits*: the
two `FW_swiglu` nodes read `ChunkPrim` shards of `4723` / `4727` rather than the
full tensors. Reconstructing the goal therefore needs

* `chunk_fw_swiglu_dim0` — swiglu is elementwise, so it commutes with the split;
* `allGatherPrimDimN_chunkPrimDimN_id_dim0_2` — gathering the two shards back is
  the identity.

Both are general in the shape, proved in the two preceding modules.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def swSm : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [4723, 4727], outs := [4728],
    params := [] }

private def swCh0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [4723], outs := [7521], params := [0] }

private def swCh1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [4723], outs := [7522], params := [0] }

private def swCh2 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [4727], outs := [7539], params := [0] }

private def swCh3 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [4727], outs := [7540], params := [0] }

private def swPm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [7521, 7539], outs := [7543], params := [] }

private def swPm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [7522, 7540], outs := [7544], params := [] }

set_option maxRecDepth 1000000 in
private theorem sw_sn : sm.nodes[33]'(by native_decide) = swSm := by native_decide

set_option maxRecDepth 1000000 in
private theorem sw_c0 : pm.nodes[100]'(by native_decide) = swCh0 := by native_decide

set_option maxRecDepth 1000000 in
private theorem sw_c1 : pm.nodes[101]'(by native_decide) = swCh1 := by native_decide

set_option maxRecDepth 1000000 in
private theorem sw_c2 : pm.nodes[102]'(by native_decide) = swCh2 := by native_decide

set_option maxRecDepth 1000000 in
private theorem sw_c3 : pm.nodes[103]'(by native_decide) = swCh3 := by native_decide

set_option maxRecDepth 1000000 in
private theorem sw_p0 : pm.nodes[106]'(by native_decide) = swPm0 := by native_decide

set_option maxRecDepth 1000000 in
private theorem sw_p1 : pm.nodes[107]'(by native_decide) = swPm1 := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4728_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4728
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hg := recon_intermediateGoal_4723_faithful initSM initPM hSM hPM hInit
  have hu := recon_intermediateGoal_4727_faithful initSM initPM hSM hPM hInit
  have hgv : denoteGraphDistributedFaithful sm initSM 4723 =
      denoteGraphDistributedFaithful pm initPM 4723 := by
    have h := hg.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have huv : denoteGraphDistributedFaithful sm initSM 4727 =
      denoteGraphDistributedFaithful pm initPM 4727 := by
    have h := hu.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hgs : (denoteGraphDistributedFaithful sm initSM 4723).shape = [4096, 512] := hg.1
  have hus : (denoteGraphDistributedFaithful sm initSM 4727).shape = [4096, 512] := hu.1
  -- SM side: the single-rank swiglu.
  have rSM : denoteGraphDistributedFaithful sm initSM 4728 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 4723)
        (denoteGraphDistributedFaithful sm initSM 4727) := by
    refine denoteGraphDistributedFaithful_reduce2 sm initSM 33 swSm 4723 4727 4728
      fw_swiglu (by native_decide) sw_sn ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold swSm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_swiglu_out sm st 0 4723 4727 4728 []
  -- PM side: four chunks, then two local swiglus.
  have rC0 : denoteGraphDistributedFaithful pm initPM 7521 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm initPM 4723) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 100 swCh0 4723 7521
      (chunkPrimDimN 0 2 0) (by native_decide) sw_c0 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold swCh0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm st 0 4723 7521 0
  have rC1 : denoteGraphDistributedFaithful pm initPM 7522 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm initPM 4723) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 101 swCh1 4723 7522
      (chunkPrimDimN 0 2 1) (by native_decide) sw_c1 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold swCh1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm st 1 4723 7522 0
  have rC2 : denoteGraphDistributedFaithful pm initPM 7539 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm initPM 4727) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 102 swCh2 4727 7539
      (chunkPrimDimN 0 2 0) (by native_decide) sw_c2 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold swCh2
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm st 0 4727 7539 0
  have rC3 : denoteGraphDistributedFaithful pm initPM 7540 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm initPM 4727) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 103 swCh3 4727 7540
      (chunkPrimDimN 0 2 1) (by native_decide) sw_c3 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold swCh3
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm st 1 4727 7540 0
  have rP0 : denoteGraphDistributedFaithful pm initPM 7543 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 7521)
        (denoteGraphDistributedFaithful pm initPM 7539) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 106 swPm0 7521 7539 7543
      fw_swiglu (by native_decide) sw_p0 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold swPm0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_swiglu_out pm st 0 7521 7539 7543 []
  have rP1 : denoteGraphDistributedFaithful pm initPM 7544 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 7522)
        (denoteGraphDistributedFaithful pm initPM 7540) := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 107 swPm1 7522 7540 7544
      fw_swiglu (by native_decide) sw_p1 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold swPm1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_swiglu_out pm st 1 7522 7540 7544 []
  -- Each PM shard is the corresponding chunk of the SM result.
  have hsh0 : denoteGraphDistributedFaithful pm initPM 7543 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful sm initSM 4728) := by
    rw [rP0, rC0, rC2, rSM, chunk_fw_swiglu_dim0 2 0 4096 512 _ _ hgs hus
      (by omega) (by omega) (by omega) (by omega), hgv, huv]
  have hsh1 : denoteGraphDistributedFaithful pm initPM 7544 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful sm initSM 4728) := by
    rw [rP1, rC1, rC3, rSM, chunk_fw_swiglu_dim0 2 1 4096 512 _ _ hgs hus
      (by omega) (by omega) (by omega) (by omega), hgv, huv]
  have hswsh : (denoteGraphDistributedFaithful sm initSM 4728).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu; simp [Tensor.mkShape, hus]
  have hchsh : ∀ r, (chunkPrimDimN 0 2 r
      (denoteGraphDistributedFaithful sm initSM 4728)).shape = [2048, 512] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r _ _ hswsh (by omega)]
    simp [List.set, List.getD]
  unfold InitGoalHolds
  simp only [intermediateGoal_4728, List.map]
  refine ⟨hswsh, ?_, ?_⟩
  · rw [hsh0, hsh1, hchsh 0, hchsh 1]
  · rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    simp only [reconstructWithDim, List.map, List.head?, Option.map, Option.getD]
    rw [hsh0, hsh1, hchsh 0]
    rw [if_neg (by decide : ¬ ([2048, 512] : List Nat) = [1])]
    exact (allGatherPrimDimN_chunkPrimDimN_id_dim0_2 _ 4096 512 hswsh
      (by omega) (by omega) (by omega)).symm

end

end TrainVerify.Denote.GeneratedPatterns
