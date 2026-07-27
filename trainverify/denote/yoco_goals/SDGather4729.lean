/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ViewSelf
import denote.yoco_goals.SDSwiglu4728

/-!
# Gathering the MoE branch back together

`4729` is where the split from `4728` closes: each rank reshapes its own
`[2048, 512]` shard (a no-op, by `fw_view_self`) and an `AllGatherPrim` puts the
two halves back into one `[4096, 512]` tensor.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def agSm : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [4728], outs := [4729],
    params := [4096, 512] }

private def agR0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7543], outs := [7545],
    params := [2048, 512] }

private def agR1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [7544], outs := [7546],
    params := [2048, 512] }

private def agGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [7545, 7546], outs := [4729],
    params := [0] }

set_option maxRecDepth 1000000 in
private theorem ag_sn : sm.nodes[34]'(by native_decide) = agSm := by native_decide

set_option maxRecDepth 1000000 in
private theorem ag_r0 : pm.nodes[109]'(by native_decide) = agR0 := by native_decide

set_option maxRecDepth 1000000 in
private theorem ag_r1 : pm.nodes[110]'(by native_decide) = agR1 := by native_decide

set_option maxRecDepth 1000000 in
private theorem ag_g : pm.nodes[111]'(by native_decide) = agGather := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4729_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4729
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsw : (denoteGraphDistributedFaithful sm initSM 4728).shape = [4096, 512] :=
    (sw_shards initSM initPM hSM hPM hInit).2.2
  -- SM side: reshape to the shape it already has.
  have rSM : denoteGraphDistributedFaithful sm initSM 4729 =
      denoteGraphDistributedFaithful sm initSM 4728 := by
    have h : denoteGraphDistributedFaithful sm initSM 4729 =
        fw_view [4096, 512] (denoteGraphDistributedFaithful sm initSM 4728) := by
      refine denoteGraphDistributedFaithful_reduce1 sm initSM 34 agSm 4728 4729
        (fw_view [4096, 512]) (by native_decide) ag_sn ?_
        (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
        (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      intro st
      unfold agSm
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide)]
      exact applyNode_fw_reshape_out sm st 0 4728 4729 [4096, 512]
    rw [h, fw_view_self _ _ hsw]
  -- PM side: each rank reshapes its own shard (also a no-op), then all-gathers.
  obtain ⟨hsh0, hsh1, _⟩ := sw_shards initSM initPM hSM hPM hInit
  have hchsh : ∀ r, (chunkPrimDimN 0 2 r
      (denoteGraphDistributedFaithful sm initSM 4728)).shape = [2048, 512] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r _ _ hsw (by omega)]
    simp [List.set, List.getD]
  have rR0 : denoteGraphDistributedFaithful pm initPM 7545 =
      denoteGraphDistributedFaithful pm initPM 7543 := by
    have h : denoteGraphDistributedFaithful pm initPM 7545 =
        fw_view [2048, 512] (denoteGraphDistributedFaithful pm initPM 7543) := by
      refine denoteGraphDistributedFaithful_reduce1 pm initPM 109 agR0 7543 7545
        (fw_view [2048, 512]) (by native_decide) ag_r0 ?_
        (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
        (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      intro st
      unfold agR0
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide)]
      exact applyNode_fw_reshape_out pm st 0 7543 7545 [2048, 512]
    rw [h, fw_view_self _ _ (by rw [hsh0]; exact hchsh 0)]
  have rR1 : denoteGraphDistributedFaithful pm initPM 7546 =
      denoteGraphDistributedFaithful pm initPM 7544 := by
    have h : denoteGraphDistributedFaithful pm initPM 7546 =
        fw_view [2048, 512] (denoteGraphDistributedFaithful pm initPM 7544) := by
      refine denoteGraphDistributedFaithful_reduce1 pm initPM 110 agR1 7544 7546
        (fw_view [2048, 512]) (by native_decide) ag_r1 ?_
        (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
        (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      intro st
      unfold agR1
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide)]
      exact applyNode_fw_reshape_out pm st 1 7544 7546 [2048, 512]
    rw [h, fw_view_self _ _ (by rw [hsh1]; exact hchsh 1)]
  have rPM : denoteGraphDistributedFaithful pm initPM 4729 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm initPM 7545,
         denoteGraphDistributedFaithful pm initPM 7546] := by
    refine denoteGraphDistributedFaithful_reduce2 pm initPM 111 agGather 7545 7546 4729
      (fun a b => allGatherPrimDimN 0 2 0 [a, b]) (by native_decide) ag_g ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide)
    intro st
    unfold agGather
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_allGatherPrimDimN_out pm st 0 [7545, 7546] 4729 0
  have hval : denoteGraphDistributedFaithful pm initPM 4729 =
      denoteGraphDistributedFaithful sm initSM 4729 := by
    rw [rPM, rR0, rR1, hsh0, hsh1, rSM]
    exact allGatherPrimDimN_chunkPrimDimN_id_dim0_2 _ 4096 512 hsw
      (by omega) (by omega) (by omega)
  have hshape : (denoteGraphDistributedFaithful sm initSM 4729).shape = [4096, 512] := by
    rw [rSM]; exact hsw
  unfold InitGoalHolds
  simp only [intermediateGoal_4729, List.map]
  exact ⟨hshape, by rw [hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval.symm⟩

end

end TrainVerify.Denote.GeneratedPatterns
