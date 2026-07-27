/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDChainHead
import denote.yoco_goals.SDRingTransport
import denote.yoco_goals.IntermediateReconstruction

/-!
# Chain-head compute nodes

The head of the self-decoder is a replicated chain: both PM ranks run the same
node on the same input tid and write the same output tid, so each goal reduces
to an equality with its parent, exactly like the single-shard fan-outs.

Two shapes appear here:

* `4681` — `FW_float` on `4680` (an identity on its input), the embedding output that `SDChainHead` just
  brought onto the faithful track;
* `4719` — `FW_sigmoid` on `4718`.

Both PM ranks write the output, so each reduction anchors on the *last* writer.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def chSm4681 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681], params := [] }

private def chPm4681 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681], params := [] }

set_option maxRecDepth 1000000 in
private theorem ch_sn4681 : sm.nodes[1]'(by native_decide) = chSm4681 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem ch_pn4681 : pm.nodes[28]'(by native_decide) = chPm4681 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4681_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4681
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_goal_5_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4680 =
      denoteGraphDistributedFaithful pm initPM 4680 :=
    oneTp_valeq goal_5 _ _ 4680 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4680).shape = [4096, 1024] := by
    have := hparent.1; simpa [goal_5] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 4681 =
      denoteGraphDistributedFaithful sm initSM 4680 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 1 chSm4681 4680 4681
      (fun x => x) (by native_decide) ch_sn4681 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold chSm4681
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm st 0 4680 4681 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4681 =
      denoteGraphDistributedFaithful pm initPM 4680 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 28 chPm4681 4680 4681
      (fun x => x) (by native_decide) ch_pn4681 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold chPm4681
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm st 1 4680 4681 []
  have hval : denoteGraphDistributedFaithful sm initSM 4681 =
      denoteGraphDistributedFaithful pm initPM 4681 := by
    rw [rSM, rPM, hv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4681).shape = [4096, 1024] := by
    rw [rSM]; exact hs
  exact wrap_1tp_gen _ _ intermediateGoal_4681 4681 [4096, 1024] rfl rfl rfl rfl rfl rfl
    hval hshape

private def chSm4719 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719], params := [] }

private def chPm4719 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719], params := [] }

set_option maxRecDepth 1000000 in
private theorem ch_sn4719 : sm.nodes[32]'(by native_decide) = chSm4719 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem ch_pn4719 : pm.nodes[99]'(by native_decide) = chPm4719 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4719_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4719
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4718_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4718 =
      denoteGraphDistributedFaithful pm initPM 4718 :=
    oneTp_valeq intermediateGoal_4718 _ _ 4718 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4718).shape = [4096, 1] := by
    have := hparent.1; simpa [intermediateGoal_4718] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 4719 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 4718) := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 32 chSm4719 4718 4719
      fw_sigmoid (by native_decide) ch_sn4719 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold chSm4719
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_sigmoid_out sm st 0 4718 4719 []
  have rPM : denoteGraphDistributedFaithful pm initPM 4719 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 4718) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 99 chPm4719 4718 4719
      fw_sigmoid (by native_decide) ch_pn4719 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold chPm4719
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_sigmoid_out pm st 1 4718 4719 []
  have hval : denoteGraphDistributedFaithful sm initSM 4719 =
      denoteGraphDistributedFaithful pm initPM 4719 := by
    rw [rSM, rPM, hv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4719).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]; exact hs
  exact wrap_1tp_gen _ _ intermediateGoal_4719 4719 [4096, 1] rfl rfl rfl rfl rfl rfl
    hval hshape

end

end TrainVerify.Denote.GeneratedPatterns
