/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.L12FaithfulReplicatedBoundary
import denote.yoco_goals.SDRingTransport
import denote.yoco_goals.SDTransportPilot
import denote.yoco_goals.IntermediateReconstruction

/-!
# Replicated fan-out goals on the faithful track

`FW_multiref` is an identity on its input, so each goal here follows from its
parent's faithful result — no `_ringAttn` proof, and in particular no
`hWF : WellFormed_YOCOMoE_A04B`, which the old fan-out proofs carried.

Two lemmas make it uniform: `applyNode_fw_multiref_at` covers any arity and
position, and `reconstructForGoal_of_replicated` closes the reconstruction
without asking a tactic to normalise the goal's `if`.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def foSm7408 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_sn7408 : sm.nodes[16]'(by native_decide) = foSm7408 := by
  native_decide

private def foPm14648 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [14644, 14648],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14648 : pm.nodes[64]'(by native_decide) = foPm14648 := by
  native_decide

private def foPm14656 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14656 : pm.nodes[65]'(by native_decide) = foPm14656 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7408_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7408
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4703_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4703 =
      denoteGraphDistributedFaithful pm initPM 4703 :=
    oneTp_valeq intermediateGoal_4703 _ _ 4703 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4703).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4703] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7408 =
      denoteGraphDistributedFaithful sm initSM 4703 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 16 foSm7408 4703 7408
      (fun x => x) (by native_decide) fo_sn7408 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm7408
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4703 [7404, 7408] 2 rfl 7408 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14648 =
      denoteGraphDistributedFaithful pm initPM 4703 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 64 foPm14648 4703 14648
      (fun x => x) (by native_decide) fo_pn14648 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14648
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4703 [14644, 14648] 2 rfl 14648 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14656 =
      denoteGraphDistributedFaithful pm initPM 4703 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 65 foPm14656 4703 14656
      (fun x => x) (by native_decide) fo_pn14656 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14656
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4703 [14652, 14656] 2 rfl 14656 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7408, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 7408 =
      reconstructForGoal intermediateGoal_7408 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14648,
         denoteGraphDistributedFaithful pm initPM 14656]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm7435 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_sn7435 : sm.nodes[41]'(by native_decide) = foSm7435 := by
  native_decide

private def foPm14660 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [14660, 14664],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14660 : pm.nodes[124]'(by native_decide) = foPm14660 := by
  native_decide

private def foPm14668 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14668 : pm.nodes[125]'(by native_decide) = foPm14668 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7435_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7435
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4736_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4736 =
      denoteGraphDistributedFaithful pm initPM 4736 :=
    oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4736).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4736] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7435 =
      denoteGraphDistributedFaithful sm initSM 4736 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 41 foSm7435 4736 7435
      (fun x => x) (by native_decide) fo_sn7435 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm7435
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4736 [7435, 7439] 2 rfl 7435 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14660 =
      denoteGraphDistributedFaithful pm initPM 4736 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 124 foPm14660 4736 14660
      (fun x => x) (by native_decide) fo_pn14660 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14660
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4736 [14660, 14664] 2 rfl 14660 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14668 =
      denoteGraphDistributedFaithful pm initPM 4736 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 125 foPm14668 4736 14668
      (fun x => x) (by native_decide) fo_pn14668 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14668
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4736 [14668, 14672] 2 rfl 14668 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7435, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 7435 =
      reconstructForGoal intermediateGoal_7435 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14660,
         denoteGraphDistributedFaithful pm initPM 14668]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm7439 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_sn7439 : sm.nodes[41]'(by native_decide) = foSm7439 := by
  native_decide

private def foPm14664 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [14660, 14664],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14664 : pm.nodes[124]'(by native_decide) = foPm14664 := by
  native_decide

private def foPm14672 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14672 : pm.nodes[125]'(by native_decide) = foPm14672 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7439_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7439
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4736_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4736 =
      denoteGraphDistributedFaithful pm initPM 4736 :=
    oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4736).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4736] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7439 =
      denoteGraphDistributedFaithful sm initSM 4736 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 41 foSm7439 4736 7439
      (fun x => x) (by native_decide) fo_sn7439 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm7439
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4736 [7435, 7439] 2 rfl 7439 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14664 =
      denoteGraphDistributedFaithful pm initPM 4736 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 124 foPm14664 4736 14664
      (fun x => x) (by native_decide) fo_pn14664 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14664
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4736 [14660, 14664] 2 rfl 14664 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14672 =
      denoteGraphDistributedFaithful pm initPM 4736 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 125 foPm14672 4736 14672
      (fun x => x) (by native_decide) fo_pn14672 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14672
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4736 [14668, 14672] 2 rfl 14672 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7439, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 7439 =
      reconstructForGoal intermediateGoal_7439 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14664,
         denoteGraphDistributedFaithful pm initPM 14672]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm7444 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_sn7444 : sm.nodes[43]'(by native_decide) = foSm7444 := by
  native_decide

private def foPm14677 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14677 : pm.nodes[128]'(by native_decide) = foPm14677 := by
  native_decide

private def foPm14689 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14689 : pm.nodes[129]'(by native_decide) = foPm14689 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7444_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7444
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4738_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4738 =
      denoteGraphDistributedFaithful pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4738).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4738] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7444 =
      denoteGraphDistributedFaithful sm initSM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 43 foSm7444 4738 7444
      (fun x => x) (by native_decide) fo_sn7444 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm7444
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4738 [7444, 7448, 7452] 3 rfl 7444 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14677 =
      denoteGraphDistributedFaithful pm initPM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 128 foPm14677 4738 14677
      (fun x => x) (by native_decide) fo_pn14677 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14677
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4738 [14677, 14681, 14685] 3 rfl 14677 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14689 =
      denoteGraphDistributedFaithful pm initPM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 129 foPm14689 4738 14689
      (fun x => x) (by native_decide) fo_pn14689 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14689
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4738 [14689, 14693, 14697] 3 rfl 14689 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7444, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 7444 =
      reconstructForGoal intermediateGoal_7444 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14677,
         denoteGraphDistributedFaithful pm initPM 14689]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm7448 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_sn7448 : sm.nodes[43]'(by native_decide) = foSm7448 := by
  native_decide

private def foPm14681 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14681 : pm.nodes[128]'(by native_decide) = foPm14681 := by
  native_decide

private def foPm14693 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14693 : pm.nodes[129]'(by native_decide) = foPm14693 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7448_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7448
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4738_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4738 =
      denoteGraphDistributedFaithful pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4738).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4738] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7448 =
      denoteGraphDistributedFaithful sm initSM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 43 foSm7448 4738 7448
      (fun x => x) (by native_decide) fo_sn7448 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm7448
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4738 [7444, 7448, 7452] 3 rfl 7448 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14681 =
      denoteGraphDistributedFaithful pm initPM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 128 foPm14681 4738 14681
      (fun x => x) (by native_decide) fo_pn14681 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14681
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4738 [14677, 14681, 14685] 3 rfl 14681 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14693 =
      denoteGraphDistributedFaithful pm initPM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 129 foPm14693 4738 14693
      (fun x => x) (by native_decide) fo_pn14693 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14693
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4738 [14689, 14693, 14697] 3 rfl 14693 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7448, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 7448 =
      reconstructForGoal intermediateGoal_7448 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14681,
         denoteGraphDistributedFaithful pm initPM 14693]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm7452 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_sn7452 : sm.nodes[43]'(by native_decide) = foSm7452 := by
  native_decide

private def foPm14685 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14685 : pm.nodes[128]'(by native_decide) = foPm14685 := by
  native_decide

private def foPm14697 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697],
    params := [3] }

set_option maxRecDepth 1000000 in
private theorem fo_pn14697 : pm.nodes[129]'(by native_decide) = foPm14697 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7452_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7452
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_4738_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 4738 =
      denoteGraphDistributedFaithful pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 4738).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_4738] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 7452 =
      denoteGraphDistributedFaithful sm initSM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 43 foSm7452 4738 7452
      (fun x => x) (by native_decide) fo_sn7452 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm7452
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 4738 [7444, 7448, 7452] 3 rfl 7452 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 14685 =
      denoteGraphDistributedFaithful pm initPM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 128 foPm14685 4738 14685
      (fun x => x) (by native_decide) fo_pn14685 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14685
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 4738 [14677, 14681, 14685] 3 rfl 14685 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 14697 =
      denoteGraphDistributedFaithful pm initPM 4738 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 129 foPm14697 4738 14697
      (fun x => x) (by native_decide) fo_pn14697 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm14697
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4738 [14689, 14693, 14697] 3 rfl 14697 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_7452, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 7452 =
      reconstructForGoal intermediateGoal_7452 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 14685,
         denoteGraphDistributedFaithful pm initPM 14697]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8019 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8019 : sm.nodes[473]'(by native_decide) = foSm8019 := by
  native_decide

private def foPm15745 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [15741, 15745],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15745 : pm.nodes[1011]'(by native_decide) = foPm15745 := by
  native_decide

private def foPm15753 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753],
    params := [2] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15753 : pm.nodes[1012]'(by native_decide) = foPm15753 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8019_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8019
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5332_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5332 =
      denoteGraphDistributedFaithful pm initPM 5332 :=
    oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5332).shape = [4096, 1024] := by
    have := hparent.1; simpa [intermediateGoal_5332] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8019 =
      denoteGraphDistributedFaithful sm initSM 5332 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 473 foSm8019 5332 8019
      (fun x => x) (by native_decide) fo_sn8019 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8019
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5332 [8015, 8019] 2 rfl 8019 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15745 =
      denoteGraphDistributedFaithful pm initPM 5332 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1011 foPm15745 5332 15745
      (fun x => x) (by native_decide) fo_pn15745 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15745
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5332 [15741, 15745] 2 rfl 15745 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15753 =
      denoteGraphDistributedFaithful pm initPM 5332 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1012 foPm15753 5332 15753
      (fun x => x) (by native_decide) fo_pn15753 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15753
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5332 [15749, 15753] 2 rfl 15753 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8019, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8019 =
      reconstructForGoal intermediateGoal_8019 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15745,
         denoteGraphDistributedFaithful pm initPM 15753]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8033 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8033 : sm.nodes[478]'(by native_decide) = foSm8033 := by
  native_decide

private def foPm15767 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15767 : pm.nodes[1020]'(by native_decide) = foPm15767 := by
  native_decide

private def foPm15815 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15815 : pm.nodes[1021]'(by native_decide) = foPm15815 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8033_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8033
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8033 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8033 5334 8033
      (fun x => x) (by native_decide) fo_sn8033 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8033
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8033 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15767 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15767 5334 15767
      (fun x => x) (by native_decide) fo_pn15767 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15767
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15767 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15815 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15815 5334 15815
      (fun x => x) (by native_decide) fo_pn15815 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15815
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15815 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8033, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8033 =
      reconstructForGoal intermediateGoal_8033 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15767,
         denoteGraphDistributedFaithful pm initPM 15815]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8037 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8037 : sm.nodes[478]'(by native_decide) = foSm8037 := by
  native_decide

private def foPm15771 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15771 : pm.nodes[1020]'(by native_decide) = foPm15771 := by
  native_decide

private def foPm15819 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15819 : pm.nodes[1021]'(by native_decide) = foPm15819 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8037_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8037
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8037 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8037 5334 8037
      (fun x => x) (by native_decide) fo_sn8037 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8037
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8037 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15771 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15771 5334 15771
      (fun x => x) (by native_decide) fo_pn15771 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15771
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15771 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15819 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15819 5334 15819
      (fun x => x) (by native_decide) fo_pn15819 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15819
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15819 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8037, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8037 =
      reconstructForGoal intermediateGoal_8037 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15771,
         denoteGraphDistributedFaithful pm initPM 15819]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8041 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8041 : sm.nodes[478]'(by native_decide) = foSm8041 := by
  native_decide

private def foPm15775 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15775 : pm.nodes[1020]'(by native_decide) = foPm15775 := by
  native_decide

private def foPm15823 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15823 : pm.nodes[1021]'(by native_decide) = foPm15823 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8041_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8041
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8041 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8041 5334 8041
      (fun x => x) (by native_decide) fo_sn8041 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8041
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8041 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15775 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15775 5334 15775
      (fun x => x) (by native_decide) fo_pn15775 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15775
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15775 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15823 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15823 5334 15823
      (fun x => x) (by native_decide) fo_pn15823 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15823
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15823 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8041, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8041 =
      reconstructForGoal intermediateGoal_8041 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15775,
         denoteGraphDistributedFaithful pm initPM 15823]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8045 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8045 : sm.nodes[478]'(by native_decide) = foSm8045 := by
  native_decide

private def foPm15779 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15779 : pm.nodes[1020]'(by native_decide) = foPm15779 := by
  native_decide

private def foPm15827 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15827 : pm.nodes[1021]'(by native_decide) = foPm15827 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8045_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8045
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8045 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8045 5334 8045
      (fun x => x) (by native_decide) fo_sn8045 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8045
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8045 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15779 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15779 5334 15779
      (fun x => x) (by native_decide) fo_pn15779 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15779
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15779 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15827 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15827 5334 15827
      (fun x => x) (by native_decide) fo_pn15827 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15827
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15827 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8045, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8045 =
      reconstructForGoal intermediateGoal_8045 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15779,
         denoteGraphDistributedFaithful pm initPM 15827]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8049 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8049 : sm.nodes[478]'(by native_decide) = foSm8049 := by
  native_decide

private def foPm15783 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15783 : pm.nodes[1020]'(by native_decide) = foPm15783 := by
  native_decide

private def foPm15831 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15831 : pm.nodes[1021]'(by native_decide) = foPm15831 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8049_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8049
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8049 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8049 5334 8049
      (fun x => x) (by native_decide) fo_sn8049 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8049
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8049 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15783 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15783 5334 15783
      (fun x => x) (by native_decide) fo_pn15783 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15783
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15783 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15831 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15831 5334 15831
      (fun x => x) (by native_decide) fo_pn15831 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15831
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15831 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8049, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8049 =
      reconstructForGoal intermediateGoal_8049 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15783,
         denoteGraphDistributedFaithful pm initPM 15831]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8053 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8053 : sm.nodes[478]'(by native_decide) = foSm8053 := by
  native_decide

private def foPm15787 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15787 : pm.nodes[1020]'(by native_decide) = foPm15787 := by
  native_decide

private def foPm15835 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15835 : pm.nodes[1021]'(by native_decide) = foPm15835 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8053_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8053
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8053 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8053 5334 8053
      (fun x => x) (by native_decide) fo_sn8053 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8053
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8053 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15787 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15787 5334 15787
      (fun x => x) (by native_decide) fo_pn15787 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15787
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15787 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15835 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15835 5334 15835
      (fun x => x) (by native_decide) fo_pn15835 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15835
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15835 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8053, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8053 =
      reconstructForGoal intermediateGoal_8053 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15787,
         denoteGraphDistributedFaithful pm initPM 15835]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8057 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8057 : sm.nodes[478]'(by native_decide) = foSm8057 := by
  native_decide

private def foPm15791 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15791 : pm.nodes[1020]'(by native_decide) = foPm15791 := by
  native_decide

private def foPm15839 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15839 : pm.nodes[1021]'(by native_decide) = foPm15839 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8057_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8057
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8057 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8057 5334 8057
      (fun x => x) (by native_decide) fo_sn8057 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8057
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8057 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15791 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15791 5334 15791
      (fun x => x) (by native_decide) fo_pn15791 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15791
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15791 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15839 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15839 5334 15839
      (fun x => x) (by native_decide) fo_pn15839 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15839
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15839 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8057, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8057 =
      reconstructForGoal intermediateGoal_8057 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15791,
         denoteGraphDistributedFaithful pm initPM 15839]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8061 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8061 : sm.nodes[478]'(by native_decide) = foSm8061 := by
  native_decide

private def foPm15795 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15795 : pm.nodes[1020]'(by native_decide) = foPm15795 := by
  native_decide

private def foPm15843 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15843 : pm.nodes[1021]'(by native_decide) = foPm15843 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8061_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8061
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8061 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8061 5334 8061
      (fun x => x) (by native_decide) fo_sn8061 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8061
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8061 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15795 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15795 5334 15795
      (fun x => x) (by native_decide) fo_pn15795 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15795
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15795 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15843 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15843 5334 15843
      (fun x => x) (by native_decide) fo_pn15843 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15843
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15843 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8061, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8061 =
      reconstructForGoal intermediateGoal_8061 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15795,
         denoteGraphDistributedFaithful pm initPM 15843]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8065 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8065 : sm.nodes[478]'(by native_decide) = foSm8065 := by
  native_decide

private def foPm15799 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15799 : pm.nodes[1020]'(by native_decide) = foPm15799 := by
  native_decide

private def foPm15847 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15847 : pm.nodes[1021]'(by native_decide) = foPm15847 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8065_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8065
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8065 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8065 5334 8065
      (fun x => x) (by native_decide) fo_sn8065 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8065
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8065 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15799 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15799 5334 15799
      (fun x => x) (by native_decide) fo_pn15799 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15799
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15799 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15847 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15847 5334 15847
      (fun x => x) (by native_decide) fo_pn15847 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15847
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15847 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8065, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8065 =
      reconstructForGoal intermediateGoal_8065 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15799,
         denoteGraphDistributedFaithful pm initPM 15847]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8069 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8069 : sm.nodes[478]'(by native_decide) = foSm8069 := by
  native_decide

private def foPm15803 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15803 : pm.nodes[1020]'(by native_decide) = foPm15803 := by
  native_decide

private def foPm15851 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15851 : pm.nodes[1021]'(by native_decide) = foPm15851 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8069_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8069
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8069 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8069 5334 8069
      (fun x => x) (by native_decide) fo_sn8069 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8069
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8069 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15803 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15803 5334 15803
      (fun x => x) (by native_decide) fo_pn15803 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15803
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15803 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15851 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15851 5334 15851
      (fun x => x) (by native_decide) fo_pn15851 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15851
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15851 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8069, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8069 =
      reconstructForGoal intermediateGoal_8069 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15803,
         denoteGraphDistributedFaithful pm initPM 15851]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8073 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8073 : sm.nodes[478]'(by native_decide) = foSm8073 := by
  native_decide

private def foPm15807 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15807 : pm.nodes[1020]'(by native_decide) = foPm15807 := by
  native_decide

private def foPm15855 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15855 : pm.nodes[1021]'(by native_decide) = foPm15855 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8073_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8073
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8073 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8073 5334 8073
      (fun x => x) (by native_decide) fo_sn8073 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8073
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8073 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15807 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15807 5334 15807
      (fun x => x) (by native_decide) fo_pn15807 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15807
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15807 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15855 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15855 5334 15855
      (fun x => x) (by native_decide) fo_pn15855 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15855
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15855 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8073, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8073 =
      reconstructForGoal intermediateGoal_8073 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15807,
         denoteGraphDistributedFaithful pm initPM 15855]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8077 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8077 : sm.nodes[478]'(by native_decide) = foSm8077 := by
  native_decide

private def foPm15811 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15811 : pm.nodes[1020]'(by native_decide) = foPm15811 := by
  native_decide

private def foPm15859 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15859 : pm.nodes[1021]'(by native_decide) = foPm15859 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8077_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8077
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5334_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5334] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8077 =
      denoteGraphDistributedFaithful sm initSM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 478 foSm8077 5334 8077
      (fun x => x) (by native_decide) fo_sn8077 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8077
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 rfl 8077 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15811 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1020 foPm15811 5334 15811
      (fun x => x) (by native_decide) fo_pn15811 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15811
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 12 rfl 15811 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15859 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1021 foPm15859 5334 15859
      (fun x => x) (by native_decide) fo_pn15859 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15859
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 rfl 15859 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8077, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8077 =
      reconstructForGoal intermediateGoal_8077 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15811,
         denoteGraphDistributedFaithful pm initPM 15859]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8091 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8091 : sm.nodes[479]'(by native_decide) = foSm8091 := by
  native_decide

private def foPm15873 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15873 : pm.nodes[1022]'(by native_decide) = foPm15873 := by
  native_decide

private def foPm15921 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15921 : pm.nodes[1023]'(by native_decide) = foPm15921 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8091_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8091
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8091 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8091 5336 8091
      (fun x => x) (by native_decide) fo_sn8091 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8091
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8091 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15873 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15873 5336 15873
      (fun x => x) (by native_decide) fo_pn15873 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15873
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15873 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15921 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15921 5336 15921
      (fun x => x) (by native_decide) fo_pn15921 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15921
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15921 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8091, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8091 =
      reconstructForGoal intermediateGoal_8091 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15873,
         denoteGraphDistributedFaithful pm initPM 15921]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8095 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8095 : sm.nodes[479]'(by native_decide) = foSm8095 := by
  native_decide

private def foPm15877 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15877 : pm.nodes[1022]'(by native_decide) = foPm15877 := by
  native_decide

private def foPm15925 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15925 : pm.nodes[1023]'(by native_decide) = foPm15925 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8095_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8095
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8095 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8095 5336 8095
      (fun x => x) (by native_decide) fo_sn8095 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8095
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8095 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15877 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15877 5336 15877
      (fun x => x) (by native_decide) fo_pn15877 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15877
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15877 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15925 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15925 5336 15925
      (fun x => x) (by native_decide) fo_pn15925 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15925
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15925 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8095, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8095 =
      reconstructForGoal intermediateGoal_8095 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15877,
         denoteGraphDistributedFaithful pm initPM 15925]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8099 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8099 : sm.nodes[479]'(by native_decide) = foSm8099 := by
  native_decide

private def foPm15881 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15881 : pm.nodes[1022]'(by native_decide) = foPm15881 := by
  native_decide

private def foPm15929 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15929 : pm.nodes[1023]'(by native_decide) = foPm15929 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8099_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8099
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8099 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8099 5336 8099
      (fun x => x) (by native_decide) fo_sn8099 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8099
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8099 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15881 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15881 5336 15881
      (fun x => x) (by native_decide) fo_pn15881 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15881
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15881 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15929 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15929 5336 15929
      (fun x => x) (by native_decide) fo_pn15929 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15929
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15929 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8099, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8099 =
      reconstructForGoal intermediateGoal_8099 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15881,
         denoteGraphDistributedFaithful pm initPM 15929]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8103 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8103 : sm.nodes[479]'(by native_decide) = foSm8103 := by
  native_decide

private def foPm15885 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15885 : pm.nodes[1022]'(by native_decide) = foPm15885 := by
  native_decide

private def foPm15933 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15933 : pm.nodes[1023]'(by native_decide) = foPm15933 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8103_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8103
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8103 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8103 5336 8103
      (fun x => x) (by native_decide) fo_sn8103 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8103
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8103 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15885 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15885 5336 15885
      (fun x => x) (by native_decide) fo_pn15885 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15885
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15885 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15933 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15933 5336 15933
      (fun x => x) (by native_decide) fo_pn15933 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15933
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15933 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8103, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8103 =
      reconstructForGoal intermediateGoal_8103 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15885,
         denoteGraphDistributedFaithful pm initPM 15933]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8107 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8107 : sm.nodes[479]'(by native_decide) = foSm8107 := by
  native_decide

private def foPm15889 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15889 : pm.nodes[1022]'(by native_decide) = foPm15889 := by
  native_decide

private def foPm15937 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15937 : pm.nodes[1023]'(by native_decide) = foPm15937 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8107_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8107
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8107 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8107 5336 8107
      (fun x => x) (by native_decide) fo_sn8107 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8107
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8107 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15889 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15889 5336 15889
      (fun x => x) (by native_decide) fo_pn15889 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15889
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15889 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15937 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15937 5336 15937
      (fun x => x) (by native_decide) fo_pn15937 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15937
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15937 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8107, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8107 =
      reconstructForGoal intermediateGoal_8107 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15889,
         denoteGraphDistributedFaithful pm initPM 15937]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8111 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8111 : sm.nodes[479]'(by native_decide) = foSm8111 := by
  native_decide

private def foPm15893 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15893 : pm.nodes[1022]'(by native_decide) = foPm15893 := by
  native_decide

private def foPm15941 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15941 : pm.nodes[1023]'(by native_decide) = foPm15941 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8111_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8111
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8111 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8111 5336 8111
      (fun x => x) (by native_decide) fo_sn8111 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8111
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8111 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15893 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15893 5336 15893
      (fun x => x) (by native_decide) fo_pn15893 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15893
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15893 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15941 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15941 5336 15941
      (fun x => x) (by native_decide) fo_pn15941 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15941
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15941 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8111, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8111 =
      reconstructForGoal intermediateGoal_8111 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15893,
         denoteGraphDistributedFaithful pm initPM 15941]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8115 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8115 : sm.nodes[479]'(by native_decide) = foSm8115 := by
  native_decide

private def foPm15897 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15897 : pm.nodes[1022]'(by native_decide) = foPm15897 := by
  native_decide

private def foPm15945 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15945 : pm.nodes[1023]'(by native_decide) = foPm15945 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8115_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8115
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8115 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8115 5336 8115
      (fun x => x) (by native_decide) fo_sn8115 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8115
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8115 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15897 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15897 5336 15897
      (fun x => x) (by native_decide) fo_pn15897 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15897
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15897 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15945 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15945 5336 15945
      (fun x => x) (by native_decide) fo_pn15945 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15945
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15945 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8115, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8115 =
      reconstructForGoal intermediateGoal_8115 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15897,
         denoteGraphDistributedFaithful pm initPM 15945]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8119 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8119 : sm.nodes[479]'(by native_decide) = foSm8119 := by
  native_decide

private def foPm15901 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15901 : pm.nodes[1022]'(by native_decide) = foPm15901 := by
  native_decide

private def foPm15949 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15949 : pm.nodes[1023]'(by native_decide) = foPm15949 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8119_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8119
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8119 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8119 5336 8119
      (fun x => x) (by native_decide) fo_sn8119 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8119
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8119 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15901 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15901 5336 15901
      (fun x => x) (by native_decide) fo_pn15901 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15901
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15901 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15949 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15949 5336 15949
      (fun x => x) (by native_decide) fo_pn15949 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15949
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15949 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8119, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8119 =
      reconstructForGoal intermediateGoal_8119 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15901,
         denoteGraphDistributedFaithful pm initPM 15949]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8123 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8123 : sm.nodes[479]'(by native_decide) = foSm8123 := by
  native_decide

private def foPm15905 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15905 : pm.nodes[1022]'(by native_decide) = foPm15905 := by
  native_decide

private def foPm15953 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15953 : pm.nodes[1023]'(by native_decide) = foPm15953 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8123_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8123
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8123 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8123 5336 8123
      (fun x => x) (by native_decide) fo_sn8123 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8123
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8123 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15905 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15905 5336 15905
      (fun x => x) (by native_decide) fo_pn15905 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15905
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15905 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15953 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15953 5336 15953
      (fun x => x) (by native_decide) fo_pn15953 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15953
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15953 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8123, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8123 =
      reconstructForGoal intermediateGoal_8123 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15905,
         denoteGraphDistributedFaithful pm initPM 15953]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8127 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8127 : sm.nodes[479]'(by native_decide) = foSm8127 := by
  native_decide

private def foPm15909 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15909 : pm.nodes[1022]'(by native_decide) = foPm15909 := by
  native_decide

private def foPm15957 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15957 : pm.nodes[1023]'(by native_decide) = foPm15957 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8127_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8127
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8127 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8127 5336 8127
      (fun x => x) (by native_decide) fo_sn8127 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8127
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8127 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15909 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15909 5336 15909
      (fun x => x) (by native_decide) fo_pn15909 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15909
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15909 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15957 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15957 5336 15957
      (fun x => x) (by native_decide) fo_pn15957 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15957
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15957 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8127, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8127 =
      reconstructForGoal intermediateGoal_8127 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15909,
         denoteGraphDistributedFaithful pm initPM 15957]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8131 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8131 : sm.nodes[479]'(by native_decide) = foSm8131 := by
  native_decide

private def foPm15913 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15913 : pm.nodes[1022]'(by native_decide) = foPm15913 := by
  native_decide

private def foPm15961 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15961 : pm.nodes[1023]'(by native_decide) = foPm15961 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8131_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8131
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8131 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8131 5336 8131
      (fun x => x) (by native_decide) fo_sn8131 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8131
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8131 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15913 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15913 5336 15913
      (fun x => x) (by native_decide) fo_pn15913 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15913
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15913 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15961 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15961 5336 15961
      (fun x => x) (by native_decide) fo_pn15961 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15961
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15961 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8131, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8131 =
      reconstructForGoal intermediateGoal_8131 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15913,
         denoteGraphDistributedFaithful pm initPM 15961]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

private def foSm8135 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_sn8135 : sm.nodes[479]'(by native_decide) = foSm8135 := by
  native_decide

private def foPm15917 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15917 : pm.nodes[1022]'(by native_decide) = foPm15917 := by
  native_decide

private def foPm15965 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem fo_pn15965 : pm.nodes[1023]'(by native_decide) = foPm15965 := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_8135_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8135
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5336_faithful initSM initPM hSM hPM hInit
  have hv : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hparent
  have hs : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    have := hparent.1; simpa [intermediateGoal_5336] using this
  have rSM : denoteGraphDistributedFaithful sm initSM 8135 =
      denoteGraphDistributedFaithful sm initSM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 479 foSm8135 5336 8135
      (fun x => x) (by native_decide) fo_sn8135 ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foSm8135
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at sm st 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 rfl 8135 (by decide)
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15917 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1022 foPm15917 5336 15917
      (fun x => x) (by native_decide) fo_pn15917 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15917
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 12 rfl 15917 (by decide)
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15965 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1023 foPm15965 5336 15965
      (fun x => x) (by native_decide) fo_pn15965 ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold foPm15965
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 rfl 15965 (by decide)
  unfold InitGoalHolds
  simp only [intermediateGoal_8135, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact hs
  · rw [rPM0, rPM1, ← hv, hs]
  · show denoteGraphDistributedFaithful sm initSM 8135 =
      reconstructForGoal intermediateGoal_8135 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15917,
         denoteGraphDistributedFaithful pm initPM 15965]
    rw [reconstructForGoal_of_replicated _ _ _ (by rfl), List.headD_cons,
      rSM, rPM0, hv]

end

end TrainVerify.Denote.GeneratedPatterns
