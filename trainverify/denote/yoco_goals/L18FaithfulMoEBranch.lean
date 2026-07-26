/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L18FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-6 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-5 段 `L13FaithfulMoEBranch` to block 6.
The block-6 cu tensor is **5639**.

* SM 733 `FW_topk_routing [5653] → [5654, 5655, 5656]` params `[8, 1]`
    (PM 1528 / 1532 → `10763, 10765, 10767` / `10764, 10766, 10768`)
* SM 734 `FW_view [5662] → [5663]` params `[4096, 1]`        (PM 1529 / 1533 → 10785 / 10786)
* SM 735 `FW_view [5667] → [5668]` params `[4096, 512]`      (PM 1530 / 1534 → 10803 / 10804)
* SM 736 `FW_view [5671] → [5672]` params `[4096, 512]`      (PM 1531 / 1535 → 10821 / 10822)
* SM 738 `FW_sigmoid [5663] → [5664]`                        (PM 1537 / 1540 → 10787 / 10788)
* SM 739 `FW_swiglu [5668, 5672] → [5673]`                   (PM 1538 / 1541 → 10825 / 10826)

The third `FW_topk_routing` output (`5656`) has no intermediate goal and is therefore
not exported, but the node reduction handles all three outputs.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-! ### Node literals -/

private def l18mbSmTopk5654 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5653], outs := [5654,5655,5656],
    params := [8,1] }
private def l18mbSmView5663 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5662], outs := [5663], params := [4096,1] }
private def l18mbSmView5668 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5667], outs := [5668], params := [4096,512] }
private def l18mbSmView5672 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5671], outs := [5672], params := [4096,512] }
private def l18mbSmSig5664 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5663], outs := [5664] }
private def l18mbSmSwi5673 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5668,5672], outs := [5673] }

private def l18mbPmTopk10763 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10761], outs := [10763,10765,10767],
    params := [8,1] }
private def l18mbPmView10785 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10779], outs := [10785], params := [2048,1] }
private def l18mbPmView10803 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10793], outs := [10803], params := [2048,512] }
private def l18mbPmView10821 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10811], outs := [10821], params := [2048,512] }
private def l18mbPmTopk10764 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10762], outs := [10764,10766,10768],
    params := [8,1] }
private def l18mbPmView10786 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10780], outs := [10786], params := [2048,1] }
private def l18mbPmView10804 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10794], outs := [10804], params := [2048,512] }
private def l18mbPmView10822 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10812], outs := [10822], params := [2048,512] }
private def l18mbPmSig10787 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10785], outs := [10787] }
private def l18mbPmSwi10825 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10803,10821], outs := [10825] }
private def l18mbPmSig10788 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10786], outs := [10788] }
private def l18mbPmSwi10826 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10804,10822], outs := [10826] }

/-! ### Certified node indices -/

private theorem l18mb_sm_node_facts :
    sm.nodes[733]'(by native_decide) = l18mbSmTopk5654 ∧
    sm.nodes[734]'(by native_decide) = l18mbSmView5663 ∧
    sm.nodes[735]'(by native_decide) = l18mbSmView5668 ∧
    sm.nodes[736]'(by native_decide) = l18mbSmView5672 ∧
    sm.nodes[738]'(by native_decide) = l18mbSmSig5664 ∧
    sm.nodes[739]'(by native_decide) = l18mbSmSwi5673 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l18mb_pm_node_facts :
    pm.nodes[1528]'(by native_decide) = l18mbPmTopk10763 ∧
    pm.nodes[1529]'(by native_decide) = l18mbPmView10785 ∧
    pm.nodes[1530]'(by native_decide) = l18mbPmView10803 ∧
    pm.nodes[1531]'(by native_decide) = l18mbPmView10821 ∧
    pm.nodes[1532]'(by native_decide) = l18mbPmTopk10764 ∧
    pm.nodes[1533]'(by native_decide) = l18mbPmView10786 ∧
    pm.nodes[1534]'(by native_decide) = l18mbPmView10804 ∧
    pm.nodes[1535]'(by native_decide) = l18mbPmView10822 ∧
    pm.nodes[1537]'(by native_decide) = l18mbPmSig10787 ∧
    pm.nodes[1538]'(by native_decide) = l18mbPmSwi10825 ∧
    pm.nodes[1540]'(by native_decide) = l18mbPmSig10788 ∧
    pm.nodes[1541]'(by native_decide) = l18mbPmSwi10826 := by
  native_decide

private theorem l18mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l18mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l18mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(734, 5654), (734, 5655), (733, 5653), (735, 5663), (734, 5662), (736, 5668), (735, 5667), (737, 5672), (736, 5671), (739, 5664), (738, 5663), (740, 5673), (739, 5668), (739, 5672)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l18mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1529, 10763), (1529, 10765), (1528, 10761), (1533, 10764), (1533, 10766), (1532, 10762), (1530, 10785), (1529, 10779), (1531, 10803), (1530, 10793), (1532, 10821), (1531, 10811), (1534, 10786), (1533, 10780), (1535, 10804), (1534, 10794), (1536, 10822), (1535, 10812), (1538, 10787), (1537, 10785), (1541, 10788), (1540, 10786), (1539, 10825), (1538, 10803), (1538, 10821), (1542, 10826), (1541, 10804), (1541, 10822), (1528, 5639)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l18mb_cu_not_written : ∀ n ∈ pm.nodes, 5639 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_sm5654 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5653).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5654 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5653) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 733 l18mbSmTopk5654
    5653 5654 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l18mb_sm_node_facts.1 ?_
    (l18mb_nonempty_sm 734) (l18mb_sm_not_written 734 5654 (by decide))
    (l18mb_nonempty_sm 733) (l18mb_sm_not_written 733 5653 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l18mbSmTopk5654
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5653 5654 5655 5656 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_sm5655 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5653).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5655 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5653) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 733 l18mbSmTopk5654
    5653 5655 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l18mb_sm_node_facts.1 ?_
    (l18mb_nonempty_sm 734) (l18mb_sm_not_written 734 5655 (by decide))
    (l18mb_nonempty_sm 733) (l18mb_sm_not_written 733 5653 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l18mbSmTopk5654
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5653 5654 5655 5656 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10763 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10761).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10763 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10761) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1528 l18mbPmTopk10763
    10761 10763 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l18mb_pm_node_facts.1 ?_
    (l18mb_nonempty_pm 1529) (l18mb_pm_not_written 1529 10763 (by decide))
    (l18mb_nonempty_pm 1528) (l18mb_pm_not_written 1528 10761 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l18mbPmTopk10763
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 10761 10763 10765 10767 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10765 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10761).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10765 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10761) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1528 l18mbPmTopk10763
    10761 10765 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l18mb_pm_node_facts.1 ?_
    (l18mb_nonempty_pm 1529) (l18mb_pm_not_written 1529 10765 (by decide))
    (l18mb_nonempty_pm 1528) (l18mb_pm_not_written 1528 10761 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l18mbPmTopk10763
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 10761 10763 10765 10767 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10764 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10762).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10764 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10762) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1532 l18mbPmTopk10764
    10762 10764 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1533) (l18mb_pm_not_written 1533 10764 (by decide))
    (l18mb_nonempty_pm 1532) (l18mb_pm_not_written 1532 10762 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l18mbPmTopk10764
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 10762 10764 10766 10768 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10766 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10762).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10766 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10762) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1532 l18mbPmTopk10764
    10762 10766 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1533) (l18mb_pm_not_written 1533 10766 (by decide))
    (l18mb_nonempty_pm 1532) (l18mb_pm_not_written 1532 10762 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l18mbPmTopk10764
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 10762 10764 10766 10768 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_sm5663 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5663 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5662) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 734 l18mbSmView5663
    5662 5663 (fun x => fw_view [4096,1] x)
    (by native_decide) l18mb_sm_node_facts.2.1 ?_
    (l18mb_nonempty_sm 735) (l18mb_sm_not_written 735 5663 (by decide))
    (l18mb_nonempty_sm 734) (l18mb_sm_not_written 734 5662 (by decide))
  intro s
  unfold l18mbSmView5663
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5662 5663

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_sm5668 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5668 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5667) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 735 l18mbSmView5668
    5667 5668 (fun x => fw_view [4096,512] x)
    (by native_decide) l18mb_sm_node_facts.2.2.1 ?_
    (l18mb_nonempty_sm 736) (l18mb_sm_not_written 736 5668 (by decide))
    (l18mb_nonempty_sm 735) (l18mb_sm_not_written 735 5667 (by decide))
  intro s
  unfold l18mbSmView5668
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5667 5668

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_sm5672 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5672 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5671) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 736 l18mbSmView5672
    5671 5672 (fun x => fw_view [4096,512] x)
    (by native_decide) l18mb_sm_node_facts.2.2.2.1 ?_
    (l18mb_nonempty_sm 737) (l18mb_sm_not_written 737 5672 (by decide))
    (l18mb_nonempty_sm 736) (l18mb_sm_not_written 736 5671 (by decide))
  intro s
  unfold l18mbSmView5672
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5671 5672

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10785 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10785 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10779) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1529 l18mbPmView10785
    10779 10785 (fun x => fw_view [2048,1] x)
    (by native_decide) l18mb_pm_node_facts.2.1 ?_
    (l18mb_nonempty_pm 1530) (l18mb_pm_not_written 1530 10785 (by decide))
    (l18mb_nonempty_pm 1529) (l18mb_pm_not_written 1529 10779 (by decide))
  intro s
  unfold l18mbPmView10785
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 10779 10785

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10803 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10803 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10793) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1530 l18mbPmView10803
    10793 10803 (fun x => fw_view [2048,512] x)
    (by native_decide) l18mb_pm_node_facts.2.2.1 ?_
    (l18mb_nonempty_pm 1531) (l18mb_pm_not_written 1531 10803 (by decide))
    (l18mb_nonempty_pm 1530) (l18mb_pm_not_written 1530 10793 (by decide))
  intro s
  unfold l18mbPmView10803
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10793 10803

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10821 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10821 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10811) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1531 l18mbPmView10821
    10811 10821 (fun x => fw_view [2048,512] x)
    (by native_decide) l18mb_pm_node_facts.2.2.2.1 ?_
    (l18mb_nonempty_pm 1532) (l18mb_pm_not_written 1532 10821 (by decide))
    (l18mb_nonempty_pm 1531) (l18mb_pm_not_written 1531 10811 (by decide))
  intro s
  unfold l18mbPmView10821
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10811 10821

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10786 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10786 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10780) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1533 l18mbPmView10786
    10780 10786 (fun x => fw_view [2048,1] x)
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1534) (l18mb_pm_not_written 1534 10786 (by decide))
    (l18mb_nonempty_pm 1533) (l18mb_pm_not_written 1533 10780 (by decide))
  intro s
  unfold l18mbPmView10786
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 10780 10786

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10804 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10804 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10794) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1534 l18mbPmView10804
    10794 10804 (fun x => fw_view [2048,512] x)
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1535) (l18mb_pm_not_written 1535 10804 (by decide))
    (l18mb_nonempty_pm 1534) (l18mb_pm_not_written 1534 10794 (by decide))
  intro s
  unfold l18mbPmView10804
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10794 10804

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10822 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10822 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10812) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1535 l18mbPmView10822
    10812 10822 (fun x => fw_view [2048,512] x)
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1536) (l18mb_pm_not_written 1536 10822 (by decide))
    (l18mb_nonempty_pm 1535) (l18mb_pm_not_written 1535 10812 (by decide))
  intro s
  unfold l18mbPmView10822
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10812 10822

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_sm5664 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5664 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5663) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 738 l18mbSmSig5664
    5663 5664 fw_sigmoid
    (by native_decide) l18mb_sm_node_facts.2.2.2.2.1 ?_
    (l18mb_nonempty_sm 739) (l18mb_sm_not_written 739 5664 (by decide))
    (l18mb_nonempty_sm 738) (l18mb_sm_not_written 738 5663 (by decide))
  intro s
  unfold l18mbSmSig5664
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5663 5664

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10787 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10787 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10785) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1537 l18mbPmSig10787
    10785 10787 fw_sigmoid
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1538) (l18mb_pm_not_written 1538 10787 (by decide))
    (l18mb_nonempty_pm 1537) (l18mb_pm_not_written 1537 10785 (by decide))
  intro s
  unfold l18mbPmSig10787
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 10785 10787

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10788 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10788 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10786) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1540 l18mbPmSig10788
    10786 10788 fw_sigmoid
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1541) (l18mb_pm_not_written 1541 10788 (by decide))
    (l18mb_nonempty_pm 1540) (l18mb_pm_not_written 1540 10786 (by decide))
  intro s
  unfold l18mbPmSig10788
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 10786 10788

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_sm5673 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5673 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5668)
        (denoteGraphDistributedFaithful sm initSM 5672) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 739 l18mbSmSwi5673
    5668 5672 5673 fw_swiglu
    (by native_decide) l18mb_sm_node_facts.2.2.2.2.2 ?_
    (l18mb_nonempty_sm 740) (l18mb_sm_not_written 740 5673 (by decide))
    (l18mb_nonempty_sm 739) (l18mb_sm_not_written 739 5668 (by decide))
    (l18mb_sm_not_written 739 5672 (by decide))
  intro s
  unfold l18mbSmSwi5673
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5668 5672 5673

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10825 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10825 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10803)
        (denoteGraphDistributedFaithful pm initPM 10821) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1538 l18mbPmSwi10825
    10803 10821 10825 fw_swiglu
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l18mb_nonempty_pm 1539) (l18mb_pm_not_written 1539 10825 (by decide))
    (l18mb_nonempty_pm 1538) (l18mb_pm_not_written 1538 10803 (by decide))
    (l18mb_pm_not_written 1538 10821 (by decide))
  intro s
  unfold l18mbPmSwi10825
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 10803 10821 10825

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_red_pm10826 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10826 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10804)
        (denoteGraphDistributedFaithful pm initPM 10822) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1541 l18mbPmSwi10826
    10804 10822 10826 fw_swiglu
    (by native_decide) l18mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18mb_nonempty_pm 1542) (l18mb_pm_not_written 1542 10826 (by decide))
    (l18mb_nonempty_pm 1541) (l18mb_pm_not_written 1541 10804 (by decide))
    (l18mb_pm_not_written 1541 10822 (by decide))
  intro s
  unfold l18mbPmSwi10826
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 10804 10822 10826

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5639).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5639 = initPM 5639 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5639
      layer1_pm_nodes_nonempty l18mb_cu_not_written
  rw [e2]
  exact hPM 5639 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5639) = [0, 2 * 2048] := by
  have hcuShape := l18mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5639)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hrel
  apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
  have ht := hs.cu_wf.local_tokens
  simp only [List.getD_cons_zero] at ht
  rw [hs.source0_shape] at ht
  norm_num at ht
  norm_num
  exact ht.symm

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5654_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5654)
      (denoteGraphDistributedFaithful pm initPM 10763)
      (denoteGraphDistributedFaithful pm initPM 10764)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5653_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l18mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5653)
      (denoteGraphDistributedFaithful pm initPM 10761)
      (denoteGraphDistributedFaithful pm initPM 10762)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l18mb_red_sm5654 initSM hs.full_shape,
    l18mb_red_pm10763 initPM hs.rank0_shape,
    l18mb_red_pm10764 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5655_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5655)
      (denoteGraphDistributedFaithful pm initPM 10765)
      (denoteGraphDistributedFaithful pm initPM 10766)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5653_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l18mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5653)
      (denoteGraphDistributedFaithful pm initPM 10761)
      (denoteGraphDistributedFaithful pm initPM 10762)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l18mb_red_sm5655 initSM hs.full_shape,
    l18mb_red_pm10765 initPM hs.rank0_shape,
    l18mb_red_pm10766 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5663_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5663)
      (denoteGraphDistributedFaithful pm initPM 10785)
      (denoteGraphDistributedFaithful pm initPM 10786)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5662_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18mb_red_sm5663 initSM, l18mb_red_pm10785 initPM, l18mb_red_pm10786 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5668_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5668)
      (denoteGraphDistributedFaithful pm initPM 10803)
      (denoteGraphDistributedFaithful pm initPM 10804)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5667_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18mb_red_sm5668 initSM, l18mb_red_pm10803 initPM, l18mb_red_pm10804 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5672_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5672)
      (denoteGraphDistributedFaithful pm initPM 10821)
      (denoteGraphDistributedFaithful pm initPM 10822)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5671_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18mb_red_sm5672 initSM, l18mb_red_pm10821 initPM, l18mb_red_pm10822 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5664_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5664)
      (denoteGraphDistributedFaithful pm initPM 10787)
      (denoteGraphDistributedFaithful pm initPM 10788)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5663_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5663)
      (denoteGraphDistributedFaithful pm initPM 10785)
      (denoteGraphDistributedFaithful pm initPM 10786)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l18mb_red_sm5664 initSM, l18mb_red_pm10787 initPM, l18mb_red_pm10788 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5673_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5673)
      (denoteGraphDistributedFaithful pm initPM 10825)
      (denoteGraphDistributedFaithful pm initPM 10826)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5668_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5672_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5668)
      (denoteGraphDistributedFaithful pm initPM 10803)
      (denoteGraphDistributedFaithful pm initPM 10804)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5672)
      (denoteGraphDistributedFaithful pm initPM 10821)
      (denoteGraphDistributedFaithful pm initPM 10822)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l18mb_red_sm5673 initSM, l18mb_red_pm10825 initPM, l18mb_red_pm10826 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
