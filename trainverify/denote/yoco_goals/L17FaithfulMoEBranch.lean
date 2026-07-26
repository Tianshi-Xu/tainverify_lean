/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L17FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-5 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-4 段 `L13FaithfulMoEBranch` to block 5.
The block-5 cu tensor is **5590**.

* SM 698 `FW_topk_routing [5604] → [5605, 5606, 5607]` params `[8, 1]`
    (PM 1458 / 1462 → `10591, 10593, 10595` / `10592, 10594, 10596`)
* SM 699 `FW_view [5613] → [5614]` params `[4096, 1]`        (PM 1459 / 1463 → 10613 / 10614)
* SM 700 `FW_view [5618] → [5619]` params `[4096, 512]`      (PM 1460 / 1464 → 10631 / 10632)
* SM 701 `FW_view [5622] → [5623]` params `[4096, 512]`      (PM 1461 / 1465 → 10649 / 10650)
* SM 703 `FW_sigmoid [5614] → [5615]`                        (PM 1467 / 1470 → 10615 / 10616)
* SM 704 `FW_swiglu [5619, 5623] → [5624]`                   (PM 1468 / 1471 → 10653 / 10654)

The third `FW_topk_routing` output (`5607`) has no intermediate goal and is therefore
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

private def l17mbSmTopk5605 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5604], outs := [5605,5606,5607],
    params := [8,1] }
private def l17mbSmView5614 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5613], outs := [5614], params := [4096,1] }
private def l17mbSmView5619 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5618], outs := [5619], params := [4096,512] }
private def l17mbSmView5623 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5622], outs := [5623], params := [4096,512] }
private def l17mbSmSig5615 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5614], outs := [5615] }
private def l17mbSmSwi5624 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5619,5623], outs := [5624] }

private def l17mbPmTopk10591 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10589], outs := [10591,10593,10595],
    params := [8,1] }
private def l17mbPmView10613 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10607], outs := [10613], params := [2048,1] }
private def l17mbPmView10631 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10621], outs := [10631], params := [2048,512] }
private def l17mbPmView10649 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10639], outs := [10649], params := [2048,512] }
private def l17mbPmTopk10592 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10590], outs := [10592,10594,10596],
    params := [8,1] }
private def l17mbPmView10614 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10608], outs := [10614], params := [2048,1] }
private def l17mbPmView10632 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10622], outs := [10632], params := [2048,512] }
private def l17mbPmView10650 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10640], outs := [10650], params := [2048,512] }
private def l17mbPmSig10615 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10613], outs := [10615] }
private def l17mbPmSwi10653 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10631,10649], outs := [10653] }
private def l17mbPmSig10616 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10614], outs := [10616] }
private def l17mbPmSwi10654 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10632,10650], outs := [10654] }

/-! ### Certified node indices -/

private theorem l17mb_sm_node_facts :
    sm.nodes[698]'(by native_decide) = l17mbSmTopk5605 ∧
    sm.nodes[699]'(by native_decide) = l17mbSmView5614 ∧
    sm.nodes[700]'(by native_decide) = l17mbSmView5619 ∧
    sm.nodes[701]'(by native_decide) = l17mbSmView5623 ∧
    sm.nodes[703]'(by native_decide) = l17mbSmSig5615 ∧
    sm.nodes[704]'(by native_decide) = l17mbSmSwi5624 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l17mb_pm_node_facts :
    pm.nodes[1458]'(by native_decide) = l17mbPmTopk10591 ∧
    pm.nodes[1459]'(by native_decide) = l17mbPmView10613 ∧
    pm.nodes[1460]'(by native_decide) = l17mbPmView10631 ∧
    pm.nodes[1461]'(by native_decide) = l17mbPmView10649 ∧
    pm.nodes[1462]'(by native_decide) = l17mbPmTopk10592 ∧
    pm.nodes[1463]'(by native_decide) = l17mbPmView10614 ∧
    pm.nodes[1464]'(by native_decide) = l17mbPmView10632 ∧
    pm.nodes[1465]'(by native_decide) = l17mbPmView10650 ∧
    pm.nodes[1467]'(by native_decide) = l17mbPmSig10615 ∧
    pm.nodes[1468]'(by native_decide) = l17mbPmSwi10653 ∧
    pm.nodes[1470]'(by native_decide) = l17mbPmSig10616 ∧
    pm.nodes[1471]'(by native_decide) = l17mbPmSwi10654 := by
  native_decide

private theorem l17mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l17mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l17mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(699, 5605), (699, 5606), (698, 5604), (700, 5614), (699, 5613), (701, 5619), (700, 5618), (702, 5623), (701, 5622), (704, 5615), (703, 5614), (705, 5624), (704, 5619), (704, 5623)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l17mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1459, 10591), (1459, 10593), (1458, 10589), (1463, 10592), (1463, 10594), (1462, 10590), (1460, 10613), (1459, 10607), (1461, 10631), (1460, 10621), (1462, 10649), (1461, 10639), (1464, 10614), (1463, 10608), (1465, 10632), (1464, 10622), (1466, 10650), (1465, 10640), (1468, 10615), (1467, 10613), (1471, 10616), (1470, 10614), (1469, 10653), (1468, 10631), (1468, 10649), (1472, 10654), (1471, 10632), (1471, 10650), (1458, 5590)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l17mb_cu_not_written : ∀ n ∈ pm.nodes, 5590 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_sm5605 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5604).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5605 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5604) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 698 l17mbSmTopk5605
    5604 5605 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l17mb_sm_node_facts.1 ?_
    (l17mb_nonempty_sm 699) (l17mb_sm_not_written 699 5605 (by decide))
    (l17mb_nonempty_sm 698) (l17mb_sm_not_written 698 5604 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l17mbSmTopk5605
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5604 5605 5606 5607 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_sm5606 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5604).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5606 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5604) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 698 l17mbSmTopk5605
    5604 5606 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l17mb_sm_node_facts.1 ?_
    (l17mb_nonempty_sm 699) (l17mb_sm_not_written 699 5606 (by decide))
    (l17mb_nonempty_sm 698) (l17mb_sm_not_written 698 5604 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l17mbSmTopk5605
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5604 5605 5606 5607 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10591 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10589).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10591 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10589) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1458 l17mbPmTopk10591
    10589 10591 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l17mb_pm_node_facts.1 ?_
    (l17mb_nonempty_pm 1459) (l17mb_pm_not_written 1459 10591 (by decide))
    (l17mb_nonempty_pm 1458) (l17mb_pm_not_written 1458 10589 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l17mbPmTopk10591
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 10589 10591 10593 10595 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10593 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10589).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10593 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10589) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1458 l17mbPmTopk10591
    10589 10593 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l17mb_pm_node_facts.1 ?_
    (l17mb_nonempty_pm 1459) (l17mb_pm_not_written 1459 10593 (by decide))
    (l17mb_nonempty_pm 1458) (l17mb_pm_not_written 1458 10589 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l17mbPmTopk10591
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 10589 10591 10593 10595 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10592 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10590).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10592 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10590) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1462 l17mbPmTopk10592
    10590 10592 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1463) (l17mb_pm_not_written 1463 10592 (by decide))
    (l17mb_nonempty_pm 1462) (l17mb_pm_not_written 1462 10590 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l17mbPmTopk10592
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 10590 10592 10594 10596 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10594 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10590).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10594 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10590) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1462 l17mbPmTopk10592
    10590 10594 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1463) (l17mb_pm_not_written 1463 10594 (by decide))
    (l17mb_nonempty_pm 1462) (l17mb_pm_not_written 1462 10590 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l17mbPmTopk10592
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 10590 10592 10594 10596 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_sm5614 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5614 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5613) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 699 l17mbSmView5614
    5613 5614 (fun x => fw_view [4096,1] x)
    (by native_decide) l17mb_sm_node_facts.2.1 ?_
    (l17mb_nonempty_sm 700) (l17mb_sm_not_written 700 5614 (by decide))
    (l17mb_nonempty_sm 699) (l17mb_sm_not_written 699 5613 (by decide))
  intro s
  unfold l17mbSmView5614
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5613 5614

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_sm5619 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5619 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5618) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 700 l17mbSmView5619
    5618 5619 (fun x => fw_view [4096,512] x)
    (by native_decide) l17mb_sm_node_facts.2.2.1 ?_
    (l17mb_nonempty_sm 701) (l17mb_sm_not_written 701 5619 (by decide))
    (l17mb_nonempty_sm 700) (l17mb_sm_not_written 700 5618 (by decide))
  intro s
  unfold l17mbSmView5619
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5618 5619

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_sm5623 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5623 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5622) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 701 l17mbSmView5623
    5622 5623 (fun x => fw_view [4096,512] x)
    (by native_decide) l17mb_sm_node_facts.2.2.2.1 ?_
    (l17mb_nonempty_sm 702) (l17mb_sm_not_written 702 5623 (by decide))
    (l17mb_nonempty_sm 701) (l17mb_sm_not_written 701 5622 (by decide))
  intro s
  unfold l17mbSmView5623
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5622 5623

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10613 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10613 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10607) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1459 l17mbPmView10613
    10607 10613 (fun x => fw_view [2048,1] x)
    (by native_decide) l17mb_pm_node_facts.2.1 ?_
    (l17mb_nonempty_pm 1460) (l17mb_pm_not_written 1460 10613 (by decide))
    (l17mb_nonempty_pm 1459) (l17mb_pm_not_written 1459 10607 (by decide))
  intro s
  unfold l17mbPmView10613
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 10607 10613

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10631 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10631 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10621) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1460 l17mbPmView10631
    10621 10631 (fun x => fw_view [2048,512] x)
    (by native_decide) l17mb_pm_node_facts.2.2.1 ?_
    (l17mb_nonempty_pm 1461) (l17mb_pm_not_written 1461 10631 (by decide))
    (l17mb_nonempty_pm 1460) (l17mb_pm_not_written 1460 10621 (by decide))
  intro s
  unfold l17mbPmView10631
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10621 10631

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10649 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10649 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10639) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1461 l17mbPmView10649
    10639 10649 (fun x => fw_view [2048,512] x)
    (by native_decide) l17mb_pm_node_facts.2.2.2.1 ?_
    (l17mb_nonempty_pm 1462) (l17mb_pm_not_written 1462 10649 (by decide))
    (l17mb_nonempty_pm 1461) (l17mb_pm_not_written 1461 10639 (by decide))
  intro s
  unfold l17mbPmView10649
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10639 10649

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10614 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10614 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10608) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1463 l17mbPmView10614
    10608 10614 (fun x => fw_view [2048,1] x)
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1464) (l17mb_pm_not_written 1464 10614 (by decide))
    (l17mb_nonempty_pm 1463) (l17mb_pm_not_written 1463 10608 (by decide))
  intro s
  unfold l17mbPmView10614
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 10608 10614

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10632 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10632 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10622) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1464 l17mbPmView10632
    10622 10632 (fun x => fw_view [2048,512] x)
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1465) (l17mb_pm_not_written 1465 10632 (by decide))
    (l17mb_nonempty_pm 1464) (l17mb_pm_not_written 1464 10622 (by decide))
  intro s
  unfold l17mbPmView10632
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10622 10632

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10650 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10650 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10640) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1465 l17mbPmView10650
    10640 10650 (fun x => fw_view [2048,512] x)
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1466) (l17mb_pm_not_written 1466 10650 (by decide))
    (l17mb_nonempty_pm 1465) (l17mb_pm_not_written 1465 10640 (by decide))
  intro s
  unfold l17mbPmView10650
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10640 10650

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_sm5615 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5615 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5614) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 703 l17mbSmSig5615
    5614 5615 fw_sigmoid
    (by native_decide) l17mb_sm_node_facts.2.2.2.2.1 ?_
    (l17mb_nonempty_sm 704) (l17mb_sm_not_written 704 5615 (by decide))
    (l17mb_nonempty_sm 703) (l17mb_sm_not_written 703 5614 (by decide))
  intro s
  unfold l17mbSmSig5615
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5614 5615

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10615 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10615 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10613) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1467 l17mbPmSig10615
    10613 10615 fw_sigmoid
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1468) (l17mb_pm_not_written 1468 10615 (by decide))
    (l17mb_nonempty_pm 1467) (l17mb_pm_not_written 1467 10613 (by decide))
  intro s
  unfold l17mbPmSig10615
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 10613 10615

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10616 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10616 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10614) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1470 l17mbPmSig10616
    10614 10616 fw_sigmoid
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1471) (l17mb_pm_not_written 1471 10616 (by decide))
    (l17mb_nonempty_pm 1470) (l17mb_pm_not_written 1470 10614 (by decide))
  intro s
  unfold l17mbPmSig10616
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 10614 10616

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_sm5624 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5624 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5619)
        (denoteGraphDistributedFaithful sm initSM 5623) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 704 l17mbSmSwi5624
    5619 5623 5624 fw_swiglu
    (by native_decide) l17mb_sm_node_facts.2.2.2.2.2 ?_
    (l17mb_nonempty_sm 705) (l17mb_sm_not_written 705 5624 (by decide))
    (l17mb_nonempty_sm 704) (l17mb_sm_not_written 704 5619 (by decide))
    (l17mb_sm_not_written 704 5623 (by decide))
  intro s
  unfold l17mbSmSwi5624
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5619 5623 5624

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10653 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10653 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10631)
        (denoteGraphDistributedFaithful pm initPM 10649) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1468 l17mbPmSwi10653
    10631 10649 10653 fw_swiglu
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l17mb_nonempty_pm 1469) (l17mb_pm_not_written 1469 10653 (by decide))
    (l17mb_nonempty_pm 1468) (l17mb_pm_not_written 1468 10631 (by decide))
    (l17mb_pm_not_written 1468 10649 (by decide))
  intro s
  unfold l17mbPmSwi10653
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 10631 10649 10653

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_red_pm10654 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10654 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10632)
        (denoteGraphDistributedFaithful pm initPM 10650) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1471 l17mbPmSwi10654
    10632 10650 10654 fw_swiglu
    (by native_decide) l17mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17mb_nonempty_pm 1472) (l17mb_pm_not_written 1472 10654 (by decide))
    (l17mb_nonempty_pm 1471) (l17mb_pm_not_written 1471 10632 (by decide))
    (l17mb_pm_not_written 1471 10650 (by decide))
  intro s
  unfold l17mbPmSwi10654
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 10632 10650 10654

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5590).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5590 = initPM 5590 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5590
      layer1_pm_nodes_nonempty l17mb_cu_not_written
  rw [e2]
  exact hPM 5590 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5590) = [0, 2 * 2048] := by
  have hcuShape := l17mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5590)).length = 2 := by
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
theorem recon_zigzagGoal_5605_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5605)
      (denoteGraphDistributedFaithful pm initPM 10591)
      (denoteGraphDistributedFaithful pm initPM 10592)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5604_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l17mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5604)
      (denoteGraphDistributedFaithful pm initPM 10589)
      (denoteGraphDistributedFaithful pm initPM 10590)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l17mb_red_sm5605 initSM hs.full_shape,
    l17mb_red_pm10591 initPM hs.rank0_shape,
    l17mb_red_pm10592 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5606_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5606)
      (denoteGraphDistributedFaithful pm initPM 10593)
      (denoteGraphDistributedFaithful pm initPM 10594)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5604_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l17mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5604)
      (denoteGraphDistributedFaithful pm initPM 10589)
      (denoteGraphDistributedFaithful pm initPM 10590)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l17mb_red_sm5606 initSM hs.full_shape,
    l17mb_red_pm10593 initPM hs.rank0_shape,
    l17mb_red_pm10594 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5614_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5614)
      (denoteGraphDistributedFaithful pm initPM 10613)
      (denoteGraphDistributedFaithful pm initPM 10614)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5613_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17mb_red_sm5614 initSM, l17mb_red_pm10613 initPM, l17mb_red_pm10614 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5619_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5619)
      (denoteGraphDistributedFaithful pm initPM 10631)
      (denoteGraphDistributedFaithful pm initPM 10632)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5618_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17mb_red_sm5619 initSM, l17mb_red_pm10631 initPM, l17mb_red_pm10632 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5623_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5623)
      (denoteGraphDistributedFaithful pm initPM 10649)
      (denoteGraphDistributedFaithful pm initPM 10650)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5622_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17mb_red_sm5623 initSM, l17mb_red_pm10649 initPM, l17mb_red_pm10650 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5615_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5615)
      (denoteGraphDistributedFaithful pm initPM 10615)
      (denoteGraphDistributedFaithful pm initPM 10616)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5614_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5614)
      (denoteGraphDistributedFaithful pm initPM 10613)
      (denoteGraphDistributedFaithful pm initPM 10614)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l17mb_red_sm5615 initSM, l17mb_red_pm10615 initPM, l17mb_red_pm10616 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5624_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5624)
      (denoteGraphDistributedFaithful pm initPM 10653)
      (denoteGraphDistributedFaithful pm initPM 10654)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5619_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5623_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5619)
      (denoteGraphDistributedFaithful pm initPM 10631)
      (denoteGraphDistributedFaithful pm initPM 10632)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5623)
      (denoteGraphDistributedFaithful pm initPM 10649)
      (denoteGraphDistributedFaithful pm initPM 10650)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l17mb_red_sm5624 initSM, l17mb_red_pm10653 initPM, l17mb_red_pm10654 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
