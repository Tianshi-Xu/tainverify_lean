/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L20FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-8 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-7 段 `L13FaithfulMoEBranch` to block 8.
The block-8 cu tensor is **5737**.

* SM 803 `FW_topk_routing [5751] → [5752, 5753, 5754]` params `[8, 1]`
    (PM 1668 / 1672 → `11107, 11109, 11111` / `11108, 11110, 11112`)
* SM 804 `FW_view [5760] → [5761]` params `[4096, 1]`        (PM 1669 / 1673 → 11129 / 11130)
* SM 805 `FW_view [5765] → [5766]` params `[4096, 512]`      (PM 1670 / 1674 → 11147 / 11148)
* SM 806 `FW_view [5769] → [5770]` params `[4096, 512]`      (PM 1671 / 1675 → 11165 / 11166)
* SM 808 `FW_sigmoid [5761] → [5762]`                        (PM 1677 / 1680 → 11131 / 11132)
* SM 809 `FW_swiglu [5766, 5770] → [5771]`                   (PM 1678 / 1681 → 11169 / 11170)

The third `FW_topk_routing` output (`5754`) has no intermediate goal and is therefore
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

private def l20mbSmTopk5752 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5751], outs := [5752,5753,5754],
    params := [8,1] }
private def l20mbSmView5761 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5760], outs := [5761], params := [4096,1] }
private def l20mbSmView5766 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5765], outs := [5766], params := [4096,512] }
private def l20mbSmView5770 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5769], outs := [5770], params := [4096,512] }
private def l20mbSmSig5762 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5761], outs := [5762] }
private def l20mbSmSwi5771 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5766,5770], outs := [5771] }

private def l20mbPmTopk11107 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [11105], outs := [11107,11109,11111],
    params := [8,1] }
private def l20mbPmView11129 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11123], outs := [11129], params := [2048,1] }
private def l20mbPmView11147 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11137], outs := [11147], params := [2048,512] }
private def l20mbPmView11165 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11155], outs := [11165], params := [2048,512] }
private def l20mbPmTopk11108 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [11106], outs := [11108,11110,11112],
    params := [8,1] }
private def l20mbPmView11130 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11124], outs := [11130], params := [2048,1] }
private def l20mbPmView11148 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11138], outs := [11148], params := [2048,512] }
private def l20mbPmView11166 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11156], outs := [11166], params := [2048,512] }
private def l20mbPmSig11131 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11129], outs := [11131] }
private def l20mbPmSwi11169 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11147,11165], outs := [11169] }
private def l20mbPmSig11132 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11130], outs := [11132] }
private def l20mbPmSwi11170 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11148,11166], outs := [11170] }

/-! ### Certified node indices -/

private theorem l20mb_sm_node_facts :
    sm.nodes[803]'(by native_decide) = l20mbSmTopk5752 ∧
    sm.nodes[804]'(by native_decide) = l20mbSmView5761 ∧
    sm.nodes[805]'(by native_decide) = l20mbSmView5766 ∧
    sm.nodes[806]'(by native_decide) = l20mbSmView5770 ∧
    sm.nodes[808]'(by native_decide) = l20mbSmSig5762 ∧
    sm.nodes[809]'(by native_decide) = l20mbSmSwi5771 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l20mb_pm_node_facts :
    pm.nodes[1668]'(by native_decide) = l20mbPmTopk11107 ∧
    pm.nodes[1669]'(by native_decide) = l20mbPmView11129 ∧
    pm.nodes[1670]'(by native_decide) = l20mbPmView11147 ∧
    pm.nodes[1671]'(by native_decide) = l20mbPmView11165 ∧
    pm.nodes[1672]'(by native_decide) = l20mbPmTopk11108 ∧
    pm.nodes[1673]'(by native_decide) = l20mbPmView11130 ∧
    pm.nodes[1674]'(by native_decide) = l20mbPmView11148 ∧
    pm.nodes[1675]'(by native_decide) = l20mbPmView11166 ∧
    pm.nodes[1677]'(by native_decide) = l20mbPmSig11131 ∧
    pm.nodes[1678]'(by native_decide) = l20mbPmSwi11169 ∧
    pm.nodes[1680]'(by native_decide) = l20mbPmSig11132 ∧
    pm.nodes[1681]'(by native_decide) = l20mbPmSwi11170 := by
  native_decide

private theorem l20mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l20mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l20mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(804, 5752), (804, 5753), (803, 5751), (805, 5761), (804, 5760), (806, 5766), (805, 5765), (807, 5770), (806, 5769), (809, 5762), (808, 5761), (810, 5771), (809, 5766), (809, 5770)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l20mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1669, 11107), (1669, 11109), (1668, 11105), (1673, 11108), (1673, 11110), (1672, 11106), (1670, 11129), (1669, 11123), (1671, 11147), (1670, 11137), (1672, 11165), (1671, 11155), (1674, 11130), (1673, 11124), (1675, 11148), (1674, 11138), (1676, 11166), (1675, 11156), (1678, 11131), (1677, 11129), (1681, 11132), (1680, 11130), (1679, 11169), (1678, 11147), (1678, 11165), (1682, 11170), (1681, 11148), (1681, 11166), (1668, 5737)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l20mb_cu_not_written : ∀ n ∈ pm.nodes, 5737 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_sm5752 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5751).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5752 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5751) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 803 l20mbSmTopk5752
    5751 5752 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l20mb_sm_node_facts.1 ?_
    (l20mb_nonempty_sm 804) (l20mb_sm_not_written 804 5752 (by decide))
    (l20mb_nonempty_sm 803) (l20mb_sm_not_written 803 5751 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l20mbSmTopk5752
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5751 5752 5753 5754 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_sm5753 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5751).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5753 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5751) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 803 l20mbSmTopk5752
    5751 5753 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l20mb_sm_node_facts.1 ?_
    (l20mb_nonempty_sm 804) (l20mb_sm_not_written 804 5753 (by decide))
    (l20mb_nonempty_sm 803) (l20mb_sm_not_written 803 5751 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l20mbSmTopk5752
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5751 5752 5753 5754 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11107 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11105).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11107 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11105) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1668 l20mbPmTopk11107
    11105 11107 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l20mb_pm_node_facts.1 ?_
    (l20mb_nonempty_pm 1669) (l20mb_pm_not_written 1669 11107 (by decide))
    (l20mb_nonempty_pm 1668) (l20mb_pm_not_written 1668 11105 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l20mbPmTopk11107
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 11105 11107 11109 11111 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11109 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11105).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11109 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11105) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1668 l20mbPmTopk11107
    11105 11109 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l20mb_pm_node_facts.1 ?_
    (l20mb_nonempty_pm 1669) (l20mb_pm_not_written 1669 11109 (by decide))
    (l20mb_nonempty_pm 1668) (l20mb_pm_not_written 1668 11105 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l20mbPmTopk11107
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 11105 11107 11109 11111 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11108 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11106).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11108 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11106) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1672 l20mbPmTopk11108
    11106 11108 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1673) (l20mb_pm_not_written 1673 11108 (by decide))
    (l20mb_nonempty_pm 1672) (l20mb_pm_not_written 1672 11106 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l20mbPmTopk11108
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 11106 11108 11110 11112 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11110 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11106).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11110 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11106) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1672 l20mbPmTopk11108
    11106 11110 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1673) (l20mb_pm_not_written 1673 11110 (by decide))
    (l20mb_nonempty_pm 1672) (l20mb_pm_not_written 1672 11106 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l20mbPmTopk11108
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 11106 11108 11110 11112 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_sm5761 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5761 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5760) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 804 l20mbSmView5761
    5760 5761 (fun x => fw_view [4096,1] x)
    (by native_decide) l20mb_sm_node_facts.2.1 ?_
    (l20mb_nonempty_sm 805) (l20mb_sm_not_written 805 5761 (by decide))
    (l20mb_nonempty_sm 804) (l20mb_sm_not_written 804 5760 (by decide))
  intro s
  unfold l20mbSmView5761
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5760 5761

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_sm5766 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5766 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5765) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 805 l20mbSmView5766
    5765 5766 (fun x => fw_view [4096,512] x)
    (by native_decide) l20mb_sm_node_facts.2.2.1 ?_
    (l20mb_nonempty_sm 806) (l20mb_sm_not_written 806 5766 (by decide))
    (l20mb_nonempty_sm 805) (l20mb_sm_not_written 805 5765 (by decide))
  intro s
  unfold l20mbSmView5766
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5765 5766

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_sm5770 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5770 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5769) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 806 l20mbSmView5770
    5769 5770 (fun x => fw_view [4096,512] x)
    (by native_decide) l20mb_sm_node_facts.2.2.2.1 ?_
    (l20mb_nonempty_sm 807) (l20mb_sm_not_written 807 5770 (by decide))
    (l20mb_nonempty_sm 806) (l20mb_sm_not_written 806 5769 (by decide))
  intro s
  unfold l20mbSmView5770
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5769 5770

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11129 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11129 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11123) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1669 l20mbPmView11129
    11123 11129 (fun x => fw_view [2048,1] x)
    (by native_decide) l20mb_pm_node_facts.2.1 ?_
    (l20mb_nonempty_pm 1670) (l20mb_pm_not_written 1670 11129 (by decide))
    (l20mb_nonempty_pm 1669) (l20mb_pm_not_written 1669 11123 (by decide))
  intro s
  unfold l20mbPmView11129
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 11123 11129

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11147 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11147 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11137) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1670 l20mbPmView11147
    11137 11147 (fun x => fw_view [2048,512] x)
    (by native_decide) l20mb_pm_node_facts.2.2.1 ?_
    (l20mb_nonempty_pm 1671) (l20mb_pm_not_written 1671 11147 (by decide))
    (l20mb_nonempty_pm 1670) (l20mb_pm_not_written 1670 11137 (by decide))
  intro s
  unfold l20mbPmView11147
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11137 11147

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11165 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11165 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11155) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1671 l20mbPmView11165
    11155 11165 (fun x => fw_view [2048,512] x)
    (by native_decide) l20mb_pm_node_facts.2.2.2.1 ?_
    (l20mb_nonempty_pm 1672) (l20mb_pm_not_written 1672 11165 (by decide))
    (l20mb_nonempty_pm 1671) (l20mb_pm_not_written 1671 11155 (by decide))
  intro s
  unfold l20mbPmView11165
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11155 11165

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11130 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11130 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11124) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1673 l20mbPmView11130
    11124 11130 (fun x => fw_view [2048,1] x)
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1674) (l20mb_pm_not_written 1674 11130 (by decide))
    (l20mb_nonempty_pm 1673) (l20mb_pm_not_written 1673 11124 (by decide))
  intro s
  unfold l20mbPmView11130
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 11124 11130

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11148 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11148 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11138) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1674 l20mbPmView11148
    11138 11148 (fun x => fw_view [2048,512] x)
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1675) (l20mb_pm_not_written 1675 11148 (by decide))
    (l20mb_nonempty_pm 1674) (l20mb_pm_not_written 1674 11138 (by decide))
  intro s
  unfold l20mbPmView11148
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11138 11148

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11166 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11166 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11156) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1675 l20mbPmView11166
    11156 11166 (fun x => fw_view [2048,512] x)
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1676) (l20mb_pm_not_written 1676 11166 (by decide))
    (l20mb_nonempty_pm 1675) (l20mb_pm_not_written 1675 11156 (by decide))
  intro s
  unfold l20mbPmView11166
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11156 11166

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_sm5762 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5762 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5761) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 808 l20mbSmSig5762
    5761 5762 fw_sigmoid
    (by native_decide) l20mb_sm_node_facts.2.2.2.2.1 ?_
    (l20mb_nonempty_sm 809) (l20mb_sm_not_written 809 5762 (by decide))
    (l20mb_nonempty_sm 808) (l20mb_sm_not_written 808 5761 (by decide))
  intro s
  unfold l20mbSmSig5762
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5761 5762

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11131 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11131 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11129) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1677 l20mbPmSig11131
    11129 11131 fw_sigmoid
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1678) (l20mb_pm_not_written 1678 11131 (by decide))
    (l20mb_nonempty_pm 1677) (l20mb_pm_not_written 1677 11129 (by decide))
  intro s
  unfold l20mbPmSig11131
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 11129 11131

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11132 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11132 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11130) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1680 l20mbPmSig11132
    11130 11132 fw_sigmoid
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1681) (l20mb_pm_not_written 1681 11132 (by decide))
    (l20mb_nonempty_pm 1680) (l20mb_pm_not_written 1680 11130 (by decide))
  intro s
  unfold l20mbPmSig11132
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 11130 11132

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_sm5771 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5771 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5766)
        (denoteGraphDistributedFaithful sm initSM 5770) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 809 l20mbSmSwi5771
    5766 5770 5771 fw_swiglu
    (by native_decide) l20mb_sm_node_facts.2.2.2.2.2 ?_
    (l20mb_nonempty_sm 810) (l20mb_sm_not_written 810 5771 (by decide))
    (l20mb_nonempty_sm 809) (l20mb_sm_not_written 809 5766 (by decide))
    (l20mb_sm_not_written 809 5770 (by decide))
  intro s
  unfold l20mbSmSwi5771
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5766 5770 5771

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11169 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11169 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11147)
        (denoteGraphDistributedFaithful pm initPM 11165) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1678 l20mbPmSwi11169
    11147 11165 11169 fw_swiglu
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l20mb_nonempty_pm 1679) (l20mb_pm_not_written 1679 11169 (by decide))
    (l20mb_nonempty_pm 1678) (l20mb_pm_not_written 1678 11147 (by decide))
    (l20mb_pm_not_written 1678 11165 (by decide))
  intro s
  unfold l20mbPmSwi11169
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 11147 11165 11169

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_red_pm11170 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11170 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11148)
        (denoteGraphDistributedFaithful pm initPM 11166) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1681 l20mbPmSwi11170
    11148 11166 11170 fw_swiglu
    (by native_decide) l20mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20mb_nonempty_pm 1682) (l20mb_pm_not_written 1682 11170 (by decide))
    (l20mb_nonempty_pm 1681) (l20mb_pm_not_written 1681 11148 (by decide))
    (l20mb_pm_not_written 1681 11166 (by decide))
  intro s
  unfold l20mbPmSwi11170
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 11148 11166 11170

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5737).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5737 = initPM 5737 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5737
      layer1_pm_nodes_nonempty l20mb_cu_not_written
  rw [e2]
  exact hPM 5737 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5737) = [0, 2 * 2048] := by
  have hcuShape := l20mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5737)).length = 2 := by
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
theorem recon_zigzagGoal_5752_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5752)
      (denoteGraphDistributedFaithful pm initPM 11107)
      (denoteGraphDistributedFaithful pm initPM 11108)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5751_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l20mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5751)
      (denoteGraphDistributedFaithful pm initPM 11105)
      (denoteGraphDistributedFaithful pm initPM 11106)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l20mb_red_sm5752 initSM hs.full_shape,
    l20mb_red_pm11107 initPM hs.rank0_shape,
    l20mb_red_pm11108 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5753_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5753)
      (denoteGraphDistributedFaithful pm initPM 11109)
      (denoteGraphDistributedFaithful pm initPM 11110)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5751_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l20mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5751)
      (denoteGraphDistributedFaithful pm initPM 11105)
      (denoteGraphDistributedFaithful pm initPM 11106)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l20mb_red_sm5753 initSM hs.full_shape,
    l20mb_red_pm11109 initPM hs.rank0_shape,
    l20mb_red_pm11110 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5761_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5761)
      (denoteGraphDistributedFaithful pm initPM 11129)
      (denoteGraphDistributedFaithful pm initPM 11130)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5760_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20mb_red_sm5761 initSM, l20mb_red_pm11129 initPM, l20mb_red_pm11130 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5766_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5766)
      (denoteGraphDistributedFaithful pm initPM 11147)
      (denoteGraphDistributedFaithful pm initPM 11148)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5765_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20mb_red_sm5766 initSM, l20mb_red_pm11147 initPM, l20mb_red_pm11148 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5770_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5770)
      (denoteGraphDistributedFaithful pm initPM 11165)
      (denoteGraphDistributedFaithful pm initPM 11166)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5769_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20mb_red_sm5770 initSM, l20mb_red_pm11165 initPM, l20mb_red_pm11166 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5762_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5762)
      (denoteGraphDistributedFaithful pm initPM 11131)
      (denoteGraphDistributedFaithful pm initPM 11132)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5761_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5761)
      (denoteGraphDistributedFaithful pm initPM 11129)
      (denoteGraphDistributedFaithful pm initPM 11130)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l20mb_red_sm5762 initSM, l20mb_red_pm11131 initPM, l20mb_red_pm11132 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5771_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5771)
      (denoteGraphDistributedFaithful pm initPM 11169)
      (denoteGraphDistributedFaithful pm initPM 11170)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5766_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5770_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5766)
      (denoteGraphDistributedFaithful pm initPM 11147)
      (denoteGraphDistributedFaithful pm initPM 11148)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5770)
      (denoteGraphDistributedFaithful pm initPM 11165)
      (denoteGraphDistributedFaithful pm initPM 11166)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l20mb_red_sm5771 initSM, l20mb_red_pm11169 initPM, l20mb_red_pm11170 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
