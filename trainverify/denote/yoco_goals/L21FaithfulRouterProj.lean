/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L21FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-9 MoE branch (router projections)

Mechanical transport of the (green) block-8 段 `L13FaithfulRouterProj` to block 9.
Every tensor id / node index is re-certified by `native_decide`.
The block-9 cu tensor is **5786**.

* SM 830 `FW_float [8509] → [5798]`                          (PM 1722 / 1726 → 11271 / 11272)
* SM 831 `FW_reshape [8517] → [5807]`                        (PM 1723 / 1727 → 11291 / 11292)
* SM 832 `FW_reshape [8521] → [5812]`                        (PM 1724 / 1728 → 11305 / 11306)
* SM 833 `FW_reshape [8525] → [5816]`                        (PM 1725 / 1729 → 11323 / 11324)
* SM 834 `FW_norm_linear [5798, 5799] → [5800]`              (PM 1730 / 1734 → 11277 / 11278)
* SM 835 `FW_mix_precision_linear [5807, 5808] → [5809]`     (PM 1731 / 1735 → 11295 / 11296)
* SM 836 `FW_mix_precision_linear [5812, 5813] → [5814]`     (PM 1732 / 1736 → 11309 / 11310)
* SM 837 `FW_mix_precision_linear [5816, 5817] → [5818]`     (PM 1733 / 1737 → 11327 / 11328)

Weights 5799 `[64,1024]`, 5808 `[1,1024]`, 5813 `[512,1024]`, 5817 `[512,1024]` are
replicated singletons.

The `hdec : decodeCuSeqlens cu = [0, 2 * 2048]` side condition of the router lemma is
**derived** from the ambient zigzag well-formedness carried by the parent relation.
No new hypotheses are introduced.
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

private def l21rpSmFloat5798 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8509], outs := [5798] }
private def l21rpSmResh5807 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8517], outs := [5807],
    params := [4096,1024] }
private def l21rpSmResh5812 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8521], outs := [5812],
    params := [4096,1024] }
private def l21rpSmResh5816 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8525], outs := [5816],
    params := [4096,1024] }
private def l21rpSmNL5800 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5798,5799], outs := [5800] }
private def l21rpSmMPL5809 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5807,5808], outs := [5809] }
private def l21rpSmMPL5814 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5812,5813], outs := [5814] }
private def l21rpSmMPL5818 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5816,5817], outs := [5818] }

private def l21rpPmFloat11271 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16706], outs := [11271] }
private def l21rpPmResh11291 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16714], outs := [11291],
    params := [2048,1024] }
private def l21rpPmResh11305 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16718], outs := [11305],
    params := [2048,1024] }
private def l21rpPmResh11323 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16722], outs := [11323],
    params := [2048,1024] }
private def l21rpPmFloat11272 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16729], outs := [11272] }
private def l21rpPmResh11292 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16737], outs := [11292],
    params := [2048,1024] }
private def l21rpPmResh11306 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16741], outs := [11306],
    params := [2048,1024] }
private def l21rpPmResh11324 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16745], outs := [11324],
    params := [2048,1024] }
private def l21rpPmNL11277 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [11271,5799], outs := [11277] }
private def l21rpPmMPL11295 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11291,5808], outs := [11295] }
private def l21rpPmMPL11309 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11305,5813], outs := [11309] }
private def l21rpPmMPL11327 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11323,5817], outs := [11327] }
private def l21rpPmNL11278 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [11272,5799], outs := [11278] }
private def l21rpPmMPL11296 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11292,5808], outs := [11296] }
private def l21rpPmMPL11310 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11306,5813], outs := [11310] }
private def l21rpPmMPL11328 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11324,5817], outs := [11328] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l21rp_sm_node_facts :
    sm.nodes[830]'(by native_decide) = l21rpSmFloat5798 ∧
    sm.nodes[831]'(by native_decide) = l21rpSmResh5807 ∧
    sm.nodes[832]'(by native_decide) = l21rpSmResh5812 ∧
    sm.nodes[833]'(by native_decide) = l21rpSmResh5816 ∧
    sm.nodes[834]'(by native_decide) = l21rpSmNL5800 ∧
    sm.nodes[835]'(by native_decide) = l21rpSmMPL5809 ∧
    sm.nodes[836]'(by native_decide) = l21rpSmMPL5814 ∧
    sm.nodes[837]'(by native_decide) = l21rpSmMPL5818 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l21rp_pm_node_facts :
    pm.nodes[1722]'(by native_decide) = l21rpPmFloat11271 ∧
    pm.nodes[1723]'(by native_decide) = l21rpPmResh11291 ∧
    pm.nodes[1724]'(by native_decide) = l21rpPmResh11305 ∧
    pm.nodes[1725]'(by native_decide) = l21rpPmResh11323 ∧
    pm.nodes[1726]'(by native_decide) = l21rpPmFloat11272 ∧
    pm.nodes[1727]'(by native_decide) = l21rpPmResh11292 ∧
    pm.nodes[1728]'(by native_decide) = l21rpPmResh11306 ∧
    pm.nodes[1729]'(by native_decide) = l21rpPmResh11324 ∧
    pm.nodes[1730]'(by native_decide) = l21rpPmNL11277 ∧
    pm.nodes[1731]'(by native_decide) = l21rpPmMPL11295 ∧
    pm.nodes[1732]'(by native_decide) = l21rpPmMPL11309 ∧
    pm.nodes[1733]'(by native_decide) = l21rpPmMPL11327 ∧
    pm.nodes[1734]'(by native_decide) = l21rpPmNL11278 ∧
    pm.nodes[1735]'(by native_decide) = l21rpPmMPL11296 ∧
    pm.nodes[1736]'(by native_decide) = l21rpPmMPL11310 ∧
    pm.nodes[1737]'(by native_decide) = l21rpPmMPL11328 := by
  native_decide

private theorem l21rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l21rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l21rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5799 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5808 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5813 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5817 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5799 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5808 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5813 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5817 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5786 ∉ n.outs)) := by
  native_decide

private theorem l21rp_w5799_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5799 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l21rp_w5799_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5799 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l21rp_w5808_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5808 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l21rp_w5808_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5808 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l21rp_w5813_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5813 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l21rp_w5813_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5813 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l21rp_w5817_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5817 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l21rp_w5817_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5817 ∉ n.outs := by
  intro n hn
  exact l21rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l21rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(831, 5798), (830, 8509), (832, 5807), (831, 8517), (833, 5812), (832, 8521), (834, 5816), (833, 8525), (835, 5800), (834, 5798), (836, 5809), (835, 5807), (837, 5814), (836, 5812), (838, 5818), (837, 5816)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l21rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1723, 11271), (1722, 16706), (1724, 11291), (1723, 16714), (1725, 11305), (1724, 16718), (1726, 11323), (1725, 16722), (1727, 11272), (1726, 16729), (1728, 11292), (1727, 16737), (1729, 11306), (1728, 16741), (1730, 11324), (1729, 16745), (1731, 11277), (1730, 11271), (1732, 11295), (1731, 11291), (1733, 11309), (1732, 11305), (1734, 11327), (1733, 11323), (1735, 11278), (1734, 11272), (1736, 11296), (1735, 11292), (1737, 11310), (1736, 11306), (1738, 11328), (1737, 11324)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5798 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5798 =
      denoteGraphDistributedFaithful sm initSM 8509 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 830 l21rpSmFloat5798
    8509 5798 (fun x => x)
    (by native_decide) l21rp_sm_node_facts.1 ?_
    (l21rp_nonempty_sm 831) (l21rp_sm_not_written 831 5798 (by decide))
    (l21rp_nonempty_sm 830) (l21rp_sm_not_written 830 8509 (by decide))
  intro s
  unfold l21rpSmFloat5798
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8509 5798 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5807 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5807 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8517) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 831 l21rpSmResh5807
    8517 5807 (fun x => fw_view [4096,1024] x)
    (by native_decide) l21rp_sm_node_facts.2.1 ?_
    (l21rp_nonempty_sm 832) (l21rp_sm_not_written 832 5807 (by decide))
    (l21rp_nonempty_sm 831) (l21rp_sm_not_written 831 8517 (by decide))
  intro s
  unfold l21rpSmResh5807
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8517 5807 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5812 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5812 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8521) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 832 l21rpSmResh5812
    8521 5812 (fun x => fw_view [4096,1024] x)
    (by native_decide) l21rp_sm_node_facts.2.2.1 ?_
    (l21rp_nonempty_sm 833) (l21rp_sm_not_written 833 5812 (by decide))
    (l21rp_nonempty_sm 832) (l21rp_sm_not_written 832 8521 (by decide))
  intro s
  unfold l21rpSmResh5812
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8521 5812 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5816 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5816 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8525) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 833 l21rpSmResh5816
    8525 5816 (fun x => fw_view [4096,1024] x)
    (by native_decide) l21rp_sm_node_facts.2.2.2.1 ?_
    (l21rp_nonempty_sm 834) (l21rp_sm_not_written 834 5816 (by decide))
    (l21rp_nonempty_sm 833) (l21rp_sm_not_written 833 8525 (by decide))
  intro s
  unfold l21rpSmResh5816
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8525 5816 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5800 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5800 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5798)
        (denoteGraphDistributedFaithful sm initSM 5799) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 834 l21rpSmNL5800
    5798 5799 5800 fw_norm_linear
    (by native_decide) l21rp_sm_node_facts.2.2.2.2.1 ?_
    (l21rp_nonempty_sm 835) (l21rp_sm_not_written 835 5800 (by decide))
    (l21rp_nonempty_sm 834) (l21rp_sm_not_written 834 5798 (by decide))
    (l21rp_w5799_sm_drop 834)
  intro s
  unfold l21rpSmNL5800
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5798 5799 5800

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5809 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5809 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5807)
        (denoteGraphDistributedFaithful sm initSM 5808) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 835 l21rpSmMPL5809
    5807 5808 5809 fw_linear
    (by native_decide) l21rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l21rp_nonempty_sm 836) (l21rp_sm_not_written 836 5809 (by decide))
    (l21rp_nonempty_sm 835) (l21rp_sm_not_written 835 5807 (by decide))
    (l21rp_w5808_sm_drop 835)
  intro s
  unfold l21rpSmMPL5809
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5807 5808 5809

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5814 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5814 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5812)
        (denoteGraphDistributedFaithful sm initSM 5813) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 836 l21rpSmMPL5814
    5812 5813 5814 fw_linear
    (by native_decide) l21rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_sm 837) (l21rp_sm_not_written 837 5814 (by decide))
    (l21rp_nonempty_sm 836) (l21rp_sm_not_written 836 5812 (by decide))
    (l21rp_w5813_sm_drop 836)
  intro s
  unfold l21rpSmMPL5814
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5812 5813 5814

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_sm5818 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5818 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5816)
        (denoteGraphDistributedFaithful sm initSM 5817) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 837 l21rpSmMPL5818
    5816 5817 5818 fw_linear
    (by native_decide) l21rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l21rp_nonempty_sm 838) (l21rp_sm_not_written 838 5818 (by decide))
    (l21rp_nonempty_sm 837) (l21rp_sm_not_written 837 5816 (by decide))
    (l21rp_w5817_sm_drop 837)
  intro s
  unfold l21rpSmMPL5818
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5816 5817 5818

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11271 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11271 =
      denoteGraphDistributedFaithful pm initPM 16706 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1722 l21rpPmFloat11271
    16706 11271 (fun x => x)
    (by native_decide) l21rp_pm_node_facts.1 ?_
    (l21rp_nonempty_pm 1723) (l21rp_pm_not_written 1723 11271 (by decide))
    (l21rp_nonempty_pm 1722) (l21rp_pm_not_written 1722 16706 (by decide))
  intro s
  unfold l21rpPmFloat11271
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16706 11271 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11291 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11291 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16714) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1723 l21rpPmResh11291
    16714 11291 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21rp_pm_node_facts.2.1 ?_
    (l21rp_nonempty_pm 1724) (l21rp_pm_not_written 1724 11291 (by decide))
    (l21rp_nonempty_pm 1723) (l21rp_pm_not_written 1723 16714 (by decide))
  intro s
  unfold l21rpPmResh11291
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16714 11291 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11305 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11305 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16718) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1724 l21rpPmResh11305
    16718 11305 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21rp_pm_node_facts.2.2.1 ?_
    (l21rp_nonempty_pm 1725) (l21rp_pm_not_written 1725 11305 (by decide))
    (l21rp_nonempty_pm 1724) (l21rp_pm_not_written 1724 16718 (by decide))
  intro s
  unfold l21rpPmResh11305
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16718 11305 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11323 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11323 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16722) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1725 l21rpPmResh11323
    16722 11323 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21rp_pm_node_facts.2.2.2.1 ?_
    (l21rp_nonempty_pm 1726) (l21rp_pm_not_written 1726 11323 (by decide))
    (l21rp_nonempty_pm 1725) (l21rp_pm_not_written 1725 16722 (by decide))
  intro s
  unfold l21rpPmResh11323
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16722 11323 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11272 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11272 =
      denoteGraphDistributedFaithful pm initPM 16729 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1726 l21rpPmFloat11272
    16729 11272 (fun x => x)
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1727) (l21rp_pm_not_written 1727 11272 (by decide))
    (l21rp_nonempty_pm 1726) (l21rp_pm_not_written 1726 16729 (by decide))
  intro s
  unfold l21rpPmFloat11272
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16729 11272 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11292 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11292 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16737) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1727 l21rpPmResh11292
    16737 11292 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1728) (l21rp_pm_not_written 1728 11292 (by decide))
    (l21rp_nonempty_pm 1727) (l21rp_pm_not_written 1727 16737 (by decide))
  intro s
  unfold l21rpPmResh11292
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16737 11292 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11306 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11306 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16741) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1728 l21rpPmResh11306
    16741 11306 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1729) (l21rp_pm_not_written 1729 11306 (by decide))
    (l21rp_nonempty_pm 1728) (l21rp_pm_not_written 1728 16741 (by decide))
  intro s
  unfold l21rpPmResh11306
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16741 11306 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11324 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11324 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16745) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1729 l21rpPmResh11324
    16745 11324 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1730) (l21rp_pm_not_written 1730 11324 (by decide))
    (l21rp_nonempty_pm 1729) (l21rp_pm_not_written 1729 16745 (by decide))
  intro s
  unfold l21rpPmResh11324
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16745 11324 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11277 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11277 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11271)
        (denoteGraphDistributedFaithful pm initPM 5799) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1730 l21rpPmNL11277
    11271 5799 11277 fw_norm_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1731) (l21rp_pm_not_written 1731 11277 (by decide))
    (l21rp_nonempty_pm 1730) (l21rp_pm_not_written 1730 11271 (by decide))
    (l21rp_w5799_pm_drop 1730)
  intro s
  unfold l21rpPmNL11277
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 11271 5799 11277

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11295 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11295 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11291)
        (denoteGraphDistributedFaithful pm initPM 5808) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1731 l21rpPmMPL11295
    11291 5808 11295 fw_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1732) (l21rp_pm_not_written 1732 11295 (by decide))
    (l21rp_nonempty_pm 1731) (l21rp_pm_not_written 1731 11291 (by decide))
    (l21rp_w5808_pm_drop 1731)
  intro s
  unfold l21rpPmMPL11295
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11291 5808 11295

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11309 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11309 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11305)
        (denoteGraphDistributedFaithful pm initPM 5813) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1732 l21rpPmMPL11309
    11305 5813 11309 fw_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1733) (l21rp_pm_not_written 1733 11309 (by decide))
    (l21rp_nonempty_pm 1732) (l21rp_pm_not_written 1732 11305 (by decide))
    (l21rp_w5813_pm_drop 1732)
  intro s
  unfold l21rpPmMPL11309
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11305 5813 11309

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11327 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11327 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11323)
        (denoteGraphDistributedFaithful pm initPM 5817) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1733 l21rpPmMPL11327
    11323 5817 11327 fw_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1734) (l21rp_pm_not_written 1734 11327 (by decide))
    (l21rp_nonempty_pm 1733) (l21rp_pm_not_written 1733 11323 (by decide))
    (l21rp_w5817_pm_drop 1733)
  intro s
  unfold l21rpPmMPL11327
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11323 5817 11327

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11278 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11278 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11272)
        (denoteGraphDistributedFaithful pm initPM 5799) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1734 l21rpPmNL11278
    11272 5799 11278 fw_norm_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1735) (l21rp_pm_not_written 1735 11278 (by decide))
    (l21rp_nonempty_pm 1734) (l21rp_pm_not_written 1734 11272 (by decide))
    (l21rp_w5799_pm_drop 1734)
  intro s
  unfold l21rpPmNL11278
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 11272 5799 11278

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11296 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11296 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11292)
        (denoteGraphDistributedFaithful pm initPM 5808) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1735 l21rpPmMPL11296
    11292 5808 11296 fw_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1736) (l21rp_pm_not_written 1736 11296 (by decide))
    (l21rp_nonempty_pm 1735) (l21rp_pm_not_written 1735 11292 (by decide))
    (l21rp_w5808_pm_drop 1735)
  intro s
  unfold l21rpPmMPL11296
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11292 5808 11296

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11310 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11310 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11306)
        (denoteGraphDistributedFaithful pm initPM 5813) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1736 l21rpPmMPL11310
    11306 5813 11310 fw_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21rp_nonempty_pm 1737) (l21rp_pm_not_written 1737 11310 (by decide))
    (l21rp_nonempty_pm 1736) (l21rp_pm_not_written 1736 11306 (by decide))
    (l21rp_w5813_pm_drop 1736)
  intro s
  unfold l21rpPmMPL11310
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11306 5813 11310

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_red_pm11328 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11328 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11324)
        (denoteGraphDistributedFaithful pm initPM 5817) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1737 l21rpPmMPL11328
    11324 5817 11328 fw_linear
    (by native_decide) l21rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21rp_nonempty_pm 1738) (l21rp_pm_not_written 1738 11328 (by decide))
    (l21rp_nonempty_pm 1737) (l21rp_pm_not_written 1737 11324 (by decide))
    (l21rp_w5817_pm_drop 1737)
  intro s
  unfold l21rpPmMPL11328
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11324 5817 11328

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (W : Tid) (g : LineageGoal) (hg : g ∈ initGoals)
    (htp : g.tps = [{rank := 0, tid := W}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = W)
    (hsw : ∀ n ∈ sm.nodes, W ∉ n.outs) (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm initSM W =
      denoteGraphDistributedFaithful pm initPM W := by
  have h : initSM W = initPM W := by
    have hr := recon_weight initSM initPM hInit g hg W htp hgd hrep hts
    unfold denoteGraph at hr
    rw [foldl_applyNode_at_not_written sm sm.nodes initSM W hsw,
      foldl_applyNode_at_not_written pm pm.nodes initPM W hpw] at hr
    exact hr
  have e1 : denoteGraphDistributedFaithful sm initSM W = initSM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM W
      layer1_sm_nodes_nonempty hsw
  have e2 : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e1, e2]; exact h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21rp_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  have e2 : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e2]
  exact hPM W sh hmem

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5798_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5798)
      (denoteGraphDistributedFaithful pm initPM 11271)
      (denoteGraphDistributedFaithful pm initPM 11272)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8509_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21rp_red_sm5798 initSM, l21rp_red_pm11271 initPM, l21rp_red_pm11272 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5807_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5807)
      (denoteGraphDistributedFaithful pm initPM 11291)
      (denoteGraphDistributedFaithful pm initPM 11292)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8517_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21rp_red_sm5807 initSM, l21rp_red_pm11291 initPM, l21rp_red_pm11292 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5812_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5812)
      (denoteGraphDistributedFaithful pm initPM 11305)
      (denoteGraphDistributedFaithful pm initPM 11306)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8521_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21rp_red_sm5812 initSM, l21rp_red_pm11305 initPM, l21rp_red_pm11306 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5816_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5816)
      (denoteGraphDistributedFaithful pm initPM 11323)
      (denoteGraphDistributedFaithful pm initPM 11324)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8525_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21rp_red_sm5816 initSM, l21rp_red_pm11323 initPM, l21rp_red_pm11324 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5809_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5809)
      (denoteGraphDistributedFaithful pm initPM 11295)
      (denoteGraphDistributedFaithful pm initPM 11296)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5807_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5808 =
      denoteGraphDistributedFaithful pm initPM 5808 :=
    l21rp_weight_eq initSM initPM hInit 5808 initGoal_5808 (by native_decide)
      rfl rfl rfl rfl
      l21rp_weights_not_written.1.2.1 l21rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5808).shape = [1,1024] :=
    l21rp_pm_weight_shape initPM hPM 5808 [1,1024] (by native_decide)
      l21rp_weights_not_written.2.2.1
  rw [l21rp_red_sm5809 initSM, l21rp_red_pm11295 initPM, l21rp_red_pm11296 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5814_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5814)
      (denoteGraphDistributedFaithful pm initPM 11309)
      (denoteGraphDistributedFaithful pm initPM 11310)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5812_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5813 =
      denoteGraphDistributedFaithful pm initPM 5813 :=
    l21rp_weight_eq initSM initPM hInit 5813 initGoal_5813 (by native_decide)
      rfl rfl rfl rfl
      l21rp_weights_not_written.1.2.2.1 l21rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5813).shape = [512,1024] :=
    l21rp_pm_weight_shape initPM hPM 5813 [512,1024] (by native_decide)
      l21rp_weights_not_written.2.2.2.1
  rw [l21rp_red_sm5814 initSM, l21rp_red_pm11309 initPM, l21rp_red_pm11310 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5818_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5818)
      (denoteGraphDistributedFaithful pm initPM 11327)
      (denoteGraphDistributedFaithful pm initPM 11328)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5816_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5817 =
      denoteGraphDistributedFaithful pm initPM 5817 :=
    l21rp_weight_eq initSM initPM hInit 5817 initGoal_5817 (by native_decide)
      rfl rfl rfl rfl
      l21rp_weights_not_written.1.2.2.2 l21rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5817).shape = [512,1024] :=
    l21rp_pm_weight_shape initPM hPM 5817 [512,1024] (by native_decide)
      l21rp_weights_not_written.2.2.2.2.1
  rw [l21rp_red_sm5818 initSM, l21rp_red_pm11327 initPM, l21rp_red_pm11328 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5800_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5800)
      (denoteGraphDistributedFaithful pm initPM 11277)
      (denoteGraphDistributedFaithful pm initPM 11278)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5798_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5799 =
      denoteGraphDistributedFaithful pm initPM 5799 :=
    l21rp_weight_eq initSM initPM hInit 5799 initGoal_5799 (by native_decide)
      rfl rfl rfl rfl
      l21rp_weights_not_written.1.1 l21rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5799).shape = [64,1024] :=
    l21rp_pm_weight_shape initPM hPM 5799 [64,1024] (by native_decide)
      l21rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5786).shape = [2] :=
    l21rp_pm_weight_shape initPM hPM 5786 [2] (by native_decide)
      l21rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5786)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5786)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5798)
      (denoteGraphDistributedFaithful pm initPM 11271)
      (denoteGraphDistributedFaithful pm initPM 11272)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l21rp_red_sm5800 initSM, l21rp_red_pm11277 initPM, l21rp_red_pm11278 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
