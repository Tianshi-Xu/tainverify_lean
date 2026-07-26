/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L20FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-8 MoE branch (router projections)

Mechanical transport of the (green) block-7 段 `L13FaithfulRouterProj` to block 8.
Every tensor id / node index is re-certified by `native_decide`.
The block-8 cu tensor is **5737**.

* SM 795 `FW_float [8470] → [5749]`                          (PM 1652 / 1656 → 11099 / 11100)
* SM 796 `FW_reshape [8478] → [5758]`                        (PM 1653 / 1657 → 11119 / 11120)
* SM 797 `FW_reshape [8482] → [5763]`                        (PM 1654 / 1658 → 11133 / 11134)
* SM 798 `FW_reshape [8486] → [5767]`                        (PM 1655 / 1659 → 11151 / 11152)
* SM 799 `FW_norm_linear [5749, 5750] → [5751]`              (PM 1660 / 1664 → 11105 / 11106)
* SM 800 `FW_mix_precision_linear [5758, 5759] → [5760]`     (PM 1661 / 1665 → 11123 / 11124)
* SM 801 `FW_mix_precision_linear [5763, 5764] → [5765]`     (PM 1662 / 1666 → 11137 / 11138)
* SM 802 `FW_mix_precision_linear [5767, 5768] → [5769]`     (PM 1663 / 1667 → 11155 / 11156)

Weights 5750 `[64,1024]`, 5759 `[1,1024]`, 5764 `[512,1024]`, 5768 `[512,1024]` are
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

private def l20rpSmFloat5749 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8470], outs := [5749] }
private def l20rpSmResh5758 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8478], outs := [5758],
    params := [4096,1024] }
private def l20rpSmResh5763 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8482], outs := [5763],
    params := [4096,1024] }
private def l20rpSmResh5767 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8486], outs := [5767],
    params := [4096,1024] }
private def l20rpSmNL5751 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5749,5750], outs := [5751] }
private def l20rpSmMPL5760 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5758,5759], outs := [5760] }
private def l20rpSmMPL5765 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5763,5764], outs := [5765] }
private def l20rpSmMPL5769 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5767,5768], outs := [5769] }

private def l20rpPmFloat11099 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16628], outs := [11099] }
private def l20rpPmResh11119 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16636], outs := [11119],
    params := [2048,1024] }
private def l20rpPmResh11133 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16640], outs := [11133],
    params := [2048,1024] }
private def l20rpPmResh11151 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16644], outs := [11151],
    params := [2048,1024] }
private def l20rpPmFloat11100 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16651], outs := [11100] }
private def l20rpPmResh11120 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16659], outs := [11120],
    params := [2048,1024] }
private def l20rpPmResh11134 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16663], outs := [11134],
    params := [2048,1024] }
private def l20rpPmResh11152 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16667], outs := [11152],
    params := [2048,1024] }
private def l20rpPmNL11105 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [11099,5750], outs := [11105] }
private def l20rpPmMPL11123 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11119,5759], outs := [11123] }
private def l20rpPmMPL11137 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11133,5764], outs := [11137] }
private def l20rpPmMPL11155 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11151,5768], outs := [11155] }
private def l20rpPmNL11106 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [11100,5750], outs := [11106] }
private def l20rpPmMPL11124 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11120,5759], outs := [11124] }
private def l20rpPmMPL11138 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11134,5764], outs := [11138] }
private def l20rpPmMPL11156 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11152,5768], outs := [11156] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l20rp_sm_node_facts :
    sm.nodes[795]'(by native_decide) = l20rpSmFloat5749 ∧
    sm.nodes[796]'(by native_decide) = l20rpSmResh5758 ∧
    sm.nodes[797]'(by native_decide) = l20rpSmResh5763 ∧
    sm.nodes[798]'(by native_decide) = l20rpSmResh5767 ∧
    sm.nodes[799]'(by native_decide) = l20rpSmNL5751 ∧
    sm.nodes[800]'(by native_decide) = l20rpSmMPL5760 ∧
    sm.nodes[801]'(by native_decide) = l20rpSmMPL5765 ∧
    sm.nodes[802]'(by native_decide) = l20rpSmMPL5769 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l20rp_pm_node_facts :
    pm.nodes[1652]'(by native_decide) = l20rpPmFloat11099 ∧
    pm.nodes[1653]'(by native_decide) = l20rpPmResh11119 ∧
    pm.nodes[1654]'(by native_decide) = l20rpPmResh11133 ∧
    pm.nodes[1655]'(by native_decide) = l20rpPmResh11151 ∧
    pm.nodes[1656]'(by native_decide) = l20rpPmFloat11100 ∧
    pm.nodes[1657]'(by native_decide) = l20rpPmResh11120 ∧
    pm.nodes[1658]'(by native_decide) = l20rpPmResh11134 ∧
    pm.nodes[1659]'(by native_decide) = l20rpPmResh11152 ∧
    pm.nodes[1660]'(by native_decide) = l20rpPmNL11105 ∧
    pm.nodes[1661]'(by native_decide) = l20rpPmMPL11123 ∧
    pm.nodes[1662]'(by native_decide) = l20rpPmMPL11137 ∧
    pm.nodes[1663]'(by native_decide) = l20rpPmMPL11155 ∧
    pm.nodes[1664]'(by native_decide) = l20rpPmNL11106 ∧
    pm.nodes[1665]'(by native_decide) = l20rpPmMPL11124 ∧
    pm.nodes[1666]'(by native_decide) = l20rpPmMPL11138 ∧
    pm.nodes[1667]'(by native_decide) = l20rpPmMPL11156 := by
  native_decide

private theorem l20rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l20rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l20rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5750 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5759 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5764 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5768 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5750 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5759 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5764 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5768 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5737 ∉ n.outs)) := by
  native_decide

private theorem l20rp_w5750_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5750 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l20rp_w5750_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5750 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l20rp_w5759_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5759 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l20rp_w5759_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5759 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l20rp_w5764_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5764 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l20rp_w5764_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5764 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l20rp_w5768_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5768 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l20rp_w5768_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5768 ∉ n.outs := by
  intro n hn
  exact l20rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l20rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(796, 5749), (795, 8470), (797, 5758), (796, 8478), (798, 5763), (797, 8482), (799, 5767), (798, 8486), (800, 5751), (799, 5749), (801, 5760), (800, 5758), (802, 5765), (801, 5763), (803, 5769), (802, 5767)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l20rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1653, 11099), (1652, 16628), (1654, 11119), (1653, 16636), (1655, 11133), (1654, 16640), (1656, 11151), (1655, 16644), (1657, 11100), (1656, 16651), (1658, 11120), (1657, 16659), (1659, 11134), (1658, 16663), (1660, 11152), (1659, 16667), (1661, 11105), (1660, 11099), (1662, 11123), (1661, 11119), (1663, 11137), (1662, 11133), (1664, 11155), (1663, 11151), (1665, 11106), (1664, 11100), (1666, 11124), (1665, 11120), (1667, 11138), (1666, 11134), (1668, 11156), (1667, 11152)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5749 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5749 =
      denoteGraphDistributedFaithful sm initSM 8470 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 795 l20rpSmFloat5749
    8470 5749 (fun x => x)
    (by native_decide) l20rp_sm_node_facts.1 ?_
    (l20rp_nonempty_sm 796) (l20rp_sm_not_written 796 5749 (by decide))
    (l20rp_nonempty_sm 795) (l20rp_sm_not_written 795 8470 (by decide))
  intro s
  unfold l20rpSmFloat5749
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8470 5749 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5758 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5758 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8478) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 796 l20rpSmResh5758
    8478 5758 (fun x => fw_view [4096,1024] x)
    (by native_decide) l20rp_sm_node_facts.2.1 ?_
    (l20rp_nonempty_sm 797) (l20rp_sm_not_written 797 5758 (by decide))
    (l20rp_nonempty_sm 796) (l20rp_sm_not_written 796 8478 (by decide))
  intro s
  unfold l20rpSmResh5758
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8478 5758 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5763 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5763 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8482) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 797 l20rpSmResh5763
    8482 5763 (fun x => fw_view [4096,1024] x)
    (by native_decide) l20rp_sm_node_facts.2.2.1 ?_
    (l20rp_nonempty_sm 798) (l20rp_sm_not_written 798 5763 (by decide))
    (l20rp_nonempty_sm 797) (l20rp_sm_not_written 797 8482 (by decide))
  intro s
  unfold l20rpSmResh5763
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8482 5763 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5767 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5767 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8486) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 798 l20rpSmResh5767
    8486 5767 (fun x => fw_view [4096,1024] x)
    (by native_decide) l20rp_sm_node_facts.2.2.2.1 ?_
    (l20rp_nonempty_sm 799) (l20rp_sm_not_written 799 5767 (by decide))
    (l20rp_nonempty_sm 798) (l20rp_sm_not_written 798 8486 (by decide))
  intro s
  unfold l20rpSmResh5767
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8486 5767 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5751 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5751 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5749)
        (denoteGraphDistributedFaithful sm initSM 5750) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 799 l20rpSmNL5751
    5749 5750 5751 fw_norm_linear
    (by native_decide) l20rp_sm_node_facts.2.2.2.2.1 ?_
    (l20rp_nonempty_sm 800) (l20rp_sm_not_written 800 5751 (by decide))
    (l20rp_nonempty_sm 799) (l20rp_sm_not_written 799 5749 (by decide))
    (l20rp_w5750_sm_drop 799)
  intro s
  unfold l20rpSmNL5751
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5749 5750 5751

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5760 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5760 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5758)
        (denoteGraphDistributedFaithful sm initSM 5759) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 800 l20rpSmMPL5760
    5758 5759 5760 fw_linear
    (by native_decide) l20rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l20rp_nonempty_sm 801) (l20rp_sm_not_written 801 5760 (by decide))
    (l20rp_nonempty_sm 800) (l20rp_sm_not_written 800 5758 (by decide))
    (l20rp_w5759_sm_drop 800)
  intro s
  unfold l20rpSmMPL5760
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5758 5759 5760

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5765 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5765 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5763)
        (denoteGraphDistributedFaithful sm initSM 5764) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 801 l20rpSmMPL5765
    5763 5764 5765 fw_linear
    (by native_decide) l20rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_sm 802) (l20rp_sm_not_written 802 5765 (by decide))
    (l20rp_nonempty_sm 801) (l20rp_sm_not_written 801 5763 (by decide))
    (l20rp_w5764_sm_drop 801)
  intro s
  unfold l20rpSmMPL5765
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5763 5764 5765

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_sm5769 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5769 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5767)
        (denoteGraphDistributedFaithful sm initSM 5768) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 802 l20rpSmMPL5769
    5767 5768 5769 fw_linear
    (by native_decide) l20rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l20rp_nonempty_sm 803) (l20rp_sm_not_written 803 5769 (by decide))
    (l20rp_nonempty_sm 802) (l20rp_sm_not_written 802 5767 (by decide))
    (l20rp_w5768_sm_drop 802)
  intro s
  unfold l20rpSmMPL5769
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5767 5768 5769

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11099 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11099 =
      denoteGraphDistributedFaithful pm initPM 16628 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1652 l20rpPmFloat11099
    16628 11099 (fun x => x)
    (by native_decide) l20rp_pm_node_facts.1 ?_
    (l20rp_nonempty_pm 1653) (l20rp_pm_not_written 1653 11099 (by decide))
    (l20rp_nonempty_pm 1652) (l20rp_pm_not_written 1652 16628 (by decide))
  intro s
  unfold l20rpPmFloat11099
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16628 11099 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11119 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11119 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16636) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1653 l20rpPmResh11119
    16636 11119 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20rp_pm_node_facts.2.1 ?_
    (l20rp_nonempty_pm 1654) (l20rp_pm_not_written 1654 11119 (by decide))
    (l20rp_nonempty_pm 1653) (l20rp_pm_not_written 1653 16636 (by decide))
  intro s
  unfold l20rpPmResh11119
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16636 11119 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11133 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11133 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16640) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1654 l20rpPmResh11133
    16640 11133 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20rp_pm_node_facts.2.2.1 ?_
    (l20rp_nonempty_pm 1655) (l20rp_pm_not_written 1655 11133 (by decide))
    (l20rp_nonempty_pm 1654) (l20rp_pm_not_written 1654 16640 (by decide))
  intro s
  unfold l20rpPmResh11133
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16640 11133 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11151 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11151 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16644) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1655 l20rpPmResh11151
    16644 11151 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20rp_pm_node_facts.2.2.2.1 ?_
    (l20rp_nonempty_pm 1656) (l20rp_pm_not_written 1656 11151 (by decide))
    (l20rp_nonempty_pm 1655) (l20rp_pm_not_written 1655 16644 (by decide))
  intro s
  unfold l20rpPmResh11151
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16644 11151 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11100 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11100 =
      denoteGraphDistributedFaithful pm initPM 16651 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1656 l20rpPmFloat11100
    16651 11100 (fun x => x)
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1657) (l20rp_pm_not_written 1657 11100 (by decide))
    (l20rp_nonempty_pm 1656) (l20rp_pm_not_written 1656 16651 (by decide))
  intro s
  unfold l20rpPmFloat11100
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16651 11100 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11120 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11120 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16659) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1657 l20rpPmResh11120
    16659 11120 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1658) (l20rp_pm_not_written 1658 11120 (by decide))
    (l20rp_nonempty_pm 1657) (l20rp_pm_not_written 1657 16659 (by decide))
  intro s
  unfold l20rpPmResh11120
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16659 11120 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11134 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11134 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16663) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1658 l20rpPmResh11134
    16663 11134 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1659) (l20rp_pm_not_written 1659 11134 (by decide))
    (l20rp_nonempty_pm 1658) (l20rp_pm_not_written 1658 16663 (by decide))
  intro s
  unfold l20rpPmResh11134
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16663 11134 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11152 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11152 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16667) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1659 l20rpPmResh11152
    16667 11152 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1660) (l20rp_pm_not_written 1660 11152 (by decide))
    (l20rp_nonempty_pm 1659) (l20rp_pm_not_written 1659 16667 (by decide))
  intro s
  unfold l20rpPmResh11152
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16667 11152 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11105 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11105 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11099)
        (denoteGraphDistributedFaithful pm initPM 5750) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1660 l20rpPmNL11105
    11099 5750 11105 fw_norm_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1661) (l20rp_pm_not_written 1661 11105 (by decide))
    (l20rp_nonempty_pm 1660) (l20rp_pm_not_written 1660 11099 (by decide))
    (l20rp_w5750_pm_drop 1660)
  intro s
  unfold l20rpPmNL11105
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 11099 5750 11105

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11123 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11123 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11119)
        (denoteGraphDistributedFaithful pm initPM 5759) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1661 l20rpPmMPL11123
    11119 5759 11123 fw_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1662) (l20rp_pm_not_written 1662 11123 (by decide))
    (l20rp_nonempty_pm 1661) (l20rp_pm_not_written 1661 11119 (by decide))
    (l20rp_w5759_pm_drop 1661)
  intro s
  unfold l20rpPmMPL11123
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11119 5759 11123

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11137 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11137 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11133)
        (denoteGraphDistributedFaithful pm initPM 5764) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1662 l20rpPmMPL11137
    11133 5764 11137 fw_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1663) (l20rp_pm_not_written 1663 11137 (by decide))
    (l20rp_nonempty_pm 1662) (l20rp_pm_not_written 1662 11133 (by decide))
    (l20rp_w5764_pm_drop 1662)
  intro s
  unfold l20rpPmMPL11137
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11133 5764 11137

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11155 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11155 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11151)
        (denoteGraphDistributedFaithful pm initPM 5768) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1663 l20rpPmMPL11155
    11151 5768 11155 fw_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1664) (l20rp_pm_not_written 1664 11155 (by decide))
    (l20rp_nonempty_pm 1663) (l20rp_pm_not_written 1663 11151 (by decide))
    (l20rp_w5768_pm_drop 1663)
  intro s
  unfold l20rpPmMPL11155
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11151 5768 11155

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11106 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11106 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11100)
        (denoteGraphDistributedFaithful pm initPM 5750) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1664 l20rpPmNL11106
    11100 5750 11106 fw_norm_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1665) (l20rp_pm_not_written 1665 11106 (by decide))
    (l20rp_nonempty_pm 1664) (l20rp_pm_not_written 1664 11100 (by decide))
    (l20rp_w5750_pm_drop 1664)
  intro s
  unfold l20rpPmNL11106
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 11100 5750 11106

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11124 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11124 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11120)
        (denoteGraphDistributedFaithful pm initPM 5759) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1665 l20rpPmMPL11124
    11120 5759 11124 fw_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1666) (l20rp_pm_not_written 1666 11124 (by decide))
    (l20rp_nonempty_pm 1665) (l20rp_pm_not_written 1665 11120 (by decide))
    (l20rp_w5759_pm_drop 1665)
  intro s
  unfold l20rpPmMPL11124
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11120 5759 11124

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11138 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11138 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11134)
        (denoteGraphDistributedFaithful pm initPM 5764) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1666 l20rpPmMPL11138
    11134 5764 11138 fw_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20rp_nonempty_pm 1667) (l20rp_pm_not_written 1667 11138 (by decide))
    (l20rp_nonempty_pm 1666) (l20rp_pm_not_written 1666 11134 (by decide))
    (l20rp_w5764_pm_drop 1666)
  intro s
  unfold l20rpPmMPL11138
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11134 5764 11138

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_red_pm11156 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11156 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11152)
        (denoteGraphDistributedFaithful pm initPM 5768) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1667 l20rpPmMPL11156
    11152 5768 11156 fw_linear
    (by native_decide) l20rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20rp_nonempty_pm 1668) (l20rp_pm_not_written 1668 11156 (by decide))
    (l20rp_nonempty_pm 1667) (l20rp_pm_not_written 1667 11152 (by decide))
    (l20rp_w5768_pm_drop 1667)
  intro s
  unfold l20rpPmMPL11156
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11152 5768 11156

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20rp_weight_eq (initSM initPM : Store)
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
private theorem l20rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5749_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5749)
      (denoteGraphDistributedFaithful pm initPM 11099)
      (denoteGraphDistributedFaithful pm initPM 11100)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8470_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20rp_red_sm5749 initSM, l20rp_red_pm11099 initPM, l20rp_red_pm11100 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5758_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5758)
      (denoteGraphDistributedFaithful pm initPM 11119)
      (denoteGraphDistributedFaithful pm initPM 11120)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8478_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20rp_red_sm5758 initSM, l20rp_red_pm11119 initPM, l20rp_red_pm11120 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5763_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5763)
      (denoteGraphDistributedFaithful pm initPM 11133)
      (denoteGraphDistributedFaithful pm initPM 11134)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8482_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20rp_red_sm5763 initSM, l20rp_red_pm11133 initPM, l20rp_red_pm11134 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5767_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5767)
      (denoteGraphDistributedFaithful pm initPM 11151)
      (denoteGraphDistributedFaithful pm initPM 11152)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8486_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20rp_red_sm5767 initSM, l20rp_red_pm11151 initPM, l20rp_red_pm11152 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5760_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5760)
      (denoteGraphDistributedFaithful pm initPM 11123)
      (denoteGraphDistributedFaithful pm initPM 11124)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5758_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5759 =
      denoteGraphDistributedFaithful pm initPM 5759 :=
    l20rp_weight_eq initSM initPM hInit 5759 initGoal_5759 (by native_decide)
      rfl rfl rfl rfl
      l20rp_weights_not_written.1.2.1 l20rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5759).shape = [1,1024] :=
    l20rp_pm_weight_shape initPM hPM 5759 [1,1024] (by native_decide)
      l20rp_weights_not_written.2.2.1
  rw [l20rp_red_sm5760 initSM, l20rp_red_pm11123 initPM, l20rp_red_pm11124 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5765_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5765)
      (denoteGraphDistributedFaithful pm initPM 11137)
      (denoteGraphDistributedFaithful pm initPM 11138)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5763_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5764 =
      denoteGraphDistributedFaithful pm initPM 5764 :=
    l20rp_weight_eq initSM initPM hInit 5764 initGoal_5764 (by native_decide)
      rfl rfl rfl rfl
      l20rp_weights_not_written.1.2.2.1 l20rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5764).shape = [512,1024] :=
    l20rp_pm_weight_shape initPM hPM 5764 [512,1024] (by native_decide)
      l20rp_weights_not_written.2.2.2.1
  rw [l20rp_red_sm5765 initSM, l20rp_red_pm11137 initPM, l20rp_red_pm11138 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5769_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5769)
      (denoteGraphDistributedFaithful pm initPM 11155)
      (denoteGraphDistributedFaithful pm initPM 11156)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5767_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5768 =
      denoteGraphDistributedFaithful pm initPM 5768 :=
    l20rp_weight_eq initSM initPM hInit 5768 initGoal_5768 (by native_decide)
      rfl rfl rfl rfl
      l20rp_weights_not_written.1.2.2.2 l20rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5768).shape = [512,1024] :=
    l20rp_pm_weight_shape initPM hPM 5768 [512,1024] (by native_decide)
      l20rp_weights_not_written.2.2.2.2.1
  rw [l20rp_red_sm5769 initSM, l20rp_red_pm11155 initPM, l20rp_red_pm11156 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5751_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5751)
      (denoteGraphDistributedFaithful pm initPM 11105)
      (denoteGraphDistributedFaithful pm initPM 11106)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5749_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5750 =
      denoteGraphDistributedFaithful pm initPM 5750 :=
    l20rp_weight_eq initSM initPM hInit 5750 initGoal_5750 (by native_decide)
      rfl rfl rfl rfl
      l20rp_weights_not_written.1.1 l20rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5750).shape = [64,1024] :=
    l20rp_pm_weight_shape initPM hPM 5750 [64,1024] (by native_decide)
      l20rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5737).shape = [2] :=
    l20rp_pm_weight_shape initPM hPM 5737 [2] (by native_decide)
      l20rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5737)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5737)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5749)
      (denoteGraphDistributedFaithful pm initPM 11099)
      (denoteGraphDistributedFaithful pm initPM 11100)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l20rp_red_sm5751 initSM, l20rp_red_pm11105 initPM, l20rp_red_pm11106 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
