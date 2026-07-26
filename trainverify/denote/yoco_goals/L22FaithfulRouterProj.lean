/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L22FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-10 MoE branch (router projections)

Mechanical transport of the (green) block-9 段 `L13FaithfulRouterProj` to block 10.
Every tensor id / node index is re-certified by `native_decide`.
The block-10 cu tensor is **5835**.

* SM 865 `FW_float [8548] → [5847]`                          (PM 1792 / 1796 → 11443 / 11444)
* SM 866 `FW_reshape [8556] → [5856]`                        (PM 1793 / 1797 → 11463 / 11464)
* SM 867 `FW_reshape [8560] → [5861]`                        (PM 1794 / 1798 → 11477 / 11478)
* SM 868 `FW_reshape [8564] → [5865]`                        (PM 1795 / 1799 → 11495 / 11496)
* SM 869 `FW_norm_linear [5847, 5848] → [5849]`              (PM 1800 / 1804 → 11449 / 11450)
* SM 870 `FW_mix_precision_linear [5856, 5857] → [5858]`     (PM 1801 / 1805 → 11467 / 11468)
* SM 871 `FW_mix_precision_linear [5861, 5862] → [5863]`     (PM 1802 / 1806 → 11481 / 11482)
* SM 872 `FW_mix_precision_linear [5865, 5866] → [5867]`     (PM 1803 / 1807 → 11499 / 11500)

Weights 5848 `[64,1024]`, 5857 `[1,1024]`, 5862 `[512,1024]`, 5866 `[512,1024]` are
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

private def l22rpSmFloat5847 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8548], outs := [5847] }
private def l22rpSmResh5856 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8556], outs := [5856],
    params := [4096,1024] }
private def l22rpSmResh5861 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8560], outs := [5861],
    params := [4096,1024] }
private def l22rpSmResh5865 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8564], outs := [5865],
    params := [4096,1024] }
private def l22rpSmNL5849 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5847,5848], outs := [5849] }
private def l22rpSmMPL5858 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5856,5857], outs := [5858] }
private def l22rpSmMPL5863 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5861,5862], outs := [5863] }
private def l22rpSmMPL5867 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5865,5866], outs := [5867] }

private def l22rpPmFloat11443 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16784], outs := [11443] }
private def l22rpPmResh11463 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16792], outs := [11463],
    params := [2048,1024] }
private def l22rpPmResh11477 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16796], outs := [11477],
    params := [2048,1024] }
private def l22rpPmResh11495 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16800], outs := [11495],
    params := [2048,1024] }
private def l22rpPmFloat11444 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16807], outs := [11444] }
private def l22rpPmResh11464 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16815], outs := [11464],
    params := [2048,1024] }
private def l22rpPmResh11478 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16819], outs := [11478],
    params := [2048,1024] }
private def l22rpPmResh11496 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16823], outs := [11496],
    params := [2048,1024] }
private def l22rpPmNL11449 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [11443,5848], outs := [11449] }
private def l22rpPmMPL11467 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11463,5857], outs := [11467] }
private def l22rpPmMPL11481 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11477,5862], outs := [11481] }
private def l22rpPmMPL11499 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11495,5866], outs := [11499] }
private def l22rpPmNL11450 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [11444,5848], outs := [11450] }
private def l22rpPmMPL11468 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11464,5857], outs := [11468] }
private def l22rpPmMPL11482 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11478,5862], outs := [11482] }
private def l22rpPmMPL11500 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11496,5866], outs := [11500] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l22rp_sm_node_facts :
    sm.nodes[865]'(by native_decide) = l22rpSmFloat5847 ∧
    sm.nodes[866]'(by native_decide) = l22rpSmResh5856 ∧
    sm.nodes[867]'(by native_decide) = l22rpSmResh5861 ∧
    sm.nodes[868]'(by native_decide) = l22rpSmResh5865 ∧
    sm.nodes[869]'(by native_decide) = l22rpSmNL5849 ∧
    sm.nodes[870]'(by native_decide) = l22rpSmMPL5858 ∧
    sm.nodes[871]'(by native_decide) = l22rpSmMPL5863 ∧
    sm.nodes[872]'(by native_decide) = l22rpSmMPL5867 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l22rp_pm_node_facts :
    pm.nodes[1792]'(by native_decide) = l22rpPmFloat11443 ∧
    pm.nodes[1793]'(by native_decide) = l22rpPmResh11463 ∧
    pm.nodes[1794]'(by native_decide) = l22rpPmResh11477 ∧
    pm.nodes[1795]'(by native_decide) = l22rpPmResh11495 ∧
    pm.nodes[1796]'(by native_decide) = l22rpPmFloat11444 ∧
    pm.nodes[1797]'(by native_decide) = l22rpPmResh11464 ∧
    pm.nodes[1798]'(by native_decide) = l22rpPmResh11478 ∧
    pm.nodes[1799]'(by native_decide) = l22rpPmResh11496 ∧
    pm.nodes[1800]'(by native_decide) = l22rpPmNL11449 ∧
    pm.nodes[1801]'(by native_decide) = l22rpPmMPL11467 ∧
    pm.nodes[1802]'(by native_decide) = l22rpPmMPL11481 ∧
    pm.nodes[1803]'(by native_decide) = l22rpPmMPL11499 ∧
    pm.nodes[1804]'(by native_decide) = l22rpPmNL11450 ∧
    pm.nodes[1805]'(by native_decide) = l22rpPmMPL11468 ∧
    pm.nodes[1806]'(by native_decide) = l22rpPmMPL11482 ∧
    pm.nodes[1807]'(by native_decide) = l22rpPmMPL11500 := by
  native_decide

private theorem l22rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l22rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l22rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5848 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5857 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5862 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5866 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5848 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5857 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5862 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5866 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5835 ∉ n.outs)) := by
  native_decide

private theorem l22rp_w5848_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5848 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l22rp_w5848_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5848 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l22rp_w5857_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5857 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l22rp_w5857_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5857 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l22rp_w5862_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5862 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l22rp_w5862_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5862 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l22rp_w5866_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5866 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l22rp_w5866_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5866 ∉ n.outs := by
  intro n hn
  exact l22rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l22rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(866, 5847), (865, 8548), (867, 5856), (866, 8556), (868, 5861), (867, 8560), (869, 5865), (868, 8564), (870, 5849), (869, 5847), (871, 5858), (870, 5856), (872, 5863), (871, 5861), (873, 5867), (872, 5865)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l22rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1793, 11443), (1792, 16784), (1794, 11463), (1793, 16792), (1795, 11477), (1794, 16796), (1796, 11495), (1795, 16800), (1797, 11444), (1796, 16807), (1798, 11464), (1797, 16815), (1799, 11478), (1798, 16819), (1800, 11496), (1799, 16823), (1801, 11449), (1800, 11443), (1802, 11467), (1801, 11463), (1803, 11481), (1802, 11477), (1804, 11499), (1803, 11495), (1805, 11450), (1804, 11444), (1806, 11468), (1805, 11464), (1807, 11482), (1806, 11478), (1808, 11500), (1807, 11496)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5847 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5847 =
      denoteGraphDistributedFaithful sm initSM 8548 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 865 l22rpSmFloat5847
    8548 5847 (fun x => x)
    (by native_decide) l22rp_sm_node_facts.1 ?_
    (l22rp_nonempty_sm 866) (l22rp_sm_not_written 866 5847 (by decide))
    (l22rp_nonempty_sm 865) (l22rp_sm_not_written 865 8548 (by decide))
  intro s
  unfold l22rpSmFloat5847
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8548 5847 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5856 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5856 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8556) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 866 l22rpSmResh5856
    8556 5856 (fun x => fw_view [4096,1024] x)
    (by native_decide) l22rp_sm_node_facts.2.1 ?_
    (l22rp_nonempty_sm 867) (l22rp_sm_not_written 867 5856 (by decide))
    (l22rp_nonempty_sm 866) (l22rp_sm_not_written 866 8556 (by decide))
  intro s
  unfold l22rpSmResh5856
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8556 5856 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5861 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5861 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8560) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 867 l22rpSmResh5861
    8560 5861 (fun x => fw_view [4096,1024] x)
    (by native_decide) l22rp_sm_node_facts.2.2.1 ?_
    (l22rp_nonempty_sm 868) (l22rp_sm_not_written 868 5861 (by decide))
    (l22rp_nonempty_sm 867) (l22rp_sm_not_written 867 8560 (by decide))
  intro s
  unfold l22rpSmResh5861
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8560 5861 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5865 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5865 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8564) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 868 l22rpSmResh5865
    8564 5865 (fun x => fw_view [4096,1024] x)
    (by native_decide) l22rp_sm_node_facts.2.2.2.1 ?_
    (l22rp_nonempty_sm 869) (l22rp_sm_not_written 869 5865 (by decide))
    (l22rp_nonempty_sm 868) (l22rp_sm_not_written 868 8564 (by decide))
  intro s
  unfold l22rpSmResh5865
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8564 5865 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5849 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5849 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5847)
        (denoteGraphDistributedFaithful sm initSM 5848) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 869 l22rpSmNL5849
    5847 5848 5849 fw_norm_linear
    (by native_decide) l22rp_sm_node_facts.2.2.2.2.1 ?_
    (l22rp_nonempty_sm 870) (l22rp_sm_not_written 870 5849 (by decide))
    (l22rp_nonempty_sm 869) (l22rp_sm_not_written 869 5847 (by decide))
    (l22rp_w5848_sm_drop 869)
  intro s
  unfold l22rpSmNL5849
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5847 5848 5849

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5858 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5858 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5856)
        (denoteGraphDistributedFaithful sm initSM 5857) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 870 l22rpSmMPL5858
    5856 5857 5858 fw_linear
    (by native_decide) l22rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l22rp_nonempty_sm 871) (l22rp_sm_not_written 871 5858 (by decide))
    (l22rp_nonempty_sm 870) (l22rp_sm_not_written 870 5856 (by decide))
    (l22rp_w5857_sm_drop 870)
  intro s
  unfold l22rpSmMPL5858
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5856 5857 5858

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5863 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5863 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5861)
        (denoteGraphDistributedFaithful sm initSM 5862) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 871 l22rpSmMPL5863
    5861 5862 5863 fw_linear
    (by native_decide) l22rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_sm 872) (l22rp_sm_not_written 872 5863 (by decide))
    (l22rp_nonempty_sm 871) (l22rp_sm_not_written 871 5861 (by decide))
    (l22rp_w5862_sm_drop 871)
  intro s
  unfold l22rpSmMPL5863
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5861 5862 5863

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_sm5867 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5867 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5865)
        (denoteGraphDistributedFaithful sm initSM 5866) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 872 l22rpSmMPL5867
    5865 5866 5867 fw_linear
    (by native_decide) l22rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l22rp_nonempty_sm 873) (l22rp_sm_not_written 873 5867 (by decide))
    (l22rp_nonempty_sm 872) (l22rp_sm_not_written 872 5865 (by decide))
    (l22rp_w5866_sm_drop 872)
  intro s
  unfold l22rpSmMPL5867
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5865 5866 5867

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11443 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11443 =
      denoteGraphDistributedFaithful pm initPM 16784 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1792 l22rpPmFloat11443
    16784 11443 (fun x => x)
    (by native_decide) l22rp_pm_node_facts.1 ?_
    (l22rp_nonempty_pm 1793) (l22rp_pm_not_written 1793 11443 (by decide))
    (l22rp_nonempty_pm 1792) (l22rp_pm_not_written 1792 16784 (by decide))
  intro s
  unfold l22rpPmFloat11443
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16784 11443 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11463 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11463 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16792) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1793 l22rpPmResh11463
    16792 11463 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22rp_pm_node_facts.2.1 ?_
    (l22rp_nonempty_pm 1794) (l22rp_pm_not_written 1794 11463 (by decide))
    (l22rp_nonempty_pm 1793) (l22rp_pm_not_written 1793 16792 (by decide))
  intro s
  unfold l22rpPmResh11463
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16792 11463 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11477 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11477 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16796) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1794 l22rpPmResh11477
    16796 11477 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22rp_pm_node_facts.2.2.1 ?_
    (l22rp_nonempty_pm 1795) (l22rp_pm_not_written 1795 11477 (by decide))
    (l22rp_nonempty_pm 1794) (l22rp_pm_not_written 1794 16796 (by decide))
  intro s
  unfold l22rpPmResh11477
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16796 11477 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11495 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11495 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16800) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1795 l22rpPmResh11495
    16800 11495 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22rp_pm_node_facts.2.2.2.1 ?_
    (l22rp_nonempty_pm 1796) (l22rp_pm_not_written 1796 11495 (by decide))
    (l22rp_nonempty_pm 1795) (l22rp_pm_not_written 1795 16800 (by decide))
  intro s
  unfold l22rpPmResh11495
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16800 11495 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11444 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11444 =
      denoteGraphDistributedFaithful pm initPM 16807 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1796 l22rpPmFloat11444
    16807 11444 (fun x => x)
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1797) (l22rp_pm_not_written 1797 11444 (by decide))
    (l22rp_nonempty_pm 1796) (l22rp_pm_not_written 1796 16807 (by decide))
  intro s
  unfold l22rpPmFloat11444
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16807 11444 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11464 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11464 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16815) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1797 l22rpPmResh11464
    16815 11464 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1798) (l22rp_pm_not_written 1798 11464 (by decide))
    (l22rp_nonempty_pm 1797) (l22rp_pm_not_written 1797 16815 (by decide))
  intro s
  unfold l22rpPmResh11464
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16815 11464 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11478 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11478 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16819) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1798 l22rpPmResh11478
    16819 11478 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1799) (l22rp_pm_not_written 1799 11478 (by decide))
    (l22rp_nonempty_pm 1798) (l22rp_pm_not_written 1798 16819 (by decide))
  intro s
  unfold l22rpPmResh11478
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16819 11478 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11496 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11496 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16823) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1799 l22rpPmResh11496
    16823 11496 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1800) (l22rp_pm_not_written 1800 11496 (by decide))
    (l22rp_nonempty_pm 1799) (l22rp_pm_not_written 1799 16823 (by decide))
  intro s
  unfold l22rpPmResh11496
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16823 11496 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11449 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11449 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11443)
        (denoteGraphDistributedFaithful pm initPM 5848) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1800 l22rpPmNL11449
    11443 5848 11449 fw_norm_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1801) (l22rp_pm_not_written 1801 11449 (by decide))
    (l22rp_nonempty_pm 1800) (l22rp_pm_not_written 1800 11443 (by decide))
    (l22rp_w5848_pm_drop 1800)
  intro s
  unfold l22rpPmNL11449
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 11443 5848 11449

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11467 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11467 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11463)
        (denoteGraphDistributedFaithful pm initPM 5857) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1801 l22rpPmMPL11467
    11463 5857 11467 fw_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1802) (l22rp_pm_not_written 1802 11467 (by decide))
    (l22rp_nonempty_pm 1801) (l22rp_pm_not_written 1801 11463 (by decide))
    (l22rp_w5857_pm_drop 1801)
  intro s
  unfold l22rpPmMPL11467
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11463 5857 11467

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11481 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11481 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11477)
        (denoteGraphDistributedFaithful pm initPM 5862) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1802 l22rpPmMPL11481
    11477 5862 11481 fw_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1803) (l22rp_pm_not_written 1803 11481 (by decide))
    (l22rp_nonempty_pm 1802) (l22rp_pm_not_written 1802 11477 (by decide))
    (l22rp_w5862_pm_drop 1802)
  intro s
  unfold l22rpPmMPL11481
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11477 5862 11481

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11499 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11499 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11495)
        (denoteGraphDistributedFaithful pm initPM 5866) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1803 l22rpPmMPL11499
    11495 5866 11499 fw_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1804) (l22rp_pm_not_written 1804 11499 (by decide))
    (l22rp_nonempty_pm 1803) (l22rp_pm_not_written 1803 11495 (by decide))
    (l22rp_w5866_pm_drop 1803)
  intro s
  unfold l22rpPmMPL11499
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11495 5866 11499

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11450 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11450 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11444)
        (denoteGraphDistributedFaithful pm initPM 5848) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1804 l22rpPmNL11450
    11444 5848 11450 fw_norm_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1805) (l22rp_pm_not_written 1805 11450 (by decide))
    (l22rp_nonempty_pm 1804) (l22rp_pm_not_written 1804 11444 (by decide))
    (l22rp_w5848_pm_drop 1804)
  intro s
  unfold l22rpPmNL11450
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 11444 5848 11450

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11468 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11468 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11464)
        (denoteGraphDistributedFaithful pm initPM 5857) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1805 l22rpPmMPL11468
    11464 5857 11468 fw_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1806) (l22rp_pm_not_written 1806 11468 (by decide))
    (l22rp_nonempty_pm 1805) (l22rp_pm_not_written 1805 11464 (by decide))
    (l22rp_w5857_pm_drop 1805)
  intro s
  unfold l22rpPmMPL11468
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11464 5857 11468

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11482 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11482 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11478)
        (denoteGraphDistributedFaithful pm initPM 5862) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1806 l22rpPmMPL11482
    11478 5862 11482 fw_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22rp_nonempty_pm 1807) (l22rp_pm_not_written 1807 11482 (by decide))
    (l22rp_nonempty_pm 1806) (l22rp_pm_not_written 1806 11478 (by decide))
    (l22rp_w5862_pm_drop 1806)
  intro s
  unfold l22rpPmMPL11482
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11478 5862 11482

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_red_pm11500 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11500 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11496)
        (denoteGraphDistributedFaithful pm initPM 5866) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1807 l22rpPmMPL11500
    11496 5866 11500 fw_linear
    (by native_decide) l22rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22rp_nonempty_pm 1808) (l22rp_pm_not_written 1808 11500 (by decide))
    (l22rp_nonempty_pm 1807) (l22rp_pm_not_written 1807 11496 (by decide))
    (l22rp_w5866_pm_drop 1807)
  intro s
  unfold l22rpPmMPL11500
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11496 5866 11500

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22rp_weight_eq (initSM initPM : Store)
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
private theorem l22rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5847_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5847)
      (denoteGraphDistributedFaithful pm initPM 11443)
      (denoteGraphDistributedFaithful pm initPM 11444)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8548_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22rp_red_sm5847 initSM, l22rp_red_pm11443 initPM, l22rp_red_pm11444 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5856_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5856)
      (denoteGraphDistributedFaithful pm initPM 11463)
      (denoteGraphDistributedFaithful pm initPM 11464)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8556_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22rp_red_sm5856 initSM, l22rp_red_pm11463 initPM, l22rp_red_pm11464 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5861_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5861)
      (denoteGraphDistributedFaithful pm initPM 11477)
      (denoteGraphDistributedFaithful pm initPM 11478)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8560_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22rp_red_sm5861 initSM, l22rp_red_pm11477 initPM, l22rp_red_pm11478 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5865_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5865)
      (denoteGraphDistributedFaithful pm initPM 11495)
      (denoteGraphDistributedFaithful pm initPM 11496)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8564_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22rp_red_sm5865 initSM, l22rp_red_pm11495 initPM, l22rp_red_pm11496 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5858_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5858)
      (denoteGraphDistributedFaithful pm initPM 11467)
      (denoteGraphDistributedFaithful pm initPM 11468)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5856_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5857 =
      denoteGraphDistributedFaithful pm initPM 5857 :=
    l22rp_weight_eq initSM initPM hInit 5857 initGoal_5857 (by native_decide)
      rfl rfl rfl rfl
      l22rp_weights_not_written.1.2.1 l22rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5857).shape = [1,1024] :=
    l22rp_pm_weight_shape initPM hPM 5857 [1,1024] (by native_decide)
      l22rp_weights_not_written.2.2.1
  rw [l22rp_red_sm5858 initSM, l22rp_red_pm11467 initPM, l22rp_red_pm11468 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5863_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5863)
      (denoteGraphDistributedFaithful pm initPM 11481)
      (denoteGraphDistributedFaithful pm initPM 11482)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5861_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5862 =
      denoteGraphDistributedFaithful pm initPM 5862 :=
    l22rp_weight_eq initSM initPM hInit 5862 initGoal_5862 (by native_decide)
      rfl rfl rfl rfl
      l22rp_weights_not_written.1.2.2.1 l22rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5862).shape = [512,1024] :=
    l22rp_pm_weight_shape initPM hPM 5862 [512,1024] (by native_decide)
      l22rp_weights_not_written.2.2.2.1
  rw [l22rp_red_sm5863 initSM, l22rp_red_pm11481 initPM, l22rp_red_pm11482 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5867_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5867)
      (denoteGraphDistributedFaithful pm initPM 11499)
      (denoteGraphDistributedFaithful pm initPM 11500)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5865_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5866 =
      denoteGraphDistributedFaithful pm initPM 5866 :=
    l22rp_weight_eq initSM initPM hInit 5866 initGoal_5866 (by native_decide)
      rfl rfl rfl rfl
      l22rp_weights_not_written.1.2.2.2 l22rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5866).shape = [512,1024] :=
    l22rp_pm_weight_shape initPM hPM 5866 [512,1024] (by native_decide)
      l22rp_weights_not_written.2.2.2.2.1
  rw [l22rp_red_sm5867 initSM, l22rp_red_pm11499 initPM, l22rp_red_pm11500 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5849_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5849)
      (denoteGraphDistributedFaithful pm initPM 11449)
      (denoteGraphDistributedFaithful pm initPM 11450)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5847_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5848 =
      denoteGraphDistributedFaithful pm initPM 5848 :=
    l22rp_weight_eq initSM initPM hInit 5848 initGoal_5848 (by native_decide)
      rfl rfl rfl rfl
      l22rp_weights_not_written.1.1 l22rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5848).shape = [64,1024] :=
    l22rp_pm_weight_shape initPM hPM 5848 [64,1024] (by native_decide)
      l22rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5835).shape = [2] :=
    l22rp_pm_weight_shape initPM hPM 5835 [2] (by native_decide)
      l22rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5835)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5835)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5847)
      (denoteGraphDistributedFaithful pm initPM 11443)
      (denoteGraphDistributedFaithful pm initPM 11444)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l22rp_red_sm5849 initSM, l22rp_red_pm11449 initPM, l22rp_red_pm11450 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
