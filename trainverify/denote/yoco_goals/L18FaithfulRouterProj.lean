/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L18FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-6 MoE branch (router projections)

Mechanical transport of the (green) block-5 段 `L13FaithfulRouterProj` to block 6.
Every tensor id / node index is re-certified by `native_decide`.
The block-6 cu tensor is **5639**.

* SM 725 `FW_float [8392] → [5651]`                          (PM 1512 / 1516 → 10755 / 10756)
* SM 726 `FW_reshape [8400] → [5660]`                        (PM 1513 / 1517 → 10775 / 10776)
* SM 727 `FW_reshape [8404] → [5665]`                        (PM 1514 / 1518 → 10789 / 10790)
* SM 728 `FW_reshape [8408] → [5669]`                        (PM 1515 / 1519 → 10807 / 10808)
* SM 729 `FW_norm_linear [5651, 5652] → [5653]`              (PM 1520 / 1524 → 10761 / 10762)
* SM 730 `FW_mix_precision_linear [5660, 5661] → [5662]`     (PM 1521 / 1525 → 10779 / 10780)
* SM 731 `FW_mix_precision_linear [5665, 5666] → [5667]`     (PM 1522 / 1526 → 10793 / 10794)
* SM 732 `FW_mix_precision_linear [5669, 5670] → [5671]`     (PM 1523 / 1527 → 10811 / 10812)

Weights 5652 `[64,1024]`, 5661 `[1,1024]`, 5666 `[512,1024]`, 5670 `[512,1024]` are
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

private def l18rpSmFloat5651 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8392], outs := [5651] }
private def l18rpSmResh5660 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8400], outs := [5660],
    params := [4096,1024] }
private def l18rpSmResh5665 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8404], outs := [5665],
    params := [4096,1024] }
private def l18rpSmResh5669 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8408], outs := [5669],
    params := [4096,1024] }
private def l18rpSmNL5653 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5651,5652], outs := [5653] }
private def l18rpSmMPL5662 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5660,5661], outs := [5662] }
private def l18rpSmMPL5667 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5665,5666], outs := [5667] }
private def l18rpSmMPL5671 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5669,5670], outs := [5671] }

private def l18rpPmFloat10755 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16472], outs := [10755] }
private def l18rpPmResh10775 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16480], outs := [10775],
    params := [2048,1024] }
private def l18rpPmResh10789 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16484], outs := [10789],
    params := [2048,1024] }
private def l18rpPmResh10807 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16488], outs := [10807],
    params := [2048,1024] }
private def l18rpPmFloat10756 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16495], outs := [10756] }
private def l18rpPmResh10776 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16503], outs := [10776],
    params := [2048,1024] }
private def l18rpPmResh10790 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16507], outs := [10790],
    params := [2048,1024] }
private def l18rpPmResh10808 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16511], outs := [10808],
    params := [2048,1024] }
private def l18rpPmNL10761 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [10755,5652], outs := [10761] }
private def l18rpPmMPL10779 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10775,5661], outs := [10779] }
private def l18rpPmMPL10793 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10789,5666], outs := [10793] }
private def l18rpPmMPL10811 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10807,5670], outs := [10811] }
private def l18rpPmNL10762 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [10756,5652], outs := [10762] }
private def l18rpPmMPL10780 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10776,5661], outs := [10780] }
private def l18rpPmMPL10794 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10790,5666], outs := [10794] }
private def l18rpPmMPL10812 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10808,5670], outs := [10812] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l18rp_sm_node_facts :
    sm.nodes[725]'(by native_decide) = l18rpSmFloat5651 ∧
    sm.nodes[726]'(by native_decide) = l18rpSmResh5660 ∧
    sm.nodes[727]'(by native_decide) = l18rpSmResh5665 ∧
    sm.nodes[728]'(by native_decide) = l18rpSmResh5669 ∧
    sm.nodes[729]'(by native_decide) = l18rpSmNL5653 ∧
    sm.nodes[730]'(by native_decide) = l18rpSmMPL5662 ∧
    sm.nodes[731]'(by native_decide) = l18rpSmMPL5667 ∧
    sm.nodes[732]'(by native_decide) = l18rpSmMPL5671 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l18rp_pm_node_facts :
    pm.nodes[1512]'(by native_decide) = l18rpPmFloat10755 ∧
    pm.nodes[1513]'(by native_decide) = l18rpPmResh10775 ∧
    pm.nodes[1514]'(by native_decide) = l18rpPmResh10789 ∧
    pm.nodes[1515]'(by native_decide) = l18rpPmResh10807 ∧
    pm.nodes[1516]'(by native_decide) = l18rpPmFloat10756 ∧
    pm.nodes[1517]'(by native_decide) = l18rpPmResh10776 ∧
    pm.nodes[1518]'(by native_decide) = l18rpPmResh10790 ∧
    pm.nodes[1519]'(by native_decide) = l18rpPmResh10808 ∧
    pm.nodes[1520]'(by native_decide) = l18rpPmNL10761 ∧
    pm.nodes[1521]'(by native_decide) = l18rpPmMPL10779 ∧
    pm.nodes[1522]'(by native_decide) = l18rpPmMPL10793 ∧
    pm.nodes[1523]'(by native_decide) = l18rpPmMPL10811 ∧
    pm.nodes[1524]'(by native_decide) = l18rpPmNL10762 ∧
    pm.nodes[1525]'(by native_decide) = l18rpPmMPL10780 ∧
    pm.nodes[1526]'(by native_decide) = l18rpPmMPL10794 ∧
    pm.nodes[1527]'(by native_decide) = l18rpPmMPL10812 := by
  native_decide

private theorem l18rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l18rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l18rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5652 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5661 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5666 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5670 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5652 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5661 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5666 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5670 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5639 ∉ n.outs)) := by
  native_decide

private theorem l18rp_w5652_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5652 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l18rp_w5652_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5652 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l18rp_w5661_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5661 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l18rp_w5661_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5661 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l18rp_w5666_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5666 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l18rp_w5666_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5666 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l18rp_w5670_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5670 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l18rp_w5670_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5670 ∉ n.outs := by
  intro n hn
  exact l18rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l18rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(726, 5651), (725, 8392), (727, 5660), (726, 8400), (728, 5665), (727, 8404), (729, 5669), (728, 8408), (730, 5653), (729, 5651), (731, 5662), (730, 5660), (732, 5667), (731, 5665), (733, 5671), (732, 5669)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l18rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1513, 10755), (1512, 16472), (1514, 10775), (1513, 16480), (1515, 10789), (1514, 16484), (1516, 10807), (1515, 16488), (1517, 10756), (1516, 16495), (1518, 10776), (1517, 16503), (1519, 10790), (1518, 16507), (1520, 10808), (1519, 16511), (1521, 10761), (1520, 10755), (1522, 10779), (1521, 10775), (1523, 10793), (1522, 10789), (1524, 10811), (1523, 10807), (1525, 10762), (1524, 10756), (1526, 10780), (1525, 10776), (1527, 10794), (1526, 10790), (1528, 10812), (1527, 10808)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5651 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5651 =
      denoteGraphDistributedFaithful sm initSM 8392 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 725 l18rpSmFloat5651
    8392 5651 (fun x => x)
    (by native_decide) l18rp_sm_node_facts.1 ?_
    (l18rp_nonempty_sm 726) (l18rp_sm_not_written 726 5651 (by decide))
    (l18rp_nonempty_sm 725) (l18rp_sm_not_written 725 8392 (by decide))
  intro s
  unfold l18rpSmFloat5651
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8392 5651 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5660 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5660 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8400) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 726 l18rpSmResh5660
    8400 5660 (fun x => fw_view [4096,1024] x)
    (by native_decide) l18rp_sm_node_facts.2.1 ?_
    (l18rp_nonempty_sm 727) (l18rp_sm_not_written 727 5660 (by decide))
    (l18rp_nonempty_sm 726) (l18rp_sm_not_written 726 8400 (by decide))
  intro s
  unfold l18rpSmResh5660
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8400 5660 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5665 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5665 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8404) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 727 l18rpSmResh5665
    8404 5665 (fun x => fw_view [4096,1024] x)
    (by native_decide) l18rp_sm_node_facts.2.2.1 ?_
    (l18rp_nonempty_sm 728) (l18rp_sm_not_written 728 5665 (by decide))
    (l18rp_nonempty_sm 727) (l18rp_sm_not_written 727 8404 (by decide))
  intro s
  unfold l18rpSmResh5665
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8404 5665 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5669 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5669 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8408) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 728 l18rpSmResh5669
    8408 5669 (fun x => fw_view [4096,1024] x)
    (by native_decide) l18rp_sm_node_facts.2.2.2.1 ?_
    (l18rp_nonempty_sm 729) (l18rp_sm_not_written 729 5669 (by decide))
    (l18rp_nonempty_sm 728) (l18rp_sm_not_written 728 8408 (by decide))
  intro s
  unfold l18rpSmResh5669
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8408 5669 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5653 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5653 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5651)
        (denoteGraphDistributedFaithful sm initSM 5652) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 729 l18rpSmNL5653
    5651 5652 5653 fw_norm_linear
    (by native_decide) l18rp_sm_node_facts.2.2.2.2.1 ?_
    (l18rp_nonempty_sm 730) (l18rp_sm_not_written 730 5653 (by decide))
    (l18rp_nonempty_sm 729) (l18rp_sm_not_written 729 5651 (by decide))
    (l18rp_w5652_sm_drop 729)
  intro s
  unfold l18rpSmNL5653
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5651 5652 5653

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5662 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5662 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5660)
        (denoteGraphDistributedFaithful sm initSM 5661) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 730 l18rpSmMPL5662
    5660 5661 5662 fw_linear
    (by native_decide) l18rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l18rp_nonempty_sm 731) (l18rp_sm_not_written 731 5662 (by decide))
    (l18rp_nonempty_sm 730) (l18rp_sm_not_written 730 5660 (by decide))
    (l18rp_w5661_sm_drop 730)
  intro s
  unfold l18rpSmMPL5662
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5660 5661 5662

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5667 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5667 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5665)
        (denoteGraphDistributedFaithful sm initSM 5666) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 731 l18rpSmMPL5667
    5665 5666 5667 fw_linear
    (by native_decide) l18rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_sm 732) (l18rp_sm_not_written 732 5667 (by decide))
    (l18rp_nonempty_sm 731) (l18rp_sm_not_written 731 5665 (by decide))
    (l18rp_w5666_sm_drop 731)
  intro s
  unfold l18rpSmMPL5667
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5665 5666 5667

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_sm5671 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5671 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5669)
        (denoteGraphDistributedFaithful sm initSM 5670) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 732 l18rpSmMPL5671
    5669 5670 5671 fw_linear
    (by native_decide) l18rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l18rp_nonempty_sm 733) (l18rp_sm_not_written 733 5671 (by decide))
    (l18rp_nonempty_sm 732) (l18rp_sm_not_written 732 5669 (by decide))
    (l18rp_w5670_sm_drop 732)
  intro s
  unfold l18rpSmMPL5671
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5669 5670 5671

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10755 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10755 =
      denoteGraphDistributedFaithful pm initPM 16472 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1512 l18rpPmFloat10755
    16472 10755 (fun x => x)
    (by native_decide) l18rp_pm_node_facts.1 ?_
    (l18rp_nonempty_pm 1513) (l18rp_pm_not_written 1513 10755 (by decide))
    (l18rp_nonempty_pm 1512) (l18rp_pm_not_written 1512 16472 (by decide))
  intro s
  unfold l18rpPmFloat10755
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16472 10755 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10775 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10775 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16480) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1513 l18rpPmResh10775
    16480 10775 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18rp_pm_node_facts.2.1 ?_
    (l18rp_nonempty_pm 1514) (l18rp_pm_not_written 1514 10775 (by decide))
    (l18rp_nonempty_pm 1513) (l18rp_pm_not_written 1513 16480 (by decide))
  intro s
  unfold l18rpPmResh10775
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16480 10775 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10789 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10789 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16484) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1514 l18rpPmResh10789
    16484 10789 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18rp_pm_node_facts.2.2.1 ?_
    (l18rp_nonempty_pm 1515) (l18rp_pm_not_written 1515 10789 (by decide))
    (l18rp_nonempty_pm 1514) (l18rp_pm_not_written 1514 16484 (by decide))
  intro s
  unfold l18rpPmResh10789
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16484 10789 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10807 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10807 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16488) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1515 l18rpPmResh10807
    16488 10807 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18rp_pm_node_facts.2.2.2.1 ?_
    (l18rp_nonempty_pm 1516) (l18rp_pm_not_written 1516 10807 (by decide))
    (l18rp_nonempty_pm 1515) (l18rp_pm_not_written 1515 16488 (by decide))
  intro s
  unfold l18rpPmResh10807
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16488 10807 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10756 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10756 =
      denoteGraphDistributedFaithful pm initPM 16495 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1516 l18rpPmFloat10756
    16495 10756 (fun x => x)
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1517) (l18rp_pm_not_written 1517 10756 (by decide))
    (l18rp_nonempty_pm 1516) (l18rp_pm_not_written 1516 16495 (by decide))
  intro s
  unfold l18rpPmFloat10756
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16495 10756 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10776 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10776 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16503) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1517 l18rpPmResh10776
    16503 10776 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1518) (l18rp_pm_not_written 1518 10776 (by decide))
    (l18rp_nonempty_pm 1517) (l18rp_pm_not_written 1517 16503 (by decide))
  intro s
  unfold l18rpPmResh10776
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16503 10776 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10790 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10790 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16507) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1518 l18rpPmResh10790
    16507 10790 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1519) (l18rp_pm_not_written 1519 10790 (by decide))
    (l18rp_nonempty_pm 1518) (l18rp_pm_not_written 1518 16507 (by decide))
  intro s
  unfold l18rpPmResh10790
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16507 10790 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10808 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10808 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16511) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1519 l18rpPmResh10808
    16511 10808 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1520) (l18rp_pm_not_written 1520 10808 (by decide))
    (l18rp_nonempty_pm 1519) (l18rp_pm_not_written 1519 16511 (by decide))
  intro s
  unfold l18rpPmResh10808
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16511 10808 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10761 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10761 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10755)
        (denoteGraphDistributedFaithful pm initPM 5652) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1520 l18rpPmNL10761
    10755 5652 10761 fw_norm_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1521) (l18rp_pm_not_written 1521 10761 (by decide))
    (l18rp_nonempty_pm 1520) (l18rp_pm_not_written 1520 10755 (by decide))
    (l18rp_w5652_pm_drop 1520)
  intro s
  unfold l18rpPmNL10761
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 10755 5652 10761

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10779 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10779 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10775)
        (denoteGraphDistributedFaithful pm initPM 5661) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1521 l18rpPmMPL10779
    10775 5661 10779 fw_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1522) (l18rp_pm_not_written 1522 10779 (by decide))
    (l18rp_nonempty_pm 1521) (l18rp_pm_not_written 1521 10775 (by decide))
    (l18rp_w5661_pm_drop 1521)
  intro s
  unfold l18rpPmMPL10779
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10775 5661 10779

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10793 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10793 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10789)
        (denoteGraphDistributedFaithful pm initPM 5666) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1522 l18rpPmMPL10793
    10789 5666 10793 fw_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1523) (l18rp_pm_not_written 1523 10793 (by decide))
    (l18rp_nonempty_pm 1522) (l18rp_pm_not_written 1522 10789 (by decide))
    (l18rp_w5666_pm_drop 1522)
  intro s
  unfold l18rpPmMPL10793
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10789 5666 10793

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10811 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10811 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10807)
        (denoteGraphDistributedFaithful pm initPM 5670) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1523 l18rpPmMPL10811
    10807 5670 10811 fw_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1524) (l18rp_pm_not_written 1524 10811 (by decide))
    (l18rp_nonempty_pm 1523) (l18rp_pm_not_written 1523 10807 (by decide))
    (l18rp_w5670_pm_drop 1523)
  intro s
  unfold l18rpPmMPL10811
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10807 5670 10811

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10762 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10762 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10756)
        (denoteGraphDistributedFaithful pm initPM 5652) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1524 l18rpPmNL10762
    10756 5652 10762 fw_norm_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1525) (l18rp_pm_not_written 1525 10762 (by decide))
    (l18rp_nonempty_pm 1524) (l18rp_pm_not_written 1524 10756 (by decide))
    (l18rp_w5652_pm_drop 1524)
  intro s
  unfold l18rpPmNL10762
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 10756 5652 10762

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10780 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10780 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10776)
        (denoteGraphDistributedFaithful pm initPM 5661) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1525 l18rpPmMPL10780
    10776 5661 10780 fw_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1526) (l18rp_pm_not_written 1526 10780 (by decide))
    (l18rp_nonempty_pm 1525) (l18rp_pm_not_written 1525 10776 (by decide))
    (l18rp_w5661_pm_drop 1525)
  intro s
  unfold l18rpPmMPL10780
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10776 5661 10780

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10794 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10794 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10790)
        (denoteGraphDistributedFaithful pm initPM 5666) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1526 l18rpPmMPL10794
    10790 5666 10794 fw_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18rp_nonempty_pm 1527) (l18rp_pm_not_written 1527 10794 (by decide))
    (l18rp_nonempty_pm 1526) (l18rp_pm_not_written 1526 10790 (by decide))
    (l18rp_w5666_pm_drop 1526)
  intro s
  unfold l18rpPmMPL10794
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10790 5666 10794

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_red_pm10812 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10812 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10808)
        (denoteGraphDistributedFaithful pm initPM 5670) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1527 l18rpPmMPL10812
    10808 5670 10812 fw_linear
    (by native_decide) l18rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18rp_nonempty_pm 1528) (l18rp_pm_not_written 1528 10812 (by decide))
    (l18rp_nonempty_pm 1527) (l18rp_pm_not_written 1527 10808 (by decide))
    (l18rp_w5670_pm_drop 1527)
  intro s
  unfold l18rpPmMPL10812
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10808 5670 10812

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18rp_weight_eq (initSM initPM : Store)
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
private theorem l18rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5651_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5651)
      (denoteGraphDistributedFaithful pm initPM 10755)
      (denoteGraphDistributedFaithful pm initPM 10756)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8392_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18rp_red_sm5651 initSM, l18rp_red_pm10755 initPM, l18rp_red_pm10756 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5660_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5660)
      (denoteGraphDistributedFaithful pm initPM 10775)
      (denoteGraphDistributedFaithful pm initPM 10776)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8400_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18rp_red_sm5660 initSM, l18rp_red_pm10775 initPM, l18rp_red_pm10776 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5665_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5665)
      (denoteGraphDistributedFaithful pm initPM 10789)
      (denoteGraphDistributedFaithful pm initPM 10790)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8404_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18rp_red_sm5665 initSM, l18rp_red_pm10789 initPM, l18rp_red_pm10790 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5669_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5669)
      (denoteGraphDistributedFaithful pm initPM 10807)
      (denoteGraphDistributedFaithful pm initPM 10808)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8408_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18rp_red_sm5669 initSM, l18rp_red_pm10807 initPM, l18rp_red_pm10808 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5662_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5662)
      (denoteGraphDistributedFaithful pm initPM 10779)
      (denoteGraphDistributedFaithful pm initPM 10780)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5660_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5661 =
      denoteGraphDistributedFaithful pm initPM 5661 :=
    l18rp_weight_eq initSM initPM hInit 5661 initGoal_5661 (by native_decide)
      rfl rfl rfl rfl
      l18rp_weights_not_written.1.2.1 l18rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5661).shape = [1,1024] :=
    l18rp_pm_weight_shape initPM hPM 5661 [1,1024] (by native_decide)
      l18rp_weights_not_written.2.2.1
  rw [l18rp_red_sm5662 initSM, l18rp_red_pm10779 initPM, l18rp_red_pm10780 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5667_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5667)
      (denoteGraphDistributedFaithful pm initPM 10793)
      (denoteGraphDistributedFaithful pm initPM 10794)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5665_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5666 =
      denoteGraphDistributedFaithful pm initPM 5666 :=
    l18rp_weight_eq initSM initPM hInit 5666 initGoal_5666 (by native_decide)
      rfl rfl rfl rfl
      l18rp_weights_not_written.1.2.2.1 l18rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5666).shape = [512,1024] :=
    l18rp_pm_weight_shape initPM hPM 5666 [512,1024] (by native_decide)
      l18rp_weights_not_written.2.2.2.1
  rw [l18rp_red_sm5667 initSM, l18rp_red_pm10793 initPM, l18rp_red_pm10794 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5671_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5671)
      (denoteGraphDistributedFaithful pm initPM 10811)
      (denoteGraphDistributedFaithful pm initPM 10812)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5669_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5670 =
      denoteGraphDistributedFaithful pm initPM 5670 :=
    l18rp_weight_eq initSM initPM hInit 5670 initGoal_5670 (by native_decide)
      rfl rfl rfl rfl
      l18rp_weights_not_written.1.2.2.2 l18rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5670).shape = [512,1024] :=
    l18rp_pm_weight_shape initPM hPM 5670 [512,1024] (by native_decide)
      l18rp_weights_not_written.2.2.2.2.1
  rw [l18rp_red_sm5671 initSM, l18rp_red_pm10811 initPM, l18rp_red_pm10812 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5653_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5653)
      (denoteGraphDistributedFaithful pm initPM 10761)
      (denoteGraphDistributedFaithful pm initPM 10762)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5651_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5652 =
      denoteGraphDistributedFaithful pm initPM 5652 :=
    l18rp_weight_eq initSM initPM hInit 5652 initGoal_5652 (by native_decide)
      rfl rfl rfl rfl
      l18rp_weights_not_written.1.1 l18rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5652).shape = [64,1024] :=
    l18rp_pm_weight_shape initPM hPM 5652 [64,1024] (by native_decide)
      l18rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5639).shape = [2] :=
    l18rp_pm_weight_shape initPM hPM 5639 [2] (by native_decide)
      l18rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5639)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5639)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5651)
      (denoteGraphDistributedFaithful pm initPM 10755)
      (denoteGraphDistributedFaithful pm initPM 10756)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l18rp_red_sm5653 initSM, l18rp_red_pm10761 initPM, l18rp_red_pm10762 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
