/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L17FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-5 MoE branch (router projections)

Mechanical transport of the (green) block-4 段 `L13FaithfulRouterProj` to block 5.
Every tensor id / node index is re-certified by `native_decide`.
The block-5 cu tensor is **5590**.

* SM 690 `FW_float [8353] → [5602]`                          (PM 1442 / 1446 → 10583 / 10584)
* SM 691 `FW_reshape [8361] → [5611]`                        (PM 1443 / 1447 → 10603 / 10604)
* SM 692 `FW_reshape [8365] → [5616]`                        (PM 1444 / 1448 → 10617 / 10618)
* SM 693 `FW_reshape [8369] → [5620]`                        (PM 1445 / 1449 → 10635 / 10636)
* SM 694 `FW_norm_linear [5602, 5603] → [5604]`              (PM 1450 / 1454 → 10589 / 10590)
* SM 695 `FW_mix_precision_linear [5611, 5612] → [5613]`     (PM 1451 / 1455 → 10607 / 10608)
* SM 696 `FW_mix_precision_linear [5616, 5617] → [5618]`     (PM 1452 / 1456 → 10621 / 10622)
* SM 697 `FW_mix_precision_linear [5620, 5621] → [5622]`     (PM 1453 / 1457 → 10639 / 10640)

Weights 5603 `[64,1024]`, 5612 `[1,1024]`, 5617 `[512,1024]`, 5621 `[512,1024]` are
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

private def l17rpSmFloat5602 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8353], outs := [5602] }
private def l17rpSmResh5611 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8361], outs := [5611],
    params := [4096,1024] }
private def l17rpSmResh5616 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8365], outs := [5616],
    params := [4096,1024] }
private def l17rpSmResh5620 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8369], outs := [5620],
    params := [4096,1024] }
private def l17rpSmNL5604 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5602,5603], outs := [5604] }
private def l17rpSmMPL5613 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5611,5612], outs := [5613] }
private def l17rpSmMPL5618 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5616,5617], outs := [5618] }
private def l17rpSmMPL5622 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5620,5621], outs := [5622] }

private def l17rpPmFloat10583 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16394], outs := [10583] }
private def l17rpPmResh10603 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16402], outs := [10603],
    params := [2048,1024] }
private def l17rpPmResh10617 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16406], outs := [10617],
    params := [2048,1024] }
private def l17rpPmResh10635 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16410], outs := [10635],
    params := [2048,1024] }
private def l17rpPmFloat10584 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16417], outs := [10584] }
private def l17rpPmResh10604 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16425], outs := [10604],
    params := [2048,1024] }
private def l17rpPmResh10618 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16429], outs := [10618],
    params := [2048,1024] }
private def l17rpPmResh10636 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16433], outs := [10636],
    params := [2048,1024] }
private def l17rpPmNL10589 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [10583,5603], outs := [10589] }
private def l17rpPmMPL10607 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10603,5612], outs := [10607] }
private def l17rpPmMPL10621 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10617,5617], outs := [10621] }
private def l17rpPmMPL10639 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10635,5621], outs := [10639] }
private def l17rpPmNL10590 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [10584,5603], outs := [10590] }
private def l17rpPmMPL10608 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10604,5612], outs := [10608] }
private def l17rpPmMPL10622 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10618,5617], outs := [10622] }
private def l17rpPmMPL10640 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10636,5621], outs := [10640] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l17rp_sm_node_facts :
    sm.nodes[690]'(by native_decide) = l17rpSmFloat5602 ∧
    sm.nodes[691]'(by native_decide) = l17rpSmResh5611 ∧
    sm.nodes[692]'(by native_decide) = l17rpSmResh5616 ∧
    sm.nodes[693]'(by native_decide) = l17rpSmResh5620 ∧
    sm.nodes[694]'(by native_decide) = l17rpSmNL5604 ∧
    sm.nodes[695]'(by native_decide) = l17rpSmMPL5613 ∧
    sm.nodes[696]'(by native_decide) = l17rpSmMPL5618 ∧
    sm.nodes[697]'(by native_decide) = l17rpSmMPL5622 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l17rp_pm_node_facts :
    pm.nodes[1442]'(by native_decide) = l17rpPmFloat10583 ∧
    pm.nodes[1443]'(by native_decide) = l17rpPmResh10603 ∧
    pm.nodes[1444]'(by native_decide) = l17rpPmResh10617 ∧
    pm.nodes[1445]'(by native_decide) = l17rpPmResh10635 ∧
    pm.nodes[1446]'(by native_decide) = l17rpPmFloat10584 ∧
    pm.nodes[1447]'(by native_decide) = l17rpPmResh10604 ∧
    pm.nodes[1448]'(by native_decide) = l17rpPmResh10618 ∧
    pm.nodes[1449]'(by native_decide) = l17rpPmResh10636 ∧
    pm.nodes[1450]'(by native_decide) = l17rpPmNL10589 ∧
    pm.nodes[1451]'(by native_decide) = l17rpPmMPL10607 ∧
    pm.nodes[1452]'(by native_decide) = l17rpPmMPL10621 ∧
    pm.nodes[1453]'(by native_decide) = l17rpPmMPL10639 ∧
    pm.nodes[1454]'(by native_decide) = l17rpPmNL10590 ∧
    pm.nodes[1455]'(by native_decide) = l17rpPmMPL10608 ∧
    pm.nodes[1456]'(by native_decide) = l17rpPmMPL10622 ∧
    pm.nodes[1457]'(by native_decide) = l17rpPmMPL10640 := by
  native_decide

private theorem l17rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l17rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l17rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5603 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5612 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5617 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5621 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5603 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5612 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5617 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5621 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5590 ∉ n.outs)) := by
  native_decide

private theorem l17rp_w5603_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5603 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l17rp_w5603_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5603 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l17rp_w5612_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5612 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l17rp_w5612_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5612 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l17rp_w5617_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5617 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l17rp_w5617_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5617 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l17rp_w5621_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5621 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l17rp_w5621_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5621 ∉ n.outs := by
  intro n hn
  exact l17rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l17rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(691, 5602), (690, 8353), (692, 5611), (691, 8361), (693, 5616), (692, 8365), (694, 5620), (693, 8369), (695, 5604), (694, 5602), (696, 5613), (695, 5611), (697, 5618), (696, 5616), (698, 5622), (697, 5620)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l17rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1443, 10583), (1442, 16394), (1444, 10603), (1443, 16402), (1445, 10617), (1444, 16406), (1446, 10635), (1445, 16410), (1447, 10584), (1446, 16417), (1448, 10604), (1447, 16425), (1449, 10618), (1448, 16429), (1450, 10636), (1449, 16433), (1451, 10589), (1450, 10583), (1452, 10607), (1451, 10603), (1453, 10621), (1452, 10617), (1454, 10639), (1453, 10635), (1455, 10590), (1454, 10584), (1456, 10608), (1455, 10604), (1457, 10622), (1456, 10618), (1458, 10640), (1457, 10636)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5602 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5602 =
      denoteGraphDistributedFaithful sm initSM 8353 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 690 l17rpSmFloat5602
    8353 5602 (fun x => x)
    (by native_decide) l17rp_sm_node_facts.1 ?_
    (l17rp_nonempty_sm 691) (l17rp_sm_not_written 691 5602 (by decide))
    (l17rp_nonempty_sm 690) (l17rp_sm_not_written 690 8353 (by decide))
  intro s
  unfold l17rpSmFloat5602
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8353 5602 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5611 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5611 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8361) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 691 l17rpSmResh5611
    8361 5611 (fun x => fw_view [4096,1024] x)
    (by native_decide) l17rp_sm_node_facts.2.1 ?_
    (l17rp_nonempty_sm 692) (l17rp_sm_not_written 692 5611 (by decide))
    (l17rp_nonempty_sm 691) (l17rp_sm_not_written 691 8361 (by decide))
  intro s
  unfold l17rpSmResh5611
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8361 5611 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5616 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5616 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8365) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 692 l17rpSmResh5616
    8365 5616 (fun x => fw_view [4096,1024] x)
    (by native_decide) l17rp_sm_node_facts.2.2.1 ?_
    (l17rp_nonempty_sm 693) (l17rp_sm_not_written 693 5616 (by decide))
    (l17rp_nonempty_sm 692) (l17rp_sm_not_written 692 8365 (by decide))
  intro s
  unfold l17rpSmResh5616
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8365 5616 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5620 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5620 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8369) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 693 l17rpSmResh5620
    8369 5620 (fun x => fw_view [4096,1024] x)
    (by native_decide) l17rp_sm_node_facts.2.2.2.1 ?_
    (l17rp_nonempty_sm 694) (l17rp_sm_not_written 694 5620 (by decide))
    (l17rp_nonempty_sm 693) (l17rp_sm_not_written 693 8369 (by decide))
  intro s
  unfold l17rpSmResh5620
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8369 5620 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5604 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5604 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5602)
        (denoteGraphDistributedFaithful sm initSM 5603) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 694 l17rpSmNL5604
    5602 5603 5604 fw_norm_linear
    (by native_decide) l17rp_sm_node_facts.2.2.2.2.1 ?_
    (l17rp_nonempty_sm 695) (l17rp_sm_not_written 695 5604 (by decide))
    (l17rp_nonempty_sm 694) (l17rp_sm_not_written 694 5602 (by decide))
    (l17rp_w5603_sm_drop 694)
  intro s
  unfold l17rpSmNL5604
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5602 5603 5604

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5613 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5613 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5611)
        (denoteGraphDistributedFaithful sm initSM 5612) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 695 l17rpSmMPL5613
    5611 5612 5613 fw_linear
    (by native_decide) l17rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l17rp_nonempty_sm 696) (l17rp_sm_not_written 696 5613 (by decide))
    (l17rp_nonempty_sm 695) (l17rp_sm_not_written 695 5611 (by decide))
    (l17rp_w5612_sm_drop 695)
  intro s
  unfold l17rpSmMPL5613
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5611 5612 5613

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5618 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5618 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5616)
        (denoteGraphDistributedFaithful sm initSM 5617) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 696 l17rpSmMPL5618
    5616 5617 5618 fw_linear
    (by native_decide) l17rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_sm 697) (l17rp_sm_not_written 697 5618 (by decide))
    (l17rp_nonempty_sm 696) (l17rp_sm_not_written 696 5616 (by decide))
    (l17rp_w5617_sm_drop 696)
  intro s
  unfold l17rpSmMPL5618
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5616 5617 5618

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_sm5622 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5622 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5620)
        (denoteGraphDistributedFaithful sm initSM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 697 l17rpSmMPL5622
    5620 5621 5622 fw_linear
    (by native_decide) l17rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l17rp_nonempty_sm 698) (l17rp_sm_not_written 698 5622 (by decide))
    (l17rp_nonempty_sm 697) (l17rp_sm_not_written 697 5620 (by decide))
    (l17rp_w5621_sm_drop 697)
  intro s
  unfold l17rpSmMPL5622
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5620 5621 5622

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10583 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10583 =
      denoteGraphDistributedFaithful pm initPM 16394 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1442 l17rpPmFloat10583
    16394 10583 (fun x => x)
    (by native_decide) l17rp_pm_node_facts.1 ?_
    (l17rp_nonempty_pm 1443) (l17rp_pm_not_written 1443 10583 (by decide))
    (l17rp_nonempty_pm 1442) (l17rp_pm_not_written 1442 16394 (by decide))
  intro s
  unfold l17rpPmFloat10583
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16394 10583 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10603 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10603 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16402) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1443 l17rpPmResh10603
    16402 10603 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17rp_pm_node_facts.2.1 ?_
    (l17rp_nonempty_pm 1444) (l17rp_pm_not_written 1444 10603 (by decide))
    (l17rp_nonempty_pm 1443) (l17rp_pm_not_written 1443 16402 (by decide))
  intro s
  unfold l17rpPmResh10603
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16402 10603 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10617 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10617 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16406) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1444 l17rpPmResh10617
    16406 10617 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17rp_pm_node_facts.2.2.1 ?_
    (l17rp_nonempty_pm 1445) (l17rp_pm_not_written 1445 10617 (by decide))
    (l17rp_nonempty_pm 1444) (l17rp_pm_not_written 1444 16406 (by decide))
  intro s
  unfold l17rpPmResh10617
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16406 10617 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10635 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10635 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16410) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1445 l17rpPmResh10635
    16410 10635 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17rp_pm_node_facts.2.2.2.1 ?_
    (l17rp_nonempty_pm 1446) (l17rp_pm_not_written 1446 10635 (by decide))
    (l17rp_nonempty_pm 1445) (l17rp_pm_not_written 1445 16410 (by decide))
  intro s
  unfold l17rpPmResh10635
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16410 10635 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10584 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10584 =
      denoteGraphDistributedFaithful pm initPM 16417 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1446 l17rpPmFloat10584
    16417 10584 (fun x => x)
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1447) (l17rp_pm_not_written 1447 10584 (by decide))
    (l17rp_nonempty_pm 1446) (l17rp_pm_not_written 1446 16417 (by decide))
  intro s
  unfold l17rpPmFloat10584
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16417 10584 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10604 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10604 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16425) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1447 l17rpPmResh10604
    16425 10604 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1448) (l17rp_pm_not_written 1448 10604 (by decide))
    (l17rp_nonempty_pm 1447) (l17rp_pm_not_written 1447 16425 (by decide))
  intro s
  unfold l17rpPmResh10604
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16425 10604 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10618 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10618 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16429) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1448 l17rpPmResh10618
    16429 10618 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1449) (l17rp_pm_not_written 1449 10618 (by decide))
    (l17rp_nonempty_pm 1448) (l17rp_pm_not_written 1448 16429 (by decide))
  intro s
  unfold l17rpPmResh10618
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16429 10618 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10636 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10636 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16433) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1449 l17rpPmResh10636
    16433 10636 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1450) (l17rp_pm_not_written 1450 10636 (by decide))
    (l17rp_nonempty_pm 1449) (l17rp_pm_not_written 1449 16433 (by decide))
  intro s
  unfold l17rpPmResh10636
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16433 10636 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10589 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10589 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10583)
        (denoteGraphDistributedFaithful pm initPM 5603) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1450 l17rpPmNL10589
    10583 5603 10589 fw_norm_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1451) (l17rp_pm_not_written 1451 10589 (by decide))
    (l17rp_nonempty_pm 1450) (l17rp_pm_not_written 1450 10583 (by decide))
    (l17rp_w5603_pm_drop 1450)
  intro s
  unfold l17rpPmNL10589
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 10583 5603 10589

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10607 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10607 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10603)
        (denoteGraphDistributedFaithful pm initPM 5612) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1451 l17rpPmMPL10607
    10603 5612 10607 fw_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1452) (l17rp_pm_not_written 1452 10607 (by decide))
    (l17rp_nonempty_pm 1451) (l17rp_pm_not_written 1451 10603 (by decide))
    (l17rp_w5612_pm_drop 1451)
  intro s
  unfold l17rpPmMPL10607
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10603 5612 10607

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10621 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10621 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10617)
        (denoteGraphDistributedFaithful pm initPM 5617) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1452 l17rpPmMPL10621
    10617 5617 10621 fw_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1453) (l17rp_pm_not_written 1453 10621 (by decide))
    (l17rp_nonempty_pm 1452) (l17rp_pm_not_written 1452 10617 (by decide))
    (l17rp_w5617_pm_drop 1452)
  intro s
  unfold l17rpPmMPL10621
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10617 5617 10621

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10639 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10639 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10635)
        (denoteGraphDistributedFaithful pm initPM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1453 l17rpPmMPL10639
    10635 5621 10639 fw_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1454) (l17rp_pm_not_written 1454 10639 (by decide))
    (l17rp_nonempty_pm 1453) (l17rp_pm_not_written 1453 10635 (by decide))
    (l17rp_w5621_pm_drop 1453)
  intro s
  unfold l17rpPmMPL10639
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10635 5621 10639

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10590 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10590 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10584)
        (denoteGraphDistributedFaithful pm initPM 5603) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1454 l17rpPmNL10590
    10584 5603 10590 fw_norm_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1455) (l17rp_pm_not_written 1455 10590 (by decide))
    (l17rp_nonempty_pm 1454) (l17rp_pm_not_written 1454 10584 (by decide))
    (l17rp_w5603_pm_drop 1454)
  intro s
  unfold l17rpPmNL10590
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 10584 5603 10590

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10608 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10608 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10604)
        (denoteGraphDistributedFaithful pm initPM 5612) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1455 l17rpPmMPL10608
    10604 5612 10608 fw_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1456) (l17rp_pm_not_written 1456 10608 (by decide))
    (l17rp_nonempty_pm 1455) (l17rp_pm_not_written 1455 10604 (by decide))
    (l17rp_w5612_pm_drop 1455)
  intro s
  unfold l17rpPmMPL10608
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10604 5612 10608

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10622 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10622 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10618)
        (denoteGraphDistributedFaithful pm initPM 5617) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1456 l17rpPmMPL10622
    10618 5617 10622 fw_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17rp_nonempty_pm 1457) (l17rp_pm_not_written 1457 10622 (by decide))
    (l17rp_nonempty_pm 1456) (l17rp_pm_not_written 1456 10618 (by decide))
    (l17rp_w5617_pm_drop 1456)
  intro s
  unfold l17rpPmMPL10622
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10618 5617 10622

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_red_pm10640 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10640 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10636)
        (denoteGraphDistributedFaithful pm initPM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1457 l17rpPmMPL10640
    10636 5621 10640 fw_linear
    (by native_decide) l17rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17rp_nonempty_pm 1458) (l17rp_pm_not_written 1458 10640 (by decide))
    (l17rp_nonempty_pm 1457) (l17rp_pm_not_written 1457 10636 (by decide))
    (l17rp_w5621_pm_drop 1457)
  intro s
  unfold l17rpPmMPL10640
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10636 5621 10640

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17rp_weight_eq (initSM initPM : Store)
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
private theorem l17rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5602_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5602)
      (denoteGraphDistributedFaithful pm initPM 10583)
      (denoteGraphDistributedFaithful pm initPM 10584)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8353_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17rp_red_sm5602 initSM, l17rp_red_pm10583 initPM, l17rp_red_pm10584 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5611_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5611)
      (denoteGraphDistributedFaithful pm initPM 10603)
      (denoteGraphDistributedFaithful pm initPM 10604)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8361_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17rp_red_sm5611 initSM, l17rp_red_pm10603 initPM, l17rp_red_pm10604 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5616_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5616)
      (denoteGraphDistributedFaithful pm initPM 10617)
      (denoteGraphDistributedFaithful pm initPM 10618)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8365_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17rp_red_sm5616 initSM, l17rp_red_pm10617 initPM, l17rp_red_pm10618 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5620_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5620)
      (denoteGraphDistributedFaithful pm initPM 10635)
      (denoteGraphDistributedFaithful pm initPM 10636)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8369_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17rp_red_sm5620 initSM, l17rp_red_pm10635 initPM, l17rp_red_pm10636 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5613_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5613)
      (denoteGraphDistributedFaithful pm initPM 10607)
      (denoteGraphDistributedFaithful pm initPM 10608)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5611_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5612 =
      denoteGraphDistributedFaithful pm initPM 5612 :=
    l17rp_weight_eq initSM initPM hInit 5612 initGoal_5612 (by native_decide)
      rfl rfl rfl rfl
      l17rp_weights_not_written.1.2.1 l17rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5612).shape = [1,1024] :=
    l17rp_pm_weight_shape initPM hPM 5612 [1,1024] (by native_decide)
      l17rp_weights_not_written.2.2.1
  rw [l17rp_red_sm5613 initSM, l17rp_red_pm10607 initPM, l17rp_red_pm10608 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5618_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5618)
      (denoteGraphDistributedFaithful pm initPM 10621)
      (denoteGraphDistributedFaithful pm initPM 10622)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5616_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5617 =
      denoteGraphDistributedFaithful pm initPM 5617 :=
    l17rp_weight_eq initSM initPM hInit 5617 initGoal_5617 (by native_decide)
      rfl rfl rfl rfl
      l17rp_weights_not_written.1.2.2.1 l17rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5617).shape = [512,1024] :=
    l17rp_pm_weight_shape initPM hPM 5617 [512,1024] (by native_decide)
      l17rp_weights_not_written.2.2.2.1
  rw [l17rp_red_sm5618 initSM, l17rp_red_pm10621 initPM, l17rp_red_pm10622 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5622_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5622)
      (denoteGraphDistributedFaithful pm initPM 10639)
      (denoteGraphDistributedFaithful pm initPM 10640)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5620_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5621 =
      denoteGraphDistributedFaithful pm initPM 5621 :=
    l17rp_weight_eq initSM initPM hInit 5621 initGoal_5621 (by native_decide)
      rfl rfl rfl rfl
      l17rp_weights_not_written.1.2.2.2 l17rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5621).shape = [512,1024] :=
    l17rp_pm_weight_shape initPM hPM 5621 [512,1024] (by native_decide)
      l17rp_weights_not_written.2.2.2.2.1
  rw [l17rp_red_sm5622 initSM, l17rp_red_pm10639 initPM, l17rp_red_pm10640 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5604_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5604)
      (denoteGraphDistributedFaithful pm initPM 10589)
      (denoteGraphDistributedFaithful pm initPM 10590)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5602_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5603 =
      denoteGraphDistributedFaithful pm initPM 5603 :=
    l17rp_weight_eq initSM initPM hInit 5603 initGoal_5603 (by native_decide)
      rfl rfl rfl rfl
      l17rp_weights_not_written.1.1 l17rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5603).shape = [64,1024] :=
    l17rp_pm_weight_shape initPM hPM 5603 [64,1024] (by native_decide)
      l17rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5590).shape = [2] :=
    l17rp_pm_weight_shape initPM hPM 5590 [2] (by native_decide)
      l17rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5590)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5590)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5602)
      (denoteGraphDistributedFaithful pm initPM 10583)
      (denoteGraphDistributedFaithful pm initPM 10584)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l17rp_red_sm5604 initSM, l17rp_red_pm10589 initPM, l17rp_red_pm10590 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
