/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L19FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-7 MoE branch (router projections)

Mechanical transport of the (green) block-6 段 `L13FaithfulRouterProj` to block 7.
Every tensor id / node index is re-certified by `native_decide`.
The block-7 cu tensor is **5688**.

* SM 760 `FW_float [8431] → [5700]`                          (PM 1582 / 1586 → 10927 / 10928)
* SM 761 `FW_reshape [8439] → [5709]`                        (PM 1583 / 1587 → 10947 / 10948)
* SM 762 `FW_reshape [8443] → [5714]`                        (PM 1584 / 1588 → 10961 / 10962)
* SM 763 `FW_reshape [8447] → [5718]`                        (PM 1585 / 1589 → 10979 / 10980)
* SM 764 `FW_norm_linear [5700, 5701] → [5702]`              (PM 1590 / 1594 → 10933 / 10934)
* SM 765 `FW_mix_precision_linear [5709, 5710] → [5711]`     (PM 1591 / 1595 → 10951 / 10952)
* SM 766 `FW_mix_precision_linear [5714, 5715] → [5716]`     (PM 1592 / 1596 → 10965 / 10966)
* SM 767 `FW_mix_precision_linear [5718, 5719] → [5720]`     (PM 1593 / 1597 → 10983 / 10984)

Weights 5701 `[64,1024]`, 5710 `[1,1024]`, 5715 `[512,1024]`, 5719 `[512,1024]` are
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

private def l19rpSmFloat5700 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8431], outs := [5700] }
private def l19rpSmResh5709 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8439], outs := [5709],
    params := [4096,1024] }
private def l19rpSmResh5714 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8443], outs := [5714],
    params := [4096,1024] }
private def l19rpSmResh5718 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8447], outs := [5718],
    params := [4096,1024] }
private def l19rpSmNL5702 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5700,5701], outs := [5702] }
private def l19rpSmMPL5711 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5709,5710], outs := [5711] }
private def l19rpSmMPL5716 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5714,5715], outs := [5716] }
private def l19rpSmMPL5720 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5718,5719], outs := [5720] }

private def l19rpPmFloat10927 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16550], outs := [10927] }
private def l19rpPmResh10947 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16558], outs := [10947],
    params := [2048,1024] }
private def l19rpPmResh10961 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16562], outs := [10961],
    params := [2048,1024] }
private def l19rpPmResh10979 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16566], outs := [10979],
    params := [2048,1024] }
private def l19rpPmFloat10928 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16573], outs := [10928] }
private def l19rpPmResh10948 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16581], outs := [10948],
    params := [2048,1024] }
private def l19rpPmResh10962 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16585], outs := [10962],
    params := [2048,1024] }
private def l19rpPmResh10980 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16589], outs := [10980],
    params := [2048,1024] }
private def l19rpPmNL10933 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [10927,5701], outs := [10933] }
private def l19rpPmMPL10951 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10947,5710], outs := [10951] }
private def l19rpPmMPL10965 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10961,5715], outs := [10965] }
private def l19rpPmMPL10983 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10979,5719], outs := [10983] }
private def l19rpPmNL10934 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [10928,5701], outs := [10934] }
private def l19rpPmMPL10952 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10948,5710], outs := [10952] }
private def l19rpPmMPL10966 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10962,5715], outs := [10966] }
private def l19rpPmMPL10984 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10980,5719], outs := [10984] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l19rp_sm_node_facts :
    sm.nodes[760]'(by native_decide) = l19rpSmFloat5700 ∧
    sm.nodes[761]'(by native_decide) = l19rpSmResh5709 ∧
    sm.nodes[762]'(by native_decide) = l19rpSmResh5714 ∧
    sm.nodes[763]'(by native_decide) = l19rpSmResh5718 ∧
    sm.nodes[764]'(by native_decide) = l19rpSmNL5702 ∧
    sm.nodes[765]'(by native_decide) = l19rpSmMPL5711 ∧
    sm.nodes[766]'(by native_decide) = l19rpSmMPL5716 ∧
    sm.nodes[767]'(by native_decide) = l19rpSmMPL5720 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l19rp_pm_node_facts :
    pm.nodes[1582]'(by native_decide) = l19rpPmFloat10927 ∧
    pm.nodes[1583]'(by native_decide) = l19rpPmResh10947 ∧
    pm.nodes[1584]'(by native_decide) = l19rpPmResh10961 ∧
    pm.nodes[1585]'(by native_decide) = l19rpPmResh10979 ∧
    pm.nodes[1586]'(by native_decide) = l19rpPmFloat10928 ∧
    pm.nodes[1587]'(by native_decide) = l19rpPmResh10948 ∧
    pm.nodes[1588]'(by native_decide) = l19rpPmResh10962 ∧
    pm.nodes[1589]'(by native_decide) = l19rpPmResh10980 ∧
    pm.nodes[1590]'(by native_decide) = l19rpPmNL10933 ∧
    pm.nodes[1591]'(by native_decide) = l19rpPmMPL10951 ∧
    pm.nodes[1592]'(by native_decide) = l19rpPmMPL10965 ∧
    pm.nodes[1593]'(by native_decide) = l19rpPmMPL10983 ∧
    pm.nodes[1594]'(by native_decide) = l19rpPmNL10934 ∧
    pm.nodes[1595]'(by native_decide) = l19rpPmMPL10952 ∧
    pm.nodes[1596]'(by native_decide) = l19rpPmMPL10966 ∧
    pm.nodes[1597]'(by native_decide) = l19rpPmMPL10984 := by
  native_decide

private theorem l19rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l19rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l19rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5701 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5710 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5715 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5719 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5701 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5710 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5715 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5719 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5688 ∉ n.outs)) := by
  native_decide

private theorem l19rp_w5701_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5701 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l19rp_w5701_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5701 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l19rp_w5710_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5710 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l19rp_w5710_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5710 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l19rp_w5715_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5715 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l19rp_w5715_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5715 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l19rp_w5719_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5719 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l19rp_w5719_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5719 ∉ n.outs := by
  intro n hn
  exact l19rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l19rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(761, 5700), (760, 8431), (762, 5709), (761, 8439), (763, 5714), (762, 8443), (764, 5718), (763, 8447), (765, 5702), (764, 5700), (766, 5711), (765, 5709), (767, 5716), (766, 5714), (768, 5720), (767, 5718)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l19rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1583, 10927), (1582, 16550), (1584, 10947), (1583, 16558), (1585, 10961), (1584, 16562), (1586, 10979), (1585, 16566), (1587, 10928), (1586, 16573), (1588, 10948), (1587, 16581), (1589, 10962), (1588, 16585), (1590, 10980), (1589, 16589), (1591, 10933), (1590, 10927), (1592, 10951), (1591, 10947), (1593, 10965), (1592, 10961), (1594, 10983), (1593, 10979), (1595, 10934), (1594, 10928), (1596, 10952), (1595, 10948), (1597, 10966), (1596, 10962), (1598, 10984), (1597, 10980)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5700 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5700 =
      denoteGraphDistributedFaithful sm initSM 8431 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 760 l19rpSmFloat5700
    8431 5700 (fun x => x)
    (by native_decide) l19rp_sm_node_facts.1 ?_
    (l19rp_nonempty_sm 761) (l19rp_sm_not_written 761 5700 (by decide))
    (l19rp_nonempty_sm 760) (l19rp_sm_not_written 760 8431 (by decide))
  intro s
  unfold l19rpSmFloat5700
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8431 5700 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5709 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5709 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8439) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 761 l19rpSmResh5709
    8439 5709 (fun x => fw_view [4096,1024] x)
    (by native_decide) l19rp_sm_node_facts.2.1 ?_
    (l19rp_nonempty_sm 762) (l19rp_sm_not_written 762 5709 (by decide))
    (l19rp_nonempty_sm 761) (l19rp_sm_not_written 761 8439 (by decide))
  intro s
  unfold l19rpSmResh5709
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8439 5709 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5714 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5714 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8443) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 762 l19rpSmResh5714
    8443 5714 (fun x => fw_view [4096,1024] x)
    (by native_decide) l19rp_sm_node_facts.2.2.1 ?_
    (l19rp_nonempty_sm 763) (l19rp_sm_not_written 763 5714 (by decide))
    (l19rp_nonempty_sm 762) (l19rp_sm_not_written 762 8443 (by decide))
  intro s
  unfold l19rpSmResh5714
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8443 5714 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5718 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5718 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8447) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 763 l19rpSmResh5718
    8447 5718 (fun x => fw_view [4096,1024] x)
    (by native_decide) l19rp_sm_node_facts.2.2.2.1 ?_
    (l19rp_nonempty_sm 764) (l19rp_sm_not_written 764 5718 (by decide))
    (l19rp_nonempty_sm 763) (l19rp_sm_not_written 763 8447 (by decide))
  intro s
  unfold l19rpSmResh5718
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8447 5718 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5702 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5702 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5700)
        (denoteGraphDistributedFaithful sm initSM 5701) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 764 l19rpSmNL5702
    5700 5701 5702 fw_norm_linear
    (by native_decide) l19rp_sm_node_facts.2.2.2.2.1 ?_
    (l19rp_nonempty_sm 765) (l19rp_sm_not_written 765 5702 (by decide))
    (l19rp_nonempty_sm 764) (l19rp_sm_not_written 764 5700 (by decide))
    (l19rp_w5701_sm_drop 764)
  intro s
  unfold l19rpSmNL5702
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5700 5701 5702

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5711 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5711 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5709)
        (denoteGraphDistributedFaithful sm initSM 5710) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 765 l19rpSmMPL5711
    5709 5710 5711 fw_linear
    (by native_decide) l19rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l19rp_nonempty_sm 766) (l19rp_sm_not_written 766 5711 (by decide))
    (l19rp_nonempty_sm 765) (l19rp_sm_not_written 765 5709 (by decide))
    (l19rp_w5710_sm_drop 765)
  intro s
  unfold l19rpSmMPL5711
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5709 5710 5711

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5716 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5716 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5714)
        (denoteGraphDistributedFaithful sm initSM 5715) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 766 l19rpSmMPL5716
    5714 5715 5716 fw_linear
    (by native_decide) l19rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_sm 767) (l19rp_sm_not_written 767 5716 (by decide))
    (l19rp_nonempty_sm 766) (l19rp_sm_not_written 766 5714 (by decide))
    (l19rp_w5715_sm_drop 766)
  intro s
  unfold l19rpSmMPL5716
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5714 5715 5716

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_sm5720 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5720 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5718)
        (denoteGraphDistributedFaithful sm initSM 5719) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 767 l19rpSmMPL5720
    5718 5719 5720 fw_linear
    (by native_decide) l19rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l19rp_nonempty_sm 768) (l19rp_sm_not_written 768 5720 (by decide))
    (l19rp_nonempty_sm 767) (l19rp_sm_not_written 767 5718 (by decide))
    (l19rp_w5719_sm_drop 767)
  intro s
  unfold l19rpSmMPL5720
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5718 5719 5720

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10927 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10927 =
      denoteGraphDistributedFaithful pm initPM 16550 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1582 l19rpPmFloat10927
    16550 10927 (fun x => x)
    (by native_decide) l19rp_pm_node_facts.1 ?_
    (l19rp_nonempty_pm 1583) (l19rp_pm_not_written 1583 10927 (by decide))
    (l19rp_nonempty_pm 1582) (l19rp_pm_not_written 1582 16550 (by decide))
  intro s
  unfold l19rpPmFloat10927
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16550 10927 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10947 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10947 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16558) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1583 l19rpPmResh10947
    16558 10947 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19rp_pm_node_facts.2.1 ?_
    (l19rp_nonempty_pm 1584) (l19rp_pm_not_written 1584 10947 (by decide))
    (l19rp_nonempty_pm 1583) (l19rp_pm_not_written 1583 16558 (by decide))
  intro s
  unfold l19rpPmResh10947
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16558 10947 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10961 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10961 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16562) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1584 l19rpPmResh10961
    16562 10961 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19rp_pm_node_facts.2.2.1 ?_
    (l19rp_nonempty_pm 1585) (l19rp_pm_not_written 1585 10961 (by decide))
    (l19rp_nonempty_pm 1584) (l19rp_pm_not_written 1584 16562 (by decide))
  intro s
  unfold l19rpPmResh10961
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16562 10961 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10979 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10979 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16566) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1585 l19rpPmResh10979
    16566 10979 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19rp_pm_node_facts.2.2.2.1 ?_
    (l19rp_nonempty_pm 1586) (l19rp_pm_not_written 1586 10979 (by decide))
    (l19rp_nonempty_pm 1585) (l19rp_pm_not_written 1585 16566 (by decide))
  intro s
  unfold l19rpPmResh10979
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16566 10979 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10928 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10928 =
      denoteGraphDistributedFaithful pm initPM 16573 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1586 l19rpPmFloat10928
    16573 10928 (fun x => x)
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1587) (l19rp_pm_not_written 1587 10928 (by decide))
    (l19rp_nonempty_pm 1586) (l19rp_pm_not_written 1586 16573 (by decide))
  intro s
  unfold l19rpPmFloat10928
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16573 10928 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10948 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10948 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16581) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1587 l19rpPmResh10948
    16581 10948 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1588) (l19rp_pm_not_written 1588 10948 (by decide))
    (l19rp_nonempty_pm 1587) (l19rp_pm_not_written 1587 16581 (by decide))
  intro s
  unfold l19rpPmResh10948
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16581 10948 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10962 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10962 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16585) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1588 l19rpPmResh10962
    16585 10962 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1589) (l19rp_pm_not_written 1589 10962 (by decide))
    (l19rp_nonempty_pm 1588) (l19rp_pm_not_written 1588 16585 (by decide))
  intro s
  unfold l19rpPmResh10962
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16585 10962 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10980 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10980 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16589) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1589 l19rpPmResh10980
    16589 10980 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1590) (l19rp_pm_not_written 1590 10980 (by decide))
    (l19rp_nonempty_pm 1589) (l19rp_pm_not_written 1589 16589 (by decide))
  intro s
  unfold l19rpPmResh10980
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16589 10980 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10933 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10933 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10927)
        (denoteGraphDistributedFaithful pm initPM 5701) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1590 l19rpPmNL10933
    10927 5701 10933 fw_norm_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1591) (l19rp_pm_not_written 1591 10933 (by decide))
    (l19rp_nonempty_pm 1590) (l19rp_pm_not_written 1590 10927 (by decide))
    (l19rp_w5701_pm_drop 1590)
  intro s
  unfold l19rpPmNL10933
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 10927 5701 10933

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10951 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10951 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10947)
        (denoteGraphDistributedFaithful pm initPM 5710) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1591 l19rpPmMPL10951
    10947 5710 10951 fw_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1592) (l19rp_pm_not_written 1592 10951 (by decide))
    (l19rp_nonempty_pm 1591) (l19rp_pm_not_written 1591 10947 (by decide))
    (l19rp_w5710_pm_drop 1591)
  intro s
  unfold l19rpPmMPL10951
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10947 5710 10951

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10965 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10965 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10961)
        (denoteGraphDistributedFaithful pm initPM 5715) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1592 l19rpPmMPL10965
    10961 5715 10965 fw_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1593) (l19rp_pm_not_written 1593 10965 (by decide))
    (l19rp_nonempty_pm 1592) (l19rp_pm_not_written 1592 10961 (by decide))
    (l19rp_w5715_pm_drop 1592)
  intro s
  unfold l19rpPmMPL10965
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10961 5715 10965

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10983 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10983 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10979)
        (denoteGraphDistributedFaithful pm initPM 5719) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1593 l19rpPmMPL10983
    10979 5719 10983 fw_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1594) (l19rp_pm_not_written 1594 10983 (by decide))
    (l19rp_nonempty_pm 1593) (l19rp_pm_not_written 1593 10979 (by decide))
    (l19rp_w5719_pm_drop 1593)
  intro s
  unfold l19rpPmMPL10983
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10979 5719 10983

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10934 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10934 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10928)
        (denoteGraphDistributedFaithful pm initPM 5701) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1594 l19rpPmNL10934
    10928 5701 10934 fw_norm_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1595) (l19rp_pm_not_written 1595 10934 (by decide))
    (l19rp_nonempty_pm 1594) (l19rp_pm_not_written 1594 10928 (by decide))
    (l19rp_w5701_pm_drop 1594)
  intro s
  unfold l19rpPmNL10934
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 10928 5701 10934

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10952 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10952 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10948)
        (denoteGraphDistributedFaithful pm initPM 5710) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1595 l19rpPmMPL10952
    10948 5710 10952 fw_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1596) (l19rp_pm_not_written 1596 10952 (by decide))
    (l19rp_nonempty_pm 1595) (l19rp_pm_not_written 1595 10948 (by decide))
    (l19rp_w5710_pm_drop 1595)
  intro s
  unfold l19rpPmMPL10952
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10948 5710 10952

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10966 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10966 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10962)
        (denoteGraphDistributedFaithful pm initPM 5715) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1596 l19rpPmMPL10966
    10962 5715 10966 fw_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19rp_nonempty_pm 1597) (l19rp_pm_not_written 1597 10966 (by decide))
    (l19rp_nonempty_pm 1596) (l19rp_pm_not_written 1596 10962 (by decide))
    (l19rp_w5715_pm_drop 1596)
  intro s
  unfold l19rpPmMPL10966
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10962 5715 10966

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_red_pm10984 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10984 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10980)
        (denoteGraphDistributedFaithful pm initPM 5719) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1597 l19rpPmMPL10984
    10980 5719 10984 fw_linear
    (by native_decide) l19rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19rp_nonempty_pm 1598) (l19rp_pm_not_written 1598 10984 (by decide))
    (l19rp_nonempty_pm 1597) (l19rp_pm_not_written 1597 10980 (by decide))
    (l19rp_w5719_pm_drop 1597)
  intro s
  unfold l19rpPmMPL10984
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10980 5719 10984

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19rp_weight_eq (initSM initPM : Store)
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
private theorem l19rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5700_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5700)
      (denoteGraphDistributedFaithful pm initPM 10927)
      (denoteGraphDistributedFaithful pm initPM 10928)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8431_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19rp_red_sm5700 initSM, l19rp_red_pm10927 initPM, l19rp_red_pm10928 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5709_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5709)
      (denoteGraphDistributedFaithful pm initPM 10947)
      (denoteGraphDistributedFaithful pm initPM 10948)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8439_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19rp_red_sm5709 initSM, l19rp_red_pm10947 initPM, l19rp_red_pm10948 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5714_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5714)
      (denoteGraphDistributedFaithful pm initPM 10961)
      (denoteGraphDistributedFaithful pm initPM 10962)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8443_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19rp_red_sm5714 initSM, l19rp_red_pm10961 initPM, l19rp_red_pm10962 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5718_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5718)
      (denoteGraphDistributedFaithful pm initPM 10979)
      (denoteGraphDistributedFaithful pm initPM 10980)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8447_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19rp_red_sm5718 initSM, l19rp_red_pm10979 initPM, l19rp_red_pm10980 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5711_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5711)
      (denoteGraphDistributedFaithful pm initPM 10951)
      (denoteGraphDistributedFaithful pm initPM 10952)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5709_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5710 =
      denoteGraphDistributedFaithful pm initPM 5710 :=
    l19rp_weight_eq initSM initPM hInit 5710 initGoal_5710 (by native_decide)
      rfl rfl rfl rfl
      l19rp_weights_not_written.1.2.1 l19rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5710).shape = [1,1024] :=
    l19rp_pm_weight_shape initPM hPM 5710 [1,1024] (by native_decide)
      l19rp_weights_not_written.2.2.1
  rw [l19rp_red_sm5711 initSM, l19rp_red_pm10951 initPM, l19rp_red_pm10952 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5716_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5716)
      (denoteGraphDistributedFaithful pm initPM 10965)
      (denoteGraphDistributedFaithful pm initPM 10966)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5714_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5715 =
      denoteGraphDistributedFaithful pm initPM 5715 :=
    l19rp_weight_eq initSM initPM hInit 5715 initGoal_5715 (by native_decide)
      rfl rfl rfl rfl
      l19rp_weights_not_written.1.2.2.1 l19rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5715).shape = [512,1024] :=
    l19rp_pm_weight_shape initPM hPM 5715 [512,1024] (by native_decide)
      l19rp_weights_not_written.2.2.2.1
  rw [l19rp_red_sm5716 initSM, l19rp_red_pm10965 initPM, l19rp_red_pm10966 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5720_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5720)
      (denoteGraphDistributedFaithful pm initPM 10983)
      (denoteGraphDistributedFaithful pm initPM 10984)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5718_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5719 =
      denoteGraphDistributedFaithful pm initPM 5719 :=
    l19rp_weight_eq initSM initPM hInit 5719 initGoal_5719 (by native_decide)
      rfl rfl rfl rfl
      l19rp_weights_not_written.1.2.2.2 l19rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5719).shape = [512,1024] :=
    l19rp_pm_weight_shape initPM hPM 5719 [512,1024] (by native_decide)
      l19rp_weights_not_written.2.2.2.2.1
  rw [l19rp_red_sm5720 initSM, l19rp_red_pm10983 initPM, l19rp_red_pm10984 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5702_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5702)
      (denoteGraphDistributedFaithful pm initPM 10933)
      (denoteGraphDistributedFaithful pm initPM 10934)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5700_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5701 =
      denoteGraphDistributedFaithful pm initPM 5701 :=
    l19rp_weight_eq initSM initPM hInit 5701 initGoal_5701 (by native_decide)
      rfl rfl rfl rfl
      l19rp_weights_not_written.1.1 l19rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5701).shape = [64,1024] :=
    l19rp_pm_weight_shape initPM hPM 5701 [64,1024] (by native_decide)
      l19rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5688).shape = [2] :=
    l19rp_pm_weight_shape initPM hPM 5688 [2] (by native_decide)
      l19rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5688)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5688)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5700)
      (denoteGraphDistributedFaithful pm initPM 10927)
      (denoteGraphDistributedFaithful pm initPM 10928)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l19rp_red_sm5702 initSM, l19rp_red_pm10933 initPM, l19rp_red_pm10934 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
