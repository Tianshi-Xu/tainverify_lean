/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L14FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-2 MoE branch (router projections)

Mechanical transport of the (green) block-1 段 `L13FaithfulRouterProj` to block 2.
Every tensor id / node index is re-certified by `native_decide`.
The block-2 cu tensor is **5443**.

* SM 585 `FW_float [8236] → [5455]`                          (PM 1232 / 1236 → 10067 / 10068)
* SM 586 `FW_reshape [8244] → [5464]`                        (PM 1233 / 1237 → 10087 / 10088)
* SM 587 `FW_reshape [8248] → [5469]`                        (PM 1234 / 1238 → 10101 / 10102)
* SM 588 `FW_reshape [8252] → [5473]`                        (PM 1235 / 1239 → 10119 / 10120)
* SM 589 `FW_norm_linear [5455, 5456] → [5457]`              (PM 1240 / 1244 → 10073 / 10074)
* SM 590 `FW_mix_precision_linear [5464, 5465] → [5466]`     (PM 1241 / 1245 → 10091 / 10092)
* SM 591 `FW_mix_precision_linear [5469, 5470] → [5471]`     (PM 1242 / 1246 → 10105 / 10106)
* SM 592 `FW_mix_precision_linear [5473, 5474] → [5475]`     (PM 1243 / 1247 → 10123 / 10124)

Weights 5456 `[64,1024]`, 5465 `[1,1024]`, 5470 `[512,1024]`, 5474 `[512,1024]` are
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

private def l14rpSmFloat5455 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8236], outs := [5455] }
private def l14rpSmResh5464 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8244], outs := [5464],
    params := [4096,1024] }
private def l14rpSmResh5469 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8248], outs := [5469],
    params := [4096,1024] }
private def l14rpSmResh5473 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8252], outs := [5473],
    params := [4096,1024] }
private def l14rpSmNL5457 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5455,5456], outs := [5457] }
private def l14rpSmMPL5466 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5464,5465], outs := [5466] }
private def l14rpSmMPL5471 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5469,5470], outs := [5471] }
private def l14rpSmMPL5475 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5473,5474], outs := [5475] }

private def l14rpPmFloat10067 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16160], outs := [10067] }
private def l14rpPmResh10087 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16168], outs := [10087],
    params := [2048,1024] }
private def l14rpPmResh10101 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16172], outs := [10101],
    params := [2048,1024] }
private def l14rpPmResh10119 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16176], outs := [10119],
    params := [2048,1024] }
private def l14rpPmFloat10068 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16183], outs := [10068] }
private def l14rpPmResh10088 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16191], outs := [10088],
    params := [2048,1024] }
private def l14rpPmResh10102 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16195], outs := [10102],
    params := [2048,1024] }
private def l14rpPmResh10120 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16199], outs := [10120],
    params := [2048,1024] }
private def l14rpPmNL10073 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [10067,5456], outs := [10073] }
private def l14rpPmMPL10091 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10087,5465], outs := [10091] }
private def l14rpPmMPL10105 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10101,5470], outs := [10105] }
private def l14rpPmMPL10123 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10119,5474], outs := [10123] }
private def l14rpPmNL10074 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [10068,5456], outs := [10074] }
private def l14rpPmMPL10092 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10088,5465], outs := [10092] }
private def l14rpPmMPL10106 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10102,5470], outs := [10106] }
private def l14rpPmMPL10124 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10120,5474], outs := [10124] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l14rp_sm_node_facts :
    sm.nodes[585]'(by native_decide) = l14rpSmFloat5455 ∧
    sm.nodes[586]'(by native_decide) = l14rpSmResh5464 ∧
    sm.nodes[587]'(by native_decide) = l14rpSmResh5469 ∧
    sm.nodes[588]'(by native_decide) = l14rpSmResh5473 ∧
    sm.nodes[589]'(by native_decide) = l14rpSmNL5457 ∧
    sm.nodes[590]'(by native_decide) = l14rpSmMPL5466 ∧
    sm.nodes[591]'(by native_decide) = l14rpSmMPL5471 ∧
    sm.nodes[592]'(by native_decide) = l14rpSmMPL5475 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l14rp_pm_node_facts :
    pm.nodes[1232]'(by native_decide) = l14rpPmFloat10067 ∧
    pm.nodes[1233]'(by native_decide) = l14rpPmResh10087 ∧
    pm.nodes[1234]'(by native_decide) = l14rpPmResh10101 ∧
    pm.nodes[1235]'(by native_decide) = l14rpPmResh10119 ∧
    pm.nodes[1236]'(by native_decide) = l14rpPmFloat10068 ∧
    pm.nodes[1237]'(by native_decide) = l14rpPmResh10088 ∧
    pm.nodes[1238]'(by native_decide) = l14rpPmResh10102 ∧
    pm.nodes[1239]'(by native_decide) = l14rpPmResh10120 ∧
    pm.nodes[1240]'(by native_decide) = l14rpPmNL10073 ∧
    pm.nodes[1241]'(by native_decide) = l14rpPmMPL10091 ∧
    pm.nodes[1242]'(by native_decide) = l14rpPmMPL10105 ∧
    pm.nodes[1243]'(by native_decide) = l14rpPmMPL10123 ∧
    pm.nodes[1244]'(by native_decide) = l14rpPmNL10074 ∧
    pm.nodes[1245]'(by native_decide) = l14rpPmMPL10092 ∧
    pm.nodes[1246]'(by native_decide) = l14rpPmMPL10106 ∧
    pm.nodes[1247]'(by native_decide) = l14rpPmMPL10124 := by
  native_decide

private theorem l14rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l14rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l14rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5456 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5465 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5470 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5474 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5456 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5465 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5470 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5474 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5443 ∉ n.outs)) := by
  native_decide

private theorem l14rp_w5456_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5456 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l14rp_w5456_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5456 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l14rp_w5465_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5465 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l14rp_w5465_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5465 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l14rp_w5470_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5470 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l14rp_w5470_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5470 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l14rp_w5474_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5474 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l14rp_w5474_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5474 ∉ n.outs := by
  intro n hn
  exact l14rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l14rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(586, 5455), (585, 8236), (587, 5464), (586, 8244), (588, 5469), (587, 8248), (589, 5473), (588, 8252), (590, 5457), (589, 5455), (591, 5466), (590, 5464), (592, 5471), (591, 5469), (593, 5475), (592, 5473)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l14rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1233, 10067), (1232, 16160), (1234, 10087), (1233, 16168), (1235, 10101), (1234, 16172), (1236, 10119), (1235, 16176), (1237, 10068), (1236, 16183), (1238, 10088), (1237, 16191), (1239, 10102), (1238, 16195), (1240, 10120), (1239, 16199), (1241, 10073), (1240, 10067), (1242, 10091), (1241, 10087), (1243, 10105), (1242, 10101), (1244, 10123), (1243, 10119), (1245, 10074), (1244, 10068), (1246, 10092), (1245, 10088), (1247, 10106), (1246, 10102), (1248, 10124), (1247, 10120)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5455 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5455 =
      denoteGraphDistributedFaithful sm initSM 8236 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 585 l14rpSmFloat5455
    8236 5455 (fun x => x)
    (by native_decide) l14rp_sm_node_facts.1 ?_
    (l14rp_nonempty_sm 586) (l14rp_sm_not_written 586 5455 (by decide))
    (l14rp_nonempty_sm 585) (l14rp_sm_not_written 585 8236 (by decide))
  intro s
  unfold l14rpSmFloat5455
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8236 5455 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5464 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5464 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8244) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 586 l14rpSmResh5464
    8244 5464 (fun x => fw_view [4096,1024] x)
    (by native_decide) l14rp_sm_node_facts.2.1 ?_
    (l14rp_nonempty_sm 587) (l14rp_sm_not_written 587 5464 (by decide))
    (l14rp_nonempty_sm 586) (l14rp_sm_not_written 586 8244 (by decide))
  intro s
  unfold l14rpSmResh5464
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8244 5464 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5469 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5469 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8248) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 587 l14rpSmResh5469
    8248 5469 (fun x => fw_view [4096,1024] x)
    (by native_decide) l14rp_sm_node_facts.2.2.1 ?_
    (l14rp_nonempty_sm 588) (l14rp_sm_not_written 588 5469 (by decide))
    (l14rp_nonempty_sm 587) (l14rp_sm_not_written 587 8248 (by decide))
  intro s
  unfold l14rpSmResh5469
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8248 5469 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5473 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5473 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8252) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 588 l14rpSmResh5473
    8252 5473 (fun x => fw_view [4096,1024] x)
    (by native_decide) l14rp_sm_node_facts.2.2.2.1 ?_
    (l14rp_nonempty_sm 589) (l14rp_sm_not_written 589 5473 (by decide))
    (l14rp_nonempty_sm 588) (l14rp_sm_not_written 588 8252 (by decide))
  intro s
  unfold l14rpSmResh5473
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8252 5473 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5457 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5457 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5455)
        (denoteGraphDistributedFaithful sm initSM 5456) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 589 l14rpSmNL5457
    5455 5456 5457 fw_norm_linear
    (by native_decide) l14rp_sm_node_facts.2.2.2.2.1 ?_
    (l14rp_nonempty_sm 590) (l14rp_sm_not_written 590 5457 (by decide))
    (l14rp_nonempty_sm 589) (l14rp_sm_not_written 589 5455 (by decide))
    (l14rp_w5456_sm_drop 589)
  intro s
  unfold l14rpSmNL5457
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5455 5456 5457

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5466 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5466 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5464)
        (denoteGraphDistributedFaithful sm initSM 5465) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 590 l14rpSmMPL5466
    5464 5465 5466 fw_linear
    (by native_decide) l14rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l14rp_nonempty_sm 591) (l14rp_sm_not_written 591 5466 (by decide))
    (l14rp_nonempty_sm 590) (l14rp_sm_not_written 590 5464 (by decide))
    (l14rp_w5465_sm_drop 590)
  intro s
  unfold l14rpSmMPL5466
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5464 5465 5466

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5471 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5471 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5469)
        (denoteGraphDistributedFaithful sm initSM 5470) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 591 l14rpSmMPL5471
    5469 5470 5471 fw_linear
    (by native_decide) l14rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_sm 592) (l14rp_sm_not_written 592 5471 (by decide))
    (l14rp_nonempty_sm 591) (l14rp_sm_not_written 591 5469 (by decide))
    (l14rp_w5470_sm_drop 591)
  intro s
  unfold l14rpSmMPL5471
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5469 5470 5471

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_sm5475 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5475 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5473)
        (denoteGraphDistributedFaithful sm initSM 5474) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 592 l14rpSmMPL5475
    5473 5474 5475 fw_linear
    (by native_decide) l14rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l14rp_nonempty_sm 593) (l14rp_sm_not_written 593 5475 (by decide))
    (l14rp_nonempty_sm 592) (l14rp_sm_not_written 592 5473 (by decide))
    (l14rp_w5474_sm_drop 592)
  intro s
  unfold l14rpSmMPL5475
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5473 5474 5475

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10067 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10067 =
      denoteGraphDistributedFaithful pm initPM 16160 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1232 l14rpPmFloat10067
    16160 10067 (fun x => x)
    (by native_decide) l14rp_pm_node_facts.1 ?_
    (l14rp_nonempty_pm 1233) (l14rp_pm_not_written 1233 10067 (by decide))
    (l14rp_nonempty_pm 1232) (l14rp_pm_not_written 1232 16160 (by decide))
  intro s
  unfold l14rpPmFloat10067
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16160 10067 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10087 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10087 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16168) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1233 l14rpPmResh10087
    16168 10087 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14rp_pm_node_facts.2.1 ?_
    (l14rp_nonempty_pm 1234) (l14rp_pm_not_written 1234 10087 (by decide))
    (l14rp_nonempty_pm 1233) (l14rp_pm_not_written 1233 16168 (by decide))
  intro s
  unfold l14rpPmResh10087
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16168 10087 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10101 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10101 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16172) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1234 l14rpPmResh10101
    16172 10101 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14rp_pm_node_facts.2.2.1 ?_
    (l14rp_nonempty_pm 1235) (l14rp_pm_not_written 1235 10101 (by decide))
    (l14rp_nonempty_pm 1234) (l14rp_pm_not_written 1234 16172 (by decide))
  intro s
  unfold l14rpPmResh10101
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16172 10101 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10119 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10119 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16176) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1235 l14rpPmResh10119
    16176 10119 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14rp_pm_node_facts.2.2.2.1 ?_
    (l14rp_nonempty_pm 1236) (l14rp_pm_not_written 1236 10119 (by decide))
    (l14rp_nonempty_pm 1235) (l14rp_pm_not_written 1235 16176 (by decide))
  intro s
  unfold l14rpPmResh10119
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16176 10119 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10068 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10068 =
      denoteGraphDistributedFaithful pm initPM 16183 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1236 l14rpPmFloat10068
    16183 10068 (fun x => x)
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1237) (l14rp_pm_not_written 1237 10068 (by decide))
    (l14rp_nonempty_pm 1236) (l14rp_pm_not_written 1236 16183 (by decide))
  intro s
  unfold l14rpPmFloat10068
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16183 10068 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10088 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10088 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16191) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1237 l14rpPmResh10088
    16191 10088 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1238) (l14rp_pm_not_written 1238 10088 (by decide))
    (l14rp_nonempty_pm 1237) (l14rp_pm_not_written 1237 16191 (by decide))
  intro s
  unfold l14rpPmResh10088
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16191 10088 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10102 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10102 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16195) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1238 l14rpPmResh10102
    16195 10102 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1239) (l14rp_pm_not_written 1239 10102 (by decide))
    (l14rp_nonempty_pm 1238) (l14rp_pm_not_written 1238 16195 (by decide))
  intro s
  unfold l14rpPmResh10102
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16195 10102 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10120 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10120 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16199) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1239 l14rpPmResh10120
    16199 10120 (fun x => fw_view [2048,1024] x)
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1240) (l14rp_pm_not_written 1240 10120 (by decide))
    (l14rp_nonempty_pm 1239) (l14rp_pm_not_written 1239 16199 (by decide))
  intro s
  unfold l14rpPmResh10120
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16199 10120 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10073 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10073 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10067)
        (denoteGraphDistributedFaithful pm initPM 5456) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1240 l14rpPmNL10073
    10067 5456 10073 fw_norm_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1241) (l14rp_pm_not_written 1241 10073 (by decide))
    (l14rp_nonempty_pm 1240) (l14rp_pm_not_written 1240 10067 (by decide))
    (l14rp_w5456_pm_drop 1240)
  intro s
  unfold l14rpPmNL10073
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 10067 5456 10073

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10091 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10091 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10087)
        (denoteGraphDistributedFaithful pm initPM 5465) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1241 l14rpPmMPL10091
    10087 5465 10091 fw_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1242) (l14rp_pm_not_written 1242 10091 (by decide))
    (l14rp_nonempty_pm 1241) (l14rp_pm_not_written 1241 10087 (by decide))
    (l14rp_w5465_pm_drop 1241)
  intro s
  unfold l14rpPmMPL10091
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10087 5465 10091

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10105 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10105 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10101)
        (denoteGraphDistributedFaithful pm initPM 5470) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1242 l14rpPmMPL10105
    10101 5470 10105 fw_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1243) (l14rp_pm_not_written 1243 10105 (by decide))
    (l14rp_nonempty_pm 1242) (l14rp_pm_not_written 1242 10101 (by decide))
    (l14rp_w5470_pm_drop 1242)
  intro s
  unfold l14rpPmMPL10105
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10101 5470 10105

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10123 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10123 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10119)
        (denoteGraphDistributedFaithful pm initPM 5474) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1243 l14rpPmMPL10123
    10119 5474 10123 fw_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1244) (l14rp_pm_not_written 1244 10123 (by decide))
    (l14rp_nonempty_pm 1243) (l14rp_pm_not_written 1243 10119 (by decide))
    (l14rp_w5474_pm_drop 1243)
  intro s
  unfold l14rpPmMPL10123
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10119 5474 10123

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10074 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10074 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10068)
        (denoteGraphDistributedFaithful pm initPM 5456) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1244 l14rpPmNL10074
    10068 5456 10074 fw_norm_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1245) (l14rp_pm_not_written 1245 10074 (by decide))
    (l14rp_nonempty_pm 1244) (l14rp_pm_not_written 1244 10068 (by decide))
    (l14rp_w5456_pm_drop 1244)
  intro s
  unfold l14rpPmNL10074
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 10068 5456 10074

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10092 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10092 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10088)
        (denoteGraphDistributedFaithful pm initPM 5465) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1245 l14rpPmMPL10092
    10088 5465 10092 fw_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1246) (l14rp_pm_not_written 1246 10092 (by decide))
    (l14rp_nonempty_pm 1245) (l14rp_pm_not_written 1245 10088 (by decide))
    (l14rp_w5465_pm_drop 1245)
  intro s
  unfold l14rpPmMPL10092
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10088 5465 10092

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10106 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10106 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10102)
        (denoteGraphDistributedFaithful pm initPM 5470) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1246 l14rpPmMPL10106
    10102 5470 10106 fw_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14rp_nonempty_pm 1247) (l14rp_pm_not_written 1247 10106 (by decide))
    (l14rp_nonempty_pm 1246) (l14rp_pm_not_written 1246 10102 (by decide))
    (l14rp_w5470_pm_drop 1246)
  intro s
  unfold l14rpPmMPL10106
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10102 5470 10106

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_red_pm10124 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10124 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10120)
        (denoteGraphDistributedFaithful pm initPM 5474) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1247 l14rpPmMPL10124
    10120 5474 10124 fw_linear
    (by native_decide) l14rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14rp_nonempty_pm 1248) (l14rp_pm_not_written 1248 10124 (by decide))
    (l14rp_nonempty_pm 1247) (l14rp_pm_not_written 1247 10120 (by decide))
    (l14rp_w5474_pm_drop 1247)
  intro s
  unfold l14rpPmMPL10124
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10120 5474 10124

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14rp_weight_eq (initSM initPM : Store)
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
private theorem l14rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5455_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5455)
      (denoteGraphDistributedFaithful pm initPM 10067)
      (denoteGraphDistributedFaithful pm initPM 10068)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8236_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14rp_red_sm5455 initSM, l14rp_red_pm10067 initPM, l14rp_red_pm10068 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5464_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5464)
      (denoteGraphDistributedFaithful pm initPM 10087)
      (denoteGraphDistributedFaithful pm initPM 10088)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8244_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14rp_red_sm5464 initSM, l14rp_red_pm10087 initPM, l14rp_red_pm10088 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5469_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5469)
      (denoteGraphDistributedFaithful pm initPM 10101)
      (denoteGraphDistributedFaithful pm initPM 10102)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8248_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14rp_red_sm5469 initSM, l14rp_red_pm10101 initPM, l14rp_red_pm10102 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5473_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5473)
      (denoteGraphDistributedFaithful pm initPM 10119)
      (denoteGraphDistributedFaithful pm initPM 10120)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8252_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14rp_red_sm5473 initSM, l14rp_red_pm10119 initPM, l14rp_red_pm10120 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5466_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5466)
      (denoteGraphDistributedFaithful pm initPM 10091)
      (denoteGraphDistributedFaithful pm initPM 10092)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5464_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5465 =
      denoteGraphDistributedFaithful pm initPM 5465 :=
    l14rp_weight_eq initSM initPM hInit 5465 initGoal_5465 (by native_decide)
      rfl rfl rfl rfl
      l14rp_weights_not_written.1.2.1 l14rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5465).shape = [1,1024] :=
    l14rp_pm_weight_shape initPM hPM 5465 [1,1024] (by native_decide)
      l14rp_weights_not_written.2.2.1
  rw [l14rp_red_sm5466 initSM, l14rp_red_pm10091 initPM, l14rp_red_pm10092 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5471_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5471)
      (denoteGraphDistributedFaithful pm initPM 10105)
      (denoteGraphDistributedFaithful pm initPM 10106)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5469_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5470 =
      denoteGraphDistributedFaithful pm initPM 5470 :=
    l14rp_weight_eq initSM initPM hInit 5470 initGoal_5470 (by native_decide)
      rfl rfl rfl rfl
      l14rp_weights_not_written.1.2.2.1 l14rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5470).shape = [512,1024] :=
    l14rp_pm_weight_shape initPM hPM 5470 [512,1024] (by native_decide)
      l14rp_weights_not_written.2.2.2.1
  rw [l14rp_red_sm5471 initSM, l14rp_red_pm10105 initPM, l14rp_red_pm10106 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5475_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5475)
      (denoteGraphDistributedFaithful pm initPM 10123)
      (denoteGraphDistributedFaithful pm initPM 10124)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5473_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5474 =
      denoteGraphDistributedFaithful pm initPM 5474 :=
    l14rp_weight_eq initSM initPM hInit 5474 initGoal_5474 (by native_decide)
      rfl rfl rfl rfl
      l14rp_weights_not_written.1.2.2.2 l14rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5474).shape = [512,1024] :=
    l14rp_pm_weight_shape initPM hPM 5474 [512,1024] (by native_decide)
      l14rp_weights_not_written.2.2.2.2.1
  rw [l14rp_red_sm5475 initSM, l14rp_red_pm10123 initPM, l14rp_red_pm10124 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5457_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5457)
      (denoteGraphDistributedFaithful pm initPM 10073)
      (denoteGraphDistributedFaithful pm initPM 10074)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5455_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5456 =
      denoteGraphDistributedFaithful pm initPM 5456 :=
    l14rp_weight_eq initSM initPM hInit 5456 initGoal_5456 (by native_decide)
      rfl rfl rfl rfl
      l14rp_weights_not_written.1.1 l14rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5456).shape = [64,1024] :=
    l14rp_pm_weight_shape initPM hPM 5456 [64,1024] (by native_decide)
      l14rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5443).shape = [2] :=
    l14rp_pm_weight_shape initPM hPM 5443 [2] (by native_decide)
      l14rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5443)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5443)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5455)
      (denoteGraphDistributedFaithful pm initPM 10067)
      (denoteGraphDistributedFaithful pm initPM 10068)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l14rp_red_sm5457 initSM, l14rp_red_pm10073 initPM, l14rp_red_pm10074 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
