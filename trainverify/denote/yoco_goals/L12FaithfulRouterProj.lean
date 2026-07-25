/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulRouterEntry
import denote.yoco_goals.ZigzagRouterRel

/-!
# Faithful zigzag relations for the MoE upper branch (router + gate/up projections)

* SM 515 `FW_float [8158] → [5357]`            (PM 1092 / 1096 → 9723 / 9724)
* SM 516 `FW_reshape [8166] → [5366]`          (PM 1093 / 1097 → 9743 / 9744)
* SM 517 `FW_reshape [8170] → [5371]`          (PM 1094 / 1098 → 9757 / 9758)
* SM 518 `FW_reshape [8174] → [5375]`          (PM 1095 / 1099 → 9775 / 9776)
* SM 519 `FW_norm_linear [5357, 5358] → [5359]`            (PM 1100 / 1104 → 9729 / 9730)
* SM 520 `FW_mix_precision_linear [5366, 5367] → [5368]`   (PM 1101 / 1105 → 9747 / 9748)
* SM 521 `FW_mix_precision_linear [5371, 5372] → [5373]`   (PM 1102 / 1106 → 9761 / 9762)
* SM 522 `FW_mix_precision_linear [5375, 5376] → [5377]`   (PM 1103 / 1107 → 9779 / 9780)

Weights 5358 `[64,1024]`, 5367 `[1,1024]`, 5372 `[512,1024]`, 5376 `[512,1024]` are all
replicated singletons.

The `hdec : decodeCuSeqlens cu = [0, 2*2048]` side condition of
`Zigzag2Rel.norm_linear` is **derived** from the ambient `hCu` chain rather than
assumed: the parent relation carries `ZigzagCuWF (decodeCuSeqlens cu) [s0, s1] 2`,
whose `cu_starts_zero` / `local_tokens` fields together with the `[2]` shape of the
cu tensor 5345 pin the decoded list down to `[0, 4096]`.
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

private def l12rpSmFloat5357 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8158], outs := [5357] }
private def l12rpSmResh5366 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8166], outs := [5366],
    params := [4096,1024] }
private def l12rpSmResh5371 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8170], outs := [5371],
    params := [4096,1024] }
private def l12rpSmResh5375 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8174], outs := [5375],
    params := [4096,1024] }
private def l12rpSmNL5359 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5357,5358], outs := [5359] }
private def l12rpSmMPL5368 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5366,5367], outs := [5368] }
private def l12rpSmMPL5373 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5371,5372], outs := [5373] }
private def l12rpSmMPL5377 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5375,5376], outs := [5377] }

private def l12rpPmFloat9723 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16004], outs := [9723] }
private def l12rpPmResh9743 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16012], outs := [9743],
    params := [2048,1024] }
private def l12rpPmResh9757 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16016], outs := [9757],
    params := [2048,1024] }
private def l12rpPmResh9775 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16020], outs := [9775],
    params := [2048,1024] }
private def l12rpPmFloat9724 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16027], outs := [9724] }
private def l12rpPmResh9744 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16035], outs := [9744],
    params := [2048,1024] }
private def l12rpPmResh9758 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16039], outs := [9758],
    params := [2048,1024] }
private def l12rpPmResh9776 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16043], outs := [9776],
    params := [2048,1024] }
private def l12rpPmNL9729 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [9723,5358], outs := [9729] }
private def l12rpPmMPL9747 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9743,5367], outs := [9747] }
private def l12rpPmMPL9761 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9757,5372], outs := [9761] }
private def l12rpPmMPL9779 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9775,5376], outs := [9779] }
private def l12rpPmNL9730 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [9724,5358], outs := [9730] }
private def l12rpPmMPL9748 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9744,5367], outs := [9748] }
private def l12rpPmMPL9762 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9758,5372], outs := [9762] }
private def l12rpPmMPL9780 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9776,5376], outs := [9780] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l12rp_sm_node_facts :
    sm.nodes[515]'(by native_decide) = l12rpSmFloat5357 ∧
    sm.nodes[516]'(by native_decide) = l12rpSmResh5366 ∧
    sm.nodes[517]'(by native_decide) = l12rpSmResh5371 ∧
    sm.nodes[518]'(by native_decide) = l12rpSmResh5375 ∧
    sm.nodes[519]'(by native_decide) = l12rpSmNL5359 ∧
    sm.nodes[520]'(by native_decide) = l12rpSmMPL5368 ∧
    sm.nodes[521]'(by native_decide) = l12rpSmMPL5373 ∧
    sm.nodes[522]'(by native_decide) = l12rpSmMPL5377 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12rp_pm_node_facts :
    pm.nodes[1092]'(by native_decide) = l12rpPmFloat9723 ∧
    pm.nodes[1093]'(by native_decide) = l12rpPmResh9743 ∧
    pm.nodes[1094]'(by native_decide) = l12rpPmResh9757 ∧
    pm.nodes[1095]'(by native_decide) = l12rpPmResh9775 ∧
    pm.nodes[1096]'(by native_decide) = l12rpPmFloat9724 ∧
    pm.nodes[1097]'(by native_decide) = l12rpPmResh9744 ∧
    pm.nodes[1098]'(by native_decide) = l12rpPmResh9758 ∧
    pm.nodes[1099]'(by native_decide) = l12rpPmResh9776 ∧
    pm.nodes[1100]'(by native_decide) = l12rpPmNL9729 ∧
    pm.nodes[1101]'(by native_decide) = l12rpPmMPL9747 ∧
    pm.nodes[1102]'(by native_decide) = l12rpPmMPL9761 ∧
    pm.nodes[1103]'(by native_decide) = l12rpPmMPL9779 ∧
    pm.nodes[1104]'(by native_decide) = l12rpPmNL9730 ∧
    pm.nodes[1105]'(by native_decide) = l12rpPmMPL9748 ∧
    pm.nodes[1106]'(by native_decide) = l12rpPmMPL9762 ∧
    pm.nodes[1107]'(by native_decide) = l12rpPmMPL9780 := by
  native_decide

private theorem l12rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5358 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5367 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5372 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5376 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5358 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5367 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5372 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5376 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5345 ∉ n.outs)) := by
  native_decide

private theorem l12rp_w5358_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5358 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l12rp_w5358_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5358 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l12rp_w5367_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5367 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l12rp_w5367_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5367 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l12rp_w5372_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5372 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l12rp_w5372_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5372 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l12rp_w5376_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5376 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l12rp_w5376_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5376 ∉ n.outs := by
  intro n hn
  exact l12rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(516, 5357), (515, 8158), (517, 5366), (516, 8166), (518, 5371), (517, 8170), (519, 5375), (518, 8174), (520, 5359), (519, 5357), (521, 5368), (520, 5366), (522, 5373), (521, 5371), (523, 5377), (522, 5375)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1093, 9723), (1092, 16004), (1094, 9743), (1093, 16012), (1095, 9757), (1094, 16016), (1096, 9775), (1095, 16020), (1097, 9724), (1096, 16027), (1098, 9744), (1097, 16035), (1099, 9758), (1098, 16039), (1100, 9776), (1099, 16043), (1101, 9729), (1100, 9723), (1102, 9747), (1101, 9743), (1103, 9761), (1102, 9757), (1104, 9779), (1103, 9775), (1105, 9730), (1104, 9724), (1106, 9748), (1105, 9744), (1107, 9762), (1106, 9758), (1108, 9780), (1107, 9776)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5357 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5357 =
      denoteGraphDistributedFaithful sm initSM 8158 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 515 l12rpSmFloat5357
    8158 5357 (fun x => x)
    (by native_decide) l12rp_sm_node_facts.1 ?_
    (l12rp_nonempty_sm 516) (l12rp_sm_not_written 516 5357 (by decide))
    (l12rp_nonempty_sm 515) (l12rp_sm_not_written 515 8158 (by decide))
  intro s
  unfold l12rpSmFloat5357
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8158 5357 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5366 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5366 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8166) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 516 l12rpSmResh5366
    8166 5366 (fun x => fw_view [4096,1024] x)
    (by native_decide) l12rp_sm_node_facts.2.1 ?_
    (l12rp_nonempty_sm 517) (l12rp_sm_not_written 517 5366 (by decide))
    (l12rp_nonempty_sm 516) (l12rp_sm_not_written 516 8166 (by decide))
  intro s
  unfold l12rpSmResh5366
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8166 5366 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5371 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5371 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8170) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 517 l12rpSmResh5371
    8170 5371 (fun x => fw_view [4096,1024] x)
    (by native_decide) l12rp_sm_node_facts.2.2.1 ?_
    (l12rp_nonempty_sm 518) (l12rp_sm_not_written 518 5371 (by decide))
    (l12rp_nonempty_sm 517) (l12rp_sm_not_written 517 8170 (by decide))
  intro s
  unfold l12rpSmResh5371
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8170 5371 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5375 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5375 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8174) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 518 l12rpSmResh5375
    8174 5375 (fun x => fw_view [4096,1024] x)
    (by native_decide) l12rp_sm_node_facts.2.2.2.1 ?_
    (l12rp_nonempty_sm 519) (l12rp_sm_not_written 519 5375 (by decide))
    (l12rp_nonempty_sm 518) (l12rp_sm_not_written 518 8174 (by decide))
  intro s
  unfold l12rpSmResh5375
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8174 5375 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5359 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5359 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5357)
        (denoteGraphDistributedFaithful sm initSM 5358) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 519 l12rpSmNL5359
    5357 5358 5359 fw_norm_linear
    (by native_decide) l12rp_sm_node_facts.2.2.2.2.1 ?_
    (l12rp_nonempty_sm 520) (l12rp_sm_not_written 520 5359 (by decide))
    (l12rp_nonempty_sm 519) (l12rp_sm_not_written 519 5357 (by decide))
    (l12rp_w5358_sm_drop 519)
  intro s
  unfold l12rpSmNL5359
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5357 5358 5359

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5368 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5368 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5366)
        (denoteGraphDistributedFaithful sm initSM 5367) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 520 l12rpSmMPL5368
    5366 5367 5368 fw_linear
    (by native_decide) l12rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l12rp_nonempty_sm 521) (l12rp_sm_not_written 521 5368 (by decide))
    (l12rp_nonempty_sm 520) (l12rp_sm_not_written 520 5366 (by decide))
    (l12rp_w5367_sm_drop 520)
  intro s
  unfold l12rpSmMPL5368
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5366 5367 5368

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5373 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5373 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5371)
        (denoteGraphDistributedFaithful sm initSM 5372) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 521 l12rpSmMPL5373
    5371 5372 5373 fw_linear
    (by native_decide) l12rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_sm 522) (l12rp_sm_not_written 522 5373 (by decide))
    (l12rp_nonempty_sm 521) (l12rp_sm_not_written 521 5371 (by decide))
    (l12rp_w5372_sm_drop 521)
  intro s
  unfold l12rpSmMPL5373
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5371 5372 5373

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_sm5377 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5377 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5375)
        (denoteGraphDistributedFaithful sm initSM 5376) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 522 l12rpSmMPL5377
    5375 5376 5377 fw_linear
    (by native_decide) l12rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l12rp_nonempty_sm 523) (l12rp_sm_not_written 523 5377 (by decide))
    (l12rp_nonempty_sm 522) (l12rp_sm_not_written 522 5375 (by decide))
    (l12rp_w5376_sm_drop 522)
  intro s
  unfold l12rpSmMPL5377
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5375 5376 5377

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9723 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9723 =
      denoteGraphDistributedFaithful pm initPM 16004 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1092 l12rpPmFloat9723
    16004 9723 (fun x => x)
    (by native_decide) l12rp_pm_node_facts.1 ?_
    (l12rp_nonempty_pm 1093) (l12rp_pm_not_written 1093 9723 (by decide))
    (l12rp_nonempty_pm 1092) (l12rp_pm_not_written 1092 16004 (by decide))
  intro s
  unfold l12rpPmFloat9723
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16004 9723 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9743 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9743 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16012) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1093 l12rpPmResh9743
    16012 9743 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12rp_pm_node_facts.2.1 ?_
    (l12rp_nonempty_pm 1094) (l12rp_pm_not_written 1094 9743 (by decide))
    (l12rp_nonempty_pm 1093) (l12rp_pm_not_written 1093 16012 (by decide))
  intro s
  unfold l12rpPmResh9743
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16012 9743 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9757 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9757 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16016) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1094 l12rpPmResh9757
    16016 9757 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12rp_pm_node_facts.2.2.1 ?_
    (l12rp_nonempty_pm 1095) (l12rp_pm_not_written 1095 9757 (by decide))
    (l12rp_nonempty_pm 1094) (l12rp_pm_not_written 1094 16016 (by decide))
  intro s
  unfold l12rpPmResh9757
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16016 9757 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9775 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9775 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16020) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1095 l12rpPmResh9775
    16020 9775 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12rp_pm_node_facts.2.2.2.1 ?_
    (l12rp_nonempty_pm 1096) (l12rp_pm_not_written 1096 9775 (by decide))
    (l12rp_nonempty_pm 1095) (l12rp_pm_not_written 1095 16020 (by decide))
  intro s
  unfold l12rpPmResh9775
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16020 9775 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9724 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9724 =
      denoteGraphDistributedFaithful pm initPM 16027 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1096 l12rpPmFloat9724
    16027 9724 (fun x => x)
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1097) (l12rp_pm_not_written 1097 9724 (by decide))
    (l12rp_nonempty_pm 1096) (l12rp_pm_not_written 1096 16027 (by decide))
  intro s
  unfold l12rpPmFloat9724
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16027 9724 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9744 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9744 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16035) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1097 l12rpPmResh9744
    16035 9744 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1098) (l12rp_pm_not_written 1098 9744 (by decide))
    (l12rp_nonempty_pm 1097) (l12rp_pm_not_written 1097 16035 (by decide))
  intro s
  unfold l12rpPmResh9744
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16035 9744 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9758 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9758 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16039) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1098 l12rpPmResh9758
    16039 9758 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1099) (l12rp_pm_not_written 1099 9758 (by decide))
    (l12rp_nonempty_pm 1098) (l12rp_pm_not_written 1098 16039 (by decide))
  intro s
  unfold l12rpPmResh9758
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16039 9758 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9776 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9776 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16043) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1099 l12rpPmResh9776
    16043 9776 (fun x => fw_view [2048,1024] x)
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1100) (l12rp_pm_not_written 1100 9776 (by decide))
    (l12rp_nonempty_pm 1099) (l12rp_pm_not_written 1099 16043 (by decide))
  intro s
  unfold l12rpPmResh9776
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16043 9776 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9729 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9729 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 9723)
        (denoteGraphDistributedFaithful pm initPM 5358) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1100 l12rpPmNL9729
    9723 5358 9729 fw_norm_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1101) (l12rp_pm_not_written 1101 9729 (by decide))
    (l12rp_nonempty_pm 1100) (l12rp_pm_not_written 1100 9723 (by decide))
    (l12rp_w5358_pm_drop 1100)
  intro s
  unfold l12rpPmNL9729
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 9723 5358 9729

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9747 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9747 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9743)
        (denoteGraphDistributedFaithful pm initPM 5367) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1101 l12rpPmMPL9747
    9743 5367 9747 fw_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1102) (l12rp_pm_not_written 1102 9747 (by decide))
    (l12rp_nonempty_pm 1101) (l12rp_pm_not_written 1101 9743 (by decide))
    (l12rp_w5367_pm_drop 1101)
  intro s
  unfold l12rpPmMPL9747
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9743 5367 9747

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9761 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9761 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9757)
        (denoteGraphDistributedFaithful pm initPM 5372) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1102 l12rpPmMPL9761
    9757 5372 9761 fw_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1103) (l12rp_pm_not_written 1103 9761 (by decide))
    (l12rp_nonempty_pm 1102) (l12rp_pm_not_written 1102 9757 (by decide))
    (l12rp_w5372_pm_drop 1102)
  intro s
  unfold l12rpPmMPL9761
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9757 5372 9761

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9779 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9779 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9775)
        (denoteGraphDistributedFaithful pm initPM 5376) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1103 l12rpPmMPL9779
    9775 5376 9779 fw_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1104) (l12rp_pm_not_written 1104 9779 (by decide))
    (l12rp_nonempty_pm 1103) (l12rp_pm_not_written 1103 9775 (by decide))
    (l12rp_w5376_pm_drop 1103)
  intro s
  unfold l12rpPmMPL9779
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9775 5376 9779

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9730 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9730 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 9724)
        (denoteGraphDistributedFaithful pm initPM 5358) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1104 l12rpPmNL9730
    9724 5358 9730 fw_norm_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1105) (l12rp_pm_not_written 1105 9730 (by decide))
    (l12rp_nonempty_pm 1104) (l12rp_pm_not_written 1104 9724 (by decide))
    (l12rp_w5358_pm_drop 1104)
  intro s
  unfold l12rpPmNL9730
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 9724 5358 9730

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9748 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9748 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9744)
        (denoteGraphDistributedFaithful pm initPM 5367) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1105 l12rpPmMPL9748
    9744 5367 9748 fw_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1106) (l12rp_pm_not_written 1106 9748 (by decide))
    (l12rp_nonempty_pm 1105) (l12rp_pm_not_written 1105 9744 (by decide))
    (l12rp_w5367_pm_drop 1105)
  intro s
  unfold l12rpPmMPL9748
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9744 5367 9748

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9762 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9762 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9758)
        (denoteGraphDistributedFaithful pm initPM 5372) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1106 l12rpPmMPL9762
    9758 5372 9762 fw_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l12rp_nonempty_pm 1107) (l12rp_pm_not_written 1107 9762 (by decide))
    (l12rp_nonempty_pm 1106) (l12rp_pm_not_written 1106 9758 (by decide))
    (l12rp_w5372_pm_drop 1106)
  intro s
  unfold l12rpPmMPL9762
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9758 5372 9762

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_red_pm9780 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9780 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9776)
        (denoteGraphDistributedFaithful pm initPM 5376) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1107 l12rpPmMPL9780
    9776 5376 9780 fw_linear
    (by native_decide) l12rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l12rp_nonempty_pm 1108) (l12rp_pm_not_written 1108 9780 (by decide))
    (l12rp_nonempty_pm 1107) (l12rp_pm_not_written 1107 9776 (by decide))
    (l12rp_w5376_pm_drop 1107)
  intro s
  unfold l12rpPmMPL9780
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9776 5376 9780

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12rp_weight_eq (initSM initPM : Store)
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
private theorem l12rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5357_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5357)
      (denoteGraphDistributedFaithful pm initPM 9723)
      (denoteGraphDistributedFaithful pm initPM 9724)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8158_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12rp_red_sm5357 initSM, l12rp_red_pm9723 initPM, l12rp_red_pm9724 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5366_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5366)
      (denoteGraphDistributedFaithful pm initPM 9743)
      (denoteGraphDistributedFaithful pm initPM 9744)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8166_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12rp_red_sm5366 initSM, l12rp_red_pm9743 initPM, l12rp_red_pm9744 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5371_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5371)
      (denoteGraphDistributedFaithful pm initPM 9757)
      (denoteGraphDistributedFaithful pm initPM 9758)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8170_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12rp_red_sm5371 initSM, l12rp_red_pm9757 initPM, l12rp_red_pm9758 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5375_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5375)
      (denoteGraphDistributedFaithful pm initPM 9775)
      (denoteGraphDistributedFaithful pm initPM 9776)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8174_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12rp_red_sm5375 initSM, l12rp_red_pm9775 initPM, l12rp_red_pm9776 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5368_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5368)
      (denoteGraphDistributedFaithful pm initPM 9747)
      (denoteGraphDistributedFaithful pm initPM 9748)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5366_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5367 =
      denoteGraphDistributedFaithful pm initPM 5367 :=
    l12rp_weight_eq initSM initPM hInit 5367 initGoal_5367 (by native_decide)
      rfl rfl rfl rfl
      l12rp_weights_not_written.1.2.1 l12rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5367).shape = [1,1024] :=
    l12rp_pm_weight_shape initPM hPM 5367 [1,1024] (by native_decide)
      l12rp_weights_not_written.2.2.1
  rw [l12rp_red_sm5368 initSM, l12rp_red_pm9747 initPM, l12rp_red_pm9748 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5373_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5373)
      (denoteGraphDistributedFaithful pm initPM 9761)
      (denoteGraphDistributedFaithful pm initPM 9762)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5371_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5372 =
      denoteGraphDistributedFaithful pm initPM 5372 :=
    l12rp_weight_eq initSM initPM hInit 5372 initGoal_5372 (by native_decide)
      rfl rfl rfl rfl
      l12rp_weights_not_written.1.2.2.1 l12rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5372).shape = [512,1024] :=
    l12rp_pm_weight_shape initPM hPM 5372 [512,1024] (by native_decide)
      l12rp_weights_not_written.2.2.2.1
  rw [l12rp_red_sm5373 initSM, l12rp_red_pm9761 initPM, l12rp_red_pm9762 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5377_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5377)
      (denoteGraphDistributedFaithful pm initPM 9779)
      (denoteGraphDistributedFaithful pm initPM 9780)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5375_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5376 =
      denoteGraphDistributedFaithful pm initPM 5376 :=
    l12rp_weight_eq initSM initPM hInit 5376 initGoal_5376 (by native_decide)
      rfl rfl rfl rfl
      l12rp_weights_not_written.1.2.2.2 l12rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5376).shape = [512,1024] :=
    l12rp_pm_weight_shape initPM hPM 5376 [512,1024] (by native_decide)
      l12rp_weights_not_written.2.2.2.2.1
  rw [l12rp_red_sm5377 initSM, l12rp_red_pm9779 initPM, l12rp_red_pm9780 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5359_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5359)
      (denoteGraphDistributedFaithful pm initPM 9729)
      (denoteGraphDistributedFaithful pm initPM 9730)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5357_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5358 =
      denoteGraphDistributedFaithful pm initPM 5358 :=
    l12rp_weight_eq initSM initPM hInit 5358 initGoal_5358 (by native_decide)
      rfl rfl rfl rfl
      l12rp_weights_not_written.1.1 l12rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5358).shape = [64,1024] :=
    l12rp_pm_weight_shape initPM hPM 5358 [64,1024] (by native_decide)
      l12rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5345).shape = [2] :=
    l12rp_pm_weight_shape initPM hPM 5345 [2] (by native_decide)
      l12rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5345)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5345)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5357)
      (denoteGraphDistributedFaithful pm initPM 9723)
      (denoteGraphDistributedFaithful pm initPM 9724)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l12rp_red_sm5359 initSM, l12rp_red_pm9729 initPM, l12rp_red_pm9730 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec

end
end TrainVerify.Denote.GeneratedPatterns
