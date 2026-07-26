/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L16FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-4 MoE branch (router projections)

Mechanical transport of the (green) block-3 段 `L13FaithfulRouterProj` to block 4.
Every tensor id / node index is re-certified by `native_decide`.
The block-4 cu tensor is **5541**.

* SM 655 `FW_float [8314] → [5553]`                          (PM 1372 / 1376 → 10411 / 10412)
* SM 656 `FW_reshape [8322] → [5562]`                        (PM 1373 / 1377 → 10431 / 10432)
* SM 657 `FW_reshape [8326] → [5567]`                        (PM 1374 / 1378 → 10445 / 10446)
* SM 658 `FW_reshape [8330] → [5571]`                        (PM 1375 / 1379 → 10463 / 10464)
* SM 659 `FW_norm_linear [5553, 5554] → [5555]`              (PM 1380 / 1384 → 10417 / 10418)
* SM 660 `FW_mix_precision_linear [5562, 5563] → [5564]`     (PM 1381 / 1385 → 10435 / 10436)
* SM 661 `FW_mix_precision_linear [5567, 5568] → [5569]`     (PM 1382 / 1386 → 10449 / 10450)
* SM 662 `FW_mix_precision_linear [5571, 5572] → [5573]`     (PM 1383 / 1387 → 10467 / 10468)

Weights 5554 `[64,1024]`, 5563 `[1,1024]`, 5568 `[512,1024]`, 5572 `[512,1024]` are
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

private def l16rpSmFloat5553 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8314], outs := [5553] }
private def l16rpSmResh5562 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8322], outs := [5562],
    params := [4096,1024] }
private def l16rpSmResh5567 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8326], outs := [5567],
    params := [4096,1024] }
private def l16rpSmResh5571 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8330], outs := [5571],
    params := [4096,1024] }
private def l16rpSmNL5555 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5553,5554], outs := [5555] }
private def l16rpSmMPL5564 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5562,5563], outs := [5564] }
private def l16rpSmMPL5569 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5567,5568], outs := [5569] }
private def l16rpSmMPL5573 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5571,5572], outs := [5573] }

private def l16rpPmFloat10411 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16316], outs := [10411] }
private def l16rpPmResh10431 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16324], outs := [10431],
    params := [2048,1024] }
private def l16rpPmResh10445 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16328], outs := [10445],
    params := [2048,1024] }
private def l16rpPmResh10463 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16332], outs := [10463],
    params := [2048,1024] }
private def l16rpPmFloat10412 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16339], outs := [10412] }
private def l16rpPmResh10432 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16347], outs := [10432],
    params := [2048,1024] }
private def l16rpPmResh10446 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16351], outs := [10446],
    params := [2048,1024] }
private def l16rpPmResh10464 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16355], outs := [10464],
    params := [2048,1024] }
private def l16rpPmNL10417 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [10411,5554], outs := [10417] }
private def l16rpPmMPL10435 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10431,5563], outs := [10435] }
private def l16rpPmMPL10449 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10445,5568], outs := [10449] }
private def l16rpPmMPL10467 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10463,5572], outs := [10467] }
private def l16rpPmNL10418 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [10412,5554], outs := [10418] }
private def l16rpPmMPL10436 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10432,5563], outs := [10436] }
private def l16rpPmMPL10450 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10446,5568], outs := [10450] }
private def l16rpPmMPL10468 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10464,5572], outs := [10468] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l16rp_sm_node_facts :
    sm.nodes[655]'(by native_decide) = l16rpSmFloat5553 ∧
    sm.nodes[656]'(by native_decide) = l16rpSmResh5562 ∧
    sm.nodes[657]'(by native_decide) = l16rpSmResh5567 ∧
    sm.nodes[658]'(by native_decide) = l16rpSmResh5571 ∧
    sm.nodes[659]'(by native_decide) = l16rpSmNL5555 ∧
    sm.nodes[660]'(by native_decide) = l16rpSmMPL5564 ∧
    sm.nodes[661]'(by native_decide) = l16rpSmMPL5569 ∧
    sm.nodes[662]'(by native_decide) = l16rpSmMPL5573 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l16rp_pm_node_facts :
    pm.nodes[1372]'(by native_decide) = l16rpPmFloat10411 ∧
    pm.nodes[1373]'(by native_decide) = l16rpPmResh10431 ∧
    pm.nodes[1374]'(by native_decide) = l16rpPmResh10445 ∧
    pm.nodes[1375]'(by native_decide) = l16rpPmResh10463 ∧
    pm.nodes[1376]'(by native_decide) = l16rpPmFloat10412 ∧
    pm.nodes[1377]'(by native_decide) = l16rpPmResh10432 ∧
    pm.nodes[1378]'(by native_decide) = l16rpPmResh10446 ∧
    pm.nodes[1379]'(by native_decide) = l16rpPmResh10464 ∧
    pm.nodes[1380]'(by native_decide) = l16rpPmNL10417 ∧
    pm.nodes[1381]'(by native_decide) = l16rpPmMPL10435 ∧
    pm.nodes[1382]'(by native_decide) = l16rpPmMPL10449 ∧
    pm.nodes[1383]'(by native_decide) = l16rpPmMPL10467 ∧
    pm.nodes[1384]'(by native_decide) = l16rpPmNL10418 ∧
    pm.nodes[1385]'(by native_decide) = l16rpPmMPL10436 ∧
    pm.nodes[1386]'(by native_decide) = l16rpPmMPL10450 ∧
    pm.nodes[1387]'(by native_decide) = l16rpPmMPL10468 := by
  native_decide

private theorem l16rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l16rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l16rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5554 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5563 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5568 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5572 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5554 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5563 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5568 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5572 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5541 ∉ n.outs)) := by
  native_decide

private theorem l16rp_w5554_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5554 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l16rp_w5554_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5554 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l16rp_w5563_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5563 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l16rp_w5563_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5563 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l16rp_w5568_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5568 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l16rp_w5568_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5568 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l16rp_w5572_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5572 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l16rp_w5572_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5572 ∉ n.outs := by
  intro n hn
  exact l16rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l16rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(656, 5553), (655, 8314), (657, 5562), (656, 8322), (658, 5567), (657, 8326), (659, 5571), (658, 8330), (660, 5555), (659, 5553), (661, 5564), (660, 5562), (662, 5569), (661, 5567), (663, 5573), (662, 5571)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1373, 10411), (1372, 16316), (1374, 10431), (1373, 16324), (1375, 10445), (1374, 16328), (1376, 10463), (1375, 16332), (1377, 10412), (1376, 16339), (1378, 10432), (1377, 16347), (1379, 10446), (1378, 16351), (1380, 10464), (1379, 16355), (1381, 10417), (1380, 10411), (1382, 10435), (1381, 10431), (1383, 10449), (1382, 10445), (1384, 10467), (1383, 10463), (1385, 10418), (1384, 10412), (1386, 10436), (1385, 10432), (1387, 10450), (1386, 10446), (1388, 10468), (1387, 10464)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5553 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5553 =
      denoteGraphDistributedFaithful sm initSM 8314 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 655 l16rpSmFloat5553
    8314 5553 (fun x => x)
    (by native_decide) l16rp_sm_node_facts.1 ?_
    (l16rp_nonempty_sm 656) (l16rp_sm_not_written 656 5553 (by decide))
    (l16rp_nonempty_sm 655) (l16rp_sm_not_written 655 8314 (by decide))
  intro s
  unfold l16rpSmFloat5553
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8314 5553 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5562 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5562 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8322) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 656 l16rpSmResh5562
    8322 5562 (fun x => fw_view [4096,1024] x)
    (by native_decide) l16rp_sm_node_facts.2.1 ?_
    (l16rp_nonempty_sm 657) (l16rp_sm_not_written 657 5562 (by decide))
    (l16rp_nonempty_sm 656) (l16rp_sm_not_written 656 8322 (by decide))
  intro s
  unfold l16rpSmResh5562
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8322 5562 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5567 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5567 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8326) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 657 l16rpSmResh5567
    8326 5567 (fun x => fw_view [4096,1024] x)
    (by native_decide) l16rp_sm_node_facts.2.2.1 ?_
    (l16rp_nonempty_sm 658) (l16rp_sm_not_written 658 5567 (by decide))
    (l16rp_nonempty_sm 657) (l16rp_sm_not_written 657 8326 (by decide))
  intro s
  unfold l16rpSmResh5567
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8326 5567 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5571 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5571 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8330) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 658 l16rpSmResh5571
    8330 5571 (fun x => fw_view [4096,1024] x)
    (by native_decide) l16rp_sm_node_facts.2.2.2.1 ?_
    (l16rp_nonempty_sm 659) (l16rp_sm_not_written 659 5571 (by decide))
    (l16rp_nonempty_sm 658) (l16rp_sm_not_written 658 8330 (by decide))
  intro s
  unfold l16rpSmResh5571
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8330 5571 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5555 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5555 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5553)
        (denoteGraphDistributedFaithful sm initSM 5554) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 659 l16rpSmNL5555
    5553 5554 5555 fw_norm_linear
    (by native_decide) l16rp_sm_node_facts.2.2.2.2.1 ?_
    (l16rp_nonempty_sm 660) (l16rp_sm_not_written 660 5555 (by decide))
    (l16rp_nonempty_sm 659) (l16rp_sm_not_written 659 5553 (by decide))
    (l16rp_w5554_sm_drop 659)
  intro s
  unfold l16rpSmNL5555
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5553 5554 5555

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5564 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5564 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5562)
        (denoteGraphDistributedFaithful sm initSM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 660 l16rpSmMPL5564
    5562 5563 5564 fw_linear
    (by native_decide) l16rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l16rp_nonempty_sm 661) (l16rp_sm_not_written 661 5564 (by decide))
    (l16rp_nonempty_sm 660) (l16rp_sm_not_written 660 5562 (by decide))
    (l16rp_w5563_sm_drop 660)
  intro s
  unfold l16rpSmMPL5564
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5562 5563 5564

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5569 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5569 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5567)
        (denoteGraphDistributedFaithful sm initSM 5568) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 661 l16rpSmMPL5569
    5567 5568 5569 fw_linear
    (by native_decide) l16rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_sm 662) (l16rp_sm_not_written 662 5569 (by decide))
    (l16rp_nonempty_sm 661) (l16rp_sm_not_written 661 5567 (by decide))
    (l16rp_w5568_sm_drop 661)
  intro s
  unfold l16rpSmMPL5569
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5567 5568 5569

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_sm5573 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5573 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5571)
        (denoteGraphDistributedFaithful sm initSM 5572) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 662 l16rpSmMPL5573
    5571 5572 5573 fw_linear
    (by native_decide) l16rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l16rp_nonempty_sm 663) (l16rp_sm_not_written 663 5573 (by decide))
    (l16rp_nonempty_sm 662) (l16rp_sm_not_written 662 5571 (by decide))
    (l16rp_w5572_sm_drop 662)
  intro s
  unfold l16rpSmMPL5573
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5571 5572 5573

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10411 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10411 =
      denoteGraphDistributedFaithful pm initPM 16316 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1372 l16rpPmFloat10411
    16316 10411 (fun x => x)
    (by native_decide) l16rp_pm_node_facts.1 ?_
    (l16rp_nonempty_pm 1373) (l16rp_pm_not_written 1373 10411 (by decide))
    (l16rp_nonempty_pm 1372) (l16rp_pm_not_written 1372 16316 (by decide))
  intro s
  unfold l16rpPmFloat10411
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16316 10411 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10431 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10431 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16324) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1373 l16rpPmResh10431
    16324 10431 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16rp_pm_node_facts.2.1 ?_
    (l16rp_nonempty_pm 1374) (l16rp_pm_not_written 1374 10431 (by decide))
    (l16rp_nonempty_pm 1373) (l16rp_pm_not_written 1373 16324 (by decide))
  intro s
  unfold l16rpPmResh10431
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16324 10431 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10445 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10445 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16328) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1374 l16rpPmResh10445
    16328 10445 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16rp_pm_node_facts.2.2.1 ?_
    (l16rp_nonempty_pm 1375) (l16rp_pm_not_written 1375 10445 (by decide))
    (l16rp_nonempty_pm 1374) (l16rp_pm_not_written 1374 16328 (by decide))
  intro s
  unfold l16rpPmResh10445
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16328 10445 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10463 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10463 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16332) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1375 l16rpPmResh10463
    16332 10463 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16rp_pm_node_facts.2.2.2.1 ?_
    (l16rp_nonempty_pm 1376) (l16rp_pm_not_written 1376 10463 (by decide))
    (l16rp_nonempty_pm 1375) (l16rp_pm_not_written 1375 16332 (by decide))
  intro s
  unfold l16rpPmResh10463
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16332 10463 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10412 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10412 =
      denoteGraphDistributedFaithful pm initPM 16339 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1376 l16rpPmFloat10412
    16339 10412 (fun x => x)
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1377) (l16rp_pm_not_written 1377 10412 (by decide))
    (l16rp_nonempty_pm 1376) (l16rp_pm_not_written 1376 16339 (by decide))
  intro s
  unfold l16rpPmFloat10412
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16339 10412 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10432 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10432 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16347) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1377 l16rpPmResh10432
    16347 10432 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1378) (l16rp_pm_not_written 1378 10432 (by decide))
    (l16rp_nonempty_pm 1377) (l16rp_pm_not_written 1377 16347 (by decide))
  intro s
  unfold l16rpPmResh10432
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16347 10432 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10446 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10446 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16351) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1378 l16rpPmResh10446
    16351 10446 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1379) (l16rp_pm_not_written 1379 10446 (by decide))
    (l16rp_nonempty_pm 1378) (l16rp_pm_not_written 1378 16351 (by decide))
  intro s
  unfold l16rpPmResh10446
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16351 10446 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10464 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10464 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16355) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1379 l16rpPmResh10464
    16355 10464 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1380) (l16rp_pm_not_written 1380 10464 (by decide))
    (l16rp_nonempty_pm 1379) (l16rp_pm_not_written 1379 16355 (by decide))
  intro s
  unfold l16rpPmResh10464
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16355 10464 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10417 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10417 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10411)
        (denoteGraphDistributedFaithful pm initPM 5554) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1380 l16rpPmNL10417
    10411 5554 10417 fw_norm_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1381) (l16rp_pm_not_written 1381 10417 (by decide))
    (l16rp_nonempty_pm 1380) (l16rp_pm_not_written 1380 10411 (by decide))
    (l16rp_w5554_pm_drop 1380)
  intro s
  unfold l16rpPmNL10417
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 10411 5554 10417

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10435 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10435 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10431)
        (denoteGraphDistributedFaithful pm initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1381 l16rpPmMPL10435
    10431 5563 10435 fw_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1382) (l16rp_pm_not_written 1382 10435 (by decide))
    (l16rp_nonempty_pm 1381) (l16rp_pm_not_written 1381 10431 (by decide))
    (l16rp_w5563_pm_drop 1381)
  intro s
  unfold l16rpPmMPL10435
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10431 5563 10435

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10449 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10449 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10445)
        (denoteGraphDistributedFaithful pm initPM 5568) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1382 l16rpPmMPL10449
    10445 5568 10449 fw_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1383) (l16rp_pm_not_written 1383 10449 (by decide))
    (l16rp_nonempty_pm 1382) (l16rp_pm_not_written 1382 10445 (by decide))
    (l16rp_w5568_pm_drop 1382)
  intro s
  unfold l16rpPmMPL10449
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10445 5568 10449

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10467 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10467 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10463)
        (denoteGraphDistributedFaithful pm initPM 5572) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1383 l16rpPmMPL10467
    10463 5572 10467 fw_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1384) (l16rp_pm_not_written 1384 10467 (by decide))
    (l16rp_nonempty_pm 1383) (l16rp_pm_not_written 1383 10463 (by decide))
    (l16rp_w5572_pm_drop 1383)
  intro s
  unfold l16rpPmMPL10467
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10463 5572 10467

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10418 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10418 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10412)
        (denoteGraphDistributedFaithful pm initPM 5554) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1384 l16rpPmNL10418
    10412 5554 10418 fw_norm_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1385) (l16rp_pm_not_written 1385 10418 (by decide))
    (l16rp_nonempty_pm 1384) (l16rp_pm_not_written 1384 10412 (by decide))
    (l16rp_w5554_pm_drop 1384)
  intro s
  unfold l16rpPmNL10418
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 10412 5554 10418

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10436 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10436 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10432)
        (denoteGraphDistributedFaithful pm initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1385 l16rpPmMPL10436
    10432 5563 10436 fw_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1386) (l16rp_pm_not_written 1386 10436 (by decide))
    (l16rp_nonempty_pm 1385) (l16rp_pm_not_written 1385 10432 (by decide))
    (l16rp_w5563_pm_drop 1385)
  intro s
  unfold l16rpPmMPL10436
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10432 5563 10436

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10450 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10450 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10446)
        (denoteGraphDistributedFaithful pm initPM 5568) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1386 l16rpPmMPL10450
    10446 5568 10450 fw_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16rp_nonempty_pm 1387) (l16rp_pm_not_written 1387 10450 (by decide))
    (l16rp_nonempty_pm 1386) (l16rp_pm_not_written 1386 10446 (by decide))
    (l16rp_w5568_pm_drop 1386)
  intro s
  unfold l16rpPmMPL10450
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10446 5568 10450

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_red_pm10468 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10468 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10464)
        (denoteGraphDistributedFaithful pm initPM 5572) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1387 l16rpPmMPL10468
    10464 5572 10468 fw_linear
    (by native_decide) l16rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16rp_nonempty_pm 1388) (l16rp_pm_not_written 1388 10468 (by decide))
    (l16rp_nonempty_pm 1387) (l16rp_pm_not_written 1387 10464 (by decide))
    (l16rp_w5572_pm_drop 1387)
  intro s
  unfold l16rpPmMPL10468
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10464 5572 10468

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16rp_weight_eq (initSM initPM : Store)
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
private theorem l16rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5553_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5553)
      (denoteGraphDistributedFaithful pm initPM 10411)
      (denoteGraphDistributedFaithful pm initPM 10412)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8314_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16rp_red_sm5553 initSM, l16rp_red_pm10411 initPM, l16rp_red_pm10412 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5562_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5562)
      (denoteGraphDistributedFaithful pm initPM 10431)
      (denoteGraphDistributedFaithful pm initPM 10432)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8322_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16rp_red_sm5562 initSM, l16rp_red_pm10431 initPM, l16rp_red_pm10432 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5567_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5567)
      (denoteGraphDistributedFaithful pm initPM 10445)
      (denoteGraphDistributedFaithful pm initPM 10446)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8326_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16rp_red_sm5567 initSM, l16rp_red_pm10445 initPM, l16rp_red_pm10446 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5571_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5571)
      (denoteGraphDistributedFaithful pm initPM 10463)
      (denoteGraphDistributedFaithful pm initPM 10464)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8330_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16rp_red_sm5571 initSM, l16rp_red_pm10463 initPM, l16rp_red_pm10464 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5564_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5564)
      (denoteGraphDistributedFaithful pm initPM 10435)
      (denoteGraphDistributedFaithful pm initPM 10436)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5562_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5563 =
      denoteGraphDistributedFaithful pm initPM 5563 :=
    l16rp_weight_eq initSM initPM hInit 5563 initGoal_5563 (by native_decide)
      rfl rfl rfl rfl
      l16rp_weights_not_written.1.2.1 l16rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5563).shape = [1,1024] :=
    l16rp_pm_weight_shape initPM hPM 5563 [1,1024] (by native_decide)
      l16rp_weights_not_written.2.2.1
  rw [l16rp_red_sm5564 initSM, l16rp_red_pm10435 initPM, l16rp_red_pm10436 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5569_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5569)
      (denoteGraphDistributedFaithful pm initPM 10449)
      (denoteGraphDistributedFaithful pm initPM 10450)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5567_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5568 =
      denoteGraphDistributedFaithful pm initPM 5568 :=
    l16rp_weight_eq initSM initPM hInit 5568 initGoal_5568 (by native_decide)
      rfl rfl rfl rfl
      l16rp_weights_not_written.1.2.2.1 l16rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5568).shape = [512,1024] :=
    l16rp_pm_weight_shape initPM hPM 5568 [512,1024] (by native_decide)
      l16rp_weights_not_written.2.2.2.1
  rw [l16rp_red_sm5569 initSM, l16rp_red_pm10449 initPM, l16rp_red_pm10450 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5573_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5573)
      (denoteGraphDistributedFaithful pm initPM 10467)
      (denoteGraphDistributedFaithful pm initPM 10468)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5571_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5572 =
      denoteGraphDistributedFaithful pm initPM 5572 :=
    l16rp_weight_eq initSM initPM hInit 5572 initGoal_5572 (by native_decide)
      rfl rfl rfl rfl
      l16rp_weights_not_written.1.2.2.2 l16rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5572).shape = [512,1024] :=
    l16rp_pm_weight_shape initPM hPM 5572 [512,1024] (by native_decide)
      l16rp_weights_not_written.2.2.2.2.1
  rw [l16rp_red_sm5573 initSM, l16rp_red_pm10467 initPM, l16rp_red_pm10468 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5555_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5555)
      (denoteGraphDistributedFaithful pm initPM 10417)
      (denoteGraphDistributedFaithful pm initPM 10418)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5553_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5554 =
      denoteGraphDistributedFaithful pm initPM 5554 :=
    l16rp_weight_eq initSM initPM hInit 5554 initGoal_5554 (by native_decide)
      rfl rfl rfl rfl
      l16rp_weights_not_written.1.1 l16rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5554).shape = [64,1024] :=
    l16rp_pm_weight_shape initPM hPM 5554 [64,1024] (by native_decide)
      l16rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5541).shape = [2] :=
    l16rp_pm_weight_shape initPM hPM 5541 [2] (by native_decide)
      l16rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5541)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5541)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5553)
      (denoteGraphDistributedFaithful pm initPM 10411)
      (denoteGraphDistributedFaithful pm initPM 10412)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l16rp_red_sm5555 initSM, l16rp_red_pm10417 initPM, l16rp_red_pm10418 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
