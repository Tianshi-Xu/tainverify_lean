/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L15FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-3 MoE branch (router projections)

Mechanical transport of the (green) block-2 段 `L13FaithfulRouterProj` to block 3.
Every tensor id / node index is re-certified by `native_decide`.
The block-3 cu tensor is **5492**.

* SM 620 `FW_float [8275] → [5504]`                          (PM 1302 / 1306 → 10239 / 10240)
* SM 621 `FW_reshape [8283] → [5513]`                        (PM 1303 / 1307 → 10259 / 10260)
* SM 622 `FW_reshape [8287] → [5518]`                        (PM 1304 / 1308 → 10273 / 10274)
* SM 623 `FW_reshape [8291] → [5522]`                        (PM 1305 / 1309 → 10291 / 10292)
* SM 624 `FW_norm_linear [5504, 5505] → [5506]`              (PM 1310 / 1314 → 10245 / 10246)
* SM 625 `FW_mix_precision_linear [5513, 5514] → [5515]`     (PM 1311 / 1315 → 10263 / 10264)
* SM 626 `FW_mix_precision_linear [5518, 5519] → [5520]`     (PM 1312 / 1316 → 10277 / 10278)
* SM 627 `FW_mix_precision_linear [5522, 5523] → [5524]`     (PM 1313 / 1317 → 10295 / 10296)

Weights 5505 `[64,1024]`, 5514 `[1,1024]`, 5519 `[512,1024]`, 5523 `[512,1024]` are
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

private def l15rpSmFloat5504 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8275], outs := [5504] }
private def l15rpSmResh5513 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8283], outs := [5513],
    params := [4096,1024] }
private def l15rpSmResh5518 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8287], outs := [5518],
    params := [4096,1024] }
private def l15rpSmResh5522 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8291], outs := [5522],
    params := [4096,1024] }
private def l15rpSmNL5506 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5504,5505], outs := [5506] }
private def l15rpSmMPL5515 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5513,5514], outs := [5515] }
private def l15rpSmMPL5520 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5518,5519], outs := [5520] }
private def l15rpSmMPL5524 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5522,5523], outs := [5524] }

private def l15rpPmFloat10239 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16238], outs := [10239] }
private def l15rpPmResh10259 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16246], outs := [10259],
    params := [2048,1024] }
private def l15rpPmResh10273 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16250], outs := [10273],
    params := [2048,1024] }
private def l15rpPmResh10291 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16254], outs := [10291],
    params := [2048,1024] }
private def l15rpPmFloat10240 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16261], outs := [10240] }
private def l15rpPmResh10260 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16269], outs := [10260],
    params := [2048,1024] }
private def l15rpPmResh10274 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16273], outs := [10274],
    params := [2048,1024] }
private def l15rpPmResh10292 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16277], outs := [10292],
    params := [2048,1024] }
private def l15rpPmNL10245 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [10239,5505], outs := [10245] }
private def l15rpPmMPL10263 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10259,5514], outs := [10263] }
private def l15rpPmMPL10277 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10273,5519], outs := [10277] }
private def l15rpPmMPL10295 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10291,5523], outs := [10295] }
private def l15rpPmNL10246 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [10240,5505], outs := [10246] }
private def l15rpPmMPL10264 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10260,5514], outs := [10264] }
private def l15rpPmMPL10278 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10274,5519], outs := [10278] }
private def l15rpPmMPL10296 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10292,5523], outs := [10296] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l15rp_sm_node_facts :
    sm.nodes[620]'(by native_decide) = l15rpSmFloat5504 ∧
    sm.nodes[621]'(by native_decide) = l15rpSmResh5513 ∧
    sm.nodes[622]'(by native_decide) = l15rpSmResh5518 ∧
    sm.nodes[623]'(by native_decide) = l15rpSmResh5522 ∧
    sm.nodes[624]'(by native_decide) = l15rpSmNL5506 ∧
    sm.nodes[625]'(by native_decide) = l15rpSmMPL5515 ∧
    sm.nodes[626]'(by native_decide) = l15rpSmMPL5520 ∧
    sm.nodes[627]'(by native_decide) = l15rpSmMPL5524 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l15rp_pm_node_facts :
    pm.nodes[1302]'(by native_decide) = l15rpPmFloat10239 ∧
    pm.nodes[1303]'(by native_decide) = l15rpPmResh10259 ∧
    pm.nodes[1304]'(by native_decide) = l15rpPmResh10273 ∧
    pm.nodes[1305]'(by native_decide) = l15rpPmResh10291 ∧
    pm.nodes[1306]'(by native_decide) = l15rpPmFloat10240 ∧
    pm.nodes[1307]'(by native_decide) = l15rpPmResh10260 ∧
    pm.nodes[1308]'(by native_decide) = l15rpPmResh10274 ∧
    pm.nodes[1309]'(by native_decide) = l15rpPmResh10292 ∧
    pm.nodes[1310]'(by native_decide) = l15rpPmNL10245 ∧
    pm.nodes[1311]'(by native_decide) = l15rpPmMPL10263 ∧
    pm.nodes[1312]'(by native_decide) = l15rpPmMPL10277 ∧
    pm.nodes[1313]'(by native_decide) = l15rpPmMPL10295 ∧
    pm.nodes[1314]'(by native_decide) = l15rpPmNL10246 ∧
    pm.nodes[1315]'(by native_decide) = l15rpPmMPL10264 ∧
    pm.nodes[1316]'(by native_decide) = l15rpPmMPL10278 ∧
    pm.nodes[1317]'(by native_decide) = l15rpPmMPL10296 := by
  native_decide

private theorem l15rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l15rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l15rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5505 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5514 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5519 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5523 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5505 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5514 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5519 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5523 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5492 ∉ n.outs)) := by
  native_decide

private theorem l15rp_w5505_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5505 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l15rp_w5505_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5505 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l15rp_w5514_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5514 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l15rp_w5514_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5514 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l15rp_w5519_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5519 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l15rp_w5519_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5519 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l15rp_w5523_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5523 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l15rp_w5523_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5523 ∉ n.outs := by
  intro n hn
  exact l15rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l15rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(621, 5504), (620, 8275), (622, 5513), (621, 8283), (623, 5518), (622, 8287), (624, 5522), (623, 8291), (625, 5506), (624, 5504), (626, 5515), (625, 5513), (627, 5520), (626, 5518), (628, 5524), (627, 5522)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l15rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1303, 10239), (1302, 16238), (1304, 10259), (1303, 16246), (1305, 10273), (1304, 16250), (1306, 10291), (1305, 16254), (1307, 10240), (1306, 16261), (1308, 10260), (1307, 16269), (1309, 10274), (1308, 16273), (1310, 10292), (1309, 16277), (1311, 10245), (1310, 10239), (1312, 10263), (1311, 10259), (1313, 10277), (1312, 10273), (1314, 10295), (1313, 10291), (1315, 10246), (1314, 10240), (1316, 10264), (1315, 10260), (1317, 10278), (1316, 10274), (1318, 10296), (1317, 10292)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5504 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5504 =
      denoteGraphDistributedFaithful sm initSM 8275 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 620 l15rpSmFloat5504
    8275 5504 (fun x => x)
    (by native_decide) l15rp_sm_node_facts.1 ?_
    (l15rp_nonempty_sm 621) (l15rp_sm_not_written 621 5504 (by decide))
    (l15rp_nonempty_sm 620) (l15rp_sm_not_written 620 8275 (by decide))
  intro s
  unfold l15rpSmFloat5504
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8275 5504 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5513 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5513 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8283) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 621 l15rpSmResh5513
    8283 5513 (fun x => fw_view [4096,1024] x)
    (by native_decide) l15rp_sm_node_facts.2.1 ?_
    (l15rp_nonempty_sm 622) (l15rp_sm_not_written 622 5513 (by decide))
    (l15rp_nonempty_sm 621) (l15rp_sm_not_written 621 8283 (by decide))
  intro s
  unfold l15rpSmResh5513
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8283 5513 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5518 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5518 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8287) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 622 l15rpSmResh5518
    8287 5518 (fun x => fw_view [4096,1024] x)
    (by native_decide) l15rp_sm_node_facts.2.2.1 ?_
    (l15rp_nonempty_sm 623) (l15rp_sm_not_written 623 5518 (by decide))
    (l15rp_nonempty_sm 622) (l15rp_sm_not_written 622 8287 (by decide))
  intro s
  unfold l15rpSmResh5518
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8287 5518 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5522 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5522 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8291) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 623 l15rpSmResh5522
    8291 5522 (fun x => fw_view [4096,1024] x)
    (by native_decide) l15rp_sm_node_facts.2.2.2.1 ?_
    (l15rp_nonempty_sm 624) (l15rp_sm_not_written 624 5522 (by decide))
    (l15rp_nonempty_sm 623) (l15rp_sm_not_written 623 8291 (by decide))
  intro s
  unfold l15rpSmResh5522
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8291 5522 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5506 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5506 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5504)
        (denoteGraphDistributedFaithful sm initSM 5505) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 624 l15rpSmNL5506
    5504 5505 5506 fw_norm_linear
    (by native_decide) l15rp_sm_node_facts.2.2.2.2.1 ?_
    (l15rp_nonempty_sm 625) (l15rp_sm_not_written 625 5506 (by decide))
    (l15rp_nonempty_sm 624) (l15rp_sm_not_written 624 5504 (by decide))
    (l15rp_w5505_sm_drop 624)
  intro s
  unfold l15rpSmNL5506
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5504 5505 5506

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5515 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5515 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5513)
        (denoteGraphDistributedFaithful sm initSM 5514) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 625 l15rpSmMPL5515
    5513 5514 5515 fw_linear
    (by native_decide) l15rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l15rp_nonempty_sm 626) (l15rp_sm_not_written 626 5515 (by decide))
    (l15rp_nonempty_sm 625) (l15rp_sm_not_written 625 5513 (by decide))
    (l15rp_w5514_sm_drop 625)
  intro s
  unfold l15rpSmMPL5515
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5513 5514 5515

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5520 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5520 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5518)
        (denoteGraphDistributedFaithful sm initSM 5519) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 626 l15rpSmMPL5520
    5518 5519 5520 fw_linear
    (by native_decide) l15rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_sm 627) (l15rp_sm_not_written 627 5520 (by decide))
    (l15rp_nonempty_sm 626) (l15rp_sm_not_written 626 5518 (by decide))
    (l15rp_w5519_sm_drop 626)
  intro s
  unfold l15rpSmMPL5520
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5518 5519 5520

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_sm5524 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5524 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5522)
        (denoteGraphDistributedFaithful sm initSM 5523) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 627 l15rpSmMPL5524
    5522 5523 5524 fw_linear
    (by native_decide) l15rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l15rp_nonempty_sm 628) (l15rp_sm_not_written 628 5524 (by decide))
    (l15rp_nonempty_sm 627) (l15rp_sm_not_written 627 5522 (by decide))
    (l15rp_w5523_sm_drop 627)
  intro s
  unfold l15rpSmMPL5524
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5522 5523 5524

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10239 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10239 =
      denoteGraphDistributedFaithful pm initPM 16238 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1302 l15rpPmFloat10239
    16238 10239 (fun x => x)
    (by native_decide) l15rp_pm_node_facts.1 ?_
    (l15rp_nonempty_pm 1303) (l15rp_pm_not_written 1303 10239 (by decide))
    (l15rp_nonempty_pm 1302) (l15rp_pm_not_written 1302 16238 (by decide))
  intro s
  unfold l15rpPmFloat10239
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16238 10239 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10259 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10259 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16246) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1303 l15rpPmResh10259
    16246 10259 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15rp_pm_node_facts.2.1 ?_
    (l15rp_nonempty_pm 1304) (l15rp_pm_not_written 1304 10259 (by decide))
    (l15rp_nonempty_pm 1303) (l15rp_pm_not_written 1303 16246 (by decide))
  intro s
  unfold l15rpPmResh10259
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16246 10259 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10273 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10273 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16250) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1304 l15rpPmResh10273
    16250 10273 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15rp_pm_node_facts.2.2.1 ?_
    (l15rp_nonempty_pm 1305) (l15rp_pm_not_written 1305 10273 (by decide))
    (l15rp_nonempty_pm 1304) (l15rp_pm_not_written 1304 16250 (by decide))
  intro s
  unfold l15rpPmResh10273
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16250 10273 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10291 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10291 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16254) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1305 l15rpPmResh10291
    16254 10291 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15rp_pm_node_facts.2.2.2.1 ?_
    (l15rp_nonempty_pm 1306) (l15rp_pm_not_written 1306 10291 (by decide))
    (l15rp_nonempty_pm 1305) (l15rp_pm_not_written 1305 16254 (by decide))
  intro s
  unfold l15rpPmResh10291
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16254 10291 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10240 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10240 =
      denoteGraphDistributedFaithful pm initPM 16261 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1306 l15rpPmFloat10240
    16261 10240 (fun x => x)
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1307) (l15rp_pm_not_written 1307 10240 (by decide))
    (l15rp_nonempty_pm 1306) (l15rp_pm_not_written 1306 16261 (by decide))
  intro s
  unfold l15rpPmFloat10240
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16261 10240 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10260 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10260 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16269) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1307 l15rpPmResh10260
    16269 10260 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1308) (l15rp_pm_not_written 1308 10260 (by decide))
    (l15rp_nonempty_pm 1307) (l15rp_pm_not_written 1307 16269 (by decide))
  intro s
  unfold l15rpPmResh10260
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16269 10260 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10274 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10274 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16273) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1308 l15rpPmResh10274
    16273 10274 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1309) (l15rp_pm_not_written 1309 10274 (by decide))
    (l15rp_nonempty_pm 1308) (l15rp_pm_not_written 1308 16273 (by decide))
  intro s
  unfold l15rpPmResh10274
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16273 10274 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10292 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10292 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16277) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1309 l15rpPmResh10292
    16277 10292 (fun x => fw_view [2048,1024] x)
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1310) (l15rp_pm_not_written 1310 10292 (by decide))
    (l15rp_nonempty_pm 1309) (l15rp_pm_not_written 1309 16277 (by decide))
  intro s
  unfold l15rpPmResh10292
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16277 10292 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10245 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10245 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10239)
        (denoteGraphDistributedFaithful pm initPM 5505) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1310 l15rpPmNL10245
    10239 5505 10245 fw_norm_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1311) (l15rp_pm_not_written 1311 10245 (by decide))
    (l15rp_nonempty_pm 1310) (l15rp_pm_not_written 1310 10239 (by decide))
    (l15rp_w5505_pm_drop 1310)
  intro s
  unfold l15rpPmNL10245
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 10239 5505 10245

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10263 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10263 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10259)
        (denoteGraphDistributedFaithful pm initPM 5514) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1311 l15rpPmMPL10263
    10259 5514 10263 fw_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1312) (l15rp_pm_not_written 1312 10263 (by decide))
    (l15rp_nonempty_pm 1311) (l15rp_pm_not_written 1311 10259 (by decide))
    (l15rp_w5514_pm_drop 1311)
  intro s
  unfold l15rpPmMPL10263
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10259 5514 10263

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10277 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10277 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10273)
        (denoteGraphDistributedFaithful pm initPM 5519) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1312 l15rpPmMPL10277
    10273 5519 10277 fw_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1313) (l15rp_pm_not_written 1313 10277 (by decide))
    (l15rp_nonempty_pm 1312) (l15rp_pm_not_written 1312 10273 (by decide))
    (l15rp_w5519_pm_drop 1312)
  intro s
  unfold l15rpPmMPL10277
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10273 5519 10277

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10295 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10295 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10291)
        (denoteGraphDistributedFaithful pm initPM 5523) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1313 l15rpPmMPL10295
    10291 5523 10295 fw_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1314) (l15rp_pm_not_written 1314 10295 (by decide))
    (l15rp_nonempty_pm 1313) (l15rp_pm_not_written 1313 10291 (by decide))
    (l15rp_w5523_pm_drop 1313)
  intro s
  unfold l15rpPmMPL10295
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10291 5523 10295

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10246 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10246 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 10240)
        (denoteGraphDistributedFaithful pm initPM 5505) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1314 l15rpPmNL10246
    10240 5505 10246 fw_norm_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1315) (l15rp_pm_not_written 1315 10246 (by decide))
    (l15rp_nonempty_pm 1314) (l15rp_pm_not_written 1314 10240 (by decide))
    (l15rp_w5505_pm_drop 1314)
  intro s
  unfold l15rpPmNL10246
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 10240 5505 10246

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10264 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10264 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10260)
        (denoteGraphDistributedFaithful pm initPM 5514) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1315 l15rpPmMPL10264
    10260 5514 10264 fw_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1316) (l15rp_pm_not_written 1316 10264 (by decide))
    (l15rp_nonempty_pm 1315) (l15rp_pm_not_written 1315 10260 (by decide))
    (l15rp_w5514_pm_drop 1315)
  intro s
  unfold l15rpPmMPL10264
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10260 5514 10264

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10278 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10278 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10274)
        (denoteGraphDistributedFaithful pm initPM 5519) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1316 l15rpPmMPL10278
    10274 5519 10278 fw_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l15rp_nonempty_pm 1317) (l15rp_pm_not_written 1317 10278 (by decide))
    (l15rp_nonempty_pm 1316) (l15rp_pm_not_written 1316 10274 (by decide))
    (l15rp_w5519_pm_drop 1316)
  intro s
  unfold l15rpPmMPL10278
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10274 5519 10278

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_red_pm10296 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10296 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10292)
        (denoteGraphDistributedFaithful pm initPM 5523) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1317 l15rpPmMPL10296
    10292 5523 10296 fw_linear
    (by native_decide) l15rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l15rp_nonempty_pm 1318) (l15rp_pm_not_written 1318 10296 (by decide))
    (l15rp_nonempty_pm 1317) (l15rp_pm_not_written 1317 10292 (by decide))
    (l15rp_w5523_pm_drop 1317)
  intro s
  unfold l15rpPmMPL10296
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10292 5523 10296

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l15rp_weight_eq (initSM initPM : Store)
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
private theorem l15rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5504_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5504)
      (denoteGraphDistributedFaithful pm initPM 10239)
      (denoteGraphDistributedFaithful pm initPM 10240)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8275_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15rp_red_sm5504 initSM, l15rp_red_pm10239 initPM, l15rp_red_pm10240 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5513_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5513)
      (denoteGraphDistributedFaithful pm initPM 10259)
      (denoteGraphDistributedFaithful pm initPM 10260)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8283_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15rp_red_sm5513 initSM, l15rp_red_pm10259 initPM, l15rp_red_pm10260 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5518_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5518)
      (denoteGraphDistributedFaithful pm initPM 10273)
      (denoteGraphDistributedFaithful pm initPM 10274)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8287_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15rp_red_sm5518 initSM, l15rp_red_pm10273 initPM, l15rp_red_pm10274 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5522_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5522)
      (denoteGraphDistributedFaithful pm initPM 10291)
      (denoteGraphDistributedFaithful pm initPM 10292)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8291_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l15rp_red_sm5522 initSM, l15rp_red_pm10291 initPM, l15rp_red_pm10292 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5515_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5515)
      (denoteGraphDistributedFaithful pm initPM 10263)
      (denoteGraphDistributedFaithful pm initPM 10264)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5513_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5514 =
      denoteGraphDistributedFaithful pm initPM 5514 :=
    l15rp_weight_eq initSM initPM hInit 5514 initGoal_5514 (by native_decide)
      rfl rfl rfl rfl
      l15rp_weights_not_written.1.2.1 l15rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5514).shape = [1,1024] :=
    l15rp_pm_weight_shape initPM hPM 5514 [1,1024] (by native_decide)
      l15rp_weights_not_written.2.2.1
  rw [l15rp_red_sm5515 initSM, l15rp_red_pm10263 initPM, l15rp_red_pm10264 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5520_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5520)
      (denoteGraphDistributedFaithful pm initPM 10277)
      (denoteGraphDistributedFaithful pm initPM 10278)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5518_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5519 =
      denoteGraphDistributedFaithful pm initPM 5519 :=
    l15rp_weight_eq initSM initPM hInit 5519 initGoal_5519 (by native_decide)
      rfl rfl rfl rfl
      l15rp_weights_not_written.1.2.2.1 l15rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5519).shape = [512,1024] :=
    l15rp_pm_weight_shape initPM hPM 5519 [512,1024] (by native_decide)
      l15rp_weights_not_written.2.2.2.1
  rw [l15rp_red_sm5520 initSM, l15rp_red_pm10277 initPM, l15rp_red_pm10278 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5524_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5524)
      (denoteGraphDistributedFaithful pm initPM 10295)
      (denoteGraphDistributedFaithful pm initPM 10296)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5522_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5523 =
      denoteGraphDistributedFaithful pm initPM 5523 :=
    l15rp_weight_eq initSM initPM hInit 5523 initGoal_5523 (by native_decide)
      rfl rfl rfl rfl
      l15rp_weights_not_written.1.2.2.2 l15rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5523).shape = [512,1024] :=
    l15rp_pm_weight_shape initPM hPM 5523 [512,1024] (by native_decide)
      l15rp_weights_not_written.2.2.2.2.1
  rw [l15rp_red_sm5524 initSM, l15rp_red_pm10295 initPM, l15rp_red_pm10296 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5506_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5506)
      (denoteGraphDistributedFaithful pm initPM 10245)
      (denoteGraphDistributedFaithful pm initPM 10246)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5504_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5505 =
      denoteGraphDistributedFaithful pm initPM 5505 :=
    l15rp_weight_eq initSM initPM hInit 5505 initGoal_5505 (by native_decide)
      rfl rfl rfl rfl
      l15rp_weights_not_written.1.1 l15rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5505).shape = [64,1024] :=
    l15rp_pm_weight_shape initPM hPM 5505 [64,1024] (by native_decide)
      l15rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5492).shape = [2] :=
    l15rp_pm_weight_shape initPM hPM 5492 [2] (by native_decide)
      l15rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5492)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5492)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5504)
      (denoteGraphDistributedFaithful pm initPM 10239)
      (denoteGraphDistributedFaithful pm initPM 10240)
      (denoteGraphDistributedFaithful pm initPM 5492)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l15rp_red_sm5506 initSM, l15rp_red_pm10245 initPM, l15rp_red_pm10246 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
