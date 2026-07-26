/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L13FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-1 MoE branch (router projections + topk / gate / swiglu)

Mechanical transport of the (green) block-0 段 `L12FaithfulRouterProj` +
`L12FaithfulMoEBranch` to block 1.  SM node indices shift by `+35`, PM node
indices by `+70`; every tensor id is re-certified by `native_decide`.

Upper half (router / gate / up projections):

* SM 550 `FW_float [8197] → [5406]`                          (PM 1162 / 1166 → 9895 / 9896)
* SM 551 `FW_reshape [8205] → [5415]`                        (PM 1163 / 1167 → 9915 / 9916)
* SM 552 `FW_reshape [8209] → [5420]`                        (PM 1164 / 1168 → 9929 / 9930)
* SM 553 `FW_reshape [8213] → [5424]`                        (PM 1165 / 1169 → 9947 / 9948)
* SM 554 `FW_norm_linear [5406, 5407] → [5408]`              (PM 1170 / 1174 → 9901 / 9902)
* SM 555 `FW_mix_precision_linear [5415, 5416] → [5417]`     (PM 1171 / 1175 → 9919 / 9920)
* SM 556 `FW_mix_precision_linear [5420, 5421] → [5422]`     (PM 1172 / 1176 → 9933 / 9934)
* SM 557 `FW_mix_precision_linear [5424, 5425] → [5426]`     (PM 1173 / 1177 → 9951 / 9952)

Lower half (topk / views / sigmoid / swiglu):

* SM 558 `FW_topk_routing [5408] → [5409, 5410, 5411]` params `[8, 1]`
    (PM 1178 / 1182 → `9903, 9905, 9907` / `9904, 9906, 9908`)
* SM 559 `FW_view [5417] → [5418]` params `[4096, 1]`        (PM 1179 / 1183 → 9925 / 9926)
* SM 560 `FW_view [5422] → [5423]` params `[4096, 512]`      (PM 1180 / 1184 → 9943 / 9944)
* SM 561 `FW_view [5426] → [5427]` params `[4096, 512]`      (PM 1181 / 1185 → 9961 / 9962)
* SM 563 `FW_sigmoid [5418] → [5419]`                        (PM 1187 / 1190 → 9927 / 9928)
* SM 564 `FW_swiglu [5423, 5427] → [5428]`                   (PM 1188 / 1191 → 9965 / 9966)

Weights 5407 `[64,1024]`, 5416 `[1,1024]`, 5421 `[512,1024]`, 5425 `[512,1024]` are
replicated singletons.  The third `FW_topk_routing` output (`5411`) has no intermediate
goal and is therefore not exported, but the node reduction handles all three outputs.

The `hdec : decodeCuSeqlens cu = [0, 2 * 2048]` side condition of the router lemmas is
**derived** from the ambient `hCu` chain (via the parent relation's `cu_wf` payload plus
the `[2]` shape of the cu tensor 5345).  No new hypotheses are introduced: every theorem
below takes literally the same five parameters as its block-0 counterpart.
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

private def l13rpSmFloat5406 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8197], outs := [5406] }
private def l13rpSmResh5415 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8205], outs := [5415],
    params := [4096,1024] }
private def l13rpSmResh5420 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8209], outs := [5420],
    params := [4096,1024] }
private def l13rpSmResh5424 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8213], outs := [5424],
    params := [4096,1024] }
private def l13rpSmNL5408 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5406,5407], outs := [5408] }
private def l13rpSmMPL5417 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5415,5416], outs := [5417] }
private def l13rpSmMPL5422 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5420,5421], outs := [5422] }
private def l13rpSmMPL5426 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5424,5425], outs := [5426] }

private def l13rpPmFloat9895 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16082], outs := [9895] }
private def l13rpPmResh9915 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16090], outs := [9915],
    params := [2048,1024] }
private def l13rpPmResh9929 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16094], outs := [9929],
    params := [2048,1024] }
private def l13rpPmResh9947 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16098], outs := [9947],
    params := [2048,1024] }
private def l13rpPmFloat9896 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16105], outs := [9896] }
private def l13rpPmResh9916 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16113], outs := [9916],
    params := [2048,1024] }
private def l13rpPmResh9930 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16117], outs := [9930],
    params := [2048,1024] }
private def l13rpPmResh9948 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16121], outs := [9948],
    params := [2048,1024] }
private def l13rpPmNL9901 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [9895,5407], outs := [9901] }
private def l13rpPmMPL9919 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9915,5416], outs := [9919] }
private def l13rpPmMPL9933 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9929,5421], outs := [9933] }
private def l13rpPmMPL9951 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9947,5425], outs := [9951] }
private def l13rpPmNL9902 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [9896,5407], outs := [9902] }
private def l13rpPmMPL9920 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9916,5416], outs := [9920] }
private def l13rpPmMPL9934 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9930,5421], outs := [9934] }
private def l13rpPmMPL9952 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9948,5425], outs := [9952] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l13rp_sm_node_facts :
    sm.nodes[550]'(by native_decide) = l13rpSmFloat5406 ∧
    sm.nodes[551]'(by native_decide) = l13rpSmResh5415 ∧
    sm.nodes[552]'(by native_decide) = l13rpSmResh5420 ∧
    sm.nodes[553]'(by native_decide) = l13rpSmResh5424 ∧
    sm.nodes[554]'(by native_decide) = l13rpSmNL5408 ∧
    sm.nodes[555]'(by native_decide) = l13rpSmMPL5417 ∧
    sm.nodes[556]'(by native_decide) = l13rpSmMPL5422 ∧
    sm.nodes[557]'(by native_decide) = l13rpSmMPL5426 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l13rp_pm_node_facts :
    pm.nodes[1162]'(by native_decide) = l13rpPmFloat9895 ∧
    pm.nodes[1163]'(by native_decide) = l13rpPmResh9915 ∧
    pm.nodes[1164]'(by native_decide) = l13rpPmResh9929 ∧
    pm.nodes[1165]'(by native_decide) = l13rpPmResh9947 ∧
    pm.nodes[1166]'(by native_decide) = l13rpPmFloat9896 ∧
    pm.nodes[1167]'(by native_decide) = l13rpPmResh9916 ∧
    pm.nodes[1168]'(by native_decide) = l13rpPmResh9930 ∧
    pm.nodes[1169]'(by native_decide) = l13rpPmResh9948 ∧
    pm.nodes[1170]'(by native_decide) = l13rpPmNL9901 ∧
    pm.nodes[1171]'(by native_decide) = l13rpPmMPL9919 ∧
    pm.nodes[1172]'(by native_decide) = l13rpPmMPL9933 ∧
    pm.nodes[1173]'(by native_decide) = l13rpPmMPL9951 ∧
    pm.nodes[1174]'(by native_decide) = l13rpPmNL9902 ∧
    pm.nodes[1175]'(by native_decide) = l13rpPmMPL9920 ∧
    pm.nodes[1176]'(by native_decide) = l13rpPmMPL9934 ∧
    pm.nodes[1177]'(by native_decide) = l13rpPmMPL9952 := by
  native_decide

private theorem l13rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l13rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l13rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5407 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5416 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5421 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5425 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5407 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5416 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5421 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5425 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5394 ∉ n.outs)) := by
  native_decide

private theorem l13rp_w5407_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5407 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l13rp_w5407_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5407 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l13rp_w5416_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5416 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l13rp_w5416_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5416 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l13rp_w5421_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5421 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l13rp_w5421_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5421 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l13rp_w5425_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5425 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l13rp_w5425_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5425 ∉ n.outs := by
  intro n hn
  exact l13rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l13rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(551, 5406), (550, 8197), (552, 5415), (551, 8205), (553, 5420), (552, 8209), (554, 5424), (553, 8213), (555, 5408), (554, 5406), (556, 5417), (555, 5415), (557, 5422), (556, 5420), (558, 5426), (557, 5424)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l13rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1163, 9895), (1162, 16082), (1164, 9915), (1163, 16090), (1165, 9929), (1164, 16094), (1166, 9947), (1165, 16098), (1167, 9896), (1166, 16105), (1168, 9916), (1167, 16113), (1169, 9930), (1168, 16117), (1170, 9948), (1169, 16121), (1171, 9901), (1170, 9895), (1172, 9919), (1171, 9915), (1173, 9933), (1172, 9929), (1174, 9951), (1173, 9947), (1175, 9902), (1174, 9896), (1176, 9920), (1175, 9916), (1177, 9934), (1176, 9930), (1178, 9952), (1177, 9948)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5406 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5406 =
      denoteGraphDistributedFaithful sm initSM 8197 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 550 l13rpSmFloat5406
    8197 5406 (fun x => x)
    (by native_decide) l13rp_sm_node_facts.1 ?_
    (l13rp_nonempty_sm 551) (l13rp_sm_not_written 551 5406 (by decide))
    (l13rp_nonempty_sm 550) (l13rp_sm_not_written 550 8197 (by decide))
  intro s
  unfold l13rpSmFloat5406
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8197 5406 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5415 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5415 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8205) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 551 l13rpSmResh5415
    8205 5415 (fun x => fw_view [4096,1024] x)
    (by native_decide) l13rp_sm_node_facts.2.1 ?_
    (l13rp_nonempty_sm 552) (l13rp_sm_not_written 552 5415 (by decide))
    (l13rp_nonempty_sm 551) (l13rp_sm_not_written 551 8205 (by decide))
  intro s
  unfold l13rpSmResh5415
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8205 5415 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5420 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5420 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8209) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 552 l13rpSmResh5420
    8209 5420 (fun x => fw_view [4096,1024] x)
    (by native_decide) l13rp_sm_node_facts.2.2.1 ?_
    (l13rp_nonempty_sm 553) (l13rp_sm_not_written 553 5420 (by decide))
    (l13rp_nonempty_sm 552) (l13rp_sm_not_written 552 8209 (by decide))
  intro s
  unfold l13rpSmResh5420
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8209 5420 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5424 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5424 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8213) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 553 l13rpSmResh5424
    8213 5424 (fun x => fw_view [4096,1024] x)
    (by native_decide) l13rp_sm_node_facts.2.2.2.1 ?_
    (l13rp_nonempty_sm 554) (l13rp_sm_not_written 554 5424 (by decide))
    (l13rp_nonempty_sm 553) (l13rp_sm_not_written 553 8213 (by decide))
  intro s
  unfold l13rpSmResh5424
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8213 5424 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5408 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5408 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5406)
        (denoteGraphDistributedFaithful sm initSM 5407) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 554 l13rpSmNL5408
    5406 5407 5408 fw_norm_linear
    (by native_decide) l13rp_sm_node_facts.2.2.2.2.1 ?_
    (l13rp_nonempty_sm 555) (l13rp_sm_not_written 555 5408 (by decide))
    (l13rp_nonempty_sm 554) (l13rp_sm_not_written 554 5406 (by decide))
    (l13rp_w5407_sm_drop 554)
  intro s
  unfold l13rpSmNL5408
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5406 5407 5408

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5417 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5417 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5415)
        (denoteGraphDistributedFaithful sm initSM 5416) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 555 l13rpSmMPL5417
    5415 5416 5417 fw_linear
    (by native_decide) l13rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l13rp_nonempty_sm 556) (l13rp_sm_not_written 556 5417 (by decide))
    (l13rp_nonempty_sm 555) (l13rp_sm_not_written 555 5415 (by decide))
    (l13rp_w5416_sm_drop 555)
  intro s
  unfold l13rpSmMPL5417
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5415 5416 5417

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5422 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5422 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5420)
        (denoteGraphDistributedFaithful sm initSM 5421) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 556 l13rpSmMPL5422
    5420 5421 5422 fw_linear
    (by native_decide) l13rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_sm 557) (l13rp_sm_not_written 557 5422 (by decide))
    (l13rp_nonempty_sm 556) (l13rp_sm_not_written 556 5420 (by decide))
    (l13rp_w5421_sm_drop 556)
  intro s
  unfold l13rpSmMPL5422
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5420 5421 5422

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_sm5426 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5426 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5424)
        (denoteGraphDistributedFaithful sm initSM 5425) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 557 l13rpSmMPL5426
    5424 5425 5426 fw_linear
    (by native_decide) l13rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l13rp_nonempty_sm 558) (l13rp_sm_not_written 558 5426 (by decide))
    (l13rp_nonempty_sm 557) (l13rp_sm_not_written 557 5424 (by decide))
    (l13rp_w5425_sm_drop 557)
  intro s
  unfold l13rpSmMPL5426
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5424 5425 5426

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9895 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9895 =
      denoteGraphDistributedFaithful pm initPM 16082 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1162 l13rpPmFloat9895
    16082 9895 (fun x => x)
    (by native_decide) l13rp_pm_node_facts.1 ?_
    (l13rp_nonempty_pm 1163) (l13rp_pm_not_written 1163 9895 (by decide))
    (l13rp_nonempty_pm 1162) (l13rp_pm_not_written 1162 16082 (by decide))
  intro s
  unfold l13rpPmFloat9895
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16082 9895 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9915 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9915 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16090) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1163 l13rpPmResh9915
    16090 9915 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13rp_pm_node_facts.2.1 ?_
    (l13rp_nonempty_pm 1164) (l13rp_pm_not_written 1164 9915 (by decide))
    (l13rp_nonempty_pm 1163) (l13rp_pm_not_written 1163 16090 (by decide))
  intro s
  unfold l13rpPmResh9915
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16090 9915 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9929 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9929 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16094) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1164 l13rpPmResh9929
    16094 9929 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13rp_pm_node_facts.2.2.1 ?_
    (l13rp_nonempty_pm 1165) (l13rp_pm_not_written 1165 9929 (by decide))
    (l13rp_nonempty_pm 1164) (l13rp_pm_not_written 1164 16094 (by decide))
  intro s
  unfold l13rpPmResh9929
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16094 9929 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9947 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9947 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16098) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1165 l13rpPmResh9947
    16098 9947 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13rp_pm_node_facts.2.2.2.1 ?_
    (l13rp_nonempty_pm 1166) (l13rp_pm_not_written 1166 9947 (by decide))
    (l13rp_nonempty_pm 1165) (l13rp_pm_not_written 1165 16098 (by decide))
  intro s
  unfold l13rpPmResh9947
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16098 9947 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9896 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9896 =
      denoteGraphDistributedFaithful pm initPM 16105 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1166 l13rpPmFloat9896
    16105 9896 (fun x => x)
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1167) (l13rp_pm_not_written 1167 9896 (by decide))
    (l13rp_nonempty_pm 1166) (l13rp_pm_not_written 1166 16105 (by decide))
  intro s
  unfold l13rpPmFloat9896
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16105 9896 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9916 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9916 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16113) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1167 l13rpPmResh9916
    16113 9916 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1168) (l13rp_pm_not_written 1168 9916 (by decide))
    (l13rp_nonempty_pm 1167) (l13rp_pm_not_written 1167 16113 (by decide))
  intro s
  unfold l13rpPmResh9916
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16113 9916 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9930 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9930 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16117) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1168 l13rpPmResh9930
    16117 9930 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1169) (l13rp_pm_not_written 1169 9930 (by decide))
    (l13rp_nonempty_pm 1168) (l13rp_pm_not_written 1168 16117 (by decide))
  intro s
  unfold l13rpPmResh9930
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16117 9930 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9948 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9948 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16121) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1169 l13rpPmResh9948
    16121 9948 (fun x => fw_view [2048,1024] x)
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1170) (l13rp_pm_not_written 1170 9948 (by decide))
    (l13rp_nonempty_pm 1169) (l13rp_pm_not_written 1169 16121 (by decide))
  intro s
  unfold l13rpPmResh9948
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16121 9948 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9901 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9901 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 9895)
        (denoteGraphDistributedFaithful pm initPM 5407) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1170 l13rpPmNL9901
    9895 5407 9901 fw_norm_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1171) (l13rp_pm_not_written 1171 9901 (by decide))
    (l13rp_nonempty_pm 1170) (l13rp_pm_not_written 1170 9895 (by decide))
    (l13rp_w5407_pm_drop 1170)
  intro s
  unfold l13rpPmNL9901
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 9895 5407 9901

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9919 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9919 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9915)
        (denoteGraphDistributedFaithful pm initPM 5416) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1171 l13rpPmMPL9919
    9915 5416 9919 fw_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1172) (l13rp_pm_not_written 1172 9919 (by decide))
    (l13rp_nonempty_pm 1171) (l13rp_pm_not_written 1171 9915 (by decide))
    (l13rp_w5416_pm_drop 1171)
  intro s
  unfold l13rpPmMPL9919
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9915 5416 9919

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9933 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9933 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9929)
        (denoteGraphDistributedFaithful pm initPM 5421) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1172 l13rpPmMPL9933
    9929 5421 9933 fw_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1173) (l13rp_pm_not_written 1173 9933 (by decide))
    (l13rp_nonempty_pm 1172) (l13rp_pm_not_written 1172 9929 (by decide))
    (l13rp_w5421_pm_drop 1172)
  intro s
  unfold l13rpPmMPL9933
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9929 5421 9933

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9951 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9951 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9947)
        (denoteGraphDistributedFaithful pm initPM 5425) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1173 l13rpPmMPL9951
    9947 5425 9951 fw_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1174) (l13rp_pm_not_written 1174 9951 (by decide))
    (l13rp_nonempty_pm 1173) (l13rp_pm_not_written 1173 9947 (by decide))
    (l13rp_w5425_pm_drop 1173)
  intro s
  unfold l13rpPmMPL9951
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 9947 5425 9951

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9902 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9902 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 9896)
        (denoteGraphDistributedFaithful pm initPM 5407) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1174 l13rpPmNL9902
    9896 5407 9902 fw_norm_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1175) (l13rp_pm_not_written 1175 9902 (by decide))
    (l13rp_nonempty_pm 1174) (l13rp_pm_not_written 1174 9896 (by decide))
    (l13rp_w5407_pm_drop 1174)
  intro s
  unfold l13rpPmNL9902
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 9896 5407 9902

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9920 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9920 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9916)
        (denoteGraphDistributedFaithful pm initPM 5416) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1175 l13rpPmMPL9920
    9916 5416 9920 fw_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1176) (l13rp_pm_not_written 1176 9920 (by decide))
    (l13rp_nonempty_pm 1175) (l13rp_pm_not_written 1175 9916 (by decide))
    (l13rp_w5416_pm_drop 1175)
  intro s
  unfold l13rpPmMPL9920
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9916 5416 9920

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9934 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9934 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9930)
        (denoteGraphDistributedFaithful pm initPM 5421) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1176 l13rpPmMPL9934
    9930 5421 9934 fw_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l13rp_nonempty_pm 1177) (l13rp_pm_not_written 1177 9934 (by decide))
    (l13rp_nonempty_pm 1176) (l13rp_pm_not_written 1176 9930 (by decide))
    (l13rp_w5421_pm_drop 1176)
  intro s
  unfold l13rpPmMPL9934
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9930 5421 9934

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_red_pm9952 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9952 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 9948)
        (denoteGraphDistributedFaithful pm initPM 5425) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1177 l13rpPmMPL9952
    9948 5425 9952 fw_linear
    (by native_decide) l13rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l13rp_nonempty_pm 1178) (l13rp_pm_not_written 1178 9952 (by decide))
    (l13rp_nonempty_pm 1177) (l13rp_pm_not_written 1177 9948 (by decide))
    (l13rp_w5425_pm_drop 1177)
  intro s
  unfold l13rpPmMPL9952
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 9948 5425 9952

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l13rp_weight_eq (initSM initPM : Store)
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
private theorem l13rp_pm_weight_shape (initPM : Store)
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
theorem recon_zigzagGoal_5406_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5406)
      (denoteGraphDistributedFaithful pm initPM 9895)
      (denoteGraphDistributedFaithful pm initPM 9896)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8197_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13rp_red_sm5406 initSM, l13rp_red_pm9895 initPM, l13rp_red_pm9896 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5415_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5415)
      (denoteGraphDistributedFaithful pm initPM 9915)
      (denoteGraphDistributedFaithful pm initPM 9916)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8205_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13rp_red_sm5415 initSM, l13rp_red_pm9915 initPM, l13rp_red_pm9916 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5420_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5420)
      (denoteGraphDistributedFaithful pm initPM 9929)
      (denoteGraphDistributedFaithful pm initPM 9930)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8209_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13rp_red_sm5420 initSM, l13rp_red_pm9929 initPM, l13rp_red_pm9930 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5424_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5424)
      (denoteGraphDistributedFaithful pm initPM 9947)
      (denoteGraphDistributedFaithful pm initPM 9948)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8213_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l13rp_red_sm5424 initSM, l13rp_red_pm9947 initPM, l13rp_red_pm9948 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5417_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5417)
      (denoteGraphDistributedFaithful pm initPM 9919)
      (denoteGraphDistributedFaithful pm initPM 9920)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5415_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5416 =
      denoteGraphDistributedFaithful pm initPM 5416 :=
    l13rp_weight_eq initSM initPM hInit 5416 initGoal_5416 (by native_decide)
      rfl rfl rfl rfl
      l13rp_weights_not_written.1.2.1 l13rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5416).shape = [1,1024] :=
    l13rp_pm_weight_shape initPM hPM 5416 [1,1024] (by native_decide)
      l13rp_weights_not_written.2.2.1
  rw [l13rp_red_sm5417 initSM, l13rp_red_pm9919 initPM, l13rp_red_pm9920 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5422_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5422)
      (denoteGraphDistributedFaithful pm initPM 9933)
      (denoteGraphDistributedFaithful pm initPM 9934)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5420_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5421 =
      denoteGraphDistributedFaithful pm initPM 5421 :=
    l13rp_weight_eq initSM initPM hInit 5421 initGoal_5421 (by native_decide)
      rfl rfl rfl rfl
      l13rp_weights_not_written.1.2.2.1 l13rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5421).shape = [512,1024] :=
    l13rp_pm_weight_shape initPM hPM 5421 [512,1024] (by native_decide)
      l13rp_weights_not_written.2.2.2.1
  rw [l13rp_red_sm5422 initSM, l13rp_red_pm9933 initPM, l13rp_red_pm9934 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5426_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5426)
      (denoteGraphDistributedFaithful pm initPM 9951)
      (denoteGraphDistributedFaithful pm initPM 9952)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5424_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5425 =
      denoteGraphDistributedFaithful pm initPM 5425 :=
    l13rp_weight_eq initSM initPM hInit 5425 initGoal_5425 (by native_decide)
      rfl rfl rfl rfl
      l13rp_weights_not_written.1.2.2.2 l13rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5425).shape = [512,1024] :=
    l13rp_pm_weight_shape initPM hPM 5425 [512,1024] (by native_decide)
      l13rp_weights_not_written.2.2.2.2.1
  rw [l13rp_red_sm5426 initSM, l13rp_red_pm9951 initPM, l13rp_red_pm9952 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5408_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5408)
      (denoteGraphDistributedFaithful pm initPM 9901)
      (denoteGraphDistributedFaithful pm initPM 9902)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5406_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5407 =
      denoteGraphDistributedFaithful pm initPM 5407 :=
    l13rp_weight_eq initSM initPM hInit 5407 initGoal_5407 (by native_decide)
      rfl rfl rfl rfl
      l13rp_weights_not_written.1.1 l13rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5407).shape = [64,1024] :=
    l13rp_pm_weight_shape initPM hPM 5407 [64,1024] (by native_decide)
      l13rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5394).shape = [2] :=
    l13rp_pm_weight_shape initPM hPM 5394 [2] (by native_decide)
      l13rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5394)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5394)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5406)
      (denoteGraphDistributedFaithful pm initPM 9895)
      (denoteGraphDistributedFaithful pm initPM 9896)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l13rp_red_sm5408 initSM, l13rp_red_pm9901 initPM, l13rp_red_pm9902 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
