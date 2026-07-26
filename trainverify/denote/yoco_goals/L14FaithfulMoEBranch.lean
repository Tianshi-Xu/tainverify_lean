/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L14FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-2 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-1 段 `L13FaithfulMoEBranch` to block 2.
The block-2 cu tensor is **5443**.

* SM 593 `FW_topk_routing [5457] → [5458, 5459, 5460]` params `[8, 1]`
    (PM 1248 / 1252 → `10075, 10077, 10079` / `10076, 10078, 10080`)
* SM 594 `FW_view [5466] → [5467]` params `[4096, 1]`        (PM 1249 / 1253 → 10097 / 10098)
* SM 595 `FW_view [5471] → [5472]` params `[4096, 512]`      (PM 1250 / 1254 → 10115 / 10116)
* SM 596 `FW_view [5475] → [5476]` params `[4096, 512]`      (PM 1251 / 1255 → 10133 / 10134)
* SM 598 `FW_sigmoid [5467] → [5468]`                        (PM 1257 / 1260 → 10099 / 10100)
* SM 599 `FW_swiglu [5472, 5476] → [5477]`                   (PM 1258 / 1261 → 10137 / 10138)

The third `FW_topk_routing` output (`5460`) has no intermediate goal and is therefore
not exported, but the node reduction handles all three outputs.
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

private def l14mbSmTopk5458 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5457], outs := [5458,5459,5460],
    params := [8,1] }
private def l14mbSmView5467 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5466], outs := [5467], params := [4096,1] }
private def l14mbSmView5472 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5471], outs := [5472], params := [4096,512] }
private def l14mbSmView5476 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5475], outs := [5476], params := [4096,512] }
private def l14mbSmSig5468 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5467], outs := [5468] }
private def l14mbSmSwi5477 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5472,5476], outs := [5477] }

private def l14mbPmTopk10075 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10073], outs := [10075,10077,10079],
    params := [8,1] }
private def l14mbPmView10097 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10091], outs := [10097], params := [2048,1] }
private def l14mbPmView10115 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10105], outs := [10115], params := [2048,512] }
private def l14mbPmView10133 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10123], outs := [10133], params := [2048,512] }
private def l14mbPmTopk10076 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10074], outs := [10076,10078,10080],
    params := [8,1] }
private def l14mbPmView10098 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10092], outs := [10098], params := [2048,1] }
private def l14mbPmView10116 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10106], outs := [10116], params := [2048,512] }
private def l14mbPmView10134 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10124], outs := [10134], params := [2048,512] }
private def l14mbPmSig10099 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10097], outs := [10099] }
private def l14mbPmSwi10137 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10115,10133], outs := [10137] }
private def l14mbPmSig10100 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10098], outs := [10100] }
private def l14mbPmSwi10138 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10116,10134], outs := [10138] }

/-! ### Certified node indices -/

private theorem l14mb_sm_node_facts :
    sm.nodes[593]'(by native_decide) = l14mbSmTopk5458 ∧
    sm.nodes[594]'(by native_decide) = l14mbSmView5467 ∧
    sm.nodes[595]'(by native_decide) = l14mbSmView5472 ∧
    sm.nodes[596]'(by native_decide) = l14mbSmView5476 ∧
    sm.nodes[598]'(by native_decide) = l14mbSmSig5468 ∧
    sm.nodes[599]'(by native_decide) = l14mbSmSwi5477 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l14mb_pm_node_facts :
    pm.nodes[1248]'(by native_decide) = l14mbPmTopk10075 ∧
    pm.nodes[1249]'(by native_decide) = l14mbPmView10097 ∧
    pm.nodes[1250]'(by native_decide) = l14mbPmView10115 ∧
    pm.nodes[1251]'(by native_decide) = l14mbPmView10133 ∧
    pm.nodes[1252]'(by native_decide) = l14mbPmTopk10076 ∧
    pm.nodes[1253]'(by native_decide) = l14mbPmView10098 ∧
    pm.nodes[1254]'(by native_decide) = l14mbPmView10116 ∧
    pm.nodes[1255]'(by native_decide) = l14mbPmView10134 ∧
    pm.nodes[1257]'(by native_decide) = l14mbPmSig10099 ∧
    pm.nodes[1258]'(by native_decide) = l14mbPmSwi10137 ∧
    pm.nodes[1260]'(by native_decide) = l14mbPmSig10100 ∧
    pm.nodes[1261]'(by native_decide) = l14mbPmSwi10138 := by
  native_decide

private theorem l14mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l14mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l14mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(594, 5458), (594, 5459), (593, 5457), (595, 5467), (594, 5466), (596, 5472), (595, 5471), (597, 5476), (596, 5475), (599, 5468), (598, 5467), (600, 5477), (599, 5472), (599, 5476)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l14mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1249, 10075), (1249, 10077), (1248, 10073), (1253, 10076), (1253, 10078), (1252, 10074), (1250, 10097), (1249, 10091), (1251, 10115), (1250, 10105), (1252, 10133), (1251, 10123), (1254, 10098), (1253, 10092), (1255, 10116), (1254, 10106), (1256, 10134), (1255, 10124), (1258, 10099), (1257, 10097), (1261, 10100), (1260, 10098), (1259, 10137), (1258, 10115), (1258, 10133), (1262, 10138), (1261, 10116), (1261, 10134), (1248, 5443)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l14mb_cu_not_written : ∀ n ∈ pm.nodes, 5443 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_sm5458 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5457).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5458 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5457) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 593 l14mbSmTopk5458
    5457 5458 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l14mb_sm_node_facts.1 ?_
    (l14mb_nonempty_sm 594) (l14mb_sm_not_written 594 5458 (by decide))
    (l14mb_nonempty_sm 593) (l14mb_sm_not_written 593 5457 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l14mbSmTopk5458
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5457 5458 5459 5460 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_sm5459 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5457).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5459 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5457) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 593 l14mbSmTopk5458
    5457 5459 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l14mb_sm_node_facts.1 ?_
    (l14mb_nonempty_sm 594) (l14mb_sm_not_written 594 5459 (by decide))
    (l14mb_nonempty_sm 593) (l14mb_sm_not_written 593 5457 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l14mbSmTopk5458
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5457 5458 5459 5460 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10075 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10073).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10075 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10073) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1248 l14mbPmTopk10075
    10073 10075 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l14mb_pm_node_facts.1 ?_
    (l14mb_nonempty_pm 1249) (l14mb_pm_not_written 1249 10075 (by decide))
    (l14mb_nonempty_pm 1248) (l14mb_pm_not_written 1248 10073 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l14mbPmTopk10075
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 10073 10075 10077 10079 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10077 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10073).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10077 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10073) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1248 l14mbPmTopk10075
    10073 10077 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l14mb_pm_node_facts.1 ?_
    (l14mb_nonempty_pm 1249) (l14mb_pm_not_written 1249 10077 (by decide))
    (l14mb_nonempty_pm 1248) (l14mb_pm_not_written 1248 10073 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l14mbPmTopk10075
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 10073 10075 10077 10079 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10076 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10074).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10076 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10074) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1252 l14mbPmTopk10076
    10074 10076 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1253) (l14mb_pm_not_written 1253 10076 (by decide))
    (l14mb_nonempty_pm 1252) (l14mb_pm_not_written 1252 10074 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l14mbPmTopk10076
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 10074 10076 10078 10080 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10078 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10074).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10078 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10074) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1252 l14mbPmTopk10076
    10074 10078 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1253) (l14mb_pm_not_written 1253 10078 (by decide))
    (l14mb_nonempty_pm 1252) (l14mb_pm_not_written 1252 10074 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l14mbPmTopk10076
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 10074 10076 10078 10080 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_sm5467 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5467 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5466) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 594 l14mbSmView5467
    5466 5467 (fun x => fw_view [4096,1] x)
    (by native_decide) l14mb_sm_node_facts.2.1 ?_
    (l14mb_nonempty_sm 595) (l14mb_sm_not_written 595 5467 (by decide))
    (l14mb_nonempty_sm 594) (l14mb_sm_not_written 594 5466 (by decide))
  intro s
  unfold l14mbSmView5467
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5466 5467

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_sm5472 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5472 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5471) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 595 l14mbSmView5472
    5471 5472 (fun x => fw_view [4096,512] x)
    (by native_decide) l14mb_sm_node_facts.2.2.1 ?_
    (l14mb_nonempty_sm 596) (l14mb_sm_not_written 596 5472 (by decide))
    (l14mb_nonempty_sm 595) (l14mb_sm_not_written 595 5471 (by decide))
  intro s
  unfold l14mbSmView5472
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5471 5472

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_sm5476 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5476 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5475) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 596 l14mbSmView5476
    5475 5476 (fun x => fw_view [4096,512] x)
    (by native_decide) l14mb_sm_node_facts.2.2.2.1 ?_
    (l14mb_nonempty_sm 597) (l14mb_sm_not_written 597 5476 (by decide))
    (l14mb_nonempty_sm 596) (l14mb_sm_not_written 596 5475 (by decide))
  intro s
  unfold l14mbSmView5476
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5475 5476

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10097 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10097 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10091) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1249 l14mbPmView10097
    10091 10097 (fun x => fw_view [2048,1] x)
    (by native_decide) l14mb_pm_node_facts.2.1 ?_
    (l14mb_nonempty_pm 1250) (l14mb_pm_not_written 1250 10097 (by decide))
    (l14mb_nonempty_pm 1249) (l14mb_pm_not_written 1249 10091 (by decide))
  intro s
  unfold l14mbPmView10097
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 10091 10097

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10115 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10115 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10105) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1250 l14mbPmView10115
    10105 10115 (fun x => fw_view [2048,512] x)
    (by native_decide) l14mb_pm_node_facts.2.2.1 ?_
    (l14mb_nonempty_pm 1251) (l14mb_pm_not_written 1251 10115 (by decide))
    (l14mb_nonempty_pm 1250) (l14mb_pm_not_written 1250 10105 (by decide))
  intro s
  unfold l14mbPmView10115
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10105 10115

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10133 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10133 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10123) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1251 l14mbPmView10133
    10123 10133 (fun x => fw_view [2048,512] x)
    (by native_decide) l14mb_pm_node_facts.2.2.2.1 ?_
    (l14mb_nonempty_pm 1252) (l14mb_pm_not_written 1252 10133 (by decide))
    (l14mb_nonempty_pm 1251) (l14mb_pm_not_written 1251 10123 (by decide))
  intro s
  unfold l14mbPmView10133
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10123 10133

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10098 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10098 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10092) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1253 l14mbPmView10098
    10092 10098 (fun x => fw_view [2048,1] x)
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1254) (l14mb_pm_not_written 1254 10098 (by decide))
    (l14mb_nonempty_pm 1253) (l14mb_pm_not_written 1253 10092 (by decide))
  intro s
  unfold l14mbPmView10098
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 10092 10098

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10116 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10116 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10106) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1254 l14mbPmView10116
    10106 10116 (fun x => fw_view [2048,512] x)
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1255) (l14mb_pm_not_written 1255 10116 (by decide))
    (l14mb_nonempty_pm 1254) (l14mb_pm_not_written 1254 10106 (by decide))
  intro s
  unfold l14mbPmView10116
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10106 10116

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10134 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10134 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10124) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1255 l14mbPmView10134
    10124 10134 (fun x => fw_view [2048,512] x)
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1256) (l14mb_pm_not_written 1256 10134 (by decide))
    (l14mb_nonempty_pm 1255) (l14mb_pm_not_written 1255 10124 (by decide))
  intro s
  unfold l14mbPmView10134
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10124 10134

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_sm5468 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5468 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5467) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 598 l14mbSmSig5468
    5467 5468 fw_sigmoid
    (by native_decide) l14mb_sm_node_facts.2.2.2.2.1 ?_
    (l14mb_nonempty_sm 599) (l14mb_sm_not_written 599 5468 (by decide))
    (l14mb_nonempty_sm 598) (l14mb_sm_not_written 598 5467 (by decide))
  intro s
  unfold l14mbSmSig5468
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5467 5468

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10099 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10099 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10097) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1257 l14mbPmSig10099
    10097 10099 fw_sigmoid
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1258) (l14mb_pm_not_written 1258 10099 (by decide))
    (l14mb_nonempty_pm 1257) (l14mb_pm_not_written 1257 10097 (by decide))
  intro s
  unfold l14mbPmSig10099
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 10097 10099

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10100 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10100 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10098) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1260 l14mbPmSig10100
    10098 10100 fw_sigmoid
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1261) (l14mb_pm_not_written 1261 10100 (by decide))
    (l14mb_nonempty_pm 1260) (l14mb_pm_not_written 1260 10098 (by decide))
  intro s
  unfold l14mbPmSig10100
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 10098 10100

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_sm5477 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5477 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5472)
        (denoteGraphDistributedFaithful sm initSM 5476) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 599 l14mbSmSwi5477
    5472 5476 5477 fw_swiglu
    (by native_decide) l14mb_sm_node_facts.2.2.2.2.2 ?_
    (l14mb_nonempty_sm 600) (l14mb_sm_not_written 600 5477 (by decide))
    (l14mb_nonempty_sm 599) (l14mb_sm_not_written 599 5472 (by decide))
    (l14mb_sm_not_written 599 5476 (by decide))
  intro s
  unfold l14mbSmSwi5477
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5472 5476 5477

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10137 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10137 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10115)
        (denoteGraphDistributedFaithful pm initPM 10133) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1258 l14mbPmSwi10137
    10115 10133 10137 fw_swiglu
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l14mb_nonempty_pm 1259) (l14mb_pm_not_written 1259 10137 (by decide))
    (l14mb_nonempty_pm 1258) (l14mb_pm_not_written 1258 10115 (by decide))
    (l14mb_pm_not_written 1258 10133 (by decide))
  intro s
  unfold l14mbPmSwi10137
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 10115 10133 10137

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_red_pm10138 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10138 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10116)
        (denoteGraphDistributedFaithful pm initPM 10134) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1261 l14mbPmSwi10138
    10116 10134 10138 fw_swiglu
    (by native_decide) l14mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l14mb_nonempty_pm 1262) (l14mb_pm_not_written 1262 10138 (by decide))
    (l14mb_nonempty_pm 1261) (l14mb_pm_not_written 1261 10116 (by decide))
    (l14mb_pm_not_written 1261 10134 (by decide))
  intro s
  unfold l14mbPmSwi10138
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 10116 10134 10138

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5443).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5443 = initPM 5443 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5443
      layer1_pm_nodes_nonempty l14mb_cu_not_written
  rw [e2]
  exact hPM 5443 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l14mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5443) = [0, 2 * 2048] := by
  have hcuShape := l14mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5443)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hrel
  apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
  have ht := hs.cu_wf.local_tokens
  simp only [List.getD_cons_zero] at ht
  rw [hs.source0_shape] at ht
  norm_num at ht
  norm_num
  exact ht.symm

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5458_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5458)
      (denoteGraphDistributedFaithful pm initPM 10075)
      (denoteGraphDistributedFaithful pm initPM 10076)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5457_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l14mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5457)
      (denoteGraphDistributedFaithful pm initPM 10073)
      (denoteGraphDistributedFaithful pm initPM 10074)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l14mb_red_sm5458 initSM hs.full_shape,
    l14mb_red_pm10075 initPM hs.rank0_shape,
    l14mb_red_pm10076 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5459_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5459)
      (denoteGraphDistributedFaithful pm initPM 10077)
      (denoteGraphDistributedFaithful pm initPM 10078)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5457_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l14mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5457)
      (denoteGraphDistributedFaithful pm initPM 10073)
      (denoteGraphDistributedFaithful pm initPM 10074)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l14mb_red_sm5459 initSM hs.full_shape,
    l14mb_red_pm10077 initPM hs.rank0_shape,
    l14mb_red_pm10078 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5467_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5467)
      (denoteGraphDistributedFaithful pm initPM 10097)
      (denoteGraphDistributedFaithful pm initPM 10098)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5466_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14mb_red_sm5467 initSM, l14mb_red_pm10097 initPM, l14mb_red_pm10098 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5472_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5472)
      (denoteGraphDistributedFaithful pm initPM 10115)
      (denoteGraphDistributedFaithful pm initPM 10116)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5471_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14mb_red_sm5472 initSM, l14mb_red_pm10115 initPM, l14mb_red_pm10116 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5476_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5476)
      (denoteGraphDistributedFaithful pm initPM 10133)
      (denoteGraphDistributedFaithful pm initPM 10134)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5475_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l14mb_red_sm5476 initSM, l14mb_red_pm10133 initPM, l14mb_red_pm10134 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5468_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5468)
      (denoteGraphDistributedFaithful pm initPM 10099)
      (denoteGraphDistributedFaithful pm initPM 10100)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5467_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5467)
      (denoteGraphDistributedFaithful pm initPM 10097)
      (denoteGraphDistributedFaithful pm initPM 10098)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l14mb_red_sm5468 initSM, l14mb_red_pm10099 initPM, l14mb_red_pm10100 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5477_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5477)
      (denoteGraphDistributedFaithful pm initPM 10137)
      (denoteGraphDistributedFaithful pm initPM 10138)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5472_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5476_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5472)
      (denoteGraphDistributedFaithful pm initPM 10115)
      (denoteGraphDistributedFaithful pm initPM 10116)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5476)
      (denoteGraphDistributedFaithful pm initPM 10133)
      (denoteGraphDistributedFaithful pm initPM 10134)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l14mb_red_sm5477 initSM, l14mb_red_pm10137 initPM, l14mb_red_pm10138 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
