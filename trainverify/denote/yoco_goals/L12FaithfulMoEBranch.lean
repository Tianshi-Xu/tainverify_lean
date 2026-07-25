/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulRouterProj
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the MoE lower branch (topk / gate / swiglu)

* SM 523 `FW_topk_routing [5359] → [5360, 5361, 5362]` params `[8, 1]`
    (PM 1108 / 1112 → `9731, 9733, 9735` / `9732, 9734, 9736`)
* SM 524 `FW_view [5368] → [5369]` params `[4096, 1]`      (PM 1109 / 1113 → 9753 / 9754)
* SM 525 `FW_view [5373] → [5374]` params `[4096, 512]`    (PM 1110 / 1114 → 9771 / 9772)
* SM 526 `FW_view [5377] → [5378]` params `[4096, 512]`    (PM 1111 / 1115 → 9789 / 9790)
* SM 528 `FW_sigmoid [5369] → [5370]`                      (PM 1117 / 1120 → 9755 / 9756)
* SM 529 `FW_swiglu [5374, 5378] → [5379]`                 (PM 1118 / 1121 → 9793 / 9794)

The third `FW_topk_routing` output (`5362`, gate scores) has no intermediate goal and is
therefore not exported, but the node reduction handles all three outputs uniformly.

The `hdec : decodeCuSeqlens cu = [0, 2 * 2048]` side condition of the router lemmas is
**derived** from the ambient `hCu` chain (via the parent relation's `cu_wf` payload plus
the `[2]` shape of the cu tensor 5345), exactly as in `recon_zigzagGoal_5359_faithful`.
No new hypotheses are introduced: every theorem below takes literally the same five
parameters as its parent.
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

private def l12mbSmTopk5360 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360,5361,5362],
    params := [8,1] }
private def l12mbSmView5369 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5368], outs := [5369], params := [4096,1] }
private def l12mbSmView5374 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5373], outs := [5374], params := [4096,512] }
private def l12mbSmView5378 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5377], outs := [5378], params := [4096,512] }
private def l12mbSmSig5370 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5369], outs := [5370] }
private def l12mbSmSwi5379 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5374,5378], outs := [5379] }

private def l12mbPmTopk9731 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731,9733,9735],
    params := [8,1] }
private def l12mbPmView9753 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9747], outs := [9753], params := [2048,1] }
private def l12mbPmView9771 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9761], outs := [9771], params := [2048,512] }
private def l12mbPmView9789 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9779], outs := [9789], params := [2048,512] }
private def l12mbPmTopk9732 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732,9734,9736],
    params := [8,1] }
private def l12mbPmView9754 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9748], outs := [9754], params := [2048,1] }
private def l12mbPmView9772 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9762], outs := [9772], params := [2048,512] }
private def l12mbPmView9790 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9780], outs := [9790], params := [2048,512] }
private def l12mbPmSig9755 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9753], outs := [9755] }
private def l12mbPmSwi9793 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9771,9789], outs := [9793] }
private def l12mbPmSig9756 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9754], outs := [9756] }
private def l12mbPmSwi9794 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9772,9790], outs := [9794] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l12mb_sm_node_facts :
    sm.nodes[523]'(by native_decide) = l12mbSmTopk5360 ∧
    sm.nodes[524]'(by native_decide) = l12mbSmView5369 ∧
    sm.nodes[525]'(by native_decide) = l12mbSmView5374 ∧
    sm.nodes[526]'(by native_decide) = l12mbSmView5378 ∧
    sm.nodes[528]'(by native_decide) = l12mbSmSig5370 ∧
    sm.nodes[529]'(by native_decide) = l12mbSmSwi5379 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12mb_pm_node_facts :
    pm.nodes[1108]'(by native_decide) = l12mbPmTopk9731 ∧
    pm.nodes[1109]'(by native_decide) = l12mbPmView9753 ∧
    pm.nodes[1110]'(by native_decide) = l12mbPmView9771 ∧
    pm.nodes[1111]'(by native_decide) = l12mbPmView9789 ∧
    pm.nodes[1112]'(by native_decide) = l12mbPmTopk9732 ∧
    pm.nodes[1113]'(by native_decide) = l12mbPmView9754 ∧
    pm.nodes[1114]'(by native_decide) = l12mbPmView9772 ∧
    pm.nodes[1115]'(by native_decide) = l12mbPmView9790 ∧
    pm.nodes[1117]'(by native_decide) = l12mbPmSig9755 ∧
    pm.nodes[1118]'(by native_decide) = l12mbPmSwi9793 ∧
    pm.nodes[1120]'(by native_decide) = l12mbPmSig9756 ∧
    pm.nodes[1121]'(by native_decide) = l12mbPmSwi9794 := by
  native_decide

private theorem l12mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(524, 5360), (524, 5361), (523, 5359), (525, 5369), (524, 5368), (526, 5374), (525, 5373), (527, 5378), (526, 5377), (529, 5370), (528, 5369), (530, 5379), (529, 5374), (529, 5378)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1109, 9731), (1109, 9733), (1108, 9729), (1113, 9732), (1113, 9734), (1112, 9730), (1110, 9753), (1109, 9747), (1111, 9771), (1110, 9761), (1112, 9789), (1111, 9779), (1114, 9754), (1113, 9748), (1115, 9772), (1114, 9762), (1116, 9790), (1115, 9780), (1118, 9755), (1117, 9753), (1121, 9756), (1120, 9754), (1119, 9793), (1118, 9771), (1118, 9789), (1122, 9794), (1121, 9772), (1121, 9790), (1108, 5345)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12mb_cu_not_written : ∀ n ∈ pm.nodes, 5345 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_sm5360 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5359).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5360 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5359) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 523 l12mbSmTopk5360
    5359 5360 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l12mb_sm_node_facts.1 ?_
    (l12mb_nonempty_sm 524) (l12mb_sm_not_written 524 5360 (by decide))
    (l12mb_nonempty_sm 523) (l12mb_sm_not_written 523 5359 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l12mbSmTopk5360
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5359 5360 5361 5362 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_sm5361 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5359).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5361 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5359) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 523 l12mbSmTopk5360
    5359 5361 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l12mb_sm_node_facts.1 ?_
    (l12mb_nonempty_sm 524) (l12mb_sm_not_written 524 5361 (by decide))
    (l12mb_nonempty_sm 523) (l12mb_sm_not_written 523 5359 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l12mbSmTopk5360
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5359 5360 5361 5362 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9731 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9729).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9731 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9729) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1108 l12mbPmTopk9731
    9729 9731 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l12mb_pm_node_facts.1 ?_
    (l12mb_nonempty_pm 1109) (l12mb_pm_not_written 1109 9731 (by decide))
    (l12mb_nonempty_pm 1108) (l12mb_pm_not_written 1108 9729 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l12mbPmTopk9731
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 9729 9731 9733 9735 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9733 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9729).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9733 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9729) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1108 l12mbPmTopk9731
    9729 9733 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l12mb_pm_node_facts.1 ?_
    (l12mb_nonempty_pm 1109) (l12mb_pm_not_written 1109 9733 (by decide))
    (l12mb_nonempty_pm 1108) (l12mb_pm_not_written 1108 9729 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l12mbPmTopk9731
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 9729 9731 9733 9735 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9732 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9730).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9732 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9730) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1112 l12mbPmTopk9732
    9730 9732 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1113) (l12mb_pm_not_written 1113 9732 (by decide))
    (l12mb_nonempty_pm 1112) (l12mb_pm_not_written 1112 9730 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l12mbPmTopk9732
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 9730 9732 9734 9736 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9734 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 9730).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 9734 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 9730) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1112 l12mbPmTopk9732
    9730 9734 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1113) (l12mb_pm_not_written 1113 9734 (by decide))
    (l12mb_nonempty_pm 1112) (l12mb_pm_not_written 1112 9730 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l12mbPmTopk9732
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 9730 9732 9734 9736 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_sm5369 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5369 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5368) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 524 l12mbSmView5369
    5368 5369 (fun x => fw_view [4096,1] x)
    (by native_decide) l12mb_sm_node_facts.2.1 ?_
    (l12mb_nonempty_sm 525) (l12mb_sm_not_written 525 5369 (by decide))
    (l12mb_nonempty_sm 524) (l12mb_sm_not_written 524 5368 (by decide))
  intro s
  unfold l12mbSmView5369
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5368 5369

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_sm5374 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5374 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5373) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 525 l12mbSmView5374
    5373 5374 (fun x => fw_view [4096,512] x)
    (by native_decide) l12mb_sm_node_facts.2.2.1 ?_
    (l12mb_nonempty_sm 526) (l12mb_sm_not_written 526 5374 (by decide))
    (l12mb_nonempty_sm 525) (l12mb_sm_not_written 525 5373 (by decide))
  intro s
  unfold l12mbSmView5374
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5373 5374

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_sm5378 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5378 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5377) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 526 l12mbSmView5378
    5377 5378 (fun x => fw_view [4096,512] x)
    (by native_decide) l12mb_sm_node_facts.2.2.2.1 ?_
    (l12mb_nonempty_sm 527) (l12mb_sm_not_written 527 5378 (by decide))
    (l12mb_nonempty_sm 526) (l12mb_sm_not_written 526 5377 (by decide))
  intro s
  unfold l12mbSmView5378
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5377 5378

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9753 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9753 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 9747) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1109 l12mbPmView9753
    9747 9753 (fun x => fw_view [2048,1] x)
    (by native_decide) l12mb_pm_node_facts.2.1 ?_
    (l12mb_nonempty_pm 1110) (l12mb_pm_not_written 1110 9753 (by decide))
    (l12mb_nonempty_pm 1109) (l12mb_pm_not_written 1109 9747 (by decide))
  intro s
  unfold l12mbPmView9753
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 9747 9753

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9754 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9754 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 9748) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1113 l12mbPmView9754
    9748 9754 (fun x => fw_view [2048,1] x)
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1114) (l12mb_pm_not_written 1114 9754 (by decide))
    (l12mb_nonempty_pm 1113) (l12mb_pm_not_written 1113 9748 (by decide))
  intro s
  unfold l12mbPmView9754
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 9748 9754

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9771 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9771 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9761) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1110 l12mbPmView9771
    9761 9771 (fun x => fw_view [2048,512] x)
    (by native_decide) l12mb_pm_node_facts.2.2.1 ?_
    (l12mb_nonempty_pm 1111) (l12mb_pm_not_written 1111 9771 (by decide))
    (l12mb_nonempty_pm 1110) (l12mb_pm_not_written 1110 9761 (by decide))
  intro s
  unfold l12mbPmView9771
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 9761 9771

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9772 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9772 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9762) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1114 l12mbPmView9772
    9762 9772 (fun x => fw_view [2048,512] x)
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1115) (l12mb_pm_not_written 1115 9772 (by decide))
    (l12mb_nonempty_pm 1114) (l12mb_pm_not_written 1114 9762 (by decide))
  intro s
  unfold l12mbPmView9772
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 9762 9772

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9789 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9789 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9779) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1111 l12mbPmView9789
    9779 9789 (fun x => fw_view [2048,512] x)
    (by native_decide) l12mb_pm_node_facts.2.2.2.1 ?_
    (l12mb_nonempty_pm 1112) (l12mb_pm_not_written 1112 9789 (by decide))
    (l12mb_nonempty_pm 1111) (l12mb_pm_not_written 1111 9779 (by decide))
  intro s
  unfold l12mbPmView9789
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 9779 9789

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9790 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9790 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 9780) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1115 l12mbPmView9790
    9780 9790 (fun x => fw_view [2048,512] x)
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1116) (l12mb_pm_not_written 1116 9790 (by decide))
    (l12mb_nonempty_pm 1115) (l12mb_pm_not_written 1115 9780 (by decide))
  intro s
  unfold l12mbPmView9790
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 9780 9790

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_sm5370 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5370 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5369) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 528 l12mbSmSig5370
    5369 5370 fw_sigmoid
    (by native_decide) l12mb_sm_node_facts.2.2.2.2.1 ?_
    (l12mb_nonempty_sm 529) (l12mb_sm_not_written 529 5370 (by decide))
    (l12mb_nonempty_sm 528) (l12mb_sm_not_written 528 5369 (by decide))
  intro s
  unfold l12mbSmSig5370
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5369 5370

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9755 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9755 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 9753) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1117 l12mbPmSig9755
    9753 9755 fw_sigmoid
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1118) (l12mb_pm_not_written 1118 9755 (by decide))
    (l12mb_nonempty_pm 1117) (l12mb_pm_not_written 1117 9753 (by decide))
  intro s
  unfold l12mbPmSig9755
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 9753 9755

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9756 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9756 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 9754) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1120 l12mbPmSig9756
    9754 9756 fw_sigmoid
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1121) (l12mb_pm_not_written 1121 9756 (by decide))
    (l12mb_nonempty_pm 1120) (l12mb_pm_not_written 1120 9754 (by decide))
  intro s
  unfold l12mbPmSig9756
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 9754 9756

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_sm5379 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5379 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5374)
        (denoteGraphDistributedFaithful sm initSM 5378) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 529 l12mbSmSwi5379
    5374 5378 5379 fw_swiglu
    (by native_decide) l12mb_sm_node_facts.2.2.2.2.2 ?_
    (l12mb_nonempty_sm 530) (l12mb_sm_not_written 530 5379 (by decide))
    (l12mb_nonempty_sm 529) (l12mb_sm_not_written 529 5374 (by decide))
    (l12mb_sm_not_written 529 5378 (by decide))
  intro s
  unfold l12mbSmSwi5379
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5374 5378 5379

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9793 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9793 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 9771)
        (denoteGraphDistributedFaithful pm initPM 9789) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1118 l12mbPmSwi9793
    9771 9789 9793 fw_swiglu
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l12mb_nonempty_pm 1119) (l12mb_pm_not_written 1119 9793 (by decide))
    (l12mb_nonempty_pm 1118) (l12mb_pm_not_written 1118 9771 (by decide))
    (l12mb_pm_not_written 1118 9789 (by decide))
  intro s
  unfold l12mbPmSwi9793
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 9771 9789 9793

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_red_pm9794 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9794 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 9772)
        (denoteGraphDistributedFaithful pm initPM 9790) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1121 l12mbPmSwi9794
    9772 9790 9794 fw_swiglu
    (by native_decide) l12mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l12mb_nonempty_pm 1122) (l12mb_pm_not_written 1122 9794 (by decide))
    (l12mb_nonempty_pm 1121) (l12mb_pm_not_written 1121 9772 (by decide))
    (l12mb_pm_not_written 1121 9790 (by decide))
  intro s
  unfold l12mbPmSwi9794
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 9772 9790 9794

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5345).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5345 = initPM 5345 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5345
      layer1_pm_nodes_nonempty l12mb_cu_not_written
  rw [e2]
  exact hPM 5345 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5345) = [0, 2 * 2048] := by
  have hcuShape := l12mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5345)).length = 2 := by
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
theorem recon_zigzagGoal_5360_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5360)
      (denoteGraphDistributedFaithful pm initPM 9731)
      (denoteGraphDistributedFaithful pm initPM 9732)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5359_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l12mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5359)
      (denoteGraphDistributedFaithful pm initPM 9729)
      (denoteGraphDistributedFaithful pm initPM 9730)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l12mb_red_sm5360 initSM hs.full_shape,
    l12mb_red_pm9731 initPM hs.rank0_shape,
    l12mb_red_pm9732 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5361_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5361)
      (denoteGraphDistributedFaithful pm initPM 9733)
      (denoteGraphDistributedFaithful pm initPM 9734)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5359_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l12mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5359)
      (denoteGraphDistributedFaithful pm initPM 9729)
      (denoteGraphDistributedFaithful pm initPM 9730)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l12mb_red_sm5361 initSM hs.full_shape,
    l12mb_red_pm9733 initPM hs.rank0_shape,
    l12mb_red_pm9734 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5369_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5369)
      (denoteGraphDistributedFaithful pm initPM 9753)
      (denoteGraphDistributedFaithful pm initPM 9754)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5368_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12mb_red_sm5369 initSM, l12mb_red_pm9753 initPM, l12mb_red_pm9754 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5374_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5374)
      (denoteGraphDistributedFaithful pm initPM 9771)
      (denoteGraphDistributedFaithful pm initPM 9772)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5373_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12mb_red_sm5374 initSM, l12mb_red_pm9771 initPM, l12mb_red_pm9772 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5378_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5378)
      (denoteGraphDistributedFaithful pm initPM 9789)
      (denoteGraphDistributedFaithful pm initPM 9790)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5377_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12mb_red_sm5378 initSM, l12mb_red_pm9789 initPM, l12mb_red_pm9790 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5370_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5370)
      (denoteGraphDistributedFaithful pm initPM 9755)
      (denoteGraphDistributedFaithful pm initPM 9756)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5369_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5369)
      (denoteGraphDistributedFaithful pm initPM 9753)
      (denoteGraphDistributedFaithful pm initPM 9754)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l12mb_red_sm5370 initSM, l12mb_red_pm9755 initPM, l12mb_red_pm9756 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5379_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5379)
      (denoteGraphDistributedFaithful pm initPM 9793)
      (denoteGraphDistributedFaithful pm initPM 9794)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5374_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5378_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5374)
      (denoteGraphDistributedFaithful pm initPM 9771)
      (denoteGraphDistributedFaithful pm initPM 9772)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5378)
      (denoteGraphDistributedFaithful pm initPM 9789)
      (denoteGraphDistributedFaithful pm initPM 9790)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l12mb_red_sm5379 initSM, l12mb_red_pm9793 initPM, l12mb_red_pm9794 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
