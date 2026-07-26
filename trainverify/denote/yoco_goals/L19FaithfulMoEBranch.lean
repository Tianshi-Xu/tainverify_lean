/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L19FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-7 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-6 段 `L13FaithfulMoEBranch` to block 7.
The block-7 cu tensor is **5688**.

* SM 768 `FW_topk_routing [5702] → [5703, 5704, 5705]` params `[8, 1]`
    (PM 1598 / 1602 → `10935, 10937, 10939` / `10936, 10938, 10940`)
* SM 769 `FW_view [5711] → [5712]` params `[4096, 1]`        (PM 1599 / 1603 → 10957 / 10958)
* SM 770 `FW_view [5716] → [5717]` params `[4096, 512]`      (PM 1600 / 1604 → 10975 / 10976)
* SM 771 `FW_view [5720] → [5721]` params `[4096, 512]`      (PM 1601 / 1605 → 10993 / 10994)
* SM 773 `FW_sigmoid [5712] → [5713]`                        (PM 1607 / 1610 → 10959 / 10960)
* SM 774 `FW_swiglu [5717, 5721] → [5722]`                   (PM 1608 / 1611 → 10997 / 10998)

The third `FW_topk_routing` output (`5705`) has no intermediate goal and is therefore
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

private def l19mbSmTopk5703 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5702], outs := [5703,5704,5705],
    params := [8,1] }
private def l19mbSmView5712 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5711], outs := [5712], params := [4096,1] }
private def l19mbSmView5717 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5716], outs := [5717], params := [4096,512] }
private def l19mbSmView5721 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5720], outs := [5721], params := [4096,512] }
private def l19mbSmSig5713 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5712], outs := [5713] }
private def l19mbSmSwi5722 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5717,5721], outs := [5722] }

private def l19mbPmTopk10935 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10933], outs := [10935,10937,10939],
    params := [8,1] }
private def l19mbPmView10957 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10951], outs := [10957], params := [2048,1] }
private def l19mbPmView10975 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10965], outs := [10975], params := [2048,512] }
private def l19mbPmView10993 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10983], outs := [10993], params := [2048,512] }
private def l19mbPmTopk10936 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10934], outs := [10936,10938,10940],
    params := [8,1] }
private def l19mbPmView10958 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10952], outs := [10958], params := [2048,1] }
private def l19mbPmView10976 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10966], outs := [10976], params := [2048,512] }
private def l19mbPmView10994 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10984], outs := [10994], params := [2048,512] }
private def l19mbPmSig10959 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10957], outs := [10959] }
private def l19mbPmSwi10997 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10975,10993], outs := [10997] }
private def l19mbPmSig10960 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10958], outs := [10960] }
private def l19mbPmSwi10998 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10976,10994], outs := [10998] }

/-! ### Certified node indices -/

private theorem l19mb_sm_node_facts :
    sm.nodes[768]'(by native_decide) = l19mbSmTopk5703 ∧
    sm.nodes[769]'(by native_decide) = l19mbSmView5712 ∧
    sm.nodes[770]'(by native_decide) = l19mbSmView5717 ∧
    sm.nodes[771]'(by native_decide) = l19mbSmView5721 ∧
    sm.nodes[773]'(by native_decide) = l19mbSmSig5713 ∧
    sm.nodes[774]'(by native_decide) = l19mbSmSwi5722 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l19mb_pm_node_facts :
    pm.nodes[1598]'(by native_decide) = l19mbPmTopk10935 ∧
    pm.nodes[1599]'(by native_decide) = l19mbPmView10957 ∧
    pm.nodes[1600]'(by native_decide) = l19mbPmView10975 ∧
    pm.nodes[1601]'(by native_decide) = l19mbPmView10993 ∧
    pm.nodes[1602]'(by native_decide) = l19mbPmTopk10936 ∧
    pm.nodes[1603]'(by native_decide) = l19mbPmView10958 ∧
    pm.nodes[1604]'(by native_decide) = l19mbPmView10976 ∧
    pm.nodes[1605]'(by native_decide) = l19mbPmView10994 ∧
    pm.nodes[1607]'(by native_decide) = l19mbPmSig10959 ∧
    pm.nodes[1608]'(by native_decide) = l19mbPmSwi10997 ∧
    pm.nodes[1610]'(by native_decide) = l19mbPmSig10960 ∧
    pm.nodes[1611]'(by native_decide) = l19mbPmSwi10998 := by
  native_decide

private theorem l19mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l19mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l19mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(769, 5703), (769, 5704), (768, 5702), (770, 5712), (769, 5711), (771, 5717), (770, 5716), (772, 5721), (771, 5720), (774, 5713), (773, 5712), (775, 5722), (774, 5717), (774, 5721)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l19mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1599, 10935), (1599, 10937), (1598, 10933), (1603, 10936), (1603, 10938), (1602, 10934), (1600, 10957), (1599, 10951), (1601, 10975), (1600, 10965), (1602, 10993), (1601, 10983), (1604, 10958), (1603, 10952), (1605, 10976), (1604, 10966), (1606, 10994), (1605, 10984), (1608, 10959), (1607, 10957), (1611, 10960), (1610, 10958), (1609, 10997), (1608, 10975), (1608, 10993), (1612, 10998), (1611, 10976), (1611, 10994), (1598, 5688)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l19mb_cu_not_written : ∀ n ∈ pm.nodes, 5688 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_sm5703 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5702).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5703 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5702) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 768 l19mbSmTopk5703
    5702 5703 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l19mb_sm_node_facts.1 ?_
    (l19mb_nonempty_sm 769) (l19mb_sm_not_written 769 5703 (by decide))
    (l19mb_nonempty_sm 768) (l19mb_sm_not_written 768 5702 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l19mbSmTopk5703
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5702 5703 5704 5705 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_sm5704 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5702).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5704 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5702) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 768 l19mbSmTopk5703
    5702 5704 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l19mb_sm_node_facts.1 ?_
    (l19mb_nonempty_sm 769) (l19mb_sm_not_written 769 5704 (by decide))
    (l19mb_nonempty_sm 768) (l19mb_sm_not_written 768 5702 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l19mbSmTopk5703
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5702 5703 5704 5705 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10935 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10933).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10935 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10933) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1598 l19mbPmTopk10935
    10933 10935 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l19mb_pm_node_facts.1 ?_
    (l19mb_nonempty_pm 1599) (l19mb_pm_not_written 1599 10935 (by decide))
    (l19mb_nonempty_pm 1598) (l19mb_pm_not_written 1598 10933 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l19mbPmTopk10935
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 10933 10935 10937 10939 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10937 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10933).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10937 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10933) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1598 l19mbPmTopk10935
    10933 10937 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l19mb_pm_node_facts.1 ?_
    (l19mb_nonempty_pm 1599) (l19mb_pm_not_written 1599 10937 (by decide))
    (l19mb_nonempty_pm 1598) (l19mb_pm_not_written 1598 10933 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l19mbPmTopk10935
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 10933 10935 10937 10939 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10936 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10934).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10936 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10934) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1602 l19mbPmTopk10936
    10934 10936 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1603) (l19mb_pm_not_written 1603 10936 (by decide))
    (l19mb_nonempty_pm 1602) (l19mb_pm_not_written 1602 10934 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l19mbPmTopk10936
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 10934 10936 10938 10940 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10938 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 10934).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 10938 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 10934) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1602 l19mbPmTopk10936
    10934 10938 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1603) (l19mb_pm_not_written 1603 10938 (by decide))
    (l19mb_nonempty_pm 1602) (l19mb_pm_not_written 1602 10934 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l19mbPmTopk10936
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 10934 10936 10938 10940 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_sm5712 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5712 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5711) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 769 l19mbSmView5712
    5711 5712 (fun x => fw_view [4096,1] x)
    (by native_decide) l19mb_sm_node_facts.2.1 ?_
    (l19mb_nonempty_sm 770) (l19mb_sm_not_written 770 5712 (by decide))
    (l19mb_nonempty_sm 769) (l19mb_sm_not_written 769 5711 (by decide))
  intro s
  unfold l19mbSmView5712
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5711 5712

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_sm5717 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5717 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5716) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 770 l19mbSmView5717
    5716 5717 (fun x => fw_view [4096,512] x)
    (by native_decide) l19mb_sm_node_facts.2.2.1 ?_
    (l19mb_nonempty_sm 771) (l19mb_sm_not_written 771 5717 (by decide))
    (l19mb_nonempty_sm 770) (l19mb_sm_not_written 770 5716 (by decide))
  intro s
  unfold l19mbSmView5717
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5716 5717

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_sm5721 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5721 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5720) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 771 l19mbSmView5721
    5720 5721 (fun x => fw_view [4096,512] x)
    (by native_decide) l19mb_sm_node_facts.2.2.2.1 ?_
    (l19mb_nonempty_sm 772) (l19mb_sm_not_written 772 5721 (by decide))
    (l19mb_nonempty_sm 771) (l19mb_sm_not_written 771 5720 (by decide))
  intro s
  unfold l19mbSmView5721
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5720 5721

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10957 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10957 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10951) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1599 l19mbPmView10957
    10951 10957 (fun x => fw_view [2048,1] x)
    (by native_decide) l19mb_pm_node_facts.2.1 ?_
    (l19mb_nonempty_pm 1600) (l19mb_pm_not_written 1600 10957 (by decide))
    (l19mb_nonempty_pm 1599) (l19mb_pm_not_written 1599 10951 (by decide))
  intro s
  unfold l19mbPmView10957
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 10951 10957

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10975 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10975 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10965) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1600 l19mbPmView10975
    10965 10975 (fun x => fw_view [2048,512] x)
    (by native_decide) l19mb_pm_node_facts.2.2.1 ?_
    (l19mb_nonempty_pm 1601) (l19mb_pm_not_written 1601 10975 (by decide))
    (l19mb_nonempty_pm 1600) (l19mb_pm_not_written 1600 10965 (by decide))
  intro s
  unfold l19mbPmView10975
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10965 10975

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10993 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10993 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10983) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1601 l19mbPmView10993
    10983 10993 (fun x => fw_view [2048,512] x)
    (by native_decide) l19mb_pm_node_facts.2.2.2.1 ?_
    (l19mb_nonempty_pm 1602) (l19mb_pm_not_written 1602 10993 (by decide))
    (l19mb_nonempty_pm 1601) (l19mb_pm_not_written 1601 10983 (by decide))
  intro s
  unfold l19mbPmView10993
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 10983 10993

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10958 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10958 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 10952) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1603 l19mbPmView10958
    10952 10958 (fun x => fw_view [2048,1] x)
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1604) (l19mb_pm_not_written 1604 10958 (by decide))
    (l19mb_nonempty_pm 1603) (l19mb_pm_not_written 1603 10952 (by decide))
  intro s
  unfold l19mbPmView10958
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 10952 10958

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10976 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10976 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10966) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1604 l19mbPmView10976
    10966 10976 (fun x => fw_view [2048,512] x)
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1605) (l19mb_pm_not_written 1605 10976 (by decide))
    (l19mb_nonempty_pm 1604) (l19mb_pm_not_written 1604 10966 (by decide))
  intro s
  unfold l19mbPmView10976
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10966 10976

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10994 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10994 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10984) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1605 l19mbPmView10994
    10984 10994 (fun x => fw_view [2048,512] x)
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1606) (l19mb_pm_not_written 1606 10994 (by decide))
    (l19mb_nonempty_pm 1605) (l19mb_pm_not_written 1605 10984 (by decide))
  intro s
  unfold l19mbPmView10994
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 10984 10994

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_sm5713 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5713 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5712) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 773 l19mbSmSig5713
    5712 5713 fw_sigmoid
    (by native_decide) l19mb_sm_node_facts.2.2.2.2.1 ?_
    (l19mb_nonempty_sm 774) (l19mb_sm_not_written 774 5713 (by decide))
    (l19mb_nonempty_sm 773) (l19mb_sm_not_written 773 5712 (by decide))
  intro s
  unfold l19mbSmSig5713
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5712 5713

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10959 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10959 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10957) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1607 l19mbPmSig10959
    10957 10959 fw_sigmoid
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1608) (l19mb_pm_not_written 1608 10959 (by decide))
    (l19mb_nonempty_pm 1607) (l19mb_pm_not_written 1607 10957 (by decide))
  intro s
  unfold l19mbPmSig10959
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 10957 10959

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10960 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10960 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 10958) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1610 l19mbPmSig10960
    10958 10960 fw_sigmoid
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1611) (l19mb_pm_not_written 1611 10960 (by decide))
    (l19mb_nonempty_pm 1610) (l19mb_pm_not_written 1610 10958 (by decide))
  intro s
  unfold l19mbPmSig10960
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 10958 10960

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_sm5722 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5722 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5717)
        (denoteGraphDistributedFaithful sm initSM 5721) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 774 l19mbSmSwi5722
    5717 5721 5722 fw_swiglu
    (by native_decide) l19mb_sm_node_facts.2.2.2.2.2 ?_
    (l19mb_nonempty_sm 775) (l19mb_sm_not_written 775 5722 (by decide))
    (l19mb_nonempty_sm 774) (l19mb_sm_not_written 774 5717 (by decide))
    (l19mb_sm_not_written 774 5721 (by decide))
  intro s
  unfold l19mbSmSwi5722
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5717 5721 5722

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10997 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10997 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10975)
        (denoteGraphDistributedFaithful pm initPM 10993) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1608 l19mbPmSwi10997
    10975 10993 10997 fw_swiglu
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l19mb_nonempty_pm 1609) (l19mb_pm_not_written 1609 10997 (by decide))
    (l19mb_nonempty_pm 1608) (l19mb_pm_not_written 1608 10975 (by decide))
    (l19mb_pm_not_written 1608 10993 (by decide))
  intro s
  unfold l19mbPmSwi10997
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 10975 10993 10997

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_red_pm10998 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10998 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 10976)
        (denoteGraphDistributedFaithful pm initPM 10994) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1611 l19mbPmSwi10998
    10976 10994 10998 fw_swiglu
    (by native_decide) l19mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19mb_nonempty_pm 1612) (l19mb_pm_not_written 1612 10998 (by decide))
    (l19mb_nonempty_pm 1611) (l19mb_pm_not_written 1611 10976 (by decide))
    (l19mb_pm_not_written 1611 10994 (by decide))
  intro s
  unfold l19mbPmSwi10998
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 10976 10994 10998

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5688).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5688 = initPM 5688 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5688
      layer1_pm_nodes_nonempty l19mb_cu_not_written
  rw [e2]
  exact hPM 5688 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5688) = [0, 2 * 2048] := by
  have hcuShape := l19mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5688)).length = 2 := by
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
theorem recon_zigzagGoal_5703_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5703)
      (denoteGraphDistributedFaithful pm initPM 10935)
      (denoteGraphDistributedFaithful pm initPM 10936)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5702_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l19mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5702)
      (denoteGraphDistributedFaithful pm initPM 10933)
      (denoteGraphDistributedFaithful pm initPM 10934)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l19mb_red_sm5703 initSM hs.full_shape,
    l19mb_red_pm10935 initPM hs.rank0_shape,
    l19mb_red_pm10936 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5704_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5704)
      (denoteGraphDistributedFaithful pm initPM 10937)
      (denoteGraphDistributedFaithful pm initPM 10938)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5702_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l19mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5702)
      (denoteGraphDistributedFaithful pm initPM 10933)
      (denoteGraphDistributedFaithful pm initPM 10934)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l19mb_red_sm5704 initSM hs.full_shape,
    l19mb_red_pm10937 initPM hs.rank0_shape,
    l19mb_red_pm10938 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5712_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5712)
      (denoteGraphDistributedFaithful pm initPM 10957)
      (denoteGraphDistributedFaithful pm initPM 10958)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5711_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19mb_red_sm5712 initSM, l19mb_red_pm10957 initPM, l19mb_red_pm10958 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5717_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5717)
      (denoteGraphDistributedFaithful pm initPM 10975)
      (denoteGraphDistributedFaithful pm initPM 10976)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5716_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19mb_red_sm5717 initSM, l19mb_red_pm10975 initPM, l19mb_red_pm10976 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5721_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5721)
      (denoteGraphDistributedFaithful pm initPM 10993)
      (denoteGraphDistributedFaithful pm initPM 10994)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5720_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19mb_red_sm5721 initSM, l19mb_red_pm10993 initPM, l19mb_red_pm10994 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5713_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5713)
      (denoteGraphDistributedFaithful pm initPM 10959)
      (denoteGraphDistributedFaithful pm initPM 10960)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5712_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5712)
      (denoteGraphDistributedFaithful pm initPM 10957)
      (denoteGraphDistributedFaithful pm initPM 10958)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l19mb_red_sm5713 initSM, l19mb_red_pm10959 initPM, l19mb_red_pm10960 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5722_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5722)
      (denoteGraphDistributedFaithful pm initPM 10997)
      (denoteGraphDistributedFaithful pm initPM 10998)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5717_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5721_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5717)
      (denoteGraphDistributedFaithful pm initPM 10975)
      (denoteGraphDistributedFaithful pm initPM 10976)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5721)
      (denoteGraphDistributedFaithful pm initPM 10993)
      (denoteGraphDistributedFaithful pm initPM 10994)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l19mb_red_sm5722 initSM, l19mb_red_pm10997 initPM, l19mb_red_pm10998 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
