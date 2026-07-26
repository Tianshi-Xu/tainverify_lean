/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L23FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-11 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-10 段 `L13FaithfulMoEBranch` to block 11.
The block-11 cu tensor is **5884**.

* SM 908 `FW_topk_routing [5898] → [5899, 5900, 5901]` params `[8, 1]`
    (PM 1878 / 1882 → `11623, 11625, 11627` / `11624, 11626, 11628`)
* SM 909 `FW_view [5907] → [5908]` params `[4096, 1]`        (PM 1879 / 1883 → 11645 / 11646)
* SM 910 `FW_view [5912] → [5913]` params `[4096, 512]`      (PM 1880 / 1884 → 11663 / 11664)
* SM 911 `FW_view [5916] → [5917]` params `[4096, 512]`      (PM 1881 / 1885 → 11681 / 11682)
* SM 913 `FW_sigmoid [5908] → [5909]`                        (PM 1887 / 1890 → 11647 / 11648)
* SM 914 `FW_swiglu [5913, 5917] → [5918]`                   (PM 1888 / 1891 → 11685 / 11686)

The third `FW_topk_routing` output (`5901`) has no intermediate goal and is therefore
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

private def l23mbSmTopk5899 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899,5900,5901],
    params := [8,1] }
private def l23mbSmView5908 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5907], outs := [5908], params := [4096,1] }
private def l23mbSmView5913 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5912], outs := [5913], params := [4096,512] }
private def l23mbSmView5917 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5916], outs := [5917], params := [4096,512] }
private def l23mbSmSig5909 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5908], outs := [5909] }
private def l23mbSmSwi5918 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5913,5917], outs := [5918] }

private def l23mbPmTopk11623 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623,11625,11627],
    params := [8,1] }
private def l23mbPmView11645 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11639], outs := [11645], params := [2048,1] }
private def l23mbPmView11663 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11653], outs := [11663], params := [2048,512] }
private def l23mbPmView11681 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11671], outs := [11681], params := [2048,512] }
private def l23mbPmTopk11624 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624,11626,11628],
    params := [8,1] }
private def l23mbPmView11646 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11640], outs := [11646], params := [2048,1] }
private def l23mbPmView11664 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11654], outs := [11664], params := [2048,512] }
private def l23mbPmView11682 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11672], outs := [11682], params := [2048,512] }
private def l23mbPmSig11647 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11645], outs := [11647] }
private def l23mbPmSwi11685 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11663,11681], outs := [11685] }
private def l23mbPmSig11648 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11646], outs := [11648] }
private def l23mbPmSwi11686 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11664,11682], outs := [11686] }

/-! ### Certified node indices -/

private theorem l23mb_sm_node_facts :
    sm.nodes[908]'(by native_decide) = l23mbSmTopk5899 ∧
    sm.nodes[909]'(by native_decide) = l23mbSmView5908 ∧
    sm.nodes[910]'(by native_decide) = l23mbSmView5913 ∧
    sm.nodes[911]'(by native_decide) = l23mbSmView5917 ∧
    sm.nodes[915]'(by native_decide) = l23mbSmSig5909 ∧
    sm.nodes[916]'(by native_decide) = l23mbSmSwi5918 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23mb_pm_node_facts :
    pm.nodes[1878]'(by native_decide) = l23mbPmTopk11623 ∧
    pm.nodes[1879]'(by native_decide) = l23mbPmView11645 ∧
    pm.nodes[1880]'(by native_decide) = l23mbPmView11663 ∧
    pm.nodes[1881]'(by native_decide) = l23mbPmView11681 ∧
    pm.nodes[1882]'(by native_decide) = l23mbPmTopk11624 ∧
    pm.nodes[1883]'(by native_decide) = l23mbPmView11646 ∧
    pm.nodes[1884]'(by native_decide) = l23mbPmView11664 ∧
    pm.nodes[1885]'(by native_decide) = l23mbPmView11682 ∧
    pm.nodes[1889]'(by native_decide) = l23mbPmSig11647 ∧
    pm.nodes[1890]'(by native_decide) = l23mbPmSwi11685 ∧
    pm.nodes[1894]'(by native_decide) = l23mbPmSig11648 ∧
    pm.nodes[1895]'(by native_decide) = l23mbPmSwi11686 := by
  native_decide

private theorem l23mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l23mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(909, 5899), (909, 5900), (908, 5898), (910, 5908), (909, 5907), (911, 5913), (910, 5912), (912, 5917), (911, 5916), (916, 5909), (913, 5908), (917, 5918), (914, 5913), (914, 5917), (915, 5908), (916, 5913), (916, 5917)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1879, 11623), (1879, 11625), (1878, 11621), (1883, 11624), (1883, 11626), (1882, 11622), (1880, 11645), (1879, 11639), (1881, 11663), (1880, 11653), (1882, 11681), (1881, 11671), (1884, 11646), (1883, 11640), (1885, 11664), (1884, 11654), (1886, 11682), (1885, 11672), (1890, 11647), (1887, 11645), (1895, 11648), (1890, 11646), (1891, 11685), (1888, 11663), (1888, 11681), (1896, 11686), (1891, 11664), (1891, 11682), (1878, 5884), (1889, 11645), (1894, 11646), (1890, 11663), (1895, 11664), (1890, 11681), (1895, 11682)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23mb_cu_not_written : ∀ n ∈ pm.nodes, 5884 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_sm5899 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5898).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5899 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5898) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 908 l23mbSmTopk5899
    5898 5899 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l23mb_sm_node_facts.1 ?_
    (l23mb_nonempty_sm 909) (l23mb_sm_not_written 909 5899 (by decide))
    (l23mb_nonempty_sm 908) (l23mb_sm_not_written 908 5898 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l23mbSmTopk5899
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5898 5899 5900 5901 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_sm5900 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5898).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5900 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5898) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 908 l23mbSmTopk5899
    5898 5900 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l23mb_sm_node_facts.1 ?_
    (l23mb_nonempty_sm 909) (l23mb_sm_not_written 909 5900 (by decide))
    (l23mb_nonempty_sm 908) (l23mb_sm_not_written 908 5898 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l23mbSmTopk5899
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5898 5899 5900 5901 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11623 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11621).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11623 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11621) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1878 l23mbPmTopk11623
    11621 11623 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l23mb_pm_node_facts.1 ?_
    (l23mb_nonempty_pm 1879) (l23mb_pm_not_written 1879 11623 (by decide))
    (l23mb_nonempty_pm 1878) (l23mb_pm_not_written 1878 11621 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l23mbPmTopk11623
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 11621 11623 11625 11627 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11625 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11621).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11625 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11621) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1878 l23mbPmTopk11623
    11621 11625 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l23mb_pm_node_facts.1 ?_
    (l23mb_nonempty_pm 1879) (l23mb_pm_not_written 1879 11625 (by decide))
    (l23mb_nonempty_pm 1878) (l23mb_pm_not_written 1878 11621 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l23mbPmTopk11623
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 11621 11623 11625 11627 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11624 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11622).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11624 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11622) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1882 l23mbPmTopk11624
    11622 11624 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1883) (l23mb_pm_not_written 1883 11624 (by decide))
    (l23mb_nonempty_pm 1882) (l23mb_pm_not_written 1882 11622 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l23mbPmTopk11624
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 11622 11624 11626 11628 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11626 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11622).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11626 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11622) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1882 l23mbPmTopk11624
    11622 11626 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1883) (l23mb_pm_not_written 1883 11626 (by decide))
    (l23mb_nonempty_pm 1882) (l23mb_pm_not_written 1882 11622 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l23mbPmTopk11624
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 11622 11624 11626 11628 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_sm5908 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5908 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5907) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 909 l23mbSmView5908
    5907 5908 (fun x => fw_view [4096,1] x)
    (by native_decide) l23mb_sm_node_facts.2.1 ?_
    (l23mb_nonempty_sm 910) (l23mb_sm_not_written 910 5908 (by decide))
    (l23mb_nonempty_sm 909) (l23mb_sm_not_written 909 5907 (by decide))
  intro s
  unfold l23mbSmView5908
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5907 5908

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_sm5913 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5913 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5912) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 910 l23mbSmView5913
    5912 5913 (fun x => fw_view [4096,512] x)
    (by native_decide) l23mb_sm_node_facts.2.2.1 ?_
    (l23mb_nonempty_sm 911) (l23mb_sm_not_written 911 5913 (by decide))
    (l23mb_nonempty_sm 910) (l23mb_sm_not_written 910 5912 (by decide))
  intro s
  unfold l23mbSmView5913
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5912 5913

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_sm5917 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5917 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5916) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 911 l23mbSmView5917
    5916 5917 (fun x => fw_view [4096,512] x)
    (by native_decide) l23mb_sm_node_facts.2.2.2.1 ?_
    (l23mb_nonempty_sm 912) (l23mb_sm_not_written 912 5917 (by decide))
    (l23mb_nonempty_sm 911) (l23mb_sm_not_written 911 5916 (by decide))
  intro s
  unfold l23mbSmView5917
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5916 5917

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11645 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11645 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11639) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1879 l23mbPmView11645
    11639 11645 (fun x => fw_view [2048,1] x)
    (by native_decide) l23mb_pm_node_facts.2.1 ?_
    (l23mb_nonempty_pm 1880) (l23mb_pm_not_written 1880 11645 (by decide))
    (l23mb_nonempty_pm 1879) (l23mb_pm_not_written 1879 11639 (by decide))
  intro s
  unfold l23mbPmView11645
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 11639 11645

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11663 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11663 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11653) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1880 l23mbPmView11663
    11653 11663 (fun x => fw_view [2048,512] x)
    (by native_decide) l23mb_pm_node_facts.2.2.1 ?_
    (l23mb_nonempty_pm 1881) (l23mb_pm_not_written 1881 11663 (by decide))
    (l23mb_nonempty_pm 1880) (l23mb_pm_not_written 1880 11653 (by decide))
  intro s
  unfold l23mbPmView11663
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11653 11663

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11681 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11681 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11671) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1881 l23mbPmView11681
    11671 11681 (fun x => fw_view [2048,512] x)
    (by native_decide) l23mb_pm_node_facts.2.2.2.1 ?_
    (l23mb_nonempty_pm 1882) (l23mb_pm_not_written 1882 11681 (by decide))
    (l23mb_nonempty_pm 1881) (l23mb_pm_not_written 1881 11671 (by decide))
  intro s
  unfold l23mbPmView11681
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11671 11681

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11646 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11646 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11640) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1883 l23mbPmView11646
    11640 11646 (fun x => fw_view [2048,1] x)
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1884) (l23mb_pm_not_written 1884 11646 (by decide))
    (l23mb_nonempty_pm 1883) (l23mb_pm_not_written 1883 11640 (by decide))
  intro s
  unfold l23mbPmView11646
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 11640 11646

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11664 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11664 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11654) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1884 l23mbPmView11664
    11654 11664 (fun x => fw_view [2048,512] x)
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1885) (l23mb_pm_not_written 1885 11664 (by decide))
    (l23mb_nonempty_pm 1884) (l23mb_pm_not_written 1884 11654 (by decide))
  intro s
  unfold l23mbPmView11664
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11654 11664

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11682 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11682 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11672) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1885 l23mbPmView11682
    11672 11682 (fun x => fw_view [2048,512] x)
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1886) (l23mb_pm_not_written 1886 11682 (by decide))
    (l23mb_nonempty_pm 1885) (l23mb_pm_not_written 1885 11672 (by decide))
  intro s
  unfold l23mbPmView11682
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11672 11682

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_sm5909 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5909 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5908) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 915 l23mbSmSig5909
    5908 5909 fw_sigmoid
    (by native_decide) l23mb_sm_node_facts.2.2.2.2.1 ?_
    (l23mb_nonempty_sm 916) (l23mb_sm_not_written 916 5909 (by decide))
    (l23mb_nonempty_sm 915) (l23mb_sm_not_written 915 5908 (by decide))
  intro s
  unfold l23mbSmSig5909
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5908 5909

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11647 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11647 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11645) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1889 l23mbPmSig11647
    11645 11647 fw_sigmoid
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1890) (l23mb_pm_not_written 1890 11647 (by decide))
    (l23mb_nonempty_pm 1889) (l23mb_pm_not_written 1889 11645 (by decide))
  intro s
  unfold l23mbPmSig11647
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 11645 11647

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11648 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11648 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11646) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1894 l23mbPmSig11648
    11646 11648 fw_sigmoid
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1895) (l23mb_pm_not_written 1895 11648 (by decide))
    (l23mb_nonempty_pm 1894) (l23mb_pm_not_written 1894 11646 (by decide))
  intro s
  unfold l23mbPmSig11648
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 11646 11648

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_sm5918 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5918 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5913)
        (denoteGraphDistributedFaithful sm initSM 5917) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 916 l23mbSmSwi5918
    5913 5917 5918 fw_swiglu
    (by native_decide) l23mb_sm_node_facts.2.2.2.2.2 ?_
    (l23mb_nonempty_sm 917) (l23mb_sm_not_written 917 5918 (by decide))
    (l23mb_nonempty_sm 916) (l23mb_sm_not_written 916 5913 (by decide))
    (l23mb_sm_not_written 916 5917 (by decide))
  intro s
  unfold l23mbSmSwi5918
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5913 5917 5918

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11685 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11685 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11663)
        (denoteGraphDistributedFaithful pm initPM 11681) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1890 l23mbPmSwi11685
    11663 11681 11685 fw_swiglu
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l23mb_nonempty_pm 1891) (l23mb_pm_not_written 1891 11685 (by decide))
    (l23mb_nonempty_pm 1890) (l23mb_pm_not_written 1890 11663 (by decide))
    (l23mb_pm_not_written 1890 11681 (by decide))
  intro s
  unfold l23mbPmSwi11685
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 11663 11681 11685

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_red_pm11686 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11686 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11664)
        (denoteGraphDistributedFaithful pm initPM 11682) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1895 l23mbPmSwi11686
    11664 11682 11686 fw_swiglu
    (by native_decide) l23mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23mb_nonempty_pm 1896) (l23mb_pm_not_written 1896 11686 (by decide))
    (l23mb_nonempty_pm 1895) (l23mb_pm_not_written 1895 11664 (by decide))
    (l23mb_pm_not_written 1895 11682 (by decide))
  intro s
  unfold l23mbPmSwi11686
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 11664 11682 11686

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5884).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5884 = initPM 5884 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5884
      layer1_pm_nodes_nonempty l23mb_cu_not_written
  rw [e2]
  exact hPM 5884 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5884) = [0, 2 * 2048] := by
  have hcuShape := l23mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5884)).length = 2 := by
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
theorem recon_zigzagGoal_5899_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5899)
      (denoteGraphDistributedFaithful pm initPM 11623)
      (denoteGraphDistributedFaithful pm initPM 11624)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5898_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l23mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5898)
      (denoteGraphDistributedFaithful pm initPM 11621)
      (denoteGraphDistributedFaithful pm initPM 11622)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l23mb_red_sm5899 initSM hs.full_shape,
    l23mb_red_pm11623 initPM hs.rank0_shape,
    l23mb_red_pm11624 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5900_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5900)
      (denoteGraphDistributedFaithful pm initPM 11625)
      (denoteGraphDistributedFaithful pm initPM 11626)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5898_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l23mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5898)
      (denoteGraphDistributedFaithful pm initPM 11621)
      (denoteGraphDistributedFaithful pm initPM 11622)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l23mb_red_sm5900 initSM hs.full_shape,
    l23mb_red_pm11625 initPM hs.rank0_shape,
    l23mb_red_pm11626 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5908_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5908)
      (denoteGraphDistributedFaithful pm initPM 11645)
      (denoteGraphDistributedFaithful pm initPM 11646)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5907_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23mb_red_sm5908 initSM, l23mb_red_pm11645 initPM, l23mb_red_pm11646 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5913_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5913)
      (denoteGraphDistributedFaithful pm initPM 11663)
      (denoteGraphDistributedFaithful pm initPM 11664)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5912_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23mb_red_sm5913 initSM, l23mb_red_pm11663 initPM, l23mb_red_pm11664 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5917_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5917)
      (denoteGraphDistributedFaithful pm initPM 11681)
      (denoteGraphDistributedFaithful pm initPM 11682)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5916_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23mb_red_sm5917 initSM, l23mb_red_pm11681 initPM, l23mb_red_pm11682 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5909_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5909)
      (denoteGraphDistributedFaithful pm initPM 11647)
      (denoteGraphDistributedFaithful pm initPM 11648)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5908_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5908)
      (denoteGraphDistributedFaithful pm initPM 11645)
      (denoteGraphDistributedFaithful pm initPM 11646)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l23mb_red_sm5909 initSM, l23mb_red_pm11647 initPM, l23mb_red_pm11648 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5918_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5918)
      (denoteGraphDistributedFaithful pm initPM 11685)
      (denoteGraphDistributedFaithful pm initPM 11686)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5913_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5917_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5913)
      (denoteGraphDistributedFaithful pm initPM 11663)
      (denoteGraphDistributedFaithful pm initPM 11664)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5917)
      (denoteGraphDistributedFaithful pm initPM 11681)
      (denoteGraphDistributedFaithful pm initPM 11682)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l23mb_red_sm5918 initSM, l23mb_red_pm11685 initPM, l23mb_red_pm11686 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
