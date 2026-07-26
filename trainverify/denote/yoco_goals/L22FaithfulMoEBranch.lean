/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L22FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-10 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-9 段 `L13FaithfulMoEBranch` to block 10.
The block-10 cu tensor is **5835**.

* SM 873 `FW_topk_routing [5849] → [5850, 5851, 5852]` params `[8, 1]`
    (PM 1808 / 1812 → `11451, 11453, 11455` / `11452, 11454, 11456`)
* SM 874 `FW_view [5858] → [5859]` params `[4096, 1]`        (PM 1809 / 1813 → 11473 / 11474)
* SM 875 `FW_view [5863] → [5864]` params `[4096, 512]`      (PM 1810 / 1814 → 11491 / 11492)
* SM 876 `FW_view [5867] → [5868]` params `[4096, 512]`      (PM 1811 / 1815 → 11509 / 11510)
* SM 878 `FW_sigmoid [5859] → [5860]`                        (PM 1817 / 1820 → 11475 / 11476)
* SM 879 `FW_swiglu [5864, 5868] → [5869]`                   (PM 1818 / 1821 → 11513 / 11514)

The third `FW_topk_routing` output (`5852`) has no intermediate goal and is therefore
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

private def l22mbSmTopk5850 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5849], outs := [5850,5851,5852],
    params := [8,1] }
private def l22mbSmView5859 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5858], outs := [5859], params := [4096,1] }
private def l22mbSmView5864 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5863], outs := [5864], params := [4096,512] }
private def l22mbSmView5868 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5867], outs := [5868], params := [4096,512] }
private def l22mbSmSig5860 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5859], outs := [5860] }
private def l22mbSmSwi5869 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5864,5868], outs := [5869] }

private def l22mbPmTopk11451 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [11449], outs := [11451,11453,11455],
    params := [8,1] }
private def l22mbPmView11473 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11467], outs := [11473], params := [2048,1] }
private def l22mbPmView11491 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11481], outs := [11491], params := [2048,512] }
private def l22mbPmView11509 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11499], outs := [11509], params := [2048,512] }
private def l22mbPmTopk11452 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [11450], outs := [11452,11454,11456],
    params := [8,1] }
private def l22mbPmView11474 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11468], outs := [11474], params := [2048,1] }
private def l22mbPmView11492 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11482], outs := [11492], params := [2048,512] }
private def l22mbPmView11510 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11500], outs := [11510], params := [2048,512] }
private def l22mbPmSig11475 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11473], outs := [11475] }
private def l22mbPmSwi11513 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11491,11509], outs := [11513] }
private def l22mbPmSig11476 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11474], outs := [11476] }
private def l22mbPmSwi11514 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11492,11510], outs := [11514] }

/-! ### Certified node indices -/

private theorem l22mb_sm_node_facts :
    sm.nodes[873]'(by native_decide) = l22mbSmTopk5850 ∧
    sm.nodes[874]'(by native_decide) = l22mbSmView5859 ∧
    sm.nodes[875]'(by native_decide) = l22mbSmView5864 ∧
    sm.nodes[876]'(by native_decide) = l22mbSmView5868 ∧
    sm.nodes[878]'(by native_decide) = l22mbSmSig5860 ∧
    sm.nodes[879]'(by native_decide) = l22mbSmSwi5869 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l22mb_pm_node_facts :
    pm.nodes[1808]'(by native_decide) = l22mbPmTopk11451 ∧
    pm.nodes[1809]'(by native_decide) = l22mbPmView11473 ∧
    pm.nodes[1810]'(by native_decide) = l22mbPmView11491 ∧
    pm.nodes[1811]'(by native_decide) = l22mbPmView11509 ∧
    pm.nodes[1812]'(by native_decide) = l22mbPmTopk11452 ∧
    pm.nodes[1813]'(by native_decide) = l22mbPmView11474 ∧
    pm.nodes[1814]'(by native_decide) = l22mbPmView11492 ∧
    pm.nodes[1815]'(by native_decide) = l22mbPmView11510 ∧
    pm.nodes[1817]'(by native_decide) = l22mbPmSig11475 ∧
    pm.nodes[1818]'(by native_decide) = l22mbPmSwi11513 ∧
    pm.nodes[1820]'(by native_decide) = l22mbPmSig11476 ∧
    pm.nodes[1821]'(by native_decide) = l22mbPmSwi11514 := by
  native_decide

private theorem l22mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l22mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l22mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(874, 5850), (874, 5851), (873, 5849), (875, 5859), (874, 5858), (876, 5864), (875, 5863), (877, 5868), (876, 5867), (879, 5860), (878, 5859), (880, 5869), (879, 5864), (879, 5868)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l22mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1809, 11451), (1809, 11453), (1808, 11449), (1813, 11452), (1813, 11454), (1812, 11450), (1810, 11473), (1809, 11467), (1811, 11491), (1810, 11481), (1812, 11509), (1811, 11499), (1814, 11474), (1813, 11468), (1815, 11492), (1814, 11482), (1816, 11510), (1815, 11500), (1818, 11475), (1817, 11473), (1821, 11476), (1820, 11474), (1819, 11513), (1818, 11491), (1818, 11509), (1822, 11514), (1821, 11492), (1821, 11510), (1808, 5835)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l22mb_cu_not_written : ∀ n ∈ pm.nodes, 5835 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_sm5850 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5849).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5850 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5849) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 873 l22mbSmTopk5850
    5849 5850 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l22mb_sm_node_facts.1 ?_
    (l22mb_nonempty_sm 874) (l22mb_sm_not_written 874 5850 (by decide))
    (l22mb_nonempty_sm 873) (l22mb_sm_not_written 873 5849 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l22mbSmTopk5850
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5849 5850 5851 5852 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_sm5851 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5849).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5851 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5849) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 873 l22mbSmTopk5850
    5849 5851 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l22mb_sm_node_facts.1 ?_
    (l22mb_nonempty_sm 874) (l22mb_sm_not_written 874 5851 (by decide))
    (l22mb_nonempty_sm 873) (l22mb_sm_not_written 873 5849 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l22mbSmTopk5850
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5849 5850 5851 5852 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11451 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11449).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11451 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11449) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1808 l22mbPmTopk11451
    11449 11451 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l22mb_pm_node_facts.1 ?_
    (l22mb_nonempty_pm 1809) (l22mb_pm_not_written 1809 11451 (by decide))
    (l22mb_nonempty_pm 1808) (l22mb_pm_not_written 1808 11449 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l22mbPmTopk11451
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 11449 11451 11453 11455 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11453 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11449).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11453 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11449) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1808 l22mbPmTopk11451
    11449 11453 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l22mb_pm_node_facts.1 ?_
    (l22mb_nonempty_pm 1809) (l22mb_pm_not_written 1809 11453 (by decide))
    (l22mb_nonempty_pm 1808) (l22mb_pm_not_written 1808 11449 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l22mbPmTopk11451
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 11449 11451 11453 11455 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11452 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11450).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11452 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11450) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1812 l22mbPmTopk11452
    11450 11452 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1813) (l22mb_pm_not_written 1813 11452 (by decide))
    (l22mb_nonempty_pm 1812) (l22mb_pm_not_written 1812 11450 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l22mbPmTopk11452
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 11450 11452 11454 11456 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11454 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11450).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11454 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11450) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1812 l22mbPmTopk11452
    11450 11454 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1813) (l22mb_pm_not_written 1813 11454 (by decide))
    (l22mb_nonempty_pm 1812) (l22mb_pm_not_written 1812 11450 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l22mbPmTopk11452
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 11450 11452 11454 11456 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_sm5859 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5859 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5858) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 874 l22mbSmView5859
    5858 5859 (fun x => fw_view [4096,1] x)
    (by native_decide) l22mb_sm_node_facts.2.1 ?_
    (l22mb_nonempty_sm 875) (l22mb_sm_not_written 875 5859 (by decide))
    (l22mb_nonempty_sm 874) (l22mb_sm_not_written 874 5858 (by decide))
  intro s
  unfold l22mbSmView5859
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5858 5859

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_sm5864 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5864 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5863) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 875 l22mbSmView5864
    5863 5864 (fun x => fw_view [4096,512] x)
    (by native_decide) l22mb_sm_node_facts.2.2.1 ?_
    (l22mb_nonempty_sm 876) (l22mb_sm_not_written 876 5864 (by decide))
    (l22mb_nonempty_sm 875) (l22mb_sm_not_written 875 5863 (by decide))
  intro s
  unfold l22mbSmView5864
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5863 5864

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_sm5868 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5868 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5867) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 876 l22mbSmView5868
    5867 5868 (fun x => fw_view [4096,512] x)
    (by native_decide) l22mb_sm_node_facts.2.2.2.1 ?_
    (l22mb_nonempty_sm 877) (l22mb_sm_not_written 877 5868 (by decide))
    (l22mb_nonempty_sm 876) (l22mb_sm_not_written 876 5867 (by decide))
  intro s
  unfold l22mbSmView5868
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5867 5868

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11473 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11473 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11467) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1809 l22mbPmView11473
    11467 11473 (fun x => fw_view [2048,1] x)
    (by native_decide) l22mb_pm_node_facts.2.1 ?_
    (l22mb_nonempty_pm 1810) (l22mb_pm_not_written 1810 11473 (by decide))
    (l22mb_nonempty_pm 1809) (l22mb_pm_not_written 1809 11467 (by decide))
  intro s
  unfold l22mbPmView11473
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 11467 11473

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11491 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11491 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11481) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1810 l22mbPmView11491
    11481 11491 (fun x => fw_view [2048,512] x)
    (by native_decide) l22mb_pm_node_facts.2.2.1 ?_
    (l22mb_nonempty_pm 1811) (l22mb_pm_not_written 1811 11491 (by decide))
    (l22mb_nonempty_pm 1810) (l22mb_pm_not_written 1810 11481 (by decide))
  intro s
  unfold l22mbPmView11491
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11481 11491

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11509 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11509 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11499) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1811 l22mbPmView11509
    11499 11509 (fun x => fw_view [2048,512] x)
    (by native_decide) l22mb_pm_node_facts.2.2.2.1 ?_
    (l22mb_nonempty_pm 1812) (l22mb_pm_not_written 1812 11509 (by decide))
    (l22mb_nonempty_pm 1811) (l22mb_pm_not_written 1811 11499 (by decide))
  intro s
  unfold l22mbPmView11509
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11499 11509

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11474 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11474 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11468) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1813 l22mbPmView11474
    11468 11474 (fun x => fw_view [2048,1] x)
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1814) (l22mb_pm_not_written 1814 11474 (by decide))
    (l22mb_nonempty_pm 1813) (l22mb_pm_not_written 1813 11468 (by decide))
  intro s
  unfold l22mbPmView11474
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 11468 11474

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11492 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11492 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11482) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1814 l22mbPmView11492
    11482 11492 (fun x => fw_view [2048,512] x)
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1815) (l22mb_pm_not_written 1815 11492 (by decide))
    (l22mb_nonempty_pm 1814) (l22mb_pm_not_written 1814 11482 (by decide))
  intro s
  unfold l22mbPmView11492
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11482 11492

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11510 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11510 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11500) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1815 l22mbPmView11510
    11500 11510 (fun x => fw_view [2048,512] x)
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1816) (l22mb_pm_not_written 1816 11510 (by decide))
    (l22mb_nonempty_pm 1815) (l22mb_pm_not_written 1815 11500 (by decide))
  intro s
  unfold l22mbPmView11510
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11500 11510

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_sm5860 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5860 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5859) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 878 l22mbSmSig5860
    5859 5860 fw_sigmoid
    (by native_decide) l22mb_sm_node_facts.2.2.2.2.1 ?_
    (l22mb_nonempty_sm 879) (l22mb_sm_not_written 879 5860 (by decide))
    (l22mb_nonempty_sm 878) (l22mb_sm_not_written 878 5859 (by decide))
  intro s
  unfold l22mbSmSig5860
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5859 5860

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11475 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11475 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11473) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1817 l22mbPmSig11475
    11473 11475 fw_sigmoid
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1818) (l22mb_pm_not_written 1818 11475 (by decide))
    (l22mb_nonempty_pm 1817) (l22mb_pm_not_written 1817 11473 (by decide))
  intro s
  unfold l22mbPmSig11475
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 11473 11475

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11476 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11476 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11474) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1820 l22mbPmSig11476
    11474 11476 fw_sigmoid
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1821) (l22mb_pm_not_written 1821 11476 (by decide))
    (l22mb_nonempty_pm 1820) (l22mb_pm_not_written 1820 11474 (by decide))
  intro s
  unfold l22mbPmSig11476
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 11474 11476

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_sm5869 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5869 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5864)
        (denoteGraphDistributedFaithful sm initSM 5868) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 879 l22mbSmSwi5869
    5864 5868 5869 fw_swiglu
    (by native_decide) l22mb_sm_node_facts.2.2.2.2.2 ?_
    (l22mb_nonempty_sm 880) (l22mb_sm_not_written 880 5869 (by decide))
    (l22mb_nonempty_sm 879) (l22mb_sm_not_written 879 5864 (by decide))
    (l22mb_sm_not_written 879 5868 (by decide))
  intro s
  unfold l22mbSmSwi5869
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5864 5868 5869

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11513 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11513 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11491)
        (denoteGraphDistributedFaithful pm initPM 11509) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1818 l22mbPmSwi11513
    11491 11509 11513 fw_swiglu
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l22mb_nonempty_pm 1819) (l22mb_pm_not_written 1819 11513 (by decide))
    (l22mb_nonempty_pm 1818) (l22mb_pm_not_written 1818 11491 (by decide))
    (l22mb_pm_not_written 1818 11509 (by decide))
  intro s
  unfold l22mbPmSwi11513
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 11491 11509 11513

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_red_pm11514 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11514 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11492)
        (denoteGraphDistributedFaithful pm initPM 11510) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1821 l22mbPmSwi11514
    11492 11510 11514 fw_swiglu
    (by native_decide) l22mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22mb_nonempty_pm 1822) (l22mb_pm_not_written 1822 11514 (by decide))
    (l22mb_nonempty_pm 1821) (l22mb_pm_not_written 1821 11492 (by decide))
    (l22mb_pm_not_written 1821 11510 (by decide))
  intro s
  unfold l22mbPmSwi11514
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 11492 11510 11514

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5835).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5835 = initPM 5835 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5835
      layer1_pm_nodes_nonempty l22mb_cu_not_written
  rw [e2]
  exact hPM 5835 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5835) = [0, 2 * 2048] := by
  have hcuShape := l22mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5835)).length = 2 := by
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
theorem recon_zigzagGoal_5850_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5850)
      (denoteGraphDistributedFaithful pm initPM 11451)
      (denoteGraphDistributedFaithful pm initPM 11452)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5849_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l22mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5849)
      (denoteGraphDistributedFaithful pm initPM 11449)
      (denoteGraphDistributedFaithful pm initPM 11450)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l22mb_red_sm5850 initSM hs.full_shape,
    l22mb_red_pm11451 initPM hs.rank0_shape,
    l22mb_red_pm11452 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5851_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5851)
      (denoteGraphDistributedFaithful pm initPM 11453)
      (denoteGraphDistributedFaithful pm initPM 11454)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5849_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l22mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5849)
      (denoteGraphDistributedFaithful pm initPM 11449)
      (denoteGraphDistributedFaithful pm initPM 11450)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l22mb_red_sm5851 initSM hs.full_shape,
    l22mb_red_pm11453 initPM hs.rank0_shape,
    l22mb_red_pm11454 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5859_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5859)
      (denoteGraphDistributedFaithful pm initPM 11473)
      (denoteGraphDistributedFaithful pm initPM 11474)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5858_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22mb_red_sm5859 initSM, l22mb_red_pm11473 initPM, l22mb_red_pm11474 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5864_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5864)
      (denoteGraphDistributedFaithful pm initPM 11491)
      (denoteGraphDistributedFaithful pm initPM 11492)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5863_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22mb_red_sm5864 initSM, l22mb_red_pm11491 initPM, l22mb_red_pm11492 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5868_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5868)
      (denoteGraphDistributedFaithful pm initPM 11509)
      (denoteGraphDistributedFaithful pm initPM 11510)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5867_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22mb_red_sm5868 initSM, l22mb_red_pm11509 initPM, l22mb_red_pm11510 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5860_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5860)
      (denoteGraphDistributedFaithful pm initPM 11475)
      (denoteGraphDistributedFaithful pm initPM 11476)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5859_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5859)
      (denoteGraphDistributedFaithful pm initPM 11473)
      (denoteGraphDistributedFaithful pm initPM 11474)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l22mb_red_sm5860 initSM, l22mb_red_pm11475 initPM, l22mb_red_pm11476 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5869_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5869)
      (denoteGraphDistributedFaithful pm initPM 11513)
      (denoteGraphDistributedFaithful pm initPM 11514)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5864_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5868_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5864)
      (denoteGraphDistributedFaithful pm initPM 11491)
      (denoteGraphDistributedFaithful pm initPM 11492)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5868)
      (denoteGraphDistributedFaithful pm initPM 11509)
      (denoteGraphDistributedFaithful pm initPM 11510)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l22mb_red_sm5869 initSM, l22mb_red_pm11513 initPM, l22mb_red_pm11514 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
