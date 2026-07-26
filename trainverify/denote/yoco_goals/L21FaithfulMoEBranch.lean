/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L21FaithfulRouterProj
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-9 MoE branch (topk / views / sigmoid / swiglu)

Mechanical transport of the (green) block-8 段 `L13FaithfulMoEBranch` to block 9.
The block-9 cu tensor is **5786**.

* SM 838 `FW_topk_routing [5800] → [5801, 5802, 5803]` params `[8, 1]`
    (PM 1738 / 1742 → `11279, 11281, 11283` / `11280, 11282, 11284`)
* SM 839 `FW_view [5809] → [5810]` params `[4096, 1]`        (PM 1739 / 1743 → 11301 / 11302)
* SM 840 `FW_view [5814] → [5815]` params `[4096, 512]`      (PM 1740 / 1744 → 11319 / 11320)
* SM 841 `FW_view [5818] → [5819]` params `[4096, 512]`      (PM 1741 / 1745 → 11337 / 11338)
* SM 843 `FW_sigmoid [5810] → [5811]`                        (PM 1747 / 1750 → 11303 / 11304)
* SM 844 `FW_swiglu [5815, 5819] → [5820]`                   (PM 1748 / 1751 → 11341 / 11342)

The third `FW_topk_routing` output (`5803`) has no intermediate goal and is therefore
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

private def l21mbSmTopk5801 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5800], outs := [5801,5802,5803],
    params := [8,1] }
private def l21mbSmView5810 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5809], outs := [5810], params := [4096,1] }
private def l21mbSmView5815 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5814], outs := [5815], params := [4096,512] }
private def l21mbSmView5819 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5818], outs := [5819], params := [4096,512] }
private def l21mbSmSig5811 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5810], outs := [5811] }
private def l21mbSmSwi5820 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5815,5819], outs := [5820] }

private def l21mbPmTopk11279 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [11277], outs := [11279,11281,11283],
    params := [8,1] }
private def l21mbPmView11301 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11295], outs := [11301], params := [2048,1] }
private def l21mbPmView11319 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11309], outs := [11319], params := [2048,512] }
private def l21mbPmView11337 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11327], outs := [11337], params := [2048,512] }
private def l21mbPmTopk11280 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [11278], outs := [11280,11282,11284],
    params := [8,1] }
private def l21mbPmView11302 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11296], outs := [11302], params := [2048,1] }
private def l21mbPmView11320 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11310], outs := [11320], params := [2048,512] }
private def l21mbPmView11338 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11328], outs := [11338], params := [2048,512] }
private def l21mbPmSig11303 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11301], outs := [11303] }
private def l21mbPmSwi11341 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11319,11337], outs := [11341] }
private def l21mbPmSig11304 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11302], outs := [11304] }
private def l21mbPmSwi11342 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11320,11338], outs := [11342] }

/-! ### Certified node indices -/

private theorem l21mb_sm_node_facts :
    sm.nodes[838]'(by native_decide) = l21mbSmTopk5801 ∧
    sm.nodes[839]'(by native_decide) = l21mbSmView5810 ∧
    sm.nodes[840]'(by native_decide) = l21mbSmView5815 ∧
    sm.nodes[841]'(by native_decide) = l21mbSmView5819 ∧
    sm.nodes[843]'(by native_decide) = l21mbSmSig5811 ∧
    sm.nodes[844]'(by native_decide) = l21mbSmSwi5820 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l21mb_pm_node_facts :
    pm.nodes[1738]'(by native_decide) = l21mbPmTopk11279 ∧
    pm.nodes[1739]'(by native_decide) = l21mbPmView11301 ∧
    pm.nodes[1740]'(by native_decide) = l21mbPmView11319 ∧
    pm.nodes[1741]'(by native_decide) = l21mbPmView11337 ∧
    pm.nodes[1742]'(by native_decide) = l21mbPmTopk11280 ∧
    pm.nodes[1743]'(by native_decide) = l21mbPmView11302 ∧
    pm.nodes[1744]'(by native_decide) = l21mbPmView11320 ∧
    pm.nodes[1745]'(by native_decide) = l21mbPmView11338 ∧
    pm.nodes[1747]'(by native_decide) = l21mbPmSig11303 ∧
    pm.nodes[1748]'(by native_decide) = l21mbPmSwi11341 ∧
    pm.nodes[1750]'(by native_decide) = l21mbPmSig11304 ∧
    pm.nodes[1751]'(by native_decide) = l21mbPmSwi11342 := by
  native_decide

private theorem l21mb_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l21mb_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l21mb_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(839, 5801), (839, 5802), (838, 5800), (840, 5810), (839, 5809), (841, 5815), (840, 5814), (842, 5819), (841, 5818), (844, 5811), (843, 5810), (845, 5820), (844, 5815), (844, 5819)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l21mb_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1739, 11279), (1739, 11281), (1738, 11277), (1743, 11280), (1743, 11282), (1742, 11278), (1740, 11301), (1739, 11295), (1741, 11319), (1740, 11309), (1742, 11337), (1741, 11327), (1744, 11302), (1743, 11296), (1745, 11320), (1744, 11310), (1746, 11338), (1745, 11328), (1748, 11303), (1747, 11301), (1751, 11304), (1750, 11302), (1749, 11341), (1748, 11319), (1748, 11337), (1752, 11342), (1751, 11320), (1751, 11338), (1738, 5786)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l21mb_cu_not_written : ∀ n ∈ pm.nodes, 5786 ∉ n.outs := by
  native_decide

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_sm5801 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5800).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5801 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5800) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 838 l21mbSmTopk5801
    5800 5801 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l21mb_sm_node_facts.1 ?_
    (l21mb_nonempty_sm 839) (l21mb_sm_not_written 839 5801 (by decide))
    (l21mb_nonempty_sm 838) (l21mb_sm_not_written 838 5800 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l21mbSmTopk5801
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out sm s 0 5800 5801 5802 5803 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_sm5802 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm initSM 5800).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm initSM 5802 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm initSM 5800) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 sm initSM 838 l21mbSmTopk5801
    5800 5802 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l21mb_sm_node_facts.1 ?_
    (l21mb_nonempty_sm 839) (l21mb_sm_not_written 839 5802 (by decide))
    (l21mb_nonempty_sm 838) (l21mb_sm_not_written 838 5800 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l21mbSmTopk5801
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out sm s 0 5800 5801 5802 5803 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11279 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11277).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11279 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11277) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1738 l21mbPmTopk11279
    11277 11279 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l21mb_pm_node_facts.1 ?_
    (l21mb_nonempty_pm 1739) (l21mb_pm_not_written 1739 11279 (by decide))
    (l21mb_nonempty_pm 1738) (l21mb_pm_not_written 1738 11277 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l21mbPmTopk11279
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 0 11277 11279 11281 11283 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11281 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11277).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11281 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11277) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1738 l21mbPmTopk11279
    11277 11281 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l21mb_pm_node_facts.1 ?_
    (l21mb_nonempty_pm 1739) (l21mb_pm_not_written 1739 11281 (by decide))
    (l21mb_nonempty_pm 1738) (l21mb_pm_not_written 1738 11277 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l21mbPmTopk11279
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 0 11277 11279 11281 11283 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11280 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11278).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11280 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11278) 8 64).1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1742 l21mbPmTopk11280
    11278 11280 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1743) (l21mb_pm_not_written 1743 11280 (by decide))
    (l21mb_nonempty_pm 1742) (l21mb_pm_not_written 1742 11278 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l21mbPmTopk11280
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_probs_out pm s 1 11278 11280 11282 11284 [8,1]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11282 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm initPM 11278).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm initPM 11282 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm initPM 11278) 8 64).2.1 := by
  have hred := denoteGraphDistributedFaithful_reduce1 pm initPM 1742 l21mbPmTopk11280
    11278 11282 (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1743) (l21mb_pm_not_written 1743 11282 (by decide))
    (l21mb_nonempty_pm 1742) (l21mb_pm_not_written 1742 11278 (by decide))
  · rw [hred, hsh]
    rfl
  · intro s
    unfold l21mbPmTopk11280
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_topk_routing_map_out pm s 1 11278 11280 11282 11284 [8,1] (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_sm5810 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5810 =
      fw_view [4096,1] (denoteGraphDistributedFaithful sm initSM 5809) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 839 l21mbSmView5810
    5809 5810 (fun x => fw_view [4096,1] x)
    (by native_decide) l21mb_sm_node_facts.2.1 ?_
    (l21mb_nonempty_sm 840) (l21mb_sm_not_written 840 5810 (by decide))
    (l21mb_nonempty_sm 839) (l21mb_sm_not_written 839 5809 (by decide))
  intro s
  unfold l21mbSmView5810
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1] 5809 5810

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_sm5815 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5815 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5814) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 840 l21mbSmView5815
    5814 5815 (fun x => fw_view [4096,512] x)
    (by native_decide) l21mb_sm_node_facts.2.2.1 ?_
    (l21mb_nonempty_sm 841) (l21mb_sm_not_written 841 5815 (by decide))
    (l21mb_nonempty_sm 840) (l21mb_sm_not_written 840 5814 (by decide))
  intro s
  unfold l21mbSmView5815
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5814 5815

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_sm5819 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5819 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5818) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 841 l21mbSmView5819
    5818 5819 (fun x => fw_view [4096,512] x)
    (by native_decide) l21mb_sm_node_facts.2.2.2.1 ?_
    (l21mb_nonempty_sm 842) (l21mb_sm_not_written 842 5819 (by decide))
    (l21mb_nonempty_sm 841) (l21mb_sm_not_written 841 5818 (by decide))
  intro s
  unfold l21mbSmView5819
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [512] 5818 5819

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11301 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11301 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11295) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1739 l21mbPmView11301
    11295 11301 (fun x => fw_view [2048,1] x)
    (by native_decide) l21mb_pm_node_facts.2.1 ?_
    (l21mb_nonempty_pm 1740) (l21mb_pm_not_written 1740 11301 (by decide))
    (l21mb_nonempty_pm 1739) (l21mb_pm_not_written 1739 11295 (by decide))
  intro s
  unfold l21mbPmView11301
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1] 11295 11301

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11319 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11319 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11309) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1740 l21mbPmView11319
    11309 11319 (fun x => fw_view [2048,512] x)
    (by native_decide) l21mb_pm_node_facts.2.2.1 ?_
    (l21mb_nonempty_pm 1741) (l21mb_pm_not_written 1741 11319 (by decide))
    (l21mb_nonempty_pm 1740) (l21mb_pm_not_written 1740 11309 (by decide))
  intro s
  unfold l21mbPmView11319
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11309 11319

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11337 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11337 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11327) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1741 l21mbPmView11337
    11327 11337 (fun x => fw_view [2048,512] x)
    (by native_decide) l21mb_pm_node_facts.2.2.2.1 ?_
    (l21mb_nonempty_pm 1742) (l21mb_pm_not_written 1742 11337 (by decide))
    (l21mb_nonempty_pm 1741) (l21mb_pm_not_written 1741 11327 (by decide))
  intro s
  unfold l21mbPmView11337
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [512] 11327 11337

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11302 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11302 =
      fw_view [2048,1] (denoteGraphDistributedFaithful pm initPM 11296) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1743 l21mbPmView11302
    11296 11302 (fun x => fw_view [2048,1] x)
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1744) (l21mb_pm_not_written 1744 11302 (by decide))
    (l21mb_nonempty_pm 1743) (l21mb_pm_not_written 1743 11296 (by decide))
  intro s
  unfold l21mbPmView11302
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1] 11296 11302

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11320 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11320 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11310) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1744 l21mbPmView11320
    11310 11320 (fun x => fw_view [2048,512] x)
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1745) (l21mb_pm_not_written 1745 11320 (by decide))
    (l21mb_nonempty_pm 1744) (l21mb_pm_not_written 1744 11310 (by decide))
  intro s
  unfold l21mbPmView11320
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11310 11320

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11338 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11338 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11328) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1745 l21mbPmView11338
    11328 11338 (fun x => fw_view [2048,512] x)
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1746) (l21mb_pm_not_written 1746 11338 (by decide))
    (l21mb_nonempty_pm 1745) (l21mb_pm_not_written 1745 11328 (by decide))
  intro s
  unfold l21mbPmView11338
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [512] 11328 11338

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_sm5811 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5811 =
      fw_sigmoid (denoteGraphDistributedFaithful sm initSM 5810) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 843 l21mbSmSig5811
    5810 5811 fw_sigmoid
    (by native_decide) l21mb_sm_node_facts.2.2.2.2.1 ?_
    (l21mb_nonempty_sm 844) (l21mb_sm_not_written 844 5811 (by decide))
    (l21mb_nonempty_sm 843) (l21mb_sm_not_written 843 5810 (by decide))
  intro s
  unfold l21mbSmSig5811
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm s 0 5810 5811

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11303 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11303 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11301) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1747 l21mbPmSig11303
    11301 11303 fw_sigmoid
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1748) (l21mb_pm_not_written 1748 11303 (by decide))
    (l21mb_nonempty_pm 1747) (l21mb_pm_not_written 1747 11301 (by decide))
  intro s
  unfold l21mbPmSig11303
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 0 11301 11303

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11304 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11304 =
      fw_sigmoid (denoteGraphDistributedFaithful pm initPM 11302) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1750 l21mbPmSig11304
    11302 11304 fw_sigmoid
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1751) (l21mb_pm_not_written 1751 11304 (by decide))
    (l21mb_nonempty_pm 1750) (l21mb_pm_not_written 1750 11302 (by decide))
  intro s
  unfold l21mbPmSig11304
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm s 1 11302 11304

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_sm5820 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5820 =
      fw_swiglu (denoteGraphDistributedFaithful sm initSM 5815)
        (denoteGraphDistributedFaithful sm initSM 5819) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 844 l21mbSmSwi5820
    5815 5819 5820 fw_swiglu
    (by native_decide) l21mb_sm_node_facts.2.2.2.2.2 ?_
    (l21mb_nonempty_sm 845) (l21mb_sm_not_written 845 5820 (by decide))
    (l21mb_nonempty_sm 844) (l21mb_sm_not_written 844 5815 (by decide))
    (l21mb_sm_not_written 844 5819 (by decide))
  intro s
  unfold l21mbSmSwi5820
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm s 0 5815 5819 5820

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11341 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11341 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11319)
        (denoteGraphDistributedFaithful pm initPM 11337) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1748 l21mbPmSwi11341
    11319 11337 11341 fw_swiglu
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l21mb_nonempty_pm 1749) (l21mb_pm_not_written 1749 11341 (by decide))
    (l21mb_nonempty_pm 1748) (l21mb_pm_not_written 1748 11319 (by decide))
    (l21mb_pm_not_written 1748 11337 (by decide))
  intro s
  unfold l21mbPmSwi11341
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 0 11319 11337 11341

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_red_pm11342 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11342 =
      fw_swiglu (denoteGraphDistributedFaithful pm initPM 11320)
        (denoteGraphDistributedFaithful pm initPM 11338) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1751 l21mbPmSwi11342
    11320 11338 11342 fw_swiglu
    (by native_decide) l21mb_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21mb_nonempty_pm 1752) (l21mb_pm_not_written 1752 11342 (by decide))
    (l21mb_nonempty_pm 1751) (l21mb_pm_not_written 1751 11320 (by decide))
    (l21mb_pm_not_written 1751 11338 (by decide))
  intro s
  unfold l21mbPmSwi11342
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm s 1 11320 11338 11342

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5786).shape = [2] := by
  have e2 : denoteGraphDistributedFaithful pm initPM 5786 = initPM 5786 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5786
      layer1_pm_nodes_nonempty l21mb_cu_not_written
  rw [e2]
  exact hPM 5786 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21mb_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5786) = [0, 2 * 2048] := by
  have hcuShape := l21mb_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5786)).length = 2 := by
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
theorem recon_zigzagGoal_5801_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5801)
      (denoteGraphDistributedFaithful pm initPM 11279)
      (denoteGraphDistributedFaithful pm initPM 11280)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5800_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l21mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5800)
      (denoteGraphDistributedFaithful pm initPM 11277)
      (denoteGraphDistributedFaithful pm initPM 11278)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l21mb_red_sm5801 initSM hs.full_shape,
    l21mb_red_pm11279 initPM hs.rank0_shape,
    l21mb_red_pm11280 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_probs 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5802_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5802)
      (denoteGraphDistributedFaithful pm initPM 11281)
      (denoteGraphDistributedFaithful pm initPM 11282)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5800_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l21mb_hdec initPM hPM hparent
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5800)
      (denoteGraphDistributedFaithful pm initPM 11277)
      (denoteGraphDistributedFaithful pm initPM 11278)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 64] [2048, 64] := ⟨source0, source1, hs⟩
  rw [l21mb_red_sm5802 initSM hs.full_shape,
    l21mb_red_pm11281 initPM hs.rank0_shape,
    l21mb_red_pm11282 initPM hs.rank1_shape]
  exact Zigzag2Rel.topk_routing_map 2048 64 8 hparent'
    (by decide) (by decide) (by decide) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5810_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5810)
      (denoteGraphDistributedFaithful pm initPM 11301)
      (denoteGraphDistributedFaithful pm initPM 11302)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5809_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21mb_red_sm5810 initSM, l21mb_red_pm11301 initPM, l21mb_red_pm11302 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5815_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5815)
      (denoteGraphDistributedFaithful pm initPM 11319)
      (denoteGraphDistributedFaithful pm initPM 11320)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5814_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21mb_red_sm5815 initSM, l21mb_red_pm11319 initPM, l21mb_red_pm11320 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5819_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5819)
      (denoteGraphDistributedFaithful pm initPM 11337)
      (denoteGraphDistributedFaithful pm initPM 11338)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5818_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21mb_red_sm5819 initSM, l21mb_red_pm11337 initPM, l21mb_red_pm11338 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5811_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5811)
      (denoteGraphDistributedFaithful pm initPM 11303)
      (denoteGraphDistributedFaithful pm initPM 11304)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5810_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5810)
      (denoteGraphDistributedFaithful pm initPM 11301)
      (denoteGraphDistributedFaithful pm initPM 11302)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l21mb_red_sm5811 initSM, l21mb_red_pm11303 initPM, l21mb_red_pm11304 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hparent' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5820_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5820)
      (denoteGraphDistributedFaithful pm initPM 11341)
      (denoteGraphDistributedFaithful pm initPM 11342)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 512] [2048, 512] := by
  have hG := recon_zigzagGoal_5815_faithful initSM initPM hSM hPM hInit hValues hCu
  have hU := recon_zigzagGoal_5819_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨g0, g1, hgs⟩ := hG
  obtain ⟨u0, u1, hus⟩ := hU
  have hG' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5815)
      (denoteGraphDistributedFaithful pm initPM 11319)
      (denoteGraphDistributedFaithful pm initPM 11320)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 512] [2048, 512] := ⟨g0, g1, hgs⟩
  have hU' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5819)
      (denoteGraphDistributedFaithful pm initPM 11337)
      (denoteGraphDistributedFaithful pm initPM 11338)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 512] [2048, 512] := ⟨u0, u1, hus⟩
  rw [l21mb_red_sm5820 initSM, l21mb_red_pm11341 initPM, l21mb_red_pm11342 initPM]
  exact Zigzag2Rel.swiglu 2048 512 hG' hU' (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
