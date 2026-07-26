/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L23FaithfulZigzagAttention
import denote.yoco_goals.L22FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-11 entry segment

Continuation of `recon_zigzagGoal_5886_faithful` (block-11 cross-decoder
attention) through the block-11 entry segment:

* SM 891: `FW_reshape [5886] → [5887]`   (PM 1844/1845: `11579 → 11581`, `11580 → 11582`)
* SM 892: `FW_reshape [5887] → [5888]`   (PM 1846/1847: `11581 → 11587`, `11582 → 11588`)
* SM 893: `FW_mix_precision_linear [5888, 5889] → [5890]`
                                          (PM 1848/1849 with replicated weight 5889)
* SM 894: `FW_view [5890] → [5891]`      (PM 1850/1851)
* SM 895: `FW_float [5891] → [5892]`     (PM 1852/1853)
* SM 896: `FW_add [8572, 5892] → [5893]` (PM 1854/1855 with bypass 16831/16839)
* SM 897: `FW_multiref [5893] → [8576, 8580]`
                                          (PM 1856: `[16843, 16847]`, PM 1857: `[16851, 16855]`)
* SM 898: `FW_rms_norm [8576, 5894] → [5895]` (PM 1858/1859, replicated weight 5894)
* SM 899: `FW_multiref [5895] → [8587, 8591, 8595, 8599, 8603]`
                                          (PM 1860: `[16862, 16866, 16870, 16874, 16878]`,
                                           PM 1861: `[16885, 16889, 16893, 16897, 16901]`)

All relations are stated against the block-11 cumulative-sequence metadata tensor
`5884` (the same cu slot used by `recon_zigzagGoal_5886_faithful`).
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

/-! ### Local `applyNode` helper for the first output of a 5-way multiref -/

private theorem l23en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l23enSmReshape5887 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5886], outs := [5887],
    params := [4096, 1024] }
private def l23enSmReshape5888 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5887], outs := [5888],
    params := [4096, 1024] }
private def l23enSmLinear5890 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5888, 5889],
    outs := [5890] }
private def l23enSmView5891 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5890], outs := [5891],
    params := [4096, 1024] }
private def l23enSmFloat5892 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5891], outs := [5892] }
private def l23enSmAdd5893 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8572, 5892], outs := [5893] }
private def l23enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580],
    params := [2] }
private def l23enSmRms5895 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8576, 5894], outs := [5895] }
private def l23enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5895],
    outs := [8587, 8591, 8595, 8599, 8603], params := [5] }

private def l23enPmReshape11581 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11579], outs := [11581],
    params := [2048, 1024] }
private def l23enPmReshape11582 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11580], outs := [11582],
    params := [2048, 1024] }
private def l23enPmReshape11587 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11581], outs := [11587],
    params := [2048, 1024] }
private def l23enPmReshape11588 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11582], outs := [11588],
    params := [2048, 1024] }
private def l23enPmLinear11591 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11587, 5889],
    outs := [11591] }
private def l23enPmLinear11592 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11588, 5889],
    outs := [11592] }
private def l23enPmView11601 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11591], outs := [11601],
    params := [2048, 1024] }
private def l23enPmView11602 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11592], outs := [11602],
    params := [2048, 1024] }
private def l23enPmFloat11605 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11601], outs := [11605] }
private def l23enPmFloat11606 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11602], outs := [11606] }
private def l23enPmAdd11609 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16831, 11605], outs := [11609] }
private def l23enPmAdd11610 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16839, 11606], outs := [11610] }
private def l23enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847],
    params := [2] }
private def l23enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855],
    params := [2] }
private def l23enPmRms11613 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16843, 5894], outs := [11613] }
private def l23enPmRms11614 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16851, 5894], outs := [11614] }
private def l23enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11613],
    outs := [16862, 16866, 16870, 16874, 16878], params := [5] }
private def l23enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11614],
    outs := [16885, 16889, 16893, 16897, 16901], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l23en_sm_node_facts :
    sm.nodes[891]'(by native_decide) = l23enSmReshape5887 ∧
    sm.nodes[892]'(by native_decide) = l23enSmReshape5888 ∧
    sm.nodes[893]'(by native_decide) = l23enSmLinear5890 ∧
    sm.nodes[894]'(by native_decide) = l23enSmView5891 ∧
    sm.nodes[895]'(by native_decide) = l23enSmFloat5892 ∧
    sm.nodes[896]'(by native_decide) = l23enSmAdd5893 ∧
    sm.nodes[897]'(by native_decide) = l23enSmMulti2 ∧
    sm.nodes[898]'(by native_decide) = l23enSmRms5895 ∧
    sm.nodes[899]'(by native_decide) = l23enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23en_pm_node_facts :
    pm.nodes[1844]'(by native_decide) = l23enPmReshape11581 ∧
    pm.nodes[1845]'(by native_decide) = l23enPmReshape11582 ∧
    pm.nodes[1846]'(by native_decide) = l23enPmReshape11587 ∧
    pm.nodes[1847]'(by native_decide) = l23enPmReshape11588 ∧
    pm.nodes[1848]'(by native_decide) = l23enPmLinear11591 ∧
    pm.nodes[1849]'(by native_decide) = l23enPmLinear11592 ∧
    pm.nodes[1850]'(by native_decide) = l23enPmView11601 ∧
    pm.nodes[1851]'(by native_decide) = l23enPmView11602 ∧
    pm.nodes[1852]'(by native_decide) = l23enPmFloat11605 ∧
    pm.nodes[1853]'(by native_decide) = l23enPmFloat11606 ∧
    pm.nodes[1854]'(by native_decide) = l23enPmAdd11609 ∧
    pm.nodes[1855]'(by native_decide) = l23enPmAdd11610 ∧
    pm.nodes[1856]'(by native_decide) = l23enPmMulti2R0 ∧
    pm.nodes[1857]'(by native_decide) = l23enPmMulti2R1 ∧
    pm.nodes[1858]'(by native_decide) = l23enPmRms11613 ∧
    pm.nodes[1859]'(by native_decide) = l23enPmRms11614 ∧
    pm.nodes[1860]'(by native_decide) = l23enPmMulti5R0 ∧
    pm.nodes[1861]'(by native_decide) = l23enPmMulti5R1 := by
  native_decide

private theorem l23en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l23en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23en_weights_not_written :
    (∀ n ∈ sm.nodes, 5889 ∉ n.outs ∧ 5894 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5889 ∉ n.outs ∧ 5894 ∉ n.outs) := by
  native_decide

private theorem l23en_w5889_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5889 ∉ n.outs := by
  intro n hn
  exact (l23en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l23en_w5889_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5889 ∉ n.outs := by
  intro n hn
  exact (l23en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l23en_w5894_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5894 ∉ n.outs := by
  intro n hn
  exact (l23en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l23en_w5894_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5894 ∉ n.outs := by
  intro n hn
  exact (l23en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l23en_cu_not_written :
    ∀ n ∈ pm.nodes, 5835 ∉ n.outs ∧ 5884 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(892, 5887), (891, 5886), (893, 5888), (894, 5890), (895, 5891), (896,
      5892), (897, 5893), (896, 8572), (898, 8576), (898, 8580), (899, 5895),
      (900, 8587), (900, 8591), (900, 8595), (900, 8599), (900, 8603)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1845, 11581), (1844, 11579), (1846, 11582), (1845, 11580), (1847, 11587),
      (1846, 11581), (1848, 11588), (1847, 11582), (1849, 11591), (1848, 11587),
      (1850, 11592), (1849, 11588), (1851, 11601), (1850, 11591), (1852, 11602),
      (1851, 11592), (1853, 11605), (1852, 11601), (1854, 11606), (1853, 11602),
      (1855, 11609), (1854, 16831), (1854, 11605), (1856, 11610), (1855, 16839),
      (1855, 11606), (1857, 16843), (1857, 16847), (1856, 11609), (1858, 16851),
      (1858, 16855), (1857, 11610), (1859, 11613), (1858, 16843), (1860, 11614),
      (1859, 16851), (1861, 16862), (1861, 16866), (1861, 16870), (1861, 16874),
      (1861, 16878), (1860, 11613), (1862, 16885), (1862, 16889), (1862, 16893),
      (1862, 16897), (1862, 16901), (1861, 11614)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm5887 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5887 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5886) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 891 l23enSmReshape5887
    5886 5887 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l23en_sm_node_facts.1 ?_
    (l23en_nonempty_sm 892) (l23en_sm_not_written 892 5887 (by decide))
    (l23en_nonempty_sm 891) (l23en_sm_not_written 891 5886 (by decide))
  intro s
  unfold l23enSmReshape5887
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5886 5887 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11581 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11581 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11579) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1844 l23enPmReshape11581
    11579 11581 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l23en_pm_node_facts.1 ?_
    (l23en_nonempty_pm 1845) (l23en_pm_not_written 1845 11581 (by decide))
    (l23en_nonempty_pm 1844) (l23en_pm_not_written 1844 11579 (by decide))
  intro s
  unfold l23enPmReshape11581
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11579 11581 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11582 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11582 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11580) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1845 l23enPmReshape11582
    11580 11582 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l23en_pm_node_facts.2.1 ?_
    (l23en_nonempty_pm 1846) (l23en_pm_not_written 1846 11582 (by decide))
    (l23en_nonempty_pm 1845) (l23en_pm_not_written 1845 11580 (by decide))
  intro s
  unfold l23enPmReshape11582
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11580 11582 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm5888 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5888 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5887) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 892 l23enSmReshape5888
    5887 5888 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l23en_sm_node_facts.2.1 ?_
    (l23en_nonempty_sm 893) (l23en_sm_not_written 893 5888 (by decide))
    (l23en_nonempty_sm 892) (l23en_sm_not_written 892 5887 (by decide))
  intro s
  unfold l23enSmReshape5888
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5887 5888 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11587 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11587 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11581) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1846 l23enPmReshape11587
    11581 11587 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l23en_pm_node_facts.2.2.1 ?_
    (l23en_nonempty_pm 1847) (l23en_pm_not_written 1847 11587 (by decide))
    (l23en_nonempty_pm 1846) (l23en_pm_not_written 1846 11581 (by decide))
  intro s
  unfold l23enPmReshape11587
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11581 11587 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11588 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11588 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11582) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1847 l23enPmReshape11588
    11582 11588 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l23en_pm_node_facts.2.2.2.1 ?_
    (l23en_nonempty_pm 1848) (l23en_pm_not_written 1848 11588 (by decide))
    (l23en_nonempty_pm 1847) (l23en_pm_not_written 1847 11582 (by decide))
  intro s
  unfold l23enPmReshape11588
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11582 11588 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm5890 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5890 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5888)
        (denoteGraphDistributedFaithful sm initSM 5889) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 893 l23enSmLinear5890
    5888 5889 5890 fw_linear
    (by native_decide) l23en_sm_node_facts.2.2.1 ?_
    (l23en_nonempty_sm 894) (l23en_sm_not_written 894 5890 (by decide))
    (l23en_nonempty_sm 893) (l23en_sm_not_written 893 5888 (by decide))
    (l23en_w5889_sm_drop 893)
  intro s
  unfold l23enSmLinear5890
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5888 5889 5890

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11591 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11591 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11587)
        (denoteGraphDistributedFaithful pm initPM 5889) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1848 l23enPmLinear11591
    11587 5889 11591 fw_linear
    (by native_decide) l23en_pm_node_facts.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1849) (l23en_pm_not_written 1849 11591 (by decide))
    (l23en_nonempty_pm 1848) (l23en_pm_not_written 1848 11587 (by decide))
    (l23en_w5889_pm_drop 1848)
  intro s
  unfold l23enPmLinear11591
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11587 5889 11591

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11592 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11592 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11588)
        (denoteGraphDistributedFaithful pm initPM 5889) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1849 l23enPmLinear11592
    11588 5889 11592 fw_linear
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1850) (l23en_pm_not_written 1850 11592 (by decide))
    (l23en_nonempty_pm 1849) (l23en_pm_not_written 1849 11588 (by decide))
    (l23en_w5889_pm_drop 1849)
  intro s
  unfold l23enPmLinear11592
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11588 5889 11592

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm5891 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5891 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5890) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 894 l23enSmView5891
    5890 5891 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l23en_sm_node_facts.2.2.2.1 ?_
    (l23en_nonempty_sm 895) (l23en_sm_not_written 895 5891 (by decide))
    (l23en_nonempty_sm 894) (l23en_sm_not_written 894 5890 (by decide))
  intro s
  unfold l23enSmView5891
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5890 5891

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11601 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11601 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11591) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1850 l23enPmView11601
    11591 11601 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1851) (l23en_pm_not_written 1851 11601 (by decide))
    (l23en_nonempty_pm 1850) (l23en_pm_not_written 1850 11591 (by decide))
  intro s
  unfold l23enPmView11601
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11591 11601

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11602 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11602 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11592) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1851 l23enPmView11602
    11592 11602 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1852) (l23en_pm_not_written 1852 11602 (by decide))
    (l23en_nonempty_pm 1851) (l23en_pm_not_written 1851 11592 (by decide))
  intro s
  unfold l23enPmView11602
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11592 11602

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm5892 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5892 =
      denoteGraphDistributedFaithful sm initSM 5891 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 895 l23enSmFloat5892
    5891 5892 id
    (by native_decide) l23en_sm_node_facts.2.2.2.2.1 ?_
    (l23en_nonempty_sm 896) (l23en_sm_not_written 896 5892 (by decide))
    (l23en_nonempty_sm 895) (l23en_sm_not_written 895 5891 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l23enSmFloat5892
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5891 5892 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11605 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11605 =
      denoteGraphDistributedFaithful pm initPM 11601 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1852 l23enPmFloat11605
    11601 11605 id
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1853) (l23en_pm_not_written 1853 11605 (by decide))
    (l23en_nonempty_pm 1852) (l23en_pm_not_written 1852 11601 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l23enPmFloat11605
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 11601 11605 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11606 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11606 =
      denoteGraphDistributedFaithful pm initPM 11602 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1853 l23enPmFloat11606
    11602 11606 id
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1854) (l23en_pm_not_written 1854 11606 (by decide))
    (l23en_nonempty_pm 1853) (l23en_pm_not_written 1853 11602 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l23enPmFloat11606
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 11602 11606 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm5893 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5893 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8572)
        (denoteGraphDistributedFaithful sm initSM 5892) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 896 l23enSmAdd5893
    8572 5892 5893 elemwiseAdd
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.1 ?_
    (l23en_nonempty_sm 897) (l23en_sm_not_written 897 5893 (by decide))
    (l23en_nonempty_sm 896) (l23en_sm_not_written 896 8572 (by decide))
    (l23en_sm_not_written 896 5892 (by decide))
  intro s
  unfold l23enSmAdd5893
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8572 5892 5893

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11609 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11609 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16831)
        (denoteGraphDistributedFaithful pm initPM 11605) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1854 l23enPmAdd11609
    16831 11605 11609 elemwiseAdd
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1855) (l23en_pm_not_written 1855 11609 (by decide))
    (l23en_nonempty_pm 1854) (l23en_pm_not_written 1854 16831 (by decide))
    (l23en_pm_not_written 1854 11605 (by decide))
  intro s
  unfold l23enPmAdd11609
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16831 11605 11609

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11610 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11610 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16839)
        (denoteGraphDistributedFaithful pm initPM 11606) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1855 l23enPmAdd11610
    16839 11606 11610 elemwiseAdd
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1856) (l23en_pm_not_written 1856 11610 (by decide))
    (l23en_nonempty_pm 1855) (l23en_pm_not_written 1855 16839 (by decide))
    (l23en_pm_not_written 1855 11606 (by decide))
  intro s
  unfold l23enPmAdd11610
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16839 11606 11610

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm8576 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8576 =
      denoteGraphDistributedFaithful sm initSM 5893 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 897 l23enSmMulti2
    5893 8576 (fun x => x)
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_sm 898) (l23en_sm_not_written 898 8576 (by decide))
    (l23en_nonempty_sm 897) (l23en_sm_not_written 897 5893 (by decide))
  intro s
  unfold l23enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5893 8576 8580

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm8580 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8580 =
      denoteGraphDistributedFaithful sm initSM 5893 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 897 l23enSmMulti2
    5893 8580 (fun x => x)
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_sm 898) (l23en_sm_not_written 898 8580 (by decide))
    (l23en_nonempty_sm 897) (l23en_sm_not_written 897 5893 (by decide))
  intro s
  unfold l23enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5893 8576 8580 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16843 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16843 =
      denoteGraphDistributedFaithful pm initPM 11609 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1856 l23enPmMulti2R0
    11609 16843 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1857) (l23en_pm_not_written 1857 16843 (by decide))
    (l23en_nonempty_pm 1856) (l23en_pm_not_written 1856 11609 (by decide))
  intro s
  unfold l23enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11609 16843 16847

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16847 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16847 =
      denoteGraphDistributedFaithful pm initPM 11609 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1856 l23enPmMulti2R0
    11609 16847 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1857) (l23en_pm_not_written 1857 16847 (by decide))
    (l23en_nonempty_pm 1856) (l23en_pm_not_written 1856 11609 (by decide))
  intro s
  unfold l23enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11609 16843 16847 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16851 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16851 =
      denoteGraphDistributedFaithful pm initPM 11610 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1857 l23enPmMulti2R1
    11610 16851 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1858) (l23en_pm_not_written 1858 16851 (by decide))
    (l23en_nonempty_pm 1857) (l23en_pm_not_written 1857 11610 (by decide))
  intro s
  unfold l23enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11610 16851 16855

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16855 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16855 =
      denoteGraphDistributedFaithful pm initPM 11610 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1857 l23enPmMulti2R1
    11610 16855 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1858) (l23en_pm_not_written 1858 16855 (by decide))
    (l23en_nonempty_pm 1857) (l23en_pm_not_written 1857 11610 (by decide))
  intro s
  unfold l23enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11610 16851 16855 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm5895 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5895 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8576)
        (denoteGraphDistributedFaithful sm initSM 5894) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 898 l23enSmRms5895
    8576 5894 5895 fw_rms_norm
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_sm 899) (l23en_sm_not_written 899 5895 (by decide))
    (l23en_nonempty_sm 898) (l23en_sm_not_written 898 8576 (by decide))
    (l23en_w5894_sm_drop 898)
  intro s
  unfold l23enSmRms5895
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8576 5894 5895

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11613 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11613 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16843)
        (denoteGraphDistributedFaithful pm initPM 5894) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1858 l23enPmRms11613
    16843 5894 11613 fw_rms_norm
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1859) (l23en_pm_not_written 1859 11613 (by decide))
    (l23en_nonempty_pm 1858) (l23en_pm_not_written 1858 16843 (by decide))
    (l23en_w5894_pm_drop 1858)
  intro s
  unfold l23enPmRms11613
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16843 5894 11613

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm11614 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11614 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16851)
        (denoteGraphDistributedFaithful pm initPM 5894) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1859 l23enPmRms11614
    16851 5894 11614 fw_rms_norm
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1860) (l23en_pm_not_written 1860 11614 (by decide))
    (l23en_nonempty_pm 1859) (l23en_pm_not_written 1859 16851 (by decide))
    (l23en_w5894_pm_drop 1859)
  intro s
  unfold l23enPmRms11614
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16851 5894 11614

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm8587 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8587 =
      denoteGraphDistributedFaithful sm initSM 5895 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 899 l23enSmMulti5
    5895 8587 (fun x => x)
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_sm 900) (l23en_sm_not_written 900 8587 (by decide))
    (l23en_nonempty_sm 899) (l23en_sm_not_written 899 5895 (by decide))
  intro s
  unfold l23enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l23en_multiref5_first_out sm s 0 5895 8587 8591 8595 8599 8603

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm8591 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8591 =
      denoteGraphDistributedFaithful sm initSM 5895 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 899 l23enSmMulti5
    5895 8591 (fun x => x)
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_sm 900) (l23en_sm_not_written 900 8591 (by decide))
    (l23en_nonempty_sm 899) (l23en_sm_not_written 899 5895 (by decide))
  intro s
  unfold l23enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5895 8587 8591 8595 8599 8603
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm8595 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8595 =
      denoteGraphDistributedFaithful sm initSM 5895 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 899 l23enSmMulti5
    5895 8595 (fun x => x)
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_sm 900) (l23en_sm_not_written 900 8595 (by decide))
    (l23en_nonempty_sm 899) (l23en_sm_not_written 899 5895 (by decide))
  intro s
  unfold l23enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5895 8587 8591 8595 8599 8603
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm8599 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8599 =
      denoteGraphDistributedFaithful sm initSM 5895 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 899 l23enSmMulti5
    5895 8599 (fun x => x)
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_sm 900) (l23en_sm_not_written 900 8599 (by decide))
    (l23en_nonempty_sm 899) (l23en_sm_not_written 899 5895 (by decide))
  intro s
  unfold l23enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5895 8587 8591 8595 8599 8603
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_sm8603 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8603 =
      denoteGraphDistributedFaithful sm initSM 5895 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 899 l23enSmMulti5
    5895 8603 (fun x => x)
    (by native_decide) l23en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_sm 900) (l23en_sm_not_written 900 8603 (by decide))
    (l23en_nonempty_sm 899) (l23en_sm_not_written 899 5895 (by decide))
  intro s
  unfold l23enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5895 8587 8591 8595 8599 8603
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16862 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16862 =
      denoteGraphDistributedFaithful pm initPM 11613 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1860 l23enPmMulti5R0
    11613 16862 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 16862 (by decide))
    (l23en_nonempty_pm 1860) (l23en_pm_not_written 1860 11613 (by decide))
  intro s
  unfold l23enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l23en_multiref5_first_out pm s 0 11613 16862 16866 16870 16874 16878

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16866 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16866 =
      denoteGraphDistributedFaithful pm initPM 11613 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1860 l23enPmMulti5R0
    11613 16866 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 16866 (by decide))
    (l23en_nonempty_pm 1860) (l23en_pm_not_written 1860 11613 (by decide))
  intro s
  unfold l23enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 11613 16862 16866 16870 16874 16878
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16870 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16870 =
      denoteGraphDistributedFaithful pm initPM 11613 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1860 l23enPmMulti5R0
    11613 16870 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 16870 (by decide))
    (l23en_nonempty_pm 1860) (l23en_pm_not_written 1860 11613 (by decide))
  intro s
  unfold l23enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 11613 16862 16866 16870 16874 16878
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16874 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16874 =
      denoteGraphDistributedFaithful pm initPM 11613 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1860 l23enPmMulti5R0
    11613 16874 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 16874 (by decide))
    (l23en_nonempty_pm 1860) (l23en_pm_not_written 1860 11613 (by decide))
  intro s
  unfold l23enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 11613 16862 16866 16870 16874 16878
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16878 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16878 =
      denoteGraphDistributedFaithful pm initPM 11613 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1860 l23enPmMulti5R0
    11613 16878 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 16878 (by decide))
    (l23en_nonempty_pm 1860) (l23en_pm_not_written 1860 11613 (by decide))
  intro s
  unfold l23enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 11613 16862 16866 16870 16874 16878
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16885 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16885 =
      denoteGraphDistributedFaithful pm initPM 11614 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1861 l23enPmMulti5R1
    11614 16885 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_pm 1862) (l23en_pm_not_written 1862 16885 (by decide))
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 11614 (by decide))
  intro s
  unfold l23enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l23en_multiref5_first_out pm s 1 11614 16885 16889 16893 16897 16901

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16889 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16889 =
      denoteGraphDistributedFaithful pm initPM 11614 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1861 l23enPmMulti5R1
    11614 16889 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_pm 1862) (l23en_pm_not_written 1862 16889 (by decide))
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 11614 (by decide))
  intro s
  unfold l23enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 11614 16885 16889 16893 16897 16901
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16893 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16893 =
      denoteGraphDistributedFaithful pm initPM 11614 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1861 l23enPmMulti5R1
    11614 16893 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_pm 1862) (l23en_pm_not_written 1862 16893 (by decide))
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 11614 (by decide))
  intro s
  unfold l23enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 11614 16885 16889 16893 16897 16901
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16897 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16897 =
      denoteGraphDistributedFaithful pm initPM 11614 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1861 l23enPmMulti5R1
    11614 16897 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_pm 1862) (l23en_pm_not_written 1862 16897 (by decide))
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 11614 (by decide))
  intro s
  unfold l23enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 11614 16885 16889 16893 16897 16901
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23en_red_pm16901 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16901 =
      denoteGraphDistributedFaithful pm initPM 11614 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1861 l23enPmMulti5R1
    11614 16901 (fun x => x)
    (by native_decide) l23en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23en_nonempty_pm 1862) (l23en_pm_not_written 1862 16901 (by decide))
    (l23en_nonempty_pm 1861) (l23en_pm_not_written 1861 11614 (by decide))
  intro s
  unfold l23enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 11614 16885 16889 16893 16897 16901
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5887 (`FW_reshape` of 5886).
theorem recon_zigzagGoal_5887_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5887)
      (denoteGraphDistributedFaithful pm initPM 11581)
      (denoteGraphDistributedFaithful pm initPM 11582)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5886_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm5887 initSM, l23en_red_pm11581 initPM, l23en_red_pm11582 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5888 (`FW_reshape` of 5887).
theorem recon_zigzagGoal_5888_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5888)
      (denoteGraphDistributedFaithful pm initPM 11587)
      (denoteGraphDistributedFaithful pm initPM 11588)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5887_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm5888 initSM, l23en_red_pm11587 initPM, l23en_red_pm11588 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5890 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5890_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5890)
      (denoteGraphDistributedFaithful pm initPM 11591)
      (denoteGraphDistributedFaithful pm initPM 11592)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5888_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5889 = initPM 5889 :=
    recon_weight initSM initPM hInit initGoal_5889 (by native_decide) 5889
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5889 = initSM 5889 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5889
      layer1_sm_nodes_nonempty (fun n hn => (l23en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5889 = initPM 5889 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5889
      layer1_pm_nodes_nonempty (fun n hn => (l23en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5889 =
      denoteGraphDistributedFaithful pm initPM 5889 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5889).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5889 [1024, 1024] (by native_decide)
  rw [l23en_red_sm5890 initSM, l23en_red_pm11591 initPM, l23en_red_pm11592 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5891 (`FW_view` of 5890).
theorem recon_zigzagGoal_5891_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5891)
      (denoteGraphDistributedFaithful pm initPM 11601)
      (denoteGraphDistributedFaithful pm initPM 11602)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5890_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm5891 initSM, l23en_red_pm11601 initPM, l23en_red_pm11602 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5892 (`FW_float` of 5891).
theorem recon_zigzagGoal_5892_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5892)
      (denoteGraphDistributedFaithful pm initPM 11605)
      (denoteGraphDistributedFaithful pm initPM 11606)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5891_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm5892 initSM, l23en_red_pm11605 initPM, l23en_red_pm11606 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5893 (residual `FW_add` of the
-- cross-layer bypass 8572 and 5892).
theorem recon_zigzagGoal_5893_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5893)
      (denoteGraphDistributedFaithful pm initPM 11609)
      (denoteGraphDistributedFaithful pm initPM 11610)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8572_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5892_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5835_5884 : denoteGraphDistributedFaithful pm initPM 5835 =
      denoteGraphDistributedFaithful pm initPM 5884 := by
    rw [pmFinal 5835 (fun n hn => (l23en_cu_not_written n hn).1),
      pmFinal 5884 (fun n hn => (l23en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5835_5884] at hA
  rw [l23en_red_sm5893 initSM, l23en_red_pm11609 initPM, l23en_red_pm11610 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8576 (2-way multiref, position 0).
theorem recon_zigzagGoal_8576_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8576)
      (denoteGraphDistributedFaithful pm initPM 16843)
      (denoteGraphDistributedFaithful pm initPM 16851)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5893_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm8576 initSM, l23en_red_pm16843 initPM, l23en_red_pm16851 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8580 (2-way multiref, position 1).
theorem recon_zigzagGoal_8580_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8580)
      (denoteGraphDistributedFaithful pm initPM 16847)
      (denoteGraphDistributedFaithful pm initPM 16855)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5893_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm8580 initSM, l23en_red_pm16847 initPM, l23en_red_pm16855 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5895 (`FW_rms_norm` of 8576 with
-- the replicated weight 5894).
theorem recon_zigzagGoal_5895_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5895)
      (denoteGraphDistributedFaithful pm initPM 11613)
      (denoteGraphDistributedFaithful pm initPM 11614)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8576_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5894 = initPM 5894 :=
    recon_weight initSM initPM hInit initGoal_5894 (by native_decide) 5894
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5894 = initSM 5894 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5894
      layer1_sm_nodes_nonempty (fun n hn => (l23en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5894 = initPM 5894 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5894
      layer1_pm_nodes_nonempty (fun n hn => (l23en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5894 =
      denoteGraphDistributedFaithful pm initPM 5894 := by
    rw [hsw, hpw]; exact hwInit
  rw [l23en_red_sm5895 initSM, l23en_red_pm11613 initPM, l23en_red_pm11614 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8587 (5-way multiref, position 0).
theorem recon_zigzagGoal_8587_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8587)
      (denoteGraphDistributedFaithful pm initPM 16862)
      (denoteGraphDistributedFaithful pm initPM 16885)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5895_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm8587 initSM, l23en_red_pm16862 initPM, l23en_red_pm16885 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8591 (5-way multiref, position 1).
theorem recon_zigzagGoal_8591_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8591)
      (denoteGraphDistributedFaithful pm initPM 16866)
      (denoteGraphDistributedFaithful pm initPM 16889)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5895_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm8591 initSM, l23en_red_pm16866 initPM, l23en_red_pm16889 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8595 (5-way multiref, position 2).
theorem recon_zigzagGoal_8595_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8595)
      (denoteGraphDistributedFaithful pm initPM 16870)
      (denoteGraphDistributedFaithful pm initPM 16893)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5895_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm8595 initSM, l23en_red_pm16870 initPM, l23en_red_pm16893 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8599 (5-way multiref, position 3).
theorem recon_zigzagGoal_8599_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8599)
      (denoteGraphDistributedFaithful pm initPM 16874)
      (denoteGraphDistributedFaithful pm initPM 16897)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5895_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm8599 initSM, l23en_red_pm16874 initPM, l23en_red_pm16897 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8603 (5-way multiref, position 4).
theorem recon_zigzagGoal_8603_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8603)
      (denoteGraphDistributedFaithful pm initPM 16878)
      (denoteGraphDistributedFaithful pm initPM 16901)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5895_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23en_red_sm8603 initSM, l23en_red_pm16878 initPM, l23en_red_pm16901 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
