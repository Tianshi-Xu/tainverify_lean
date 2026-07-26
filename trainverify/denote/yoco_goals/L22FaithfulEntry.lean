/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L22FaithfulZigzagAttention
import denote.yoco_goals.L21FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-10 entry segment

Continuation of `recon_zigzagGoal_5837_faithful` (block-10 cross-decoder
attention) through the block-10 entry segment:

* SM 856: `FW_reshape [5837] → [5838]`   (PM 1774/1775: `11407 → 11409`, `11408 → 11410`)
* SM 857: `FW_reshape [5838] → [5839]`   (PM 1776/1777: `11409 → 11415`, `11410 → 11416`)
* SM 858: `FW_mix_precision_linear [5839, 5840] → [5841]`
                                          (PM 1778/1779 with replicated weight 5840)
* SM 859: `FW_view [5841] → [5842]`      (PM 1780/1781)
* SM 860: `FW_float [5842] → [5843]`     (PM 1782/1783)
* SM 861: `FW_add [8533, 5843] → [5844]` (PM 1784/1785 with bypass 16753/16761)
* SM 862: `FW_multiref [5844] → [8537, 8541]`
                                          (PM 1786: `[16765, 16769]`, PM 1787: `[16773, 16777]`)
* SM 863: `FW_rms_norm [8537, 5845] → [5846]` (PM 1788/1789, replicated weight 5845)
* SM 864: `FW_multiref [5846] → [8548, 8552, 8556, 8560, 8564]`
                                          (PM 1790: `[16784, 16788, 16792, 16796, 16800]`,
                                           PM 1791: `[16807, 16811, 16815, 16819, 16823]`)

All relations are stated against the block-10 cumulative-sequence metadata tensor
`5835` (the same cu slot used by `recon_zigzagGoal_5837_faithful`).
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

private theorem l22en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l22enSmReshape5838 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5837], outs := [5838],
    params := [4096, 1024] }
private def l22enSmReshape5839 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5838], outs := [5839],
    params := [4096, 1024] }
private def l22enSmLinear5841 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5839, 5840],
    outs := [5841] }
private def l22enSmView5842 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5841], outs := [5842],
    params := [4096, 1024] }
private def l22enSmFloat5843 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5842], outs := [5843] }
private def l22enSmAdd5844 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8533, 5843], outs := [5844] }
private def l22enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5844], outs := [8537, 8541],
    params := [2] }
private def l22enSmRms5846 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8537, 5845], outs := [5846] }
private def l22enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5846],
    outs := [8548, 8552, 8556, 8560, 8564], params := [5] }

private def l22enPmReshape11409 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11407], outs := [11409],
    params := [2048, 1024] }
private def l22enPmReshape11410 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11408], outs := [11410],
    params := [2048, 1024] }
private def l22enPmReshape11415 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11409], outs := [11415],
    params := [2048, 1024] }
private def l22enPmReshape11416 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11410], outs := [11416],
    params := [2048, 1024] }
private def l22enPmLinear11419 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11415, 5840],
    outs := [11419] }
private def l22enPmLinear11420 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11416, 5840],
    outs := [11420] }
private def l22enPmView11429 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11419], outs := [11429],
    params := [2048, 1024] }
private def l22enPmView11430 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11420], outs := [11430],
    params := [2048, 1024] }
private def l22enPmFloat11433 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11429], outs := [11433] }
private def l22enPmFloat11434 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11430], outs := [11434] }
private def l22enPmAdd11437 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16753, 11433], outs := [11437] }
private def l22enPmAdd11438 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16761, 11434], outs := [11438] }
private def l22enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11437], outs := [16765, 16769],
    params := [2] }
private def l22enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11438], outs := [16773, 16777],
    params := [2] }
private def l22enPmRms11441 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16765, 5845], outs := [11441] }
private def l22enPmRms11442 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16773, 5845], outs := [11442] }
private def l22enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11441],
    outs := [16784, 16788, 16792, 16796, 16800], params := [5] }
private def l22enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11442],
    outs := [16807, 16811, 16815, 16819, 16823], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l22en_sm_node_facts :
    sm.nodes[856]'(by native_decide) = l22enSmReshape5838 ∧
    sm.nodes[857]'(by native_decide) = l22enSmReshape5839 ∧
    sm.nodes[858]'(by native_decide) = l22enSmLinear5841 ∧
    sm.nodes[859]'(by native_decide) = l22enSmView5842 ∧
    sm.nodes[860]'(by native_decide) = l22enSmFloat5843 ∧
    sm.nodes[861]'(by native_decide) = l22enSmAdd5844 ∧
    sm.nodes[862]'(by native_decide) = l22enSmMulti2 ∧
    sm.nodes[863]'(by native_decide) = l22enSmRms5846 ∧
    sm.nodes[864]'(by native_decide) = l22enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l22en_pm_node_facts :
    pm.nodes[1774]'(by native_decide) = l22enPmReshape11409 ∧
    pm.nodes[1775]'(by native_decide) = l22enPmReshape11410 ∧
    pm.nodes[1776]'(by native_decide) = l22enPmReshape11415 ∧
    pm.nodes[1777]'(by native_decide) = l22enPmReshape11416 ∧
    pm.nodes[1778]'(by native_decide) = l22enPmLinear11419 ∧
    pm.nodes[1779]'(by native_decide) = l22enPmLinear11420 ∧
    pm.nodes[1780]'(by native_decide) = l22enPmView11429 ∧
    pm.nodes[1781]'(by native_decide) = l22enPmView11430 ∧
    pm.nodes[1782]'(by native_decide) = l22enPmFloat11433 ∧
    pm.nodes[1783]'(by native_decide) = l22enPmFloat11434 ∧
    pm.nodes[1784]'(by native_decide) = l22enPmAdd11437 ∧
    pm.nodes[1785]'(by native_decide) = l22enPmAdd11438 ∧
    pm.nodes[1786]'(by native_decide) = l22enPmMulti2R0 ∧
    pm.nodes[1787]'(by native_decide) = l22enPmMulti2R1 ∧
    pm.nodes[1788]'(by native_decide) = l22enPmRms11441 ∧
    pm.nodes[1789]'(by native_decide) = l22enPmRms11442 ∧
    pm.nodes[1790]'(by native_decide) = l22enPmMulti5R0 ∧
    pm.nodes[1791]'(by native_decide) = l22enPmMulti5R1 := by
  native_decide

private theorem l22en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l22en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l22en_weights_not_written :
    (∀ n ∈ sm.nodes, 5840 ∉ n.outs ∧ 5845 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5840 ∉ n.outs ∧ 5845 ∉ n.outs) := by
  native_decide

private theorem l22en_w5840_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5840 ∉ n.outs := by
  intro n hn
  exact (l22en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l22en_w5840_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5840 ∉ n.outs := by
  intro n hn
  exact (l22en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l22en_w5845_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5845 ∉ n.outs := by
  intro n hn
  exact (l22en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l22en_w5845_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5845 ∉ n.outs := by
  intro n hn
  exact (l22en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l22en_cu_not_written :
    ∀ n ∈ pm.nodes, 5786 ∉ n.outs ∧ 5835 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l22en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(857, 5838), (856, 5837), (858, 5839), (859, 5841), (860, 5842), (861,
      5843), (862, 5844), (861, 8533), (863, 8537), (863, 8541), (864, 5846),
      (865, 8548), (865, 8552), (865, 8556), (865, 8560), (865, 8564)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l22en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1775, 11409), (1774, 11407), (1776, 11410), (1775, 11408), (1777, 11415),
      (1776, 11409), (1778, 11416), (1777, 11410), (1779, 11419), (1778, 11415),
      (1780, 11420), (1779, 11416), (1781, 11429), (1780, 11419), (1782, 11430),
      (1781, 11420), (1783, 11433), (1782, 11429), (1784, 11434), (1783, 11430),
      (1785, 11437), (1784, 16753), (1784, 11433), (1786, 11438), (1785, 16761),
      (1785, 11434), (1787, 16765), (1787, 16769), (1786, 11437), (1788, 16773),
      (1788, 16777), (1787, 11438), (1789, 11441), (1788, 16765), (1790, 11442),
      (1789, 16773), (1791, 16784), (1791, 16788), (1791, 16792), (1791, 16796),
      (1791, 16800), (1790, 11441), (1792, 16807), (1792, 16811), (1792, 16815),
      (1792, 16819), (1792, 16823), (1791, 11442)]) :
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
private theorem l22en_red_sm5838 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5838 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5837) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 856 l22enSmReshape5838
    5837 5838 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l22en_sm_node_facts.1 ?_
    (l22en_nonempty_sm 857) (l22en_sm_not_written 857 5838 (by decide))
    (l22en_nonempty_sm 856) (l22en_sm_not_written 856 5837 (by decide))
  intro s
  unfold l22enSmReshape5838
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5837 5838 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11409 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11409 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11407) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1774 l22enPmReshape11409
    11407 11409 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l22en_pm_node_facts.1 ?_
    (l22en_nonempty_pm 1775) (l22en_pm_not_written 1775 11409 (by decide))
    (l22en_nonempty_pm 1774) (l22en_pm_not_written 1774 11407 (by decide))
  intro s
  unfold l22enPmReshape11409
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11407 11409 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11410 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11410 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11408) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1775 l22enPmReshape11410
    11408 11410 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l22en_pm_node_facts.2.1 ?_
    (l22en_nonempty_pm 1776) (l22en_pm_not_written 1776 11410 (by decide))
    (l22en_nonempty_pm 1775) (l22en_pm_not_written 1775 11408 (by decide))
  intro s
  unfold l22enPmReshape11410
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11408 11410 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm5839 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5839 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5838) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 857 l22enSmReshape5839
    5838 5839 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l22en_sm_node_facts.2.1 ?_
    (l22en_nonempty_sm 858) (l22en_sm_not_written 858 5839 (by decide))
    (l22en_nonempty_sm 857) (l22en_sm_not_written 857 5838 (by decide))
  intro s
  unfold l22enSmReshape5839
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5838 5839 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11415 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11415 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11409) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1776 l22enPmReshape11415
    11409 11415 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l22en_pm_node_facts.2.2.1 ?_
    (l22en_nonempty_pm 1777) (l22en_pm_not_written 1777 11415 (by decide))
    (l22en_nonempty_pm 1776) (l22en_pm_not_written 1776 11409 (by decide))
  intro s
  unfold l22enPmReshape11415
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11409 11415 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11416 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11416 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11410) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1777 l22enPmReshape11416
    11410 11416 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l22en_pm_node_facts.2.2.2.1 ?_
    (l22en_nonempty_pm 1778) (l22en_pm_not_written 1778 11416 (by decide))
    (l22en_nonempty_pm 1777) (l22en_pm_not_written 1777 11410 (by decide))
  intro s
  unfold l22enPmReshape11416
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11410 11416 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm5841 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5841 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5839)
        (denoteGraphDistributedFaithful sm initSM 5840) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 858 l22enSmLinear5841
    5839 5840 5841 fw_linear
    (by native_decide) l22en_sm_node_facts.2.2.1 ?_
    (l22en_nonempty_sm 859) (l22en_sm_not_written 859 5841 (by decide))
    (l22en_nonempty_sm 858) (l22en_sm_not_written 858 5839 (by decide))
    (l22en_w5840_sm_drop 858)
  intro s
  unfold l22enSmLinear5841
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5839 5840 5841

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11419 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11419 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11415)
        (denoteGraphDistributedFaithful pm initPM 5840) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1778 l22enPmLinear11419
    11415 5840 11419 fw_linear
    (by native_decide) l22en_pm_node_facts.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1779) (l22en_pm_not_written 1779 11419 (by decide))
    (l22en_nonempty_pm 1778) (l22en_pm_not_written 1778 11415 (by decide))
    (l22en_w5840_pm_drop 1778)
  intro s
  unfold l22enPmLinear11419
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11415 5840 11419

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11420 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11420 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11416)
        (denoteGraphDistributedFaithful pm initPM 5840) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1779 l22enPmLinear11420
    11416 5840 11420 fw_linear
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1780) (l22en_pm_not_written 1780 11420 (by decide))
    (l22en_nonempty_pm 1779) (l22en_pm_not_written 1779 11416 (by decide))
    (l22en_w5840_pm_drop 1779)
  intro s
  unfold l22enPmLinear11420
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11416 5840 11420

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm5842 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5842 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5841) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 859 l22enSmView5842
    5841 5842 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l22en_sm_node_facts.2.2.2.1 ?_
    (l22en_nonempty_sm 860) (l22en_sm_not_written 860 5842 (by decide))
    (l22en_nonempty_sm 859) (l22en_sm_not_written 859 5841 (by decide))
  intro s
  unfold l22enSmView5842
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5841 5842

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11429 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11429 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11419) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1780 l22enPmView11429
    11419 11429 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1781) (l22en_pm_not_written 1781 11429 (by decide))
    (l22en_nonempty_pm 1780) (l22en_pm_not_written 1780 11419 (by decide))
  intro s
  unfold l22enPmView11429
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11419 11429

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11430 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11430 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11420) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1781 l22enPmView11430
    11420 11430 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1782) (l22en_pm_not_written 1782 11430 (by decide))
    (l22en_nonempty_pm 1781) (l22en_pm_not_written 1781 11420 (by decide))
  intro s
  unfold l22enPmView11430
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11420 11430

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm5843 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5843 =
      denoteGraphDistributedFaithful sm initSM 5842 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 860 l22enSmFloat5843
    5842 5843 id
    (by native_decide) l22en_sm_node_facts.2.2.2.2.1 ?_
    (l22en_nonempty_sm 861) (l22en_sm_not_written 861 5843 (by decide))
    (l22en_nonempty_sm 860) (l22en_sm_not_written 860 5842 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l22enSmFloat5843
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5842 5843 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11433 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11433 =
      denoteGraphDistributedFaithful pm initPM 11429 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1782 l22enPmFloat11433
    11429 11433 id
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1783) (l22en_pm_not_written 1783 11433 (by decide))
    (l22en_nonempty_pm 1782) (l22en_pm_not_written 1782 11429 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l22enPmFloat11433
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 11429 11433 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11434 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11434 =
      denoteGraphDistributedFaithful pm initPM 11430 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1783 l22enPmFloat11434
    11430 11434 id
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1784) (l22en_pm_not_written 1784 11434 (by decide))
    (l22en_nonempty_pm 1783) (l22en_pm_not_written 1783 11430 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l22enPmFloat11434
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 11430 11434 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm5844 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5844 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8533)
        (denoteGraphDistributedFaithful sm initSM 5843) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 861 l22enSmAdd5844
    8533 5843 5844 elemwiseAdd
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.1 ?_
    (l22en_nonempty_sm 862) (l22en_sm_not_written 862 5844 (by decide))
    (l22en_nonempty_sm 861) (l22en_sm_not_written 861 8533 (by decide))
    (l22en_sm_not_written 861 5843 (by decide))
  intro s
  unfold l22enSmAdd5844
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8533 5843 5844

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11437 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11437 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16753)
        (denoteGraphDistributedFaithful pm initPM 11433) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1784 l22enPmAdd11437
    16753 11433 11437 elemwiseAdd
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1785) (l22en_pm_not_written 1785 11437 (by decide))
    (l22en_nonempty_pm 1784) (l22en_pm_not_written 1784 16753 (by decide))
    (l22en_pm_not_written 1784 11433 (by decide))
  intro s
  unfold l22enPmAdd11437
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16753 11433 11437

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11438 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11438 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16761)
        (denoteGraphDistributedFaithful pm initPM 11434) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1785 l22enPmAdd11438
    16761 11434 11438 elemwiseAdd
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1786) (l22en_pm_not_written 1786 11438 (by decide))
    (l22en_nonempty_pm 1785) (l22en_pm_not_written 1785 16761 (by decide))
    (l22en_pm_not_written 1785 11434 (by decide))
  intro s
  unfold l22enPmAdd11438
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16761 11434 11438

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm8537 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8537 =
      denoteGraphDistributedFaithful sm initSM 5844 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 862 l22enSmMulti2
    5844 8537 (fun x => x)
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_sm 863) (l22en_sm_not_written 863 8537 (by decide))
    (l22en_nonempty_sm 862) (l22en_sm_not_written 862 5844 (by decide))
  intro s
  unfold l22enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5844 8537 8541

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm8541 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8541 =
      denoteGraphDistributedFaithful sm initSM 5844 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 862 l22enSmMulti2
    5844 8541 (fun x => x)
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_sm 863) (l22en_sm_not_written 863 8541 (by decide))
    (l22en_nonempty_sm 862) (l22en_sm_not_written 862 5844 (by decide))
  intro s
  unfold l22enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5844 8537 8541 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16765 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16765 =
      denoteGraphDistributedFaithful pm initPM 11437 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1786 l22enPmMulti2R0
    11437 16765 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1787) (l22en_pm_not_written 1787 16765 (by decide))
    (l22en_nonempty_pm 1786) (l22en_pm_not_written 1786 11437 (by decide))
  intro s
  unfold l22enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11437 16765 16769

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16769 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16769 =
      denoteGraphDistributedFaithful pm initPM 11437 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1786 l22enPmMulti2R0
    11437 16769 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1787) (l22en_pm_not_written 1787 16769 (by decide))
    (l22en_nonempty_pm 1786) (l22en_pm_not_written 1786 11437 (by decide))
  intro s
  unfold l22enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11437 16765 16769 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16773 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16773 =
      denoteGraphDistributedFaithful pm initPM 11438 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1787 l22enPmMulti2R1
    11438 16773 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1788) (l22en_pm_not_written 1788 16773 (by decide))
    (l22en_nonempty_pm 1787) (l22en_pm_not_written 1787 11438 (by decide))
  intro s
  unfold l22enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11438 16773 16777

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16777 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16777 =
      denoteGraphDistributedFaithful pm initPM 11438 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1787 l22enPmMulti2R1
    11438 16777 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1788) (l22en_pm_not_written 1788 16777 (by decide))
    (l22en_nonempty_pm 1787) (l22en_pm_not_written 1787 11438 (by decide))
  intro s
  unfold l22enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11438 16773 16777 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm5846 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5846 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8537)
        (denoteGraphDistributedFaithful sm initSM 5845) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 863 l22enSmRms5846
    8537 5845 5846 fw_rms_norm
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_sm 864) (l22en_sm_not_written 864 5846 (by decide))
    (l22en_nonempty_sm 863) (l22en_sm_not_written 863 8537 (by decide))
    (l22en_w5845_sm_drop 863)
  intro s
  unfold l22enSmRms5846
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8537 5845 5846

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11441 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11441 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16765)
        (denoteGraphDistributedFaithful pm initPM 5845) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1788 l22enPmRms11441
    16765 5845 11441 fw_rms_norm
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1789) (l22en_pm_not_written 1789 11441 (by decide))
    (l22en_nonempty_pm 1788) (l22en_pm_not_written 1788 16765 (by decide))
    (l22en_w5845_pm_drop 1788)
  intro s
  unfold l22enPmRms11441
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16765 5845 11441

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm11442 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11442 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16773)
        (denoteGraphDistributedFaithful pm initPM 5845) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1789 l22enPmRms11442
    16773 5845 11442 fw_rms_norm
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1790) (l22en_pm_not_written 1790 11442 (by decide))
    (l22en_nonempty_pm 1789) (l22en_pm_not_written 1789 16773 (by decide))
    (l22en_w5845_pm_drop 1789)
  intro s
  unfold l22enPmRms11442
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16773 5845 11442

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm8548 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8548 =
      denoteGraphDistributedFaithful sm initSM 5846 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 864 l22enSmMulti5
    5846 8548 (fun x => x)
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_sm 865) (l22en_sm_not_written 865 8548 (by decide))
    (l22en_nonempty_sm 864) (l22en_sm_not_written 864 5846 (by decide))
  intro s
  unfold l22enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l22en_multiref5_first_out sm s 0 5846 8548 8552 8556 8560 8564

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm8552 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8552 =
      denoteGraphDistributedFaithful sm initSM 5846 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 864 l22enSmMulti5
    5846 8552 (fun x => x)
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_sm 865) (l22en_sm_not_written 865 8552 (by decide))
    (l22en_nonempty_sm 864) (l22en_sm_not_written 864 5846 (by decide))
  intro s
  unfold l22enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5846 8548 8552 8556 8560 8564
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm8556 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8556 =
      denoteGraphDistributedFaithful sm initSM 5846 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 864 l22enSmMulti5
    5846 8556 (fun x => x)
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_sm 865) (l22en_sm_not_written 865 8556 (by decide))
    (l22en_nonempty_sm 864) (l22en_sm_not_written 864 5846 (by decide))
  intro s
  unfold l22enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5846 8548 8552 8556 8560 8564
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm8560 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8560 =
      denoteGraphDistributedFaithful sm initSM 5846 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 864 l22enSmMulti5
    5846 8560 (fun x => x)
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_sm 865) (l22en_sm_not_written 865 8560 (by decide))
    (l22en_nonempty_sm 864) (l22en_sm_not_written 864 5846 (by decide))
  intro s
  unfold l22enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5846 8548 8552 8556 8560 8564
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_sm8564 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8564 =
      denoteGraphDistributedFaithful sm initSM 5846 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 864 l22enSmMulti5
    5846 8564 (fun x => x)
    (by native_decide) l22en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_sm 865) (l22en_sm_not_written 865 8564 (by decide))
    (l22en_nonempty_sm 864) (l22en_sm_not_written 864 5846 (by decide))
  intro s
  unfold l22enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5846 8548 8552 8556 8560 8564
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16784 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16784 =
      denoteGraphDistributedFaithful pm initPM 11441 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1790 l22enPmMulti5R0
    11441 16784 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 16784 (by decide))
    (l22en_nonempty_pm 1790) (l22en_pm_not_written 1790 11441 (by decide))
  intro s
  unfold l22enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l22en_multiref5_first_out pm s 0 11441 16784 16788 16792 16796 16800

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16788 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16788 =
      denoteGraphDistributedFaithful pm initPM 11441 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1790 l22enPmMulti5R0
    11441 16788 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 16788 (by decide))
    (l22en_nonempty_pm 1790) (l22en_pm_not_written 1790 11441 (by decide))
  intro s
  unfold l22enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 11441 16784 16788 16792 16796 16800
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16792 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16792 =
      denoteGraphDistributedFaithful pm initPM 11441 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1790 l22enPmMulti5R0
    11441 16792 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 16792 (by decide))
    (l22en_nonempty_pm 1790) (l22en_pm_not_written 1790 11441 (by decide))
  intro s
  unfold l22enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 11441 16784 16788 16792 16796 16800
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16796 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16796 =
      denoteGraphDistributedFaithful pm initPM 11441 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1790 l22enPmMulti5R0
    11441 16796 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 16796 (by decide))
    (l22en_nonempty_pm 1790) (l22en_pm_not_written 1790 11441 (by decide))
  intro s
  unfold l22enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 11441 16784 16788 16792 16796 16800
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16800 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16800 =
      denoteGraphDistributedFaithful pm initPM 11441 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1790 l22enPmMulti5R0
    11441 16800 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 16800 (by decide))
    (l22en_nonempty_pm 1790) (l22en_pm_not_written 1790 11441 (by decide))
  intro s
  unfold l22enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 11441 16784 16788 16792 16796 16800
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16807 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16807 =
      denoteGraphDistributedFaithful pm initPM 11442 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1791 l22enPmMulti5R1
    11442 16807 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_pm 1792) (l22en_pm_not_written 1792 16807 (by decide))
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 11442 (by decide))
  intro s
  unfold l22enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l22en_multiref5_first_out pm s 1 11442 16807 16811 16815 16819 16823

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16811 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16811 =
      denoteGraphDistributedFaithful pm initPM 11442 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1791 l22enPmMulti5R1
    11442 16811 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_pm 1792) (l22en_pm_not_written 1792 16811 (by decide))
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 11442 (by decide))
  intro s
  unfold l22enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 11442 16807 16811 16815 16819 16823
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16815 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16815 =
      denoteGraphDistributedFaithful pm initPM 11442 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1791 l22enPmMulti5R1
    11442 16815 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_pm 1792) (l22en_pm_not_written 1792 16815 (by decide))
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 11442 (by decide))
  intro s
  unfold l22enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 11442 16807 16811 16815 16819 16823
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16819 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16819 =
      denoteGraphDistributedFaithful pm initPM 11442 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1791 l22enPmMulti5R1
    11442 16819 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_pm 1792) (l22en_pm_not_written 1792 16819 (by decide))
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 11442 (by decide))
  intro s
  unfold l22enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 11442 16807 16811 16815 16819 16823
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22en_red_pm16823 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16823 =
      denoteGraphDistributedFaithful pm initPM 11442 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1791 l22enPmMulti5R1
    11442 16823 (fun x => x)
    (by native_decide) l22en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22en_nonempty_pm 1792) (l22en_pm_not_written 1792 16823 (by decide))
    (l22en_nonempty_pm 1791) (l22en_pm_not_written 1791 11442 (by decide))
  intro s
  unfold l22enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 11442 16807 16811 16815 16819 16823
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5838 (`FW_reshape` of 5837).
theorem recon_zigzagGoal_5838_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5838)
      (denoteGraphDistributedFaithful pm initPM 11409)
      (denoteGraphDistributedFaithful pm initPM 11410)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5837_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm5838 initSM, l22en_red_pm11409 initPM, l22en_red_pm11410 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5839 (`FW_reshape` of 5838).
theorem recon_zigzagGoal_5839_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5839)
      (denoteGraphDistributedFaithful pm initPM 11415)
      (denoteGraphDistributedFaithful pm initPM 11416)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5838_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm5839 initSM, l22en_red_pm11415 initPM, l22en_red_pm11416 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5841 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5841_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5841)
      (denoteGraphDistributedFaithful pm initPM 11419)
      (denoteGraphDistributedFaithful pm initPM 11420)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5839_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5840 = initPM 5840 :=
    recon_weight initSM initPM hInit initGoal_5840 (by native_decide) 5840
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5840 = initSM 5840 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5840
      layer1_sm_nodes_nonempty (fun n hn => (l22en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5840 = initPM 5840 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5840
      layer1_pm_nodes_nonempty (fun n hn => (l22en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5840 =
      denoteGraphDistributedFaithful pm initPM 5840 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5840).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5840 [1024, 1024] (by native_decide)
  rw [l22en_red_sm5841 initSM, l22en_red_pm11419 initPM, l22en_red_pm11420 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5842 (`FW_view` of 5841).
theorem recon_zigzagGoal_5842_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5842)
      (denoteGraphDistributedFaithful pm initPM 11429)
      (denoteGraphDistributedFaithful pm initPM 11430)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5841_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm5842 initSM, l22en_red_pm11429 initPM, l22en_red_pm11430 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5843 (`FW_float` of 5842).
theorem recon_zigzagGoal_5843_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5843)
      (denoteGraphDistributedFaithful pm initPM 11433)
      (denoteGraphDistributedFaithful pm initPM 11434)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5842_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm5843 initSM, l22en_red_pm11433 initPM, l22en_red_pm11434 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5844 (residual `FW_add` of the
-- cross-layer bypass 8533 and 5843).
theorem recon_zigzagGoal_5844_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5844)
      (denoteGraphDistributedFaithful pm initPM 11437)
      (denoteGraphDistributedFaithful pm initPM 11438)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8533_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5843_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5786_5835 : denoteGraphDistributedFaithful pm initPM 5786 =
      denoteGraphDistributedFaithful pm initPM 5835 := by
    rw [pmFinal 5786 (fun n hn => (l22en_cu_not_written n hn).1),
      pmFinal 5835 (fun n hn => (l22en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5786_5835] at hA
  rw [l22en_red_sm5844 initSM, l22en_red_pm11437 initPM, l22en_red_pm11438 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8537 (2-way multiref, position 0).
theorem recon_zigzagGoal_8537_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8537)
      (denoteGraphDistributedFaithful pm initPM 16765)
      (denoteGraphDistributedFaithful pm initPM 16773)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5844_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm8537 initSM, l22en_red_pm16765 initPM, l22en_red_pm16773 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8541 (2-way multiref, position 1).
theorem recon_zigzagGoal_8541_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8541)
      (denoteGraphDistributedFaithful pm initPM 16769)
      (denoteGraphDistributedFaithful pm initPM 16777)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5844_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm8541 initSM, l22en_red_pm16769 initPM, l22en_red_pm16777 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5846 (`FW_rms_norm` of 8537 with
-- the replicated weight 5845).
theorem recon_zigzagGoal_5846_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5846)
      (denoteGraphDistributedFaithful pm initPM 11441)
      (denoteGraphDistributedFaithful pm initPM 11442)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8537_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5845 = initPM 5845 :=
    recon_weight initSM initPM hInit initGoal_5845 (by native_decide) 5845
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5845 = initSM 5845 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5845
      layer1_sm_nodes_nonempty (fun n hn => (l22en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5845 = initPM 5845 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5845
      layer1_pm_nodes_nonempty (fun n hn => (l22en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5845 =
      denoteGraphDistributedFaithful pm initPM 5845 := by
    rw [hsw, hpw]; exact hwInit
  rw [l22en_red_sm5846 initSM, l22en_red_pm11441 initPM, l22en_red_pm11442 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8548 (5-way multiref, position 0).
theorem recon_zigzagGoal_8548_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8548)
      (denoteGraphDistributedFaithful pm initPM 16784)
      (denoteGraphDistributedFaithful pm initPM 16807)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5846_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm8548 initSM, l22en_red_pm16784 initPM, l22en_red_pm16807 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8552 (5-way multiref, position 1).
theorem recon_zigzagGoal_8552_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8552)
      (denoteGraphDistributedFaithful pm initPM 16788)
      (denoteGraphDistributedFaithful pm initPM 16811)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5846_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm8552 initSM, l22en_red_pm16788 initPM, l22en_red_pm16811 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8556 (5-way multiref, position 2).
theorem recon_zigzagGoal_8556_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8556)
      (denoteGraphDistributedFaithful pm initPM 16792)
      (denoteGraphDistributedFaithful pm initPM 16815)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5846_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm8556 initSM, l22en_red_pm16792 initPM, l22en_red_pm16815 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8560 (5-way multiref, position 3).
theorem recon_zigzagGoal_8560_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8560)
      (denoteGraphDistributedFaithful pm initPM 16796)
      (denoteGraphDistributedFaithful pm initPM 16819)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5846_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm8560 initSM, l22en_red_pm16796 initPM, l22en_red_pm16819 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8564 (5-way multiref, position 4).
theorem recon_zigzagGoal_8564_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8564)
      (denoteGraphDistributedFaithful pm initPM 16800)
      (denoteGraphDistributedFaithful pm initPM 16823)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5846_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22en_red_sm8564 initSM, l22en_red_pm16800 initPM, l22en_red_pm16823 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
