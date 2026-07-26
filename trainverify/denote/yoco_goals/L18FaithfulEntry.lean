/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L18FaithfulZigzagAttention
import denote.yoco_goals.L17FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-6 entry segment

Continuation of `recon_zigzagGoal_5641_faithful` (block-6 cross-decoder
attention) through the block-6 entry segment:

* SM 716: `FW_reshape [5641] → [5642]`   (PM 1494/1495: `10719 → 10721`, `10720 → 10722`)
* SM 717: `FW_reshape [5642] → [5643]`   (PM 1496/1497: `10721 → 10727`, `10722 → 10728`)
* SM 718: `FW_mix_precision_linear [5643, 5644] → [5645]`
                                          (PM 1498/1499 with replicated weight 5644)
* SM 719: `FW_view [5645] → [5646]`      (PM 1500/1501)
* SM 720: `FW_float [5646] → [5647]`     (PM 1502/1503)
* SM 721: `FW_add [8377, 5647] → [5648]` (PM 1504/1505 with bypass 16441/16449)
* SM 722: `FW_multiref [5648] → [8381, 8385]`
                                          (PM 1506: `[16453, 16457]`, PM 1507: `[16461, 16465]`)
* SM 723: `FW_rms_norm [8381, 5649] → [5650]` (PM 1508/1509, replicated weight 5649)
* SM 724: `FW_multiref [5650] → [8392, 8396, 8400, 8404, 8408]`
                                          (PM 1510: `[16472, 16476, 16480, 16484, 16488]`,
                                           PM 1511: `[16495, 16499, 16503, 16507, 16511]`)

All relations are stated against the block-6 cumulative-sequence metadata tensor
`5639` (the same cu slot used by `recon_zigzagGoal_5641_faithful`).
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

private theorem l18en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l18enSmReshape5642 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5641], outs := [5642],
    params := [4096, 1024] }
private def l18enSmReshape5643 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5642], outs := [5643],
    params := [4096, 1024] }
private def l18enSmLinear5645 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5643, 5644],
    outs := [5645] }
private def l18enSmView5646 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5645], outs := [5646],
    params := [4096, 1024] }
private def l18enSmFloat5647 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5646], outs := [5647] }
private def l18enSmAdd5648 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8377, 5647], outs := [5648] }
private def l18enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5648], outs := [8381, 8385],
    params := [2] }
private def l18enSmRms5650 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8381, 5649], outs := [5650] }
private def l18enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5650],
    outs := [8392, 8396, 8400, 8404, 8408], params := [5] }

private def l18enPmReshape10721 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10719], outs := [10721],
    params := [2048, 1024] }
private def l18enPmReshape10722 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10720], outs := [10722],
    params := [2048, 1024] }
private def l18enPmReshape10727 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10721], outs := [10727],
    params := [2048, 1024] }
private def l18enPmReshape10728 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10722], outs := [10728],
    params := [2048, 1024] }
private def l18enPmLinear10731 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10727, 5644],
    outs := [10731] }
private def l18enPmLinear10732 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10728, 5644],
    outs := [10732] }
private def l18enPmView10741 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10731], outs := [10741],
    params := [2048, 1024] }
private def l18enPmView10742 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10732], outs := [10742],
    params := [2048, 1024] }
private def l18enPmFloat10745 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10741], outs := [10745] }
private def l18enPmFloat10746 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10742], outs := [10746] }
private def l18enPmAdd10749 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16441, 10745], outs := [10749] }
private def l18enPmAdd10750 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16449, 10746], outs := [10750] }
private def l18enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10749], outs := [16453, 16457],
    params := [2] }
private def l18enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10750], outs := [16461, 16465],
    params := [2] }
private def l18enPmRms10753 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16453, 5649], outs := [10753] }
private def l18enPmRms10754 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16461, 5649], outs := [10754] }
private def l18enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10753],
    outs := [16472, 16476, 16480, 16484, 16488], params := [5] }
private def l18enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10754],
    outs := [16495, 16499, 16503, 16507, 16511], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l18en_sm_node_facts :
    sm.nodes[716]'(by native_decide) = l18enSmReshape5642 ∧
    sm.nodes[717]'(by native_decide) = l18enSmReshape5643 ∧
    sm.nodes[718]'(by native_decide) = l18enSmLinear5645 ∧
    sm.nodes[719]'(by native_decide) = l18enSmView5646 ∧
    sm.nodes[720]'(by native_decide) = l18enSmFloat5647 ∧
    sm.nodes[721]'(by native_decide) = l18enSmAdd5648 ∧
    sm.nodes[722]'(by native_decide) = l18enSmMulti2 ∧
    sm.nodes[723]'(by native_decide) = l18enSmRms5650 ∧
    sm.nodes[724]'(by native_decide) = l18enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l18en_pm_node_facts :
    pm.nodes[1494]'(by native_decide) = l18enPmReshape10721 ∧
    pm.nodes[1495]'(by native_decide) = l18enPmReshape10722 ∧
    pm.nodes[1496]'(by native_decide) = l18enPmReshape10727 ∧
    pm.nodes[1497]'(by native_decide) = l18enPmReshape10728 ∧
    pm.nodes[1498]'(by native_decide) = l18enPmLinear10731 ∧
    pm.nodes[1499]'(by native_decide) = l18enPmLinear10732 ∧
    pm.nodes[1500]'(by native_decide) = l18enPmView10741 ∧
    pm.nodes[1501]'(by native_decide) = l18enPmView10742 ∧
    pm.nodes[1502]'(by native_decide) = l18enPmFloat10745 ∧
    pm.nodes[1503]'(by native_decide) = l18enPmFloat10746 ∧
    pm.nodes[1504]'(by native_decide) = l18enPmAdd10749 ∧
    pm.nodes[1505]'(by native_decide) = l18enPmAdd10750 ∧
    pm.nodes[1506]'(by native_decide) = l18enPmMulti2R0 ∧
    pm.nodes[1507]'(by native_decide) = l18enPmMulti2R1 ∧
    pm.nodes[1508]'(by native_decide) = l18enPmRms10753 ∧
    pm.nodes[1509]'(by native_decide) = l18enPmRms10754 ∧
    pm.nodes[1510]'(by native_decide) = l18enPmMulti5R0 ∧
    pm.nodes[1511]'(by native_decide) = l18enPmMulti5R1 := by
  native_decide

private theorem l18en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l18en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l18en_weights_not_written :
    (∀ n ∈ sm.nodes, 5644 ∉ n.outs ∧ 5649 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5644 ∉ n.outs ∧ 5649 ∉ n.outs) := by
  native_decide

private theorem l18en_w5644_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5644 ∉ n.outs := by
  intro n hn
  exact (l18en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l18en_w5644_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5644 ∉ n.outs := by
  intro n hn
  exact (l18en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l18en_w5649_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5649 ∉ n.outs := by
  intro n hn
  exact (l18en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l18en_w5649_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5649 ∉ n.outs := by
  intro n hn
  exact (l18en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l18en_cu_not_written :
    ∀ n ∈ pm.nodes, 5590 ∉ n.outs ∧ 5639 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l18en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(717, 5642), (716, 5641), (718, 5643), (719, 5645), (720, 5646), (721,
      5647), (722, 5648), (721, 8377), (723, 8381), (723, 8385), (724, 5650),
      (725, 8392), (725, 8396), (725, 8400), (725, 8404), (725, 8408)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l18en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1495, 10721), (1494, 10719), (1496, 10722), (1495, 10720), (1497, 10727),
      (1496, 10721), (1498, 10728), (1497, 10722), (1499, 10731), (1498, 10727),
      (1500, 10732), (1499, 10728), (1501, 10741), (1500, 10731), (1502, 10742),
      (1501, 10732), (1503, 10745), (1502, 10741), (1504, 10746), (1503, 10742),
      (1505, 10749), (1504, 16441), (1504, 10745), (1506, 10750), (1505, 16449),
      (1505, 10746), (1507, 16453), (1507, 16457), (1506, 10749), (1508, 16461),
      (1508, 16465), (1507, 10750), (1509, 10753), (1508, 16453), (1510, 10754),
      (1509, 16461), (1511, 16472), (1511, 16476), (1511, 16480), (1511, 16484),
      (1511, 16488), (1510, 10753), (1512, 16495), (1512, 16499), (1512, 16503),
      (1512, 16507), (1512, 16511), (1511, 10754)]) :
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
private theorem l18en_red_sm5642 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5642 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5641) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 716 l18enSmReshape5642
    5641 5642 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l18en_sm_node_facts.1 ?_
    (l18en_nonempty_sm 717) (l18en_sm_not_written 717 5642 (by decide))
    (l18en_nonempty_sm 716) (l18en_sm_not_written 716 5641 (by decide))
  intro s
  unfold l18enSmReshape5642
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5641 5642 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10721 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10721 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10719) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1494 l18enPmReshape10721
    10719 10721 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l18en_pm_node_facts.1 ?_
    (l18en_nonempty_pm 1495) (l18en_pm_not_written 1495 10721 (by decide))
    (l18en_nonempty_pm 1494) (l18en_pm_not_written 1494 10719 (by decide))
  intro s
  unfold l18enPmReshape10721
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10719 10721 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10722 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10722 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10720) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1495 l18enPmReshape10722
    10720 10722 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l18en_pm_node_facts.2.1 ?_
    (l18en_nonempty_pm 1496) (l18en_pm_not_written 1496 10722 (by decide))
    (l18en_nonempty_pm 1495) (l18en_pm_not_written 1495 10720 (by decide))
  intro s
  unfold l18enPmReshape10722
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10720 10722 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm5643 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5643 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5642) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 717 l18enSmReshape5643
    5642 5643 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l18en_sm_node_facts.2.1 ?_
    (l18en_nonempty_sm 718) (l18en_sm_not_written 718 5643 (by decide))
    (l18en_nonempty_sm 717) (l18en_sm_not_written 717 5642 (by decide))
  intro s
  unfold l18enSmReshape5643
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5642 5643 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10727 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10727 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10721) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1496 l18enPmReshape10727
    10721 10727 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l18en_pm_node_facts.2.2.1 ?_
    (l18en_nonempty_pm 1497) (l18en_pm_not_written 1497 10727 (by decide))
    (l18en_nonempty_pm 1496) (l18en_pm_not_written 1496 10721 (by decide))
  intro s
  unfold l18enPmReshape10727
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10721 10727 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10728 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10728 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10722) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1497 l18enPmReshape10728
    10722 10728 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l18en_pm_node_facts.2.2.2.1 ?_
    (l18en_nonempty_pm 1498) (l18en_pm_not_written 1498 10728 (by decide))
    (l18en_nonempty_pm 1497) (l18en_pm_not_written 1497 10722 (by decide))
  intro s
  unfold l18enPmReshape10728
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10722 10728 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm5645 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5645 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5643)
        (denoteGraphDistributedFaithful sm initSM 5644) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 718 l18enSmLinear5645
    5643 5644 5645 fw_linear
    (by native_decide) l18en_sm_node_facts.2.2.1 ?_
    (l18en_nonempty_sm 719) (l18en_sm_not_written 719 5645 (by decide))
    (l18en_nonempty_sm 718) (l18en_sm_not_written 718 5643 (by decide))
    (l18en_w5644_sm_drop 718)
  intro s
  unfold l18enSmLinear5645
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5643 5644 5645

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10731 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10731 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10727)
        (denoteGraphDistributedFaithful pm initPM 5644) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1498 l18enPmLinear10731
    10727 5644 10731 fw_linear
    (by native_decide) l18en_pm_node_facts.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1499) (l18en_pm_not_written 1499 10731 (by decide))
    (l18en_nonempty_pm 1498) (l18en_pm_not_written 1498 10727 (by decide))
    (l18en_w5644_pm_drop 1498)
  intro s
  unfold l18enPmLinear10731
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10727 5644 10731

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10732 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10732 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10728)
        (denoteGraphDistributedFaithful pm initPM 5644) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1499 l18enPmLinear10732
    10728 5644 10732 fw_linear
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1500) (l18en_pm_not_written 1500 10732 (by decide))
    (l18en_nonempty_pm 1499) (l18en_pm_not_written 1499 10728 (by decide))
    (l18en_w5644_pm_drop 1499)
  intro s
  unfold l18enPmLinear10732
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10728 5644 10732

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm5646 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5646 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5645) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 719 l18enSmView5646
    5645 5646 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l18en_sm_node_facts.2.2.2.1 ?_
    (l18en_nonempty_sm 720) (l18en_sm_not_written 720 5646 (by decide))
    (l18en_nonempty_sm 719) (l18en_sm_not_written 719 5645 (by decide))
  intro s
  unfold l18enSmView5646
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5645 5646

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10741 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10741 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10731) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1500 l18enPmView10741
    10731 10741 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1501) (l18en_pm_not_written 1501 10741 (by decide))
    (l18en_nonempty_pm 1500) (l18en_pm_not_written 1500 10731 (by decide))
  intro s
  unfold l18enPmView10741
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10731 10741

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10742 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10742 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10732) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1501 l18enPmView10742
    10732 10742 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1502) (l18en_pm_not_written 1502 10742 (by decide))
    (l18en_nonempty_pm 1501) (l18en_pm_not_written 1501 10732 (by decide))
  intro s
  unfold l18enPmView10742
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10732 10742

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm5647 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5647 =
      denoteGraphDistributedFaithful sm initSM 5646 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 720 l18enSmFloat5647
    5646 5647 id
    (by native_decide) l18en_sm_node_facts.2.2.2.2.1 ?_
    (l18en_nonempty_sm 721) (l18en_sm_not_written 721 5647 (by decide))
    (l18en_nonempty_sm 720) (l18en_sm_not_written 720 5646 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l18enSmFloat5647
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5646 5647 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10745 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10745 =
      denoteGraphDistributedFaithful pm initPM 10741 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1502 l18enPmFloat10745
    10741 10745 id
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1503) (l18en_pm_not_written 1503 10745 (by decide))
    (l18en_nonempty_pm 1502) (l18en_pm_not_written 1502 10741 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l18enPmFloat10745
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 10741 10745 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10746 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10746 =
      denoteGraphDistributedFaithful pm initPM 10742 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1503 l18enPmFloat10746
    10742 10746 id
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1504) (l18en_pm_not_written 1504 10746 (by decide))
    (l18en_nonempty_pm 1503) (l18en_pm_not_written 1503 10742 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l18enPmFloat10746
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 10742 10746 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm5648 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5648 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8377)
        (denoteGraphDistributedFaithful sm initSM 5647) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 721 l18enSmAdd5648
    8377 5647 5648 elemwiseAdd
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.1 ?_
    (l18en_nonempty_sm 722) (l18en_sm_not_written 722 5648 (by decide))
    (l18en_nonempty_sm 721) (l18en_sm_not_written 721 8377 (by decide))
    (l18en_sm_not_written 721 5647 (by decide))
  intro s
  unfold l18enSmAdd5648
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8377 5647 5648

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10749 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10749 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16441)
        (denoteGraphDistributedFaithful pm initPM 10745) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1504 l18enPmAdd10749
    16441 10745 10749 elemwiseAdd
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1505) (l18en_pm_not_written 1505 10749 (by decide))
    (l18en_nonempty_pm 1504) (l18en_pm_not_written 1504 16441 (by decide))
    (l18en_pm_not_written 1504 10745 (by decide))
  intro s
  unfold l18enPmAdd10749
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16441 10745 10749

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10750 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10750 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16449)
        (denoteGraphDistributedFaithful pm initPM 10746) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1505 l18enPmAdd10750
    16449 10746 10750 elemwiseAdd
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1506) (l18en_pm_not_written 1506 10750 (by decide))
    (l18en_nonempty_pm 1505) (l18en_pm_not_written 1505 16449 (by decide))
    (l18en_pm_not_written 1505 10746 (by decide))
  intro s
  unfold l18enPmAdd10750
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16449 10746 10750

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm8381 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8381 =
      denoteGraphDistributedFaithful sm initSM 5648 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 722 l18enSmMulti2
    5648 8381 (fun x => x)
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_sm 723) (l18en_sm_not_written 723 8381 (by decide))
    (l18en_nonempty_sm 722) (l18en_sm_not_written 722 5648 (by decide))
  intro s
  unfold l18enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5648 8381 8385

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm8385 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8385 =
      denoteGraphDistributedFaithful sm initSM 5648 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 722 l18enSmMulti2
    5648 8385 (fun x => x)
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_sm 723) (l18en_sm_not_written 723 8385 (by decide))
    (l18en_nonempty_sm 722) (l18en_sm_not_written 722 5648 (by decide))
  intro s
  unfold l18enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5648 8381 8385 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16453 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16453 =
      denoteGraphDistributedFaithful pm initPM 10749 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1506 l18enPmMulti2R0
    10749 16453 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1507) (l18en_pm_not_written 1507 16453 (by decide))
    (l18en_nonempty_pm 1506) (l18en_pm_not_written 1506 10749 (by decide))
  intro s
  unfold l18enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10749 16453 16457

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16457 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16457 =
      denoteGraphDistributedFaithful pm initPM 10749 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1506 l18enPmMulti2R0
    10749 16457 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1507) (l18en_pm_not_written 1507 16457 (by decide))
    (l18en_nonempty_pm 1506) (l18en_pm_not_written 1506 10749 (by decide))
  intro s
  unfold l18enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10749 16453 16457 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16461 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16461 =
      denoteGraphDistributedFaithful pm initPM 10750 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1507 l18enPmMulti2R1
    10750 16461 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1508) (l18en_pm_not_written 1508 16461 (by decide))
    (l18en_nonempty_pm 1507) (l18en_pm_not_written 1507 10750 (by decide))
  intro s
  unfold l18enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10750 16461 16465

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16465 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16465 =
      denoteGraphDistributedFaithful pm initPM 10750 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1507 l18enPmMulti2R1
    10750 16465 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1508) (l18en_pm_not_written 1508 16465 (by decide))
    (l18en_nonempty_pm 1507) (l18en_pm_not_written 1507 10750 (by decide))
  intro s
  unfold l18enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10750 16461 16465 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm5650 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5650 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8381)
        (denoteGraphDistributedFaithful sm initSM 5649) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 723 l18enSmRms5650
    8381 5649 5650 fw_rms_norm
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_sm 724) (l18en_sm_not_written 724 5650 (by decide))
    (l18en_nonempty_sm 723) (l18en_sm_not_written 723 8381 (by decide))
    (l18en_w5649_sm_drop 723)
  intro s
  unfold l18enSmRms5650
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8381 5649 5650

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10753 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10753 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16453)
        (denoteGraphDistributedFaithful pm initPM 5649) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1508 l18enPmRms10753
    16453 5649 10753 fw_rms_norm
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1509) (l18en_pm_not_written 1509 10753 (by decide))
    (l18en_nonempty_pm 1508) (l18en_pm_not_written 1508 16453 (by decide))
    (l18en_w5649_pm_drop 1508)
  intro s
  unfold l18enPmRms10753
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16453 5649 10753

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm10754 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10754 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16461)
        (denoteGraphDistributedFaithful pm initPM 5649) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1509 l18enPmRms10754
    16461 5649 10754 fw_rms_norm
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1510) (l18en_pm_not_written 1510 10754 (by decide))
    (l18en_nonempty_pm 1509) (l18en_pm_not_written 1509 16461 (by decide))
    (l18en_w5649_pm_drop 1509)
  intro s
  unfold l18enPmRms10754
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16461 5649 10754

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm8392 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8392 =
      denoteGraphDistributedFaithful sm initSM 5650 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 724 l18enSmMulti5
    5650 8392 (fun x => x)
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_sm 725) (l18en_sm_not_written 725 8392 (by decide))
    (l18en_nonempty_sm 724) (l18en_sm_not_written 724 5650 (by decide))
  intro s
  unfold l18enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l18en_multiref5_first_out sm s 0 5650 8392 8396 8400 8404 8408

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm8396 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8396 =
      denoteGraphDistributedFaithful sm initSM 5650 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 724 l18enSmMulti5
    5650 8396 (fun x => x)
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_sm 725) (l18en_sm_not_written 725 8396 (by decide))
    (l18en_nonempty_sm 724) (l18en_sm_not_written 724 5650 (by decide))
  intro s
  unfold l18enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5650 8392 8396 8400 8404 8408
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm8400 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8400 =
      denoteGraphDistributedFaithful sm initSM 5650 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 724 l18enSmMulti5
    5650 8400 (fun x => x)
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_sm 725) (l18en_sm_not_written 725 8400 (by decide))
    (l18en_nonempty_sm 724) (l18en_sm_not_written 724 5650 (by decide))
  intro s
  unfold l18enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5650 8392 8396 8400 8404 8408
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm8404 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8404 =
      denoteGraphDistributedFaithful sm initSM 5650 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 724 l18enSmMulti5
    5650 8404 (fun x => x)
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_sm 725) (l18en_sm_not_written 725 8404 (by decide))
    (l18en_nonempty_sm 724) (l18en_sm_not_written 724 5650 (by decide))
  intro s
  unfold l18enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5650 8392 8396 8400 8404 8408
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_sm8408 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8408 =
      denoteGraphDistributedFaithful sm initSM 5650 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 724 l18enSmMulti5
    5650 8408 (fun x => x)
    (by native_decide) l18en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_sm 725) (l18en_sm_not_written 725 8408 (by decide))
    (l18en_nonempty_sm 724) (l18en_sm_not_written 724 5650 (by decide))
  intro s
  unfold l18enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5650 8392 8396 8400 8404 8408
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16472 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16472 =
      denoteGraphDistributedFaithful pm initPM 10753 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1510 l18enPmMulti5R0
    10753 16472 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 16472 (by decide))
    (l18en_nonempty_pm 1510) (l18en_pm_not_written 1510 10753 (by decide))
  intro s
  unfold l18enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l18en_multiref5_first_out pm s 0 10753 16472 16476 16480 16484 16488

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16476 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16476 =
      denoteGraphDistributedFaithful pm initPM 10753 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1510 l18enPmMulti5R0
    10753 16476 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 16476 (by decide))
    (l18en_nonempty_pm 1510) (l18en_pm_not_written 1510 10753 (by decide))
  intro s
  unfold l18enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 10753 16472 16476 16480 16484 16488
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16480 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16480 =
      denoteGraphDistributedFaithful pm initPM 10753 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1510 l18enPmMulti5R0
    10753 16480 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 16480 (by decide))
    (l18en_nonempty_pm 1510) (l18en_pm_not_written 1510 10753 (by decide))
  intro s
  unfold l18enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 10753 16472 16476 16480 16484 16488
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16484 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16484 =
      denoteGraphDistributedFaithful pm initPM 10753 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1510 l18enPmMulti5R0
    10753 16484 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 16484 (by decide))
    (l18en_nonempty_pm 1510) (l18en_pm_not_written 1510 10753 (by decide))
  intro s
  unfold l18enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 10753 16472 16476 16480 16484 16488
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16488 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16488 =
      denoteGraphDistributedFaithful pm initPM 10753 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1510 l18enPmMulti5R0
    10753 16488 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 16488 (by decide))
    (l18en_nonempty_pm 1510) (l18en_pm_not_written 1510 10753 (by decide))
  intro s
  unfold l18enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 10753 16472 16476 16480 16484 16488
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16495 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16495 =
      denoteGraphDistributedFaithful pm initPM 10754 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1511 l18enPmMulti5R1
    10754 16495 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_pm 1512) (l18en_pm_not_written 1512 16495 (by decide))
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 10754 (by decide))
  intro s
  unfold l18enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l18en_multiref5_first_out pm s 1 10754 16495 16499 16503 16507 16511

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16499 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16499 =
      denoteGraphDistributedFaithful pm initPM 10754 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1511 l18enPmMulti5R1
    10754 16499 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_pm 1512) (l18en_pm_not_written 1512 16499 (by decide))
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 10754 (by decide))
  intro s
  unfold l18enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 10754 16495 16499 16503 16507 16511
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16503 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16503 =
      denoteGraphDistributedFaithful pm initPM 10754 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1511 l18enPmMulti5R1
    10754 16503 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_pm 1512) (l18en_pm_not_written 1512 16503 (by decide))
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 10754 (by decide))
  intro s
  unfold l18enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 10754 16495 16499 16503 16507 16511
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16507 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16507 =
      denoteGraphDistributedFaithful pm initPM 10754 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1511 l18enPmMulti5R1
    10754 16507 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_pm 1512) (l18en_pm_not_written 1512 16507 (by decide))
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 10754 (by decide))
  intro s
  unfold l18enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 10754 16495 16499 16503 16507 16511
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18en_red_pm16511 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16511 =
      denoteGraphDistributedFaithful pm initPM 10754 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1511 l18enPmMulti5R1
    10754 16511 (fun x => x)
    (by native_decide) l18en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18en_nonempty_pm 1512) (l18en_pm_not_written 1512 16511 (by decide))
    (l18en_nonempty_pm 1511) (l18en_pm_not_written 1511 10754 (by decide))
  intro s
  unfold l18enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 10754 16495 16499 16503 16507 16511
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5642 (`FW_reshape` of 5641).
theorem recon_zigzagGoal_5642_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5642)
      (denoteGraphDistributedFaithful pm initPM 10721)
      (denoteGraphDistributedFaithful pm initPM 10722)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5641_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm5642 initSM, l18en_red_pm10721 initPM, l18en_red_pm10722 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5643 (`FW_reshape` of 5642).
theorem recon_zigzagGoal_5643_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5643)
      (denoteGraphDistributedFaithful pm initPM 10727)
      (denoteGraphDistributedFaithful pm initPM 10728)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5642_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm5643 initSM, l18en_red_pm10727 initPM, l18en_red_pm10728 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5645 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5645_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5645)
      (denoteGraphDistributedFaithful pm initPM 10731)
      (denoteGraphDistributedFaithful pm initPM 10732)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5643_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5644 = initPM 5644 :=
    recon_weight initSM initPM hInit initGoal_5644 (by native_decide) 5644
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5644 = initSM 5644 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5644
      layer1_sm_nodes_nonempty (fun n hn => (l18en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5644 = initPM 5644 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5644
      layer1_pm_nodes_nonempty (fun n hn => (l18en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5644 =
      denoteGraphDistributedFaithful pm initPM 5644 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5644).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5644 [1024, 1024] (by native_decide)
  rw [l18en_red_sm5645 initSM, l18en_red_pm10731 initPM, l18en_red_pm10732 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5646 (`FW_view` of 5645).
theorem recon_zigzagGoal_5646_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5646)
      (denoteGraphDistributedFaithful pm initPM 10741)
      (denoteGraphDistributedFaithful pm initPM 10742)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5645_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm5646 initSM, l18en_red_pm10741 initPM, l18en_red_pm10742 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5647 (`FW_float` of 5646).
theorem recon_zigzagGoal_5647_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5647)
      (denoteGraphDistributedFaithful pm initPM 10745)
      (denoteGraphDistributedFaithful pm initPM 10746)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5646_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm5647 initSM, l18en_red_pm10745 initPM, l18en_red_pm10746 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5648 (residual `FW_add` of the
-- cross-layer bypass 8377 and 5647).
theorem recon_zigzagGoal_5648_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5648)
      (denoteGraphDistributedFaithful pm initPM 10749)
      (denoteGraphDistributedFaithful pm initPM 10750)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8377_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5647_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5590_5639 : denoteGraphDistributedFaithful pm initPM 5590 =
      denoteGraphDistributedFaithful pm initPM 5639 := by
    rw [pmFinal 5590 (fun n hn => (l18en_cu_not_written n hn).1),
      pmFinal 5639 (fun n hn => (l18en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5590_5639] at hA
  rw [l18en_red_sm5648 initSM, l18en_red_pm10749 initPM, l18en_red_pm10750 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8381 (2-way multiref, position 0).
theorem recon_zigzagGoal_8381_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8381)
      (denoteGraphDistributedFaithful pm initPM 16453)
      (denoteGraphDistributedFaithful pm initPM 16461)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5648_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm8381 initSM, l18en_red_pm16453 initPM, l18en_red_pm16461 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8385 (2-way multiref, position 1).
theorem recon_zigzagGoal_8385_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8385)
      (denoteGraphDistributedFaithful pm initPM 16457)
      (denoteGraphDistributedFaithful pm initPM 16465)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5648_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm8385 initSM, l18en_red_pm16457 initPM, l18en_red_pm16465 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5650 (`FW_rms_norm` of 8381 with
-- the replicated weight 5649).
theorem recon_zigzagGoal_5650_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5650)
      (denoteGraphDistributedFaithful pm initPM 10753)
      (denoteGraphDistributedFaithful pm initPM 10754)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8381_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5649 = initPM 5649 :=
    recon_weight initSM initPM hInit initGoal_5649 (by native_decide) 5649
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5649 = initSM 5649 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5649
      layer1_sm_nodes_nonempty (fun n hn => (l18en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5649 = initPM 5649 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5649
      layer1_pm_nodes_nonempty (fun n hn => (l18en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5649 =
      denoteGraphDistributedFaithful pm initPM 5649 := by
    rw [hsw, hpw]; exact hwInit
  rw [l18en_red_sm5650 initSM, l18en_red_pm10753 initPM, l18en_red_pm10754 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8392 (5-way multiref, position 0).
theorem recon_zigzagGoal_8392_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8392)
      (denoteGraphDistributedFaithful pm initPM 16472)
      (denoteGraphDistributedFaithful pm initPM 16495)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5650_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm8392 initSM, l18en_red_pm16472 initPM, l18en_red_pm16495 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8396 (5-way multiref, position 1).
theorem recon_zigzagGoal_8396_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8396)
      (denoteGraphDistributedFaithful pm initPM 16476)
      (denoteGraphDistributedFaithful pm initPM 16499)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5650_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm8396 initSM, l18en_red_pm16476 initPM, l18en_red_pm16499 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8400 (5-way multiref, position 2).
theorem recon_zigzagGoal_8400_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8400)
      (denoteGraphDistributedFaithful pm initPM 16480)
      (denoteGraphDistributedFaithful pm initPM 16503)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5650_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm8400 initSM, l18en_red_pm16480 initPM, l18en_red_pm16503 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8404 (5-way multiref, position 3).
theorem recon_zigzagGoal_8404_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8404)
      (denoteGraphDistributedFaithful pm initPM 16484)
      (denoteGraphDistributedFaithful pm initPM 16507)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5650_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm8404 initSM, l18en_red_pm16484 initPM, l18en_red_pm16507 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8408 (5-way multiref, position 4).
theorem recon_zigzagGoal_8408_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8408)
      (denoteGraphDistributedFaithful pm initPM 16488)
      (denoteGraphDistributedFaithful pm initPM 16511)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5650_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18en_red_sm8408 initSM, l18en_red_pm16488 initPM, l18en_red_pm16511 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
