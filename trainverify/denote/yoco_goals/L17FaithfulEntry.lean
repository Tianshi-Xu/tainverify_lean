/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L17FaithfulZigzagAttention
import denote.yoco_goals.L16FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-5 entry segment

Continuation of `recon_zigzagGoal_5592_faithful` (block-5 cross-decoder
attention) through the block-5 entry segment:

* SM 681: `FW_reshape [5592] → [5593]`   (PM 1424/1425: `10547 → 10549`, `10548 → 10550`)
* SM 682: `FW_reshape [5593] → [5594]`   (PM 1426/1427: `10549 → 10555`, `10550 → 10556`)
* SM 683: `FW_mix_precision_linear [5594, 5595] → [5596]`
                                          (PM 1428/1429 with replicated weight 5595)
* SM 684: `FW_view [5596] → [5597]`      (PM 1430/1431)
* SM 685: `FW_float [5597] → [5598]`     (PM 1432/1433)
* SM 686: `FW_add [8338, 5598] → [5599]` (PM 1434/1435 with bypass 16363/16371)
* SM 687: `FW_multiref [5599] → [8342, 8346]`
                                          (PM 1436: `[16375, 16379]`, PM 1437: `[16383, 16387]`)
* SM 688: `FW_rms_norm [8342, 5600] → [5601]` (PM 1438/1439, replicated weight 5600)
* SM 689: `FW_multiref [5601] → [8353, 8357, 8361, 8365, 8369]`
                                          (PM 1440: `[16394, 16398, 16402, 16406, 16410]`,
                                           PM 1441: `[16417, 16421, 16425, 16429, 16433]`)

All relations are stated against the block-5 cumulative-sequence metadata tensor
`5590` (the same cu slot used by `recon_zigzagGoal_5592_faithful`).
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

private theorem l17en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l17enSmReshape5593 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5592], outs := [5593],
    params := [4096, 1024] }
private def l17enSmReshape5594 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5593], outs := [5594],
    params := [4096, 1024] }
private def l17enSmLinear5596 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5594, 5595],
    outs := [5596] }
private def l17enSmView5597 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5596], outs := [5597],
    params := [4096, 1024] }
private def l17enSmFloat5598 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5597], outs := [5598] }
private def l17enSmAdd5599 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8338, 5598], outs := [5599] }
private def l17enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5599], outs := [8342, 8346],
    params := [2] }
private def l17enSmRms5601 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8342, 5600], outs := [5601] }
private def l17enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5601],
    outs := [8353, 8357, 8361, 8365, 8369], params := [5] }

private def l17enPmReshape10549 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10547], outs := [10549],
    params := [2048, 1024] }
private def l17enPmReshape10550 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10548], outs := [10550],
    params := [2048, 1024] }
private def l17enPmReshape10555 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10549], outs := [10555],
    params := [2048, 1024] }
private def l17enPmReshape10556 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10550], outs := [10556],
    params := [2048, 1024] }
private def l17enPmLinear10559 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10555, 5595],
    outs := [10559] }
private def l17enPmLinear10560 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10556, 5595],
    outs := [10560] }
private def l17enPmView10569 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10559], outs := [10569],
    params := [2048, 1024] }
private def l17enPmView10570 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10560], outs := [10570],
    params := [2048, 1024] }
private def l17enPmFloat10573 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10569], outs := [10573] }
private def l17enPmFloat10574 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10570], outs := [10574] }
private def l17enPmAdd10577 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16363, 10573], outs := [10577] }
private def l17enPmAdd10578 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16371, 10574], outs := [10578] }
private def l17enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10577], outs := [16375, 16379],
    params := [2] }
private def l17enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10578], outs := [16383, 16387],
    params := [2] }
private def l17enPmRms10581 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16375, 5600], outs := [10581] }
private def l17enPmRms10582 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16383, 5600], outs := [10582] }
private def l17enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10581],
    outs := [16394, 16398, 16402, 16406, 16410], params := [5] }
private def l17enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10582],
    outs := [16417, 16421, 16425, 16429, 16433], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l17en_sm_node_facts :
    sm.nodes[681]'(by native_decide) = l17enSmReshape5593 ∧
    sm.nodes[682]'(by native_decide) = l17enSmReshape5594 ∧
    sm.nodes[683]'(by native_decide) = l17enSmLinear5596 ∧
    sm.nodes[684]'(by native_decide) = l17enSmView5597 ∧
    sm.nodes[685]'(by native_decide) = l17enSmFloat5598 ∧
    sm.nodes[686]'(by native_decide) = l17enSmAdd5599 ∧
    sm.nodes[687]'(by native_decide) = l17enSmMulti2 ∧
    sm.nodes[688]'(by native_decide) = l17enSmRms5601 ∧
    sm.nodes[689]'(by native_decide) = l17enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l17en_pm_node_facts :
    pm.nodes[1424]'(by native_decide) = l17enPmReshape10549 ∧
    pm.nodes[1425]'(by native_decide) = l17enPmReshape10550 ∧
    pm.nodes[1426]'(by native_decide) = l17enPmReshape10555 ∧
    pm.nodes[1427]'(by native_decide) = l17enPmReshape10556 ∧
    pm.nodes[1428]'(by native_decide) = l17enPmLinear10559 ∧
    pm.nodes[1429]'(by native_decide) = l17enPmLinear10560 ∧
    pm.nodes[1430]'(by native_decide) = l17enPmView10569 ∧
    pm.nodes[1431]'(by native_decide) = l17enPmView10570 ∧
    pm.nodes[1432]'(by native_decide) = l17enPmFloat10573 ∧
    pm.nodes[1433]'(by native_decide) = l17enPmFloat10574 ∧
    pm.nodes[1434]'(by native_decide) = l17enPmAdd10577 ∧
    pm.nodes[1435]'(by native_decide) = l17enPmAdd10578 ∧
    pm.nodes[1436]'(by native_decide) = l17enPmMulti2R0 ∧
    pm.nodes[1437]'(by native_decide) = l17enPmMulti2R1 ∧
    pm.nodes[1438]'(by native_decide) = l17enPmRms10581 ∧
    pm.nodes[1439]'(by native_decide) = l17enPmRms10582 ∧
    pm.nodes[1440]'(by native_decide) = l17enPmMulti5R0 ∧
    pm.nodes[1441]'(by native_decide) = l17enPmMulti5R1 := by
  native_decide

private theorem l17en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l17en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l17en_weights_not_written :
    (∀ n ∈ sm.nodes, 5595 ∉ n.outs ∧ 5600 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5595 ∉ n.outs ∧ 5600 ∉ n.outs) := by
  native_decide

private theorem l17en_w5595_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5595 ∉ n.outs := by
  intro n hn
  exact (l17en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l17en_w5595_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5595 ∉ n.outs := by
  intro n hn
  exact (l17en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l17en_w5600_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5600 ∉ n.outs := by
  intro n hn
  exact (l17en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l17en_w5600_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5600 ∉ n.outs := by
  intro n hn
  exact (l17en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l17en_cu_not_written :
    ∀ n ∈ pm.nodes, 5541 ∉ n.outs ∧ 5590 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l17en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(682, 5593), (681, 5592), (683, 5594), (684, 5596), (685, 5597), (686,
      5598), (687, 5599), (686, 8338), (688, 8342), (688, 8346), (689, 5601),
      (690, 8353), (690, 8357), (690, 8361), (690, 8365), (690, 8369)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l17en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1425, 10549), (1424, 10547), (1426, 10550), (1425, 10548), (1427, 10555),
      (1426, 10549), (1428, 10556), (1427, 10550), (1429, 10559), (1428, 10555),
      (1430, 10560), (1429, 10556), (1431, 10569), (1430, 10559), (1432, 10570),
      (1431, 10560), (1433, 10573), (1432, 10569), (1434, 10574), (1433, 10570),
      (1435, 10577), (1434, 16363), (1434, 10573), (1436, 10578), (1435, 16371),
      (1435, 10574), (1437, 16375), (1437, 16379), (1436, 10577), (1438, 16383),
      (1438, 16387), (1437, 10578), (1439, 10581), (1438, 16375), (1440, 10582),
      (1439, 16383), (1441, 16394), (1441, 16398), (1441, 16402), (1441, 16406),
      (1441, 16410), (1440, 10581), (1442, 16417), (1442, 16421), (1442, 16425),
      (1442, 16429), (1442, 16433), (1441, 10582)]) :
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
private theorem l17en_red_sm5593 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5593 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5592) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 681 l17enSmReshape5593
    5592 5593 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l17en_sm_node_facts.1 ?_
    (l17en_nonempty_sm 682) (l17en_sm_not_written 682 5593 (by decide))
    (l17en_nonempty_sm 681) (l17en_sm_not_written 681 5592 (by decide))
  intro s
  unfold l17enSmReshape5593
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5592 5593 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10549 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10549 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10547) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1424 l17enPmReshape10549
    10547 10549 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l17en_pm_node_facts.1 ?_
    (l17en_nonempty_pm 1425) (l17en_pm_not_written 1425 10549 (by decide))
    (l17en_nonempty_pm 1424) (l17en_pm_not_written 1424 10547 (by decide))
  intro s
  unfold l17enPmReshape10549
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10547 10549 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10550 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10550 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10548) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1425 l17enPmReshape10550
    10548 10550 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l17en_pm_node_facts.2.1 ?_
    (l17en_nonempty_pm 1426) (l17en_pm_not_written 1426 10550 (by decide))
    (l17en_nonempty_pm 1425) (l17en_pm_not_written 1425 10548 (by decide))
  intro s
  unfold l17enPmReshape10550
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10548 10550 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm5594 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5594 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5593) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 682 l17enSmReshape5594
    5593 5594 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l17en_sm_node_facts.2.1 ?_
    (l17en_nonempty_sm 683) (l17en_sm_not_written 683 5594 (by decide))
    (l17en_nonempty_sm 682) (l17en_sm_not_written 682 5593 (by decide))
  intro s
  unfold l17enSmReshape5594
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5593 5594 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10555 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10555 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10549) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1426 l17enPmReshape10555
    10549 10555 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l17en_pm_node_facts.2.2.1 ?_
    (l17en_nonempty_pm 1427) (l17en_pm_not_written 1427 10555 (by decide))
    (l17en_nonempty_pm 1426) (l17en_pm_not_written 1426 10549 (by decide))
  intro s
  unfold l17enPmReshape10555
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10549 10555 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10556 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10556 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10550) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1427 l17enPmReshape10556
    10550 10556 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l17en_pm_node_facts.2.2.2.1 ?_
    (l17en_nonempty_pm 1428) (l17en_pm_not_written 1428 10556 (by decide))
    (l17en_nonempty_pm 1427) (l17en_pm_not_written 1427 10550 (by decide))
  intro s
  unfold l17enPmReshape10556
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10550 10556 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm5596 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5596 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5594)
        (denoteGraphDistributedFaithful sm initSM 5595) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 683 l17enSmLinear5596
    5594 5595 5596 fw_linear
    (by native_decide) l17en_sm_node_facts.2.2.1 ?_
    (l17en_nonempty_sm 684) (l17en_sm_not_written 684 5596 (by decide))
    (l17en_nonempty_sm 683) (l17en_sm_not_written 683 5594 (by decide))
    (l17en_w5595_sm_drop 683)
  intro s
  unfold l17enSmLinear5596
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5594 5595 5596

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10559 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10559 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10555)
        (denoteGraphDistributedFaithful pm initPM 5595) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1428 l17enPmLinear10559
    10555 5595 10559 fw_linear
    (by native_decide) l17en_pm_node_facts.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1429) (l17en_pm_not_written 1429 10559 (by decide))
    (l17en_nonempty_pm 1428) (l17en_pm_not_written 1428 10555 (by decide))
    (l17en_w5595_pm_drop 1428)
  intro s
  unfold l17enPmLinear10559
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10555 5595 10559

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10560 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10560 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10556)
        (denoteGraphDistributedFaithful pm initPM 5595) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1429 l17enPmLinear10560
    10556 5595 10560 fw_linear
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1430) (l17en_pm_not_written 1430 10560 (by decide))
    (l17en_nonempty_pm 1429) (l17en_pm_not_written 1429 10556 (by decide))
    (l17en_w5595_pm_drop 1429)
  intro s
  unfold l17enPmLinear10560
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10556 5595 10560

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm5597 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5597 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5596) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 684 l17enSmView5597
    5596 5597 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l17en_sm_node_facts.2.2.2.1 ?_
    (l17en_nonempty_sm 685) (l17en_sm_not_written 685 5597 (by decide))
    (l17en_nonempty_sm 684) (l17en_sm_not_written 684 5596 (by decide))
  intro s
  unfold l17enSmView5597
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5596 5597

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10569 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10569 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10559) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1430 l17enPmView10569
    10559 10569 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1431) (l17en_pm_not_written 1431 10569 (by decide))
    (l17en_nonempty_pm 1430) (l17en_pm_not_written 1430 10559 (by decide))
  intro s
  unfold l17enPmView10569
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10559 10569

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10570 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10570 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 10560) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1431 l17enPmView10570
    10560 10570 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1432) (l17en_pm_not_written 1432 10570 (by decide))
    (l17en_nonempty_pm 1431) (l17en_pm_not_written 1431 10560 (by decide))
  intro s
  unfold l17enPmView10570
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10560 10570

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm5598 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5598 =
      denoteGraphDistributedFaithful sm initSM 5597 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 685 l17enSmFloat5598
    5597 5598 id
    (by native_decide) l17en_sm_node_facts.2.2.2.2.1 ?_
    (l17en_nonempty_sm 686) (l17en_sm_not_written 686 5598 (by decide))
    (l17en_nonempty_sm 685) (l17en_sm_not_written 685 5597 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l17enSmFloat5598
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5597 5598 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10573 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10573 =
      denoteGraphDistributedFaithful pm initPM 10569 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1432 l17enPmFloat10573
    10569 10573 id
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1433) (l17en_pm_not_written 1433 10573 (by decide))
    (l17en_nonempty_pm 1432) (l17en_pm_not_written 1432 10569 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l17enPmFloat10573
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 10569 10573 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10574 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10574 =
      denoteGraphDistributedFaithful pm initPM 10570 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1433 l17enPmFloat10574
    10570 10574 id
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1434) (l17en_pm_not_written 1434 10574 (by decide))
    (l17en_nonempty_pm 1433) (l17en_pm_not_written 1433 10570 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l17enPmFloat10574
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 10570 10574 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm5599 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5599 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8338)
        (denoteGraphDistributedFaithful sm initSM 5598) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 686 l17enSmAdd5599
    8338 5598 5599 elemwiseAdd
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.1 ?_
    (l17en_nonempty_sm 687) (l17en_sm_not_written 687 5599 (by decide))
    (l17en_nonempty_sm 686) (l17en_sm_not_written 686 8338 (by decide))
    (l17en_sm_not_written 686 5598 (by decide))
  intro s
  unfold l17enSmAdd5599
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8338 5598 5599

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10577 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10577 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16363)
        (denoteGraphDistributedFaithful pm initPM 10573) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1434 l17enPmAdd10577
    16363 10573 10577 elemwiseAdd
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1435) (l17en_pm_not_written 1435 10577 (by decide))
    (l17en_nonempty_pm 1434) (l17en_pm_not_written 1434 16363 (by decide))
    (l17en_pm_not_written 1434 10573 (by decide))
  intro s
  unfold l17enPmAdd10577
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16363 10573 10577

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10578 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10578 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16371)
        (denoteGraphDistributedFaithful pm initPM 10574) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1435 l17enPmAdd10578
    16371 10574 10578 elemwiseAdd
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1436) (l17en_pm_not_written 1436 10578 (by decide))
    (l17en_nonempty_pm 1435) (l17en_pm_not_written 1435 16371 (by decide))
    (l17en_pm_not_written 1435 10574 (by decide))
  intro s
  unfold l17enPmAdd10578
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16371 10574 10578

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm8342 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8342 =
      denoteGraphDistributedFaithful sm initSM 5599 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 687 l17enSmMulti2
    5599 8342 (fun x => x)
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_sm 688) (l17en_sm_not_written 688 8342 (by decide))
    (l17en_nonempty_sm 687) (l17en_sm_not_written 687 5599 (by decide))
  intro s
  unfold l17enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5599 8342 8346

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm8346 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8346 =
      denoteGraphDistributedFaithful sm initSM 5599 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 687 l17enSmMulti2
    5599 8346 (fun x => x)
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_sm 688) (l17en_sm_not_written 688 8346 (by decide))
    (l17en_nonempty_sm 687) (l17en_sm_not_written 687 5599 (by decide))
  intro s
  unfold l17enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5599 8342 8346 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16375 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16375 =
      denoteGraphDistributedFaithful pm initPM 10577 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1436 l17enPmMulti2R0
    10577 16375 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1437) (l17en_pm_not_written 1437 16375 (by decide))
    (l17en_nonempty_pm 1436) (l17en_pm_not_written 1436 10577 (by decide))
  intro s
  unfold l17enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10577 16375 16379

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16379 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16379 =
      denoteGraphDistributedFaithful pm initPM 10577 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1436 l17enPmMulti2R0
    10577 16379 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1437) (l17en_pm_not_written 1437 16379 (by decide))
    (l17en_nonempty_pm 1436) (l17en_pm_not_written 1436 10577 (by decide))
  intro s
  unfold l17enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10577 16375 16379 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16383 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16383 =
      denoteGraphDistributedFaithful pm initPM 10578 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1437 l17enPmMulti2R1
    10578 16383 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1438) (l17en_pm_not_written 1438 16383 (by decide))
    (l17en_nonempty_pm 1437) (l17en_pm_not_written 1437 10578 (by decide))
  intro s
  unfold l17enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10578 16383 16387

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16387 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16387 =
      denoteGraphDistributedFaithful pm initPM 10578 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1437 l17enPmMulti2R1
    10578 16387 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1438) (l17en_pm_not_written 1438 16387 (by decide))
    (l17en_nonempty_pm 1437) (l17en_pm_not_written 1437 10578 (by decide))
  intro s
  unfold l17enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10578 16383 16387 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm5601 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5601 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8342)
        (denoteGraphDistributedFaithful sm initSM 5600) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 688 l17enSmRms5601
    8342 5600 5601 fw_rms_norm
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_sm 689) (l17en_sm_not_written 689 5601 (by decide))
    (l17en_nonempty_sm 688) (l17en_sm_not_written 688 8342 (by decide))
    (l17en_w5600_sm_drop 688)
  intro s
  unfold l17enSmRms5601
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8342 5600 5601

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10581 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10581 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16375)
        (denoteGraphDistributedFaithful pm initPM 5600) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1438 l17enPmRms10581
    16375 5600 10581 fw_rms_norm
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1439) (l17en_pm_not_written 1439 10581 (by decide))
    (l17en_nonempty_pm 1438) (l17en_pm_not_written 1438 16375 (by decide))
    (l17en_w5600_pm_drop 1438)
  intro s
  unfold l17enPmRms10581
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16375 5600 10581

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm10582 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10582 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16383)
        (denoteGraphDistributedFaithful pm initPM 5600) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1439 l17enPmRms10582
    16383 5600 10582 fw_rms_norm
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1440) (l17en_pm_not_written 1440 10582 (by decide))
    (l17en_nonempty_pm 1439) (l17en_pm_not_written 1439 16383 (by decide))
    (l17en_w5600_pm_drop 1439)
  intro s
  unfold l17enPmRms10582
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16383 5600 10582

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm8353 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8353 =
      denoteGraphDistributedFaithful sm initSM 5601 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 689 l17enSmMulti5
    5601 8353 (fun x => x)
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_sm 690) (l17en_sm_not_written 690 8353 (by decide))
    (l17en_nonempty_sm 689) (l17en_sm_not_written 689 5601 (by decide))
  intro s
  unfold l17enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l17en_multiref5_first_out sm s 0 5601 8353 8357 8361 8365 8369

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm8357 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8357 =
      denoteGraphDistributedFaithful sm initSM 5601 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 689 l17enSmMulti5
    5601 8357 (fun x => x)
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_sm 690) (l17en_sm_not_written 690 8357 (by decide))
    (l17en_nonempty_sm 689) (l17en_sm_not_written 689 5601 (by decide))
  intro s
  unfold l17enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5601 8353 8357 8361 8365 8369
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm8361 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8361 =
      denoteGraphDistributedFaithful sm initSM 5601 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 689 l17enSmMulti5
    5601 8361 (fun x => x)
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_sm 690) (l17en_sm_not_written 690 8361 (by decide))
    (l17en_nonempty_sm 689) (l17en_sm_not_written 689 5601 (by decide))
  intro s
  unfold l17enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5601 8353 8357 8361 8365 8369
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm8365 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8365 =
      denoteGraphDistributedFaithful sm initSM 5601 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 689 l17enSmMulti5
    5601 8365 (fun x => x)
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_sm 690) (l17en_sm_not_written 690 8365 (by decide))
    (l17en_nonempty_sm 689) (l17en_sm_not_written 689 5601 (by decide))
  intro s
  unfold l17enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5601 8353 8357 8361 8365 8369
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_sm8369 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8369 =
      denoteGraphDistributedFaithful sm initSM 5601 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 689 l17enSmMulti5
    5601 8369 (fun x => x)
    (by native_decide) l17en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_sm 690) (l17en_sm_not_written 690 8369 (by decide))
    (l17en_nonempty_sm 689) (l17en_sm_not_written 689 5601 (by decide))
  intro s
  unfold l17enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5601 8353 8357 8361 8365 8369
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16394 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16394 =
      denoteGraphDistributedFaithful pm initPM 10581 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1440 l17enPmMulti5R0
    10581 16394 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 16394 (by decide))
    (l17en_nonempty_pm 1440) (l17en_pm_not_written 1440 10581 (by decide))
  intro s
  unfold l17enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l17en_multiref5_first_out pm s 0 10581 16394 16398 16402 16406 16410

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16398 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16398 =
      denoteGraphDistributedFaithful pm initPM 10581 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1440 l17enPmMulti5R0
    10581 16398 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 16398 (by decide))
    (l17en_nonempty_pm 1440) (l17en_pm_not_written 1440 10581 (by decide))
  intro s
  unfold l17enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 10581 16394 16398 16402 16406 16410
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16402 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16402 =
      denoteGraphDistributedFaithful pm initPM 10581 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1440 l17enPmMulti5R0
    10581 16402 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 16402 (by decide))
    (l17en_nonempty_pm 1440) (l17en_pm_not_written 1440 10581 (by decide))
  intro s
  unfold l17enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 10581 16394 16398 16402 16406 16410
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16406 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16406 =
      denoteGraphDistributedFaithful pm initPM 10581 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1440 l17enPmMulti5R0
    10581 16406 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 16406 (by decide))
    (l17en_nonempty_pm 1440) (l17en_pm_not_written 1440 10581 (by decide))
  intro s
  unfold l17enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 10581 16394 16398 16402 16406 16410
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16410 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16410 =
      denoteGraphDistributedFaithful pm initPM 10581 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1440 l17enPmMulti5R0
    10581 16410 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 16410 (by decide))
    (l17en_nonempty_pm 1440) (l17en_pm_not_written 1440 10581 (by decide))
  intro s
  unfold l17enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 10581 16394 16398 16402 16406 16410
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16417 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16417 =
      denoteGraphDistributedFaithful pm initPM 10582 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1441 l17enPmMulti5R1
    10582 16417 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_pm 1442) (l17en_pm_not_written 1442 16417 (by decide))
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 10582 (by decide))
  intro s
  unfold l17enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l17en_multiref5_first_out pm s 1 10582 16417 16421 16425 16429 16433

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16421 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16421 =
      denoteGraphDistributedFaithful pm initPM 10582 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1441 l17enPmMulti5R1
    10582 16421 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_pm 1442) (l17en_pm_not_written 1442 16421 (by decide))
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 10582 (by decide))
  intro s
  unfold l17enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 10582 16417 16421 16425 16429 16433
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16425 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16425 =
      denoteGraphDistributedFaithful pm initPM 10582 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1441 l17enPmMulti5R1
    10582 16425 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_pm 1442) (l17en_pm_not_written 1442 16425 (by decide))
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 10582 (by decide))
  intro s
  unfold l17enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 10582 16417 16421 16425 16429 16433
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16429 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16429 =
      denoteGraphDistributedFaithful pm initPM 10582 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1441 l17enPmMulti5R1
    10582 16429 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_pm 1442) (l17en_pm_not_written 1442 16429 (by decide))
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 10582 (by decide))
  intro s
  unfold l17enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 10582 16417 16421 16425 16429 16433
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17en_red_pm16433 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16433 =
      denoteGraphDistributedFaithful pm initPM 10582 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1441 l17enPmMulti5R1
    10582 16433 (fun x => x)
    (by native_decide) l17en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17en_nonempty_pm 1442) (l17en_pm_not_written 1442 16433 (by decide))
    (l17en_nonempty_pm 1441) (l17en_pm_not_written 1441 10582 (by decide))
  intro s
  unfold l17enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 10582 16417 16421 16425 16429 16433
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5593 (`FW_reshape` of 5592).
theorem recon_zigzagGoal_5593_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5593)
      (denoteGraphDistributedFaithful pm initPM 10549)
      (denoteGraphDistributedFaithful pm initPM 10550)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5592_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm5593 initSM, l17en_red_pm10549 initPM, l17en_red_pm10550 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5594 (`FW_reshape` of 5593).
theorem recon_zigzagGoal_5594_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5594)
      (denoteGraphDistributedFaithful pm initPM 10555)
      (denoteGraphDistributedFaithful pm initPM 10556)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5593_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm5594 initSM, l17en_red_pm10555 initPM, l17en_red_pm10556 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5596 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5596_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5596)
      (denoteGraphDistributedFaithful pm initPM 10559)
      (denoteGraphDistributedFaithful pm initPM 10560)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5594_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5595 = initPM 5595 :=
    recon_weight initSM initPM hInit initGoal_5595 (by native_decide) 5595
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5595 = initSM 5595 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5595
      layer1_sm_nodes_nonempty (fun n hn => (l17en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5595 = initPM 5595 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5595
      layer1_pm_nodes_nonempty (fun n hn => (l17en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5595 =
      denoteGraphDistributedFaithful pm initPM 5595 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5595).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5595 [1024, 1024] (by native_decide)
  rw [l17en_red_sm5596 initSM, l17en_red_pm10559 initPM, l17en_red_pm10560 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5597 (`FW_view` of 5596).
theorem recon_zigzagGoal_5597_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5597)
      (denoteGraphDistributedFaithful pm initPM 10569)
      (denoteGraphDistributedFaithful pm initPM 10570)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5596_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm5597 initSM, l17en_red_pm10569 initPM, l17en_red_pm10570 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5598 (`FW_float` of 5597).
theorem recon_zigzagGoal_5598_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5598)
      (denoteGraphDistributedFaithful pm initPM 10573)
      (denoteGraphDistributedFaithful pm initPM 10574)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5597_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm5598 initSM, l17en_red_pm10573 initPM, l17en_red_pm10574 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5599 (residual `FW_add` of the
-- cross-layer bypass 8338 and 5598).
theorem recon_zigzagGoal_5599_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5599)
      (denoteGraphDistributedFaithful pm initPM 10577)
      (denoteGraphDistributedFaithful pm initPM 10578)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8338_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5598_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5541_5590 : denoteGraphDistributedFaithful pm initPM 5541 =
      denoteGraphDistributedFaithful pm initPM 5590 := by
    rw [pmFinal 5541 (fun n hn => (l17en_cu_not_written n hn).1),
      pmFinal 5590 (fun n hn => (l17en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5541_5590] at hA
  rw [l17en_red_sm5599 initSM, l17en_red_pm10577 initPM, l17en_red_pm10578 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8342 (2-way multiref, position 0).
theorem recon_zigzagGoal_8342_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8342)
      (denoteGraphDistributedFaithful pm initPM 16375)
      (denoteGraphDistributedFaithful pm initPM 16383)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5599_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm8342 initSM, l17en_red_pm16375 initPM, l17en_red_pm16383 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8346 (2-way multiref, position 1).
theorem recon_zigzagGoal_8346_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8346)
      (denoteGraphDistributedFaithful pm initPM 16379)
      (denoteGraphDistributedFaithful pm initPM 16387)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5599_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm8346 initSM, l17en_red_pm16379 initPM, l17en_red_pm16387 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5601 (`FW_rms_norm` of 8342 with
-- the replicated weight 5600).
theorem recon_zigzagGoal_5601_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5601)
      (denoteGraphDistributedFaithful pm initPM 10581)
      (denoteGraphDistributedFaithful pm initPM 10582)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8342_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5600 = initPM 5600 :=
    recon_weight initSM initPM hInit initGoal_5600 (by native_decide) 5600
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5600 = initSM 5600 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5600
      layer1_sm_nodes_nonempty (fun n hn => (l17en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5600 = initPM 5600 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5600
      layer1_pm_nodes_nonempty (fun n hn => (l17en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5600 =
      denoteGraphDistributedFaithful pm initPM 5600 := by
    rw [hsw, hpw]; exact hwInit
  rw [l17en_red_sm5601 initSM, l17en_red_pm10581 initPM, l17en_red_pm10582 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8353 (5-way multiref, position 0).
theorem recon_zigzagGoal_8353_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8353)
      (denoteGraphDistributedFaithful pm initPM 16394)
      (denoteGraphDistributedFaithful pm initPM 16417)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5601_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm8353 initSM, l17en_red_pm16394 initPM, l17en_red_pm16417 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8357 (5-way multiref, position 1).
theorem recon_zigzagGoal_8357_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8357)
      (denoteGraphDistributedFaithful pm initPM 16398)
      (denoteGraphDistributedFaithful pm initPM 16421)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5601_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm8357 initSM, l17en_red_pm16398 initPM, l17en_red_pm16421 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8361 (5-way multiref, position 2).
theorem recon_zigzagGoal_8361_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8361)
      (denoteGraphDistributedFaithful pm initPM 16402)
      (denoteGraphDistributedFaithful pm initPM 16425)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5601_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm8361 initSM, l17en_red_pm16402 initPM, l17en_red_pm16425 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8365 (5-way multiref, position 3).
theorem recon_zigzagGoal_8365_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8365)
      (denoteGraphDistributedFaithful pm initPM 16406)
      (denoteGraphDistributedFaithful pm initPM 16429)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5601_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm8365 initSM, l17en_red_pm16406 initPM, l17en_red_pm16429 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8369 (5-way multiref, position 4).
theorem recon_zigzagGoal_8369_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8369)
      (denoteGraphDistributedFaithful pm initPM 16410)
      (denoteGraphDistributedFaithful pm initPM 16433)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5601_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17en_red_sm8369 initSM, l17en_red_pm16410 initPM, l17en_red_pm16433 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
