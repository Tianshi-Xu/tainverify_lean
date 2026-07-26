/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L20FaithfulZigzagAttention
import denote.yoco_goals.L19FaithfulBlockTail
import denote.yoco_goals.L12FaithfulRouterEntry

/-!
# Faithful zigzag relations for the block-8 entry segment

Continuation of `recon_zigzagGoal_5739_faithful` (block-8 cross-decoder
attention) through the block-8 entry segment:

* SM 786: `FW_reshape [5739] → [5740]`   (PM 1634/1635: `11063 → 11065`, `11064 → 11066`)
* SM 787: `FW_reshape [5740] → [5741]`   (PM 1636/1637: `11065 → 11071`, `11066 → 11072`)
* SM 788: `FW_mix_precision_linear [5741, 5742] → [5743]`
                                          (PM 1638/1639 with replicated weight 5742)
* SM 789: `FW_view [5743] → [5744]`      (PM 1640/1641)
* SM 790: `FW_float [5744] → [5745]`     (PM 1642/1643)
* SM 791: `FW_add [8455, 5745] → [5746]` (PM 1644/1645 with bypass 16597/16605)
* SM 792: `FW_multiref [5746] → [8459, 8463]`
                                          (PM 1646: `[16609, 16613]`, PM 1647: `[16617, 16621]`)
* SM 793: `FW_rms_norm [8459, 5747] → [5748]` (PM 1648/1649, replicated weight 5747)
* SM 794: `FW_multiref [5748] → [8470, 8474, 8478, 8482, 8486]`
                                          (PM 1650: `[16628, 16632, 16636, 16640, 16644]`,
                                           PM 1651: `[16651, 16655, 16659, 16663, 16667]`)

All relations are stated against the block-8 cumulative-sequence metadata tensor
`5737` (the same cu slot used by `recon_zigzagGoal_5739_faithful`).
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

private theorem l20en_multiref5_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 t3 t4 t5 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2, t3, t4, t5], params := [5] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3, t4, t5].zip (List.replicate 5 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ### Node literals -/

private def l20enSmReshape5740 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5739], outs := [5740],
    params := [4096, 1024] }
private def l20enSmReshape5741 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5740], outs := [5741],
    params := [4096, 1024] }
private def l20enSmLinear5743 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5741, 5742],
    outs := [5743] }
private def l20enSmView5744 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5743], outs := [5744],
    params := [4096, 1024] }
private def l20enSmFloat5745 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5744], outs := [5745] }
private def l20enSmAdd5746 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8455, 5745], outs := [5746] }
private def l20enSmMulti2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5746], outs := [8459, 8463],
    params := [2] }
private def l20enSmRms5748 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8459, 5747], outs := [5748] }
private def l20enSmMulti5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5748],
    outs := [8470, 8474, 8478, 8482, 8486], params := [5] }

private def l20enPmReshape11065 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11063], outs := [11065],
    params := [2048, 1024] }
private def l20enPmReshape11066 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11064], outs := [11066],
    params := [2048, 1024] }
private def l20enPmReshape11071 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11065], outs := [11071],
    params := [2048, 1024] }
private def l20enPmReshape11072 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11066], outs := [11072],
    params := [2048, 1024] }
private def l20enPmLinear11075 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11071, 5742],
    outs := [11075] }
private def l20enPmLinear11076 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11072, 5742],
    outs := [11076] }
private def l20enPmView11085 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11075], outs := [11085],
    params := [2048, 1024] }
private def l20enPmView11086 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11076], outs := [11086],
    params := [2048, 1024] }
private def l20enPmFloat11089 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11085], outs := [11089] }
private def l20enPmFloat11090 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11086], outs := [11090] }
private def l20enPmAdd11093 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16597, 11089], outs := [11093] }
private def l20enPmAdd11094 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16605, 11090], outs := [11094] }
private def l20enPmMulti2R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11093], outs := [16609, 16613],
    params := [2] }
private def l20enPmMulti2R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11094], outs := [16617, 16621],
    params := [2] }
private def l20enPmRms11097 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16609, 5747], outs := [11097] }
private def l20enPmRms11098 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16617, 5747], outs := [11098] }
private def l20enPmMulti5R0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11097],
    outs := [16628, 16632, 16636, 16640, 16644], params := [5] }
private def l20enPmMulti5R1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11098],
    outs := [16651, 16655, 16659, 16663, 16667], params := [5] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l20en_sm_node_facts :
    sm.nodes[786]'(by native_decide) = l20enSmReshape5740 ∧
    sm.nodes[787]'(by native_decide) = l20enSmReshape5741 ∧
    sm.nodes[788]'(by native_decide) = l20enSmLinear5743 ∧
    sm.nodes[789]'(by native_decide) = l20enSmView5744 ∧
    sm.nodes[790]'(by native_decide) = l20enSmFloat5745 ∧
    sm.nodes[791]'(by native_decide) = l20enSmAdd5746 ∧
    sm.nodes[792]'(by native_decide) = l20enSmMulti2 ∧
    sm.nodes[793]'(by native_decide) = l20enSmRms5748 ∧
    sm.nodes[794]'(by native_decide) = l20enSmMulti5 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l20en_pm_node_facts :
    pm.nodes[1634]'(by native_decide) = l20enPmReshape11065 ∧
    pm.nodes[1635]'(by native_decide) = l20enPmReshape11066 ∧
    pm.nodes[1636]'(by native_decide) = l20enPmReshape11071 ∧
    pm.nodes[1637]'(by native_decide) = l20enPmReshape11072 ∧
    pm.nodes[1638]'(by native_decide) = l20enPmLinear11075 ∧
    pm.nodes[1639]'(by native_decide) = l20enPmLinear11076 ∧
    pm.nodes[1640]'(by native_decide) = l20enPmView11085 ∧
    pm.nodes[1641]'(by native_decide) = l20enPmView11086 ∧
    pm.nodes[1642]'(by native_decide) = l20enPmFloat11089 ∧
    pm.nodes[1643]'(by native_decide) = l20enPmFloat11090 ∧
    pm.nodes[1644]'(by native_decide) = l20enPmAdd11093 ∧
    pm.nodes[1645]'(by native_decide) = l20enPmAdd11094 ∧
    pm.nodes[1646]'(by native_decide) = l20enPmMulti2R0 ∧
    pm.nodes[1647]'(by native_decide) = l20enPmMulti2R1 ∧
    pm.nodes[1648]'(by native_decide) = l20enPmRms11097 ∧
    pm.nodes[1649]'(by native_decide) = l20enPmRms11098 ∧
    pm.nodes[1650]'(by native_decide) = l20enPmMulti5R0 ∧
    pm.nodes[1651]'(by native_decide) = l20enPmMulti5R1 := by
  native_decide

private theorem l20en_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l20en_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l20en_weights_not_written :
    (∀ n ∈ sm.nodes, 5742 ∉ n.outs ∧ 5747 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5742 ∉ n.outs ∧ 5747 ∉ n.outs) := by
  native_decide

private theorem l20en_w5742_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5742 ∉ n.outs := by
  intro n hn
  exact (l20en_weights_not_written.1 n (List.mem_of_mem_drop hn)).1

private theorem l20en_w5742_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5742 ∉ n.outs := by
  intro n hn
  exact (l20en_weights_not_written.2 n (List.mem_of_mem_drop hn)).1

private theorem l20en_w5747_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5747 ∉ n.outs := by
  intro n hn
  exact (l20en_weights_not_written.1 n (List.mem_of_mem_drop hn)).2

private theorem l20en_w5747_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5747 ∉ n.outs := by
  intro n hn
  exact (l20en_weights_not_written.2 n (List.mem_of_mem_drop hn)).2

set_option maxRecDepth 1000000 in
private theorem l20en_cu_not_written :
    ∀ n ∈ pm.nodes, 5688 ∉ n.outs ∧ 5737 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l20en_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(787, 5740), (786, 5739), (788, 5741), (789, 5743), (790, 5744), (791,
      5745), (792, 5746), (791, 8455), (793, 8459), (793, 8463), (794, 5748),
      (795, 8470), (795, 8474), (795, 8478), (795, 8482), (795, 8486)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l20en_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1635, 11065), (1634, 11063), (1636, 11066), (1635, 11064), (1637, 11071),
      (1636, 11065), (1638, 11072), (1637, 11066), (1639, 11075), (1638, 11071),
      (1640, 11076), (1639, 11072), (1641, 11085), (1640, 11075), (1642, 11086),
      (1641, 11076), (1643, 11089), (1642, 11085), (1644, 11090), (1643, 11086),
      (1645, 11093), (1644, 16597), (1644, 11089), (1646, 11094), (1645, 16605),
      (1645, 11090), (1647, 16609), (1647, 16613), (1646, 11093), (1648, 16617),
      (1648, 16621), (1647, 11094), (1649, 11097), (1648, 16609), (1650, 11098),
      (1649, 16617), (1651, 16628), (1651, 16632), (1651, 16636), (1651, 16640),
      (1651, 16644), (1650, 11097), (1652, 16651), (1652, 16655), (1652, 16659),
      (1652, 16663), (1652, 16667), (1651, 11098)]) :
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
private theorem l20en_red_sm5740 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5740 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5739) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 786 l20enSmReshape5740
    5739 5740 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l20en_sm_node_facts.1 ?_
    (l20en_nonempty_sm 787) (l20en_sm_not_written 787 5740 (by decide))
    (l20en_nonempty_sm 786) (l20en_sm_not_written 786 5739 (by decide))
  intro s
  unfold l20enSmReshape5740
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5739 5740 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11065 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11065 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11063) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1634 l20enPmReshape11065
    11063 11065 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l20en_pm_node_facts.1 ?_
    (l20en_nonempty_pm 1635) (l20en_pm_not_written 1635 11065 (by decide))
    (l20en_nonempty_pm 1634) (l20en_pm_not_written 1634 11063 (by decide))
  intro s
  unfold l20enPmReshape11065
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11063 11065 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11066 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11066 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11064) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1635 l20enPmReshape11066
    11064 11066 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l20en_pm_node_facts.2.1 ?_
    (l20en_nonempty_pm 1636) (l20en_pm_not_written 1636 11066 (by decide))
    (l20en_nonempty_pm 1635) (l20en_pm_not_written 1635 11064 (by decide))
  intro s
  unfold l20enPmReshape11066
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11064 11066 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm5741 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5741 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5740) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 787 l20enSmReshape5741
    5740 5741 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l20en_sm_node_facts.2.1 ?_
    (l20en_nonempty_sm 788) (l20en_sm_not_written 788 5741 (by decide))
    (l20en_nonempty_sm 787) (l20en_sm_not_written 787 5740 (by decide))
  intro s
  unfold l20enSmReshape5741
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5740 5741 [4096, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11071 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11071 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11065) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1636 l20enPmReshape11071
    11065 11071 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l20en_pm_node_facts.2.2.1 ?_
    (l20en_nonempty_pm 1637) (l20en_pm_not_written 1637 11071 (by decide))
    (l20en_nonempty_pm 1636) (l20en_pm_not_written 1636 11065 (by decide))
  intro s
  unfold l20enPmReshape11071
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11065 11071 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11072 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11072 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11066) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1637 l20enPmReshape11072
    11066 11072 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l20en_pm_node_facts.2.2.2.1 ?_
    (l20en_nonempty_pm 1638) (l20en_pm_not_written 1638 11072 (by decide))
    (l20en_nonempty_pm 1637) (l20en_pm_not_written 1637 11066 (by decide))
  intro s
  unfold l20enPmReshape11072
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11066 11072 [2048, 1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm5743 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5743 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5741)
        (denoteGraphDistributedFaithful sm initSM 5742) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 788 l20enSmLinear5743
    5741 5742 5743 fw_linear
    (by native_decide) l20en_sm_node_facts.2.2.1 ?_
    (l20en_nonempty_sm 789) (l20en_sm_not_written 789 5743 (by decide))
    (l20en_nonempty_sm 788) (l20en_sm_not_written 788 5741 (by decide))
    (l20en_w5742_sm_drop 788)
  intro s
  unfold l20enSmLinear5743
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5741 5742 5743

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11075 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11075 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11071)
        (denoteGraphDistributedFaithful pm initPM 5742) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1638 l20enPmLinear11075
    11071 5742 11075 fw_linear
    (by native_decide) l20en_pm_node_facts.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1639) (l20en_pm_not_written 1639 11075 (by decide))
    (l20en_nonempty_pm 1638) (l20en_pm_not_written 1638 11071 (by decide))
    (l20en_w5742_pm_drop 1638)
  intro s
  unfold l20enPmLinear11075
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11071 5742 11075

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11076 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11076 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11072)
        (denoteGraphDistributedFaithful pm initPM 5742) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1639 l20enPmLinear11076
    11072 5742 11076 fw_linear
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1640) (l20en_pm_not_written 1640 11076 (by decide))
    (l20en_nonempty_pm 1639) (l20en_pm_not_written 1639 11072 (by decide))
    (l20en_w5742_pm_drop 1639)
  intro s
  unfold l20enPmLinear11076
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11072 5742 11076

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm5744 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5744 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5743) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 789 l20enSmView5744
    5743 5744 (fun x => fw_view [4096, 1024] x)
    (by native_decide) l20en_sm_node_facts.2.2.2.1 ?_
    (l20en_nonempty_sm 790) (l20en_sm_not_written 790 5744 (by decide))
    (l20en_nonempty_sm 789) (l20en_sm_not_written 789 5743 (by decide))
  intro s
  unfold l20enSmView5744
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5743 5744

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11085 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11085 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11075) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1640 l20enPmView11085
    11075 11085 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1641) (l20en_pm_not_written 1641 11085 (by decide))
    (l20en_nonempty_pm 1640) (l20en_pm_not_written 1640 11075 (by decide))
  intro s
  unfold l20enPmView11085
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11075 11085

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11086 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11086 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 11076) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1641 l20enPmView11086
    11076 11086 (fun x => fw_view [2048, 1024] x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1642) (l20en_pm_not_written 1642 11086 (by decide))
    (l20en_nonempty_pm 1641) (l20en_pm_not_written 1641 11076 (by decide))
  intro s
  unfold l20enPmView11086
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11076 11086

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm5745 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5745 =
      denoteGraphDistributedFaithful sm initSM 5744 := by
  have h := denoteGraphDistributedFaithful_reduce1 sm initSM 790 l20enSmFloat5745
    5744 5745 id
    (by native_decide) l20en_sm_node_facts.2.2.2.2.1 ?_
    (l20en_nonempty_sm 791) (l20en_sm_not_written 791 5745 (by decide))
    (l20en_nonempty_sm 790) (l20en_sm_not_written 790 5744 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l20enSmFloat5745
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out sm s 0 5744 5745 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11089 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11089 =
      denoteGraphDistributedFaithful pm initPM 11085 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1642 l20enPmFloat11089
    11085 11089 id
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1643) (l20en_pm_not_written 1643 11089 (by decide))
    (l20en_nonempty_pm 1642) (l20en_pm_not_written 1642 11085 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l20enPmFloat11089
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 0 11085 11089 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11090 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11090 =
      denoteGraphDistributedFaithful pm initPM 11086 := by
  have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1643 l20enPmFloat11090
    11086 11090 id
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1644) (l20en_pm_not_written 1644 11090 (by decide))
    (l20en_nonempty_pm 1643) (l20en_pm_not_written 1643 11086 (by decide))
  · simpa only [id_eq] using h
  · intro s
    unfold l20enPmFloat11090
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_float_out pm s 1 11086 11090 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm5746 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5746 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8455)
        (denoteGraphDistributedFaithful sm initSM 5745) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 791 l20enSmAdd5746
    8455 5745 5746 elemwiseAdd
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.1 ?_
    (l20en_nonempty_sm 792) (l20en_sm_not_written 792 5746 (by decide))
    (l20en_nonempty_sm 791) (l20en_sm_not_written 791 8455 (by decide))
    (l20en_sm_not_written 791 5745 (by decide))
  intro s
  unfold l20enSmAdd5746
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8455 5745 5746

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11093 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11093 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16597)
        (denoteGraphDistributedFaithful pm initPM 11089) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1644 l20enPmAdd11093
    16597 11089 11093 elemwiseAdd
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1645) (l20en_pm_not_written 1645 11093 (by decide))
    (l20en_nonempty_pm 1644) (l20en_pm_not_written 1644 16597 (by decide))
    (l20en_pm_not_written 1644 11089 (by decide))
  intro s
  unfold l20enPmAdd11093
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16597 11089 11093

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11094 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11094 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16605)
        (denoteGraphDistributedFaithful pm initPM 11090) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1645 l20enPmAdd11094
    16605 11090 11094 elemwiseAdd
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1646) (l20en_pm_not_written 1646 11094 (by decide))
    (l20en_nonempty_pm 1645) (l20en_pm_not_written 1645 16605 (by decide))
    (l20en_pm_not_written 1645 11090 (by decide))
  intro s
  unfold l20enPmAdd11094
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16605 11090 11094

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm8459 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8459 =
      denoteGraphDistributedFaithful sm initSM 5746 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 792 l20enSmMulti2
    5746 8459 (fun x => x)
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_sm 793) (l20en_sm_not_written 793 8459 (by decide))
    (l20en_nonempty_sm 792) (l20en_sm_not_written 792 5746 (by decide))
  intro s
  unfold l20enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5746 8459 8463

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm8463 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8463 =
      denoteGraphDistributedFaithful sm initSM 5746 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 792 l20enSmMulti2
    5746 8463 (fun x => x)
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_sm 793) (l20en_sm_not_written 793 8463 (by decide))
    (l20en_nonempty_sm 792) (l20en_sm_not_written 792 5746 (by decide))
  intro s
  unfold l20enSmMulti2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5746 8459 8463 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16609 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16609 =
      denoteGraphDistributedFaithful pm initPM 11093 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1646 l20enPmMulti2R0
    11093 16609 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1647) (l20en_pm_not_written 1647 16609 (by decide))
    (l20en_nonempty_pm 1646) (l20en_pm_not_written 1646 11093 (by decide))
  intro s
  unfold l20enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11093 16609 16613

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16613 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16613 =
      denoteGraphDistributedFaithful pm initPM 11093 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1646 l20enPmMulti2R0
    11093 16613 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1647) (l20en_pm_not_written 1647 16613 (by decide))
    (l20en_nonempty_pm 1646) (l20en_pm_not_written 1646 11093 (by decide))
  intro s
  unfold l20enPmMulti2R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11093 16609 16613 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16617 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16617 =
      denoteGraphDistributedFaithful pm initPM 11094 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1647 l20enPmMulti2R1
    11094 16617 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1648) (l20en_pm_not_written 1648 16617 (by decide))
    (l20en_nonempty_pm 1647) (l20en_pm_not_written 1647 11094 (by decide))
  intro s
  unfold l20enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11094 16617 16621

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16621 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16621 =
      denoteGraphDistributedFaithful pm initPM 11094 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1647 l20enPmMulti2R1
    11094 16621 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1648) (l20en_pm_not_written 1648 16621 (by decide))
    (l20en_nonempty_pm 1647) (l20en_pm_not_written 1647 11094 (by decide))
  intro s
  unfold l20enPmMulti2R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11094 16617 16621 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm5748 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5748 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8459)
        (denoteGraphDistributedFaithful sm initSM 5747) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 793 l20enSmRms5748
    8459 5747 5748 fw_rms_norm
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_sm 794) (l20en_sm_not_written 794 5748 (by decide))
    (l20en_nonempty_sm 793) (l20en_sm_not_written 793 8459 (by decide))
    (l20en_w5747_sm_drop 793)
  intro s
  unfold l20enSmRms5748
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8459 5747 5748

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11097 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11097 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16609)
        (denoteGraphDistributedFaithful pm initPM 5747) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1648 l20enPmRms11097
    16609 5747 11097 fw_rms_norm
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1649) (l20en_pm_not_written 1649 11097 (by decide))
    (l20en_nonempty_pm 1648) (l20en_pm_not_written 1648 16609 (by decide))
    (l20en_w5747_pm_drop 1648)
  intro s
  unfold l20enPmRms11097
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16609 5747 11097

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm11098 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11098 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16617)
        (denoteGraphDistributedFaithful pm initPM 5747) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1649 l20enPmRms11098
    16617 5747 11098 fw_rms_norm
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1650) (l20en_pm_not_written 1650 11098 (by decide))
    (l20en_nonempty_pm 1649) (l20en_pm_not_written 1649 16617 (by decide))
    (l20en_w5747_pm_drop 1649)
  intro s
  unfold l20enPmRms11098
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16617 5747 11098

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm8470 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8470 =
      denoteGraphDistributedFaithful sm initSM 5748 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 794 l20enSmMulti5
    5748 8470 (fun x => x)
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_sm 795) (l20en_sm_not_written 795 8470 (by decide))
    (l20en_nonempty_sm 794) (l20en_sm_not_written 794 5748 (by decide))
  intro s
  unfold l20enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l20en_multiref5_first_out sm s 0 5748 8470 8474 8478 8482 8486

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm8474 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8474 =
      denoteGraphDistributedFaithful sm initSM 5748 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 794 l20enSmMulti5
    5748 8474 (fun x => x)
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_sm 795) (l20en_sm_not_written 795 8474 (by decide))
    (l20en_nonempty_sm 794) (l20en_sm_not_written 794 5748 (by decide))
  intro s
  unfold l20enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out sm s 0 5748 8470 8474 8478 8482 8486
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm8478 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8478 =
      denoteGraphDistributedFaithful sm initSM 5748 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 794 l20enSmMulti5
    5748 8478 (fun x => x)
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_sm 795) (l20en_sm_not_written 795 8478 (by decide))
    (l20en_nonempty_sm 794) (l20en_sm_not_written 794 5748 (by decide))
  intro s
  unfold l20enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out sm s 0 5748 8470 8474 8478 8482 8486
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm8482 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8482 =
      denoteGraphDistributedFaithful sm initSM 5748 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 794 l20enSmMulti5
    5748 8482 (fun x => x)
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_sm 795) (l20en_sm_not_written 795 8482 (by decide))
    (l20en_nonempty_sm 794) (l20en_sm_not_written 794 5748 (by decide))
  intro s
  unfold l20enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out sm s 0 5748 8470 8474 8478 8482 8486
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_sm8486 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8486 =
      denoteGraphDistributedFaithful sm initSM 5748 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 794 l20enSmMulti5
    5748 8486 (fun x => x)
    (by native_decide) l20en_sm_node_facts.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_sm 795) (l20en_sm_not_written 795 8486 (by decide))
    (l20en_nonempty_sm 794) (l20en_sm_not_written 794 5748 (by decide))
  intro s
  unfold l20enSmMulti5
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out sm s 0 5748 8470 8474 8478 8482 8486
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16628 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16628 =
      denoteGraphDistributedFaithful pm initPM 11097 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1650 l20enPmMulti5R0
    11097 16628 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 16628 (by decide))
    (l20en_nonempty_pm 1650) (l20en_pm_not_written 1650 11097 (by decide))
  intro s
  unfold l20enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l20en_multiref5_first_out pm s 0 11097 16628 16632 16636 16640 16644

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16632 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16632 =
      denoteGraphDistributedFaithful pm initPM 11097 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1650 l20enPmMulti5R0
    11097 16632 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 16632 (by decide))
    (l20en_nonempty_pm 1650) (l20en_pm_not_written 1650 11097 (by decide))
  intro s
  unfold l20enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 0 11097 16628 16632 16636 16640 16644
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16636 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16636 =
      denoteGraphDistributedFaithful pm initPM 11097 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1650 l20enPmMulti5R0
    11097 16636 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 16636 (by decide))
    (l20en_nonempty_pm 1650) (l20en_pm_not_written 1650 11097 (by decide))
  intro s
  unfold l20enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 0 11097 16628 16632 16636 16640 16644
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16640 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16640 =
      denoteGraphDistributedFaithful pm initPM 11097 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1650 l20enPmMulti5R0
    11097 16640 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 16640 (by decide))
    (l20en_nonempty_pm 1650) (l20en_pm_not_written 1650 11097 (by decide))
  intro s
  unfold l20enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 0 11097 16628 16632 16636 16640 16644
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16644 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16644 =
      denoteGraphDistributedFaithful pm initPM 11097 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1650 l20enPmMulti5R0
    11097 16644 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 16644 (by decide))
    (l20en_nonempty_pm 1650) (l20en_pm_not_written 1650 11097 (by decide))
  intro s
  unfold l20enPmMulti5R0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 0 11097 16628 16632 16636 16640 16644
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16651 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16651 =
      denoteGraphDistributedFaithful pm initPM 11098 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1651 l20enPmMulti5R1
    11098 16651 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_pm 1652) (l20en_pm_not_written 1652 16651 (by decide))
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 11098 (by decide))
  intro s
  unfold l20enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact l20en_multiref5_first_out pm s 1 11098 16651 16655 16659 16663 16667

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16655 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16655 =
      denoteGraphDistributedFaithful pm initPM 11098 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1651 l20enPmMulti5R1
    11098 16655 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_pm 1652) (l20en_pm_not_written 1652 16655 (by decide))
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 11098 (by decide))
  intro s
  unfold l20enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos1_out pm s 1 11098 16651 16655 16659 16663 16667
    (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16659 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16659 =
      denoteGraphDistributedFaithful pm initPM 11098 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1651 l20enPmMulti5R1
    11098 16659 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_pm 1652) (l20en_pm_not_written 1652 16659 (by decide))
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 11098 (by decide))
  intro s
  unfold l20enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos2_out pm s 1 11098 16651 16655 16659 16663 16667
    (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16663 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16663 =
      denoteGraphDistributedFaithful pm initPM 11098 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1651 l20enPmMulti5R1
    11098 16663 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_pm 1652) (l20en_pm_not_written 1652 16663 (by decide))
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 11098 (by decide))
  intro s
  unfold l20enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos3_out pm s 1 11098 16651 16655 16659 16663 16667
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20en_red_pm16667 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16667 =
      denoteGraphDistributedFaithful pm initPM 11098 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1651 l20enPmMulti5R1
    11098 16667 (fun x => x)
    (by native_decide) l20en_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20en_nonempty_pm 1652) (l20en_pm_not_written 1652 16667 (by decide))
    (l20en_nonempty_pm 1651) (l20en_pm_not_written 1651 11098 (by decide))
  intro s
  unfold l20enPmMulti5R1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref5_at_pos4_out pm s 1 11098 16651 16655 16659 16663 16667
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5740 (`FW_reshape` of 5739).
theorem recon_zigzagGoal_5740_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5740)
      (denoteGraphDistributedFaithful pm initPM 11065)
      (denoteGraphDistributedFaithful pm initPM 11066)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5739_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm5740 initSM, l20en_red_pm11065 initPM, l20en_red_pm11066 initPM]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5741 (`FW_reshape` of 5740).
theorem recon_zigzagGoal_5741_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5741)
      (denoteGraphDistributedFaithful pm initPM 11071)
      (denoteGraphDistributedFaithful pm initPM 11072)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5740_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm5741 initSM, l20en_red_pm11071 initPM, l20en_red_pm11072 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5743 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5743_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5743)
      (denoteGraphDistributedFaithful pm initPM 11075)
      (denoteGraphDistributedFaithful pm initPM 11076)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5741_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5742 = initPM 5742 :=
    recon_weight initSM initPM hInit initGoal_5742 (by native_decide) 5742
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5742 = initSM 5742 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5742
      layer1_sm_nodes_nonempty (fun n hn => (l20en_weights_not_written.1 n hn).1)
  have hpw : denoteGraphDistributedFaithful pm initPM 5742 = initPM 5742 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5742
      layer1_pm_nodes_nonempty (fun n hn => (l20en_weights_not_written.2 n hn).1)
  have hw : denoteGraphDistributedFaithful sm initSM 5742 =
      denoteGraphDistributedFaithful pm initPM 5742 := by
    rw [hsw, hpw]; exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5742).shape =
      [1024, 1024] := by
    rw [hpw]
    exact hPM 5742 [1024, 1024] (by native_decide)
  rw [l20en_red_sm5743 initSM, l20en_red_pm11075 initPM, l20en_red_pm11076 initPM, hw]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5744 (`FW_view` of 5743).
theorem recon_zigzagGoal_5744_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5744)
      (denoteGraphDistributedFaithful pm initPM 11085)
      (denoteGraphDistributedFaithful pm initPM 11086)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5743_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm5744 initSM, l20en_red_pm11085 initPM, l20en_red_pm11086 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5745 (`FW_float` of 5744).
theorem recon_zigzagGoal_5745_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5745)
      (denoteGraphDistributedFaithful pm initPM 11089)
      (denoteGraphDistributedFaithful pm initPM 11090)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5744_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm5745 initSM, l20en_red_pm11089 initPM, l20en_red_pm11090 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5746 (residual `FW_add` of the
-- cross-layer bypass 8455 and 5745).
theorem recon_zigzagGoal_5746_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5746)
      (denoteGraphDistributedFaithful pm initPM 11093)
      (denoteGraphDistributedFaithful pm initPM 11094)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8455_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5745_faithful initSM initPM hSM hPM hInit hValues hCu
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have h5688_5737 : denoteGraphDistributedFaithful pm initPM 5688 =
      denoteGraphDistributedFaithful pm initPM 5737 := by
    rw [pmFinal 5688 (fun n hn => (l20en_cu_not_written n hn).1),
      pmFinal 5737 (fun n hn => (l20en_cu_not_written n hn).2)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  rw [h5688_5737] at hA
  rw [l20en_red_sm5746 initSM, l20en_red_pm11093 initPM, l20en_red_pm11094 initPM]
  exact Zigzag2Rel.add 2048 1024 hA hB (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8459 (2-way multiref, position 0).
theorem recon_zigzagGoal_8459_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8459)
      (denoteGraphDistributedFaithful pm initPM 16609)
      (denoteGraphDistributedFaithful pm initPM 16617)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5746_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm8459 initSM, l20en_red_pm16609 initPM, l20en_red_pm16617 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8463 (2-way multiref, position 1).
theorem recon_zigzagGoal_8463_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8463)
      (denoteGraphDistributedFaithful pm initPM 16613)
      (denoteGraphDistributedFaithful pm initPM 16621)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5746_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm8463 initSM, l20en_red_pm16613 initPM, l20en_red_pm16621 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5748 (`FW_rms_norm` of 8459 with
-- the replicated weight 5747).
theorem recon_zigzagGoal_5748_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5748)
      (denoteGraphDistributedFaithful pm initPM 11097)
      (denoteGraphDistributedFaithful pm initPM 11098)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8459_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwInit : initSM 5747 = initPM 5747 :=
    recon_weight initSM initPM hInit initGoal_5747 (by native_decide) 5747
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5747 = initSM 5747 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5747
      layer1_sm_nodes_nonempty (fun n hn => (l20en_weights_not_written.1 n hn).2)
  have hpw : denoteGraphDistributedFaithful pm initPM 5747 = initPM 5747 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5747
      layer1_pm_nodes_nonempty (fun n hn => (l20en_weights_not_written.2 n hn).2)
  have hw : denoteGraphDistributedFaithful sm initSM 5747 =
      denoteGraphDistributedFaithful pm initPM 5747 := by
    rw [hsw, hpw]; exact hwInit
  rw [l20en_red_sm5748 initSM, l20en_red_pm11097 initPM, l20en_red_pm11098 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8470 (5-way multiref, position 0).
theorem recon_zigzagGoal_8470_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8470)
      (denoteGraphDistributedFaithful pm initPM 16628)
      (denoteGraphDistributedFaithful pm initPM 16651)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5748_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm8470 initSM, l20en_red_pm16628 initPM, l20en_red_pm16651 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8474 (5-way multiref, position 1).
theorem recon_zigzagGoal_8474_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8474)
      (denoteGraphDistributedFaithful pm initPM 16632)
      (denoteGraphDistributedFaithful pm initPM 16655)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5748_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm8474 initSM, l20en_red_pm16632 initPM, l20en_red_pm16655 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8478 (5-way multiref, position 2).
theorem recon_zigzagGoal_8478_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8478)
      (denoteGraphDistributedFaithful pm initPM 16636)
      (denoteGraphDistributedFaithful pm initPM 16659)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5748_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm8478 initSM, l20en_red_pm16636 initPM, l20en_red_pm16659 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8482 (5-way multiref, position 3).
theorem recon_zigzagGoal_8482_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8482)
      (denoteGraphDistributedFaithful pm initPM 16640)
      (denoteGraphDistributedFaithful pm initPM 16663)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5748_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm8482 initSM, l20en_red_pm16640 initPM, l20en_red_pm16663 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8486 (5-way multiref, position 4).
theorem recon_zigzagGoal_8486_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8486)
      (denoteGraphDistributedFaithful pm initPM 16644)
      (denoteGraphDistributedFaithful pm initPM 16667)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5748_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20en_red_sm8486 initSM, l20en_red_pm16644 initPM, l20en_red_pm16667 initPM]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
