/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L12FaithfulMoEExpert

/-!
# Faithful zigzag relations for the block-0 tail (MoE join → next-block Q)

* SM 534 `FW_add [5365, 5384] → [5385]`                       (PM 1130 / 1131 → 9819 / 9820)
* SM 535 `FW_float [5385] → [5386]`                           (PM 1132 / 1133 → 9825 / 9826)
* SM 536 `FW_add [8151, 5386] → [5387]`                       (PM 1134 / 1135 → 9829 / 9830)
* SM 537 `FW_multiref [5387] → [8178, 8182]` params `[2]`     (PM 1136 → 16047 / 16051,
                                                               PM 1137 → 16055 / 16059)
* SM 538 `FW_rms_norm [8178, 5388] → [5389]`                  (PM 1138 / 1139 → 9833 / 9834)
* SM 539 `FW_per_head_mix_precision_linear [5389, 5390] → [5391]`
                                                              (PM 1140 / 1141 → 9835 / 9836)

`5388 : [1024]` and `5390 : [16, 64, 1024]` are replicated singleton weights
(`initGoal_5388.tps = [{rank := 0, tid := 5388}]`, likewise `5390`), so they are
shared verbatim between SM and PM.

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8182_faithful` — the cross-layer residual bypass, consumed by
  SM node 546 `FW_add [8182, 5402]`;
* `recon_zigzagGoal_5391_faithful` — the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding the next block's attention entry.

Every theorem below takes literally the same five parameters as its parents; no new
hypotheses are introduced.
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

private def l12btSmAdd5385 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5365, 5384], outs := [5385] }
private def l12btSmFloat5386 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5385], outs := [5386] }
private def l12btSmAdd5387 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8151, 5386], outs := [5387] }
private def l12btSmMref5387 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5387], outs := [8178, 8182],
    params := [2] }
private def l12btSmRms5389 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8178, 5388], outs := [5389] }
private def l12btSmPhl5391 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5389, 5390],
    outs := [5391] }

private def l12btPmAdd9819 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [9741, 9815], outs := [9819] }
private def l12btPmAdd9820 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [9742, 9816], outs := [9820] }
private def l12btPmFloat9825 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [9819], outs := [9825] }
private def l12btPmFloat9826 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [9820], outs := [9826] }
private def l12btPmAdd9829 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [15989, 9825], outs := [9829] }
private def l12btPmAdd9830 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [15997, 9826], outs := [9830] }
private def l12btPmMref9829 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9829], outs := [16047, 16051],
    params := [2] }
private def l12btPmMref9830 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9830], outs := [16055, 16059],
    params := [2] }
private def l12btPmRms9833 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16047, 5388], outs := [9833] }
private def l12btPmRms9834 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16055, 5388], outs := [9834] }
private def l12btPmPhl9835 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9833, 5390],
    outs := [9835] }
private def l12btPmPhl9836 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9834, 5390],
    outs := [9836] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l12bt_sm_node_facts :
    sm.nodes[534]'(by native_decide) = l12btSmAdd5385 ∧
    sm.nodes[535]'(by native_decide) = l12btSmFloat5386 ∧
    sm.nodes[536]'(by native_decide) = l12btSmAdd5387 ∧
    sm.nodes[537]'(by native_decide) = l12btSmMref5387 ∧
    sm.nodes[538]'(by native_decide) = l12btSmRms5389 ∧
    sm.nodes[539]'(by native_decide) = l12btSmPhl5391 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12bt_pm_node_facts :
    pm.nodes[1130]'(by native_decide) = l12btPmAdd9819 ∧
    pm.nodes[1131]'(by native_decide) = l12btPmAdd9820 ∧
    pm.nodes[1132]'(by native_decide) = l12btPmFloat9825 ∧
    pm.nodes[1133]'(by native_decide) = l12btPmFloat9826 ∧
    pm.nodes[1134]'(by native_decide) = l12btPmAdd9829 ∧
    pm.nodes[1135]'(by native_decide) = l12btPmAdd9830 ∧
    pm.nodes[1136]'(by native_decide) = l12btPmMref9829 ∧
    pm.nodes[1137]'(by native_decide) = l12btPmMref9830 ∧
    pm.nodes[1138]'(by native_decide) = l12btPmRms9833 ∧
    pm.nodes[1139]'(by native_decide) = l12btPmRms9834 ∧
    pm.nodes[1140]'(by native_decide) = l12btPmPhl9835 ∧
    pm.nodes[1141]'(by native_decide) = l12btPmPhl9836 := by
  native_decide

private theorem l12bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5388 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5390 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5388 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5390 ∉ n.outs)) := by
  native_decide

private theorem l12bt_w5388_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5388 ∉ n.outs := by
  intro n hn
  exact l12bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l12bt_w5388_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5388 ∉ n.outs := by
  intro n hn
  exact l12bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l12bt_w5390_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5390 ∉ n.outs := by
  intro n hn
  exact l12bt_weights_not_written.1.2 n (List.mem_of_mem_drop hn)

private theorem l12bt_w5390_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5390 ∉ n.outs := by
  intro n hn
  exact l12bt_weights_not_written.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(535, 5385), (534, 5365), (534, 5384),
      (536, 5386), (535, 5385),
      (537, 5387), (536, 8151), (536, 5386),
      (538, 8178), (538, 8182), (537, 5387),
      (539, 5389), (538, 8178),
      (540, 5391), (539, 5389)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1131, 9819), (1130, 9741), (1130, 9815),
      (1132, 9820), (1131, 9742), (1131, 9816),
      (1133, 9825), (1132, 9819),
      (1134, 9826), (1133, 9820),
      (1135, 9829), (1134, 15989), (1134, 9825),
      (1136, 9830), (1135, 15997), (1135, 9826),
      (1137, 16047), (1137, 16051), (1136, 9829),
      (1138, 16055), (1138, 16059), (1137, 9830),
      (1139, 9833), (1138, 16047),
      (1140, 9834), (1139, 16055),
      (1141, 9835), (1140, 9833),
      (1142, 9836), (1141, 9834)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions: `FW_add` 5385 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_sm5385 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5385 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5365)
        (denoteGraphDistributedFaithful sm initSM 5384) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 534 l12btSmAdd5385
    5365 5384 5385 elemwiseAdd
    (by native_decide) l12bt_sm_node_facts.1 ?_
    (l12bt_nonempty_sm 535) (l12bt_sm_not_written 535 5385 (by decide))
    (l12bt_nonempty_sm 534) (l12bt_sm_not_written 534 5365 (by decide))
    (l12bt_sm_not_written 534 5384 (by decide))
  intro s
  unfold l12btSmAdd5385
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5365 5384 5385

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9819 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9819 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 9741)
        (denoteGraphDistributedFaithful pm initPM 9815) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1130 l12btPmAdd9819
    9741 9815 9819 elemwiseAdd
    (by native_decide) l12bt_pm_node_facts.1 ?_
    (l12bt_nonempty_pm 1131) (l12bt_pm_not_written 1131 9819 (by decide))
    (l12bt_nonempty_pm 1130) (l12bt_pm_not_written 1130 9741 (by decide))
    (l12bt_pm_not_written 1130 9815 (by decide))
  intro s
  unfold l12btPmAdd9819
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 9741 9815 9819

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9820 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9820 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 9742)
        (denoteGraphDistributedFaithful pm initPM 9816) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1131 l12btPmAdd9820
    9742 9816 9820 elemwiseAdd
    (by native_decide) l12bt_pm_node_facts.2.1 ?_
    (l12bt_nonempty_pm 1132) (l12bt_pm_not_written 1132 9820 (by decide))
    (l12bt_nonempty_pm 1131) (l12bt_pm_not_written 1131 9742 (by decide))
    (l12bt_pm_not_written 1131 9816 (by decide))
  intro s
  unfold l12btPmAdd9820
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 9742 9816 9820

/-! ### Node reductions: `FW_float` 5386 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_sm5386 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5386 =
      denoteGraphDistributedFaithful sm initSM 5385 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 535 l12btSmFloat5386
    5385 5386 (fun x => x)
    (by native_decide) l12bt_sm_node_facts.2.1 ?_
    (l12bt_nonempty_sm 536) (l12bt_sm_not_written 536 5386 (by decide))
    (l12bt_nonempty_sm 535) (l12bt_sm_not_written 535 5385 (by decide))
  intro s
  unfold l12btSmFloat5386
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5385 5386 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9825 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9825 =
      denoteGraphDistributedFaithful pm initPM 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1132 l12btPmFloat9825
    9819 9825 (fun x => x)
    (by native_decide) l12bt_pm_node_facts.2.2.1 ?_
    (l12bt_nonempty_pm 1133) (l12bt_pm_not_written 1133 9825 (by decide))
    (l12bt_nonempty_pm 1132) (l12bt_pm_not_written 1132 9819 (by decide))
  intro s
  unfold l12btPmFloat9825
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 9819 9825 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9826 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9826 =
      denoteGraphDistributedFaithful pm initPM 9820 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1133 l12btPmFloat9826
    9820 9826 (fun x => x)
    (by native_decide) l12bt_pm_node_facts.2.2.2.1 ?_
    (l12bt_nonempty_pm 1134) (l12bt_pm_not_written 1134 9826 (by decide))
    (l12bt_nonempty_pm 1133) (l12bt_pm_not_written 1133 9820 (by decide))
  intro s
  unfold l12btPmFloat9826
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 9820 9826 []

/-! ### Node reductions: `FW_add` 5387 (cross-MoE residual join) -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_sm5387 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5387 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8151)
        (denoteGraphDistributedFaithful sm initSM 5386) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 536 l12btSmAdd5387
    8151 5386 5387 elemwiseAdd
    (by native_decide) l12bt_sm_node_facts.2.2.1 ?_
    (l12bt_nonempty_sm 537) (l12bt_sm_not_written 537 5387 (by decide))
    (l12bt_nonempty_sm 536) (l12bt_sm_not_written 536 8151 (by decide))
    (l12bt_sm_not_written 536 5386 (by decide))
  intro s
  unfold l12btSmAdd5387
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8151 5386 5387

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9829 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9829 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 15989)
        (denoteGraphDistributedFaithful pm initPM 9825) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1134 l12btPmAdd9829
    15989 9825 9829 elemwiseAdd
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1135) (l12bt_pm_not_written 1135 9829 (by decide))
    (l12bt_nonempty_pm 1134) (l12bt_pm_not_written 1134 15989 (by decide))
    (l12bt_pm_not_written 1134 9825 (by decide))
  intro s
  unfold l12btPmAdd9829
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 15989 9825 9829

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9830 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9830 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 15997)
        (denoteGraphDistributedFaithful pm initPM 9826) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1135 l12btPmAdd9830
    15997 9826 9830 elemwiseAdd
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1136) (l12bt_pm_not_written 1136 9830 (by decide))
    (l12bt_nonempty_pm 1135) (l12bt_pm_not_written 1135 15997 (by decide))
    (l12bt_pm_not_written 1135 9826 (by decide))
  intro s
  unfold l12btPmAdd9830
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 15997 9826 9830

/-! ### Node reductions: 2-way multiref off 5387 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_sm8178 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8178 =
      denoteGraphDistributedFaithful sm initSM 5387 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 537 l12btSmMref5387
    5387 8178 (fun x => x)
    (by native_decide) l12bt_sm_node_facts.2.2.2.1 ?_
    (l12bt_nonempty_sm 538) (l12bt_sm_not_written 538 8178 (by decide))
    (l12bt_nonempty_sm 537) (l12bt_sm_not_written 537 5387 (by decide))
  intro s
  unfold l12btSmMref5387
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5387 8178 8182

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_sm8182 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8182 =
      denoteGraphDistributedFaithful sm initSM 5387 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 537 l12btSmMref5387
    5387 8182 (fun x => x)
    (by native_decide) l12bt_sm_node_facts.2.2.2.1 ?_
    (l12bt_nonempty_sm 538) (l12bt_sm_not_written 538 8182 (by decide))
    (l12bt_nonempty_sm 537) (l12bt_sm_not_written 537 5387 (by decide))
  intro s
  unfold l12btSmMref5387
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5387 8178 8182 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm16047 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16047 =
      denoteGraphDistributedFaithful pm initPM 9829 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1136 l12btPmMref9829
    9829 16047 (fun x => x)
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1137) (l12bt_pm_not_written 1137 16047 (by decide))
    (l12bt_nonempty_pm 1136) (l12bt_pm_not_written 1136 9829 (by decide))
  intro s
  unfold l12btPmMref9829
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 9829 16047 16051

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm16051 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16051 =
      denoteGraphDistributedFaithful pm initPM 9829 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1136 l12btPmMref9829
    9829 16051 (fun x => x)
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1137) (l12bt_pm_not_written 1137 16051 (by decide))
    (l12bt_nonempty_pm 1136) (l12bt_pm_not_written 1136 9829 (by decide))
  intro s
  unfold l12btPmMref9829
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 9829 16047 16051 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm16055 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16055 =
      denoteGraphDistributedFaithful pm initPM 9830 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1137 l12btPmMref9830
    9830 16055 (fun x => x)
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1138) (l12bt_pm_not_written 1138 16055 (by decide))
    (l12bt_nonempty_pm 1137) (l12bt_pm_not_written 1137 9830 (by decide))
  intro s
  unfold l12btPmMref9830
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 9830 16055 16059

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm16059 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16059 =
      denoteGraphDistributedFaithful pm initPM 9830 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1137 l12btPmMref9830
    9830 16059 (fun x => x)
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1138) (l12bt_pm_not_written 1138 16059 (by decide))
    (l12bt_nonempty_pm 1137) (l12bt_pm_not_written 1137 9830 (by decide))
  intro s
  unfold l12btPmMref9830
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 9830 16055 16059 (by decide)

/-! ### Node reductions: RMSNorm 5389 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_sm5389 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5389 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8178)
        (denoteGraphDistributedFaithful sm initSM 5388) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 538 l12btSmRms5389
    8178 5388 5389 fw_rms_norm
    (by native_decide) l12bt_sm_node_facts.2.2.2.2.1 ?_
    (l12bt_nonempty_sm 539) (l12bt_sm_not_written 539 5389 (by decide))
    (l12bt_nonempty_sm 538) (l12bt_sm_not_written 538 8178 (by decide))
    (l12bt_w5388_sm_drop 538)
  intro s
  unfold l12btSmRms5389
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8178 5388 5389

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9833 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9833 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16047)
        (denoteGraphDistributedFaithful pm initPM 5388) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1138 l12btPmRms9833
    16047 5388 9833 fw_rms_norm
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1139) (l12bt_pm_not_written 1139 9833 (by decide))
    (l12bt_nonempty_pm 1138) (l12bt_pm_not_written 1138 16047 (by decide))
    (l12bt_w5388_pm_drop 1138)
  intro s
  unfold l12btPmRms9833
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16047 5388 9833

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9834 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9834 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16055)
        (denoteGraphDistributedFaithful pm initPM 5388) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1139 l12btPmRms9834
    16055 5388 9834 fw_rms_norm
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1140) (l12bt_pm_not_written 1140 9834 (by decide))
    (l12bt_nonempty_pm 1139) (l12bt_pm_not_written 1139 16055 (by decide))
    (l12bt_w5388_pm_drop 1139)
  intro s
  unfold l12btPmRms9834
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16055 5388 9834

/-! ### Node reductions: per-head Q projection 5391 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_sm5391 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5391 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5389)
        (denoteGraphDistributedFaithful sm initSM 5390) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 539 l12btSmPhl5391
    5389 5390 5391 fw_per_head_linear
    (by native_decide) l12bt_sm_node_facts.2.2.2.2.2 ?_
    (l12bt_nonempty_sm 540) (l12bt_sm_not_written 540 5391 (by decide))
    (l12bt_nonempty_sm 539) (l12bt_sm_not_written 539 5389 (by decide))
    (l12bt_w5390_sm_drop 539)
  intro s
  unfold l12btSmPhl5391
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5389 5390 5391 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9835 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9835 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 9833)
        (denoteGraphDistributedFaithful pm initPM 5390) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1140 l12btPmPhl9835
    9833 5390 9835 fw_per_head_linear
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l12bt_nonempty_pm 1141) (l12bt_pm_not_written 1141 9835 (by decide))
    (l12bt_nonempty_pm 1140) (l12bt_pm_not_written 1140 9833 (by decide))
    (l12bt_w5390_pm_drop 1140)
  intro s
  unfold l12btPmPhl9835
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 9833 5390 9835 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_red_pm9836 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9836 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 9834)
        (denoteGraphDistributedFaithful pm initPM 5390) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1141 l12btPmPhl9836
    9834 5390 9836 fw_per_head_linear
    (by native_decide) l12bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l12bt_nonempty_pm 1142) (l12bt_pm_not_written 1142 9836 (by decide))
    (l12bt_nonempty_pm 1141) (l12bt_pm_not_written 1141 9834 (by decide))
    (l12bt_w5390_pm_drop 1141)
  intro s
  unfold l12btPmPhl9836
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 9834 5390 9836 []

/-! ### Replicated weight transport -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (W : Tid) (g : LineageGoal) (hg : g ∈ initGoals)
    (htp : g.tps = [{rank := 0, tid := W}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = W)
    (hsw : ∀ n ∈ sm.nodes, W ∉ n.outs) (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm initSM W =
      denoteGraphDistributedFaithful pm initPM W := by
  have h : initSM W = initPM W := by
    have hr := recon_weight initSM initPM hInit g hg W htp hgd hrep hts
    unfold denoteGraph at hr
    rw [foldl_applyNode_at_not_written sm sm.nodes initSM W hsw,
      foldl_applyNode_at_not_written pm pm.nodes initPM W hpw] at hr
    exact hr
  have e1 : denoteGraphDistributedFaithful sm initSM W = initSM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM W
      layer1_sm_nodes_nonempty hsw
  have e2 : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e1, e2]; exact h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  have e2 : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e2]
  exact hPM W sh hmem

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5385 (`FW_add [5365, 5384]`:
-- the MoE expert output joined with the gated shared-expert branch).
theorem recon_zigzagGoal_5385_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5385)
      (denoteGraphDistributedFaithful pm initPM 9819)
      (denoteGraphDistributedFaithful pm initPM 9820)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5365_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5384_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5365)
      (denoteGraphDistributedFaithful pm initPM 9741)
      (denoteGraphDistributedFaithful pm initPM 9742)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5384)
      (denoteGraphDistributedFaithful pm initPM 9815)
      (denoteGraphDistributedFaithful pm initPM 9816)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l12bt_red_sm5385 initSM, l12bt_red_pm9819 initPM, l12bt_red_pm9820 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5386 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5386_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5386)
      (denoteGraphDistributedFaithful pm initPM 9825)
      (denoteGraphDistributedFaithful pm initPM 9826)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5385_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12bt_red_sm5386 initSM, l12bt_red_pm9825 initPM, l12bt_red_pm9826 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5387 (`FW_add [8151, 5386]`:
-- the block residual bypass rejoining the MoE output).
theorem recon_zigzagGoal_5387_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5387)
      (denoteGraphDistributedFaithful pm initPM 9829)
      (denoteGraphDistributedFaithful pm initPM 9830)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8151_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5386_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8151)
      (denoteGraphDistributedFaithful pm initPM 15989)
      (denoteGraphDistributedFaithful pm initPM 15997)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5386)
      (denoteGraphDistributedFaithful pm initPM 9825)
      (denoteGraphDistributedFaithful pm initPM 9826)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l12bt_red_sm5387 initSM, l12bt_red_pm9829 initPM, l12bt_red_pm9830 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8178 (multiref position 0 off 5387,
-- the RMSNorm input of the next block entry).
theorem recon_zigzagGoal_8178_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8178)
      (denoteGraphDistributedFaithful pm initPM 16047)
      (denoteGraphDistributedFaithful pm initPM 16055)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5387_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12bt_red_sm8178 initSM, l12bt_red_pm16047 initPM, l12bt_red_pm16055 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Faithful zigzag relation for generated goal
-- 8182 (multiref position 1 off 5387): the cross-layer residual bypass consumed by
-- SM node 546 `FW_add [8182, 5402]`.
theorem recon_zigzagGoal_8182_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8182)
      (denoteGraphDistributedFaithful pm initPM 16051)
      (denoteGraphDistributedFaithful pm initPM 16059)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5387_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l12bt_red_sm8182 initSM, l12bt_red_pm16051 initPM, l12bt_red_pm16059 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5389 (`FW_rms_norm` of 8178 with the
-- replicated `[1024]` weight 5388).
theorem recon_zigzagGoal_5389_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5389)
      (denoteGraphDistributedFaithful pm initPM 9833)
      (denoteGraphDistributedFaithful pm initPM 9834)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8178_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5388 =
      denoteGraphDistributedFaithful pm initPM 5388 :=
    l12bt_weight_eq initSM initPM hInit 5388 initGoal_5388 (by native_decide)
      rfl rfl rfl rfl
      l12bt_weights_not_written.1.1 l12bt_weights_not_written.2.1
  rw [l12bt_red_sm5389 initSM, l12bt_red_pm9833 initPM, l12bt_red_pm9834 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Faithful zigzag relation for generated goal
-- 5391 (`FW_per_head_mix_precision_linear [5389, 5390]`, weight `[16, 64, 1024]`
-- replicated): the per-head Q projection `[4096,16,64]` / `[2048,16,64]` that feeds
-- the next block's zigzag attention entry.
theorem recon_zigzagGoal_5391_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5391)
      (denoteGraphDistributedFaithful pm initPM 9835)
      (denoteGraphDistributedFaithful pm initPM 9836)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent :=
    recon_zigzagGoal_5389_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5390 =
      denoteGraphDistributedFaithful pm initPM 5390 :=
    l12bt_weight_eq initSM initPM hInit 5390 initGoal_5390 (by native_decide)
      rfl rfl rfl rfl
      l12bt_weights_not_written.1.2 l12bt_weights_not_written.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5390).shape = [16, 64, 1024] :=
    l12bt_pm_weight_shape initPM hPM 5390 [16, 64, 1024] (by native_decide)
      l12bt_weights_not_written.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5389)
      (denoteGraphDistributedFaithful pm initPM 9833)
      (denoteGraphDistributedFaithful pm initPM 9834)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l12bt_red_sm5391 initSM, l12bt_red_pm9835 initPM, l12bt_red_pm9836 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
