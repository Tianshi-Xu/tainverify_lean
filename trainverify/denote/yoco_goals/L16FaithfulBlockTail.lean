/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L16FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L15FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-4 tail (MoE join -> block-4 Q)

Mechanical transport of the (green) block-3 tail `L13FaithfulBlockTail` to
block 4.  The block-4 cu tensor is **5541**.

* SM 667 `FW_all2all_moe_gmm [8318,5556,5557,5559,5560] -> [5561]` (PM 1396/1399 -> 10429/10430)
* SM 670 `FW_reshape [5575] -> [5576]`                             (PM 1402/1403 -> 10483/10484)
* SM 671 `FW_mix_precision_linear [5576,5577] -> [5578]`           (PM 1404/1405 -> 10489/10490)
* SM 672 `FW_view [5578] -> [5579]`                                (PM 1406/1407 -> 10499/10500)
* SM 673 `FW_mul [5566,5579] -> [5580]` (broadcast `[N,1]x[N,1024]`)(PM 1408/1409 -> 10503/10504)
* SM 674 `FW_add [5561,5580] -> [5581]`                            (PM 1410/1411 -> 10507/10508)
* SM 675 `FW_float [5581] -> [5582]`                               (PM 1412/1413 -> 10513/10514)
* SM 676 `FW_add [8307,5582] -> [5583]`                            (PM 1414/1415 -> 10517/10518)
* SM 677 `FW_multiref [5583] -> [8334,8338]`                       (PM 1416/1417)
* SM 678 `FW_rms_norm [8334,5584] -> [5585]`                       (PM 1418/1419 -> 10521/10522)
* SM 679 `FW_per_head_mix_precision_linear [5585,5586] -> [5587]`  (PM 1420/1421 -> 10523/10524)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8338_faithful` -- the cross-layer residual bypass consumed by
  block 4 (SM node 686 `FW_add`);
* `recon_zigzagGoal_5587_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 4's zigzag attention entry.

The MoE node is evaluated by `applyNodeFullExpertMoE_value`, i.e. over the **full**
expert range after gathering both rank shards, so the plain
`Zigzag2Rel.all2all_moe_gmm` applies -- no routing-map disjointness contract needed.

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

/-! ### Local seven-read reduction (MoE: five declared inputs + buddy weight shards) -/

private theorem l16bt_reduce7
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 in5 in6 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4) (s in5) (s in6))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs)
    (hpre5 : ∀ n ∈ g.nodes.drop k, in5 ∉ n.outs)
    (hpre6 : ∀ n ∈ g.nodes.drop k, in6 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4)
        (denoteGraphDistributedFaithful g init in5)
        (denoteGraphDistributedFaithful g init in6) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4,
    denoteGraphDistributedFaithful_prefix_read g init k in5 hpreNil hpre5,
    denoteGraphDistributedFaithful_prefix_read g init k in6 hpreNil hpre6]

private theorem l16bt_reduce5
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4]

/-! ### Node literals -/
private def l16btSmMoE5561 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8318,5556,5557,5559,5560], outs := [5561],
    params := [64,0,64,8] }
private def l16btSmResh5576 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5575], outs := [5576],
    params := [4096,512] }
private def l16btSmMPL5578 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5576,5577], outs := [5578] }
private def l16btSmView5579 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5578], outs := [5579],
    params := [4096,1024] }
private def l16btSmMul5580 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5566,5579], outs := [5580] }
private def l16btSmAdd5581 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5561,5580], outs := [5581] }
private def l16btSmFloat5582 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5581], outs := [5582] }
private def l16btSmAdd5583 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8307,5582], outs := [5583] }
private def l16btSmMref5583 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5583], outs := [8334,8338],
    params := [2] }
private def l16btSmRms5585 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8334,5584], outs := [5585] }
private def l16btSmPhl5587 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5585,5586], outs := [5587] }

private def l16btPmMoE10429 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16320,10419,10421,10425,10427], outs := [10429],
    params := [64,0,32,8] }
private def l16btPmMoE10430 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16343,10420,10422,10426,10428], outs := [10430],
    params := [64,32,64,8] }
private def l16btPmResh10483 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10481], outs := [10483],
    params := [2048,512] }
private def l16btPmResh10484 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10482], outs := [10484],
    params := [2048,512] }
private def l16btPmMPL10489 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10483,5577], outs := [10489] }
private def l16btPmMPL10490 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10484,5577], outs := [10490] }
private def l16btPmView10499 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10489], outs := [10499],
    params := [2048,1024] }
private def l16btPmView10500 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10490], outs := [10500],
    params := [2048,1024] }
private def l16btPmMul10503 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10443,10499], outs := [10503] }
private def l16btPmMul10504 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10444,10500], outs := [10504] }
private def l16btPmAdd10507 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10429,10503], outs := [10507] }
private def l16btPmAdd10508 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10430,10504], outs := [10508] }
private def l16btPmFloat10513 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10507], outs := [10513] }
private def l16btPmFloat10514 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10508], outs := [10514] }
private def l16btPmAdd10517 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16301,10513], outs := [10517] }
private def l16btPmAdd10518 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16309,10514], outs := [10518] }
private def l16btPmMref10517 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10517], outs := [16359,16363],
    params := [2] }
private def l16btPmMref10518 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10518], outs := [16367,16371],
    params := [2] }
private def l16btPmRms10521 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16359,5584], outs := [10521] }
private def l16btPmRms10522 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16367,5584], outs := [10522] }
private def l16btPmPhl10523 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10521,5586], outs := [10523] }
private def l16btPmPhl10524 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10522,5586], outs := [10524] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l16bt_sm_node_facts :
    sm.nodes[667]'(by native_decide) = l16btSmMoE5561 ∧
    sm.nodes[670]'(by native_decide) = l16btSmResh5576 ∧
    sm.nodes[671]'(by native_decide) = l16btSmMPL5578 ∧
    sm.nodes[672]'(by native_decide) = l16btSmView5579 ∧
    sm.nodes[673]'(by native_decide) = l16btSmMul5580 ∧
    sm.nodes[674]'(by native_decide) = l16btSmAdd5581 ∧
    sm.nodes[675]'(by native_decide) = l16btSmFloat5582 ∧
    sm.nodes[676]'(by native_decide) = l16btSmAdd5583 ∧
    sm.nodes[677]'(by native_decide) = l16btSmMref5583 ∧
    sm.nodes[678]'(by native_decide) = l16btSmRms5585 ∧
    sm.nodes[679]'(by native_decide) = l16btSmPhl5587 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l16bt_pm_node_facts :
    pm.nodes[1396]'(by native_decide) = l16btPmMoE10429 ∧
    pm.nodes[1399]'(by native_decide) = l16btPmMoE10430 ∧
    pm.nodes[1402]'(by native_decide) = l16btPmResh10483 ∧
    pm.nodes[1403]'(by native_decide) = l16btPmResh10484 ∧
    pm.nodes[1404]'(by native_decide) = l16btPmMPL10489 ∧
    pm.nodes[1405]'(by native_decide) = l16btPmMPL10490 ∧
    pm.nodes[1406]'(by native_decide) = l16btPmView10499 ∧
    pm.nodes[1407]'(by native_decide) = l16btPmView10500 ∧
    pm.nodes[1408]'(by native_decide) = l16btPmMul10503 ∧
    pm.nodes[1409]'(by native_decide) = l16btPmMul10504 ∧
    pm.nodes[1410]'(by native_decide) = l16btPmAdd10507 ∧
    pm.nodes[1411]'(by native_decide) = l16btPmAdd10508 ∧
    pm.nodes[1412]'(by native_decide) = l16btPmFloat10513 ∧
    pm.nodes[1413]'(by native_decide) = l16btPmFloat10514 ∧
    pm.nodes[1414]'(by native_decide) = l16btPmAdd10517 ∧
    pm.nodes[1415]'(by native_decide) = l16btPmAdd10518 ∧
    pm.nodes[1416]'(by native_decide) = l16btPmMref10517 ∧
    pm.nodes[1417]'(by native_decide) = l16btPmMref10518 ∧
    pm.nodes[1418]'(by native_decide) = l16btPmRms10521 ∧
    pm.nodes[1419]'(by native_decide) = l16btPmRms10522 ∧
    pm.nodes[1420]'(by native_decide) = l16btPmPhl10523 ∧
    pm.nodes[1421]'(by native_decide) = l16btPmPhl10524 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l16bt_buddy_facts :
    sm.replicaBuddies l16btSmMoE5561 = [l16btSmMoE5561] ∧
    pm.replicaBuddies l16btPmMoE10429 = [l16btPmMoE10429, l16btPmMoE10430] ∧
    pm.replicaBuddies l16btPmMoE10430 = [l16btPmMoE10429, l16btPmMoE10430] := by
  native_decide

private theorem l16bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l16bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l16bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5577 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5584 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5586 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5577 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5584 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5586 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l16bt_cu_not_written : ∀ n ∈ pm.nodes, 5541 ∉ n.outs := by
  native_decide

private theorem l16bt_w5577_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5577 ∉ n.outs := by
  intro n hn
  exact l16bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l16bt_w5577_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5577 ∉ n.outs := by
  intro n hn
  exact l16bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l16bt_w5584_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5584 ∉ n.outs := by
  intro n hn
  exact l16bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l16bt_w5584_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5584 ∉ n.outs := by
  intro n hn
  exact l16bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l16bt_w5586_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5586 ∉ n.outs := by
  intro n hn
  exact l16bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l16bt_w5586_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5586 ∉ n.outs := by
  intro n hn
  exact l16bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l16bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(668, 5561), (667, 8318), (667, 5556), (667, 5557), (667, 5559), (667, 5560), (671, 5576), (670, 5575), (672, 5578), (671, 5576), (673, 5579), (672, 5578), (674, 5580), (673, 5566), (673, 5579), (675, 5581), (674, 5561), (674, 5580), (676, 5582), (675, 5581), (677, 5583), (676, 8307), (676, 5582), (678, 8334), (678, 8338), (677, 5583), (679, 5585), (678, 8334), (680, 5587), (679, 5585)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1397, 10429), (1396, 16320), (1396, 10419), (1396, 10421), (1396, 10425), (1396, 10427), (1396, 10426), (1396, 10428), (1400, 10430), (1399, 16343), (1399, 10420), (1399, 10422), (1399, 10425), (1399, 10426), (1399, 10427), (1399, 10428), (1403, 10483), (1402, 10481), (1404, 10484), (1403, 10482), (1405, 10489), (1404, 10483), (1406, 10490), (1405, 10484), (1407, 10499), (1406, 10489), (1408, 10500), (1407, 10490), (1409, 10503), (1408, 10443), (1408, 10499), (1410, 10504), (1409, 10444), (1409, 10500), (1411, 10507), (1410, 10429), (1410, 10503), (1412, 10508), (1411, 10430), (1411, 10504), (1413, 10513), (1412, 10507), (1414, 10514), (1413, 10508), (1415, 10517), (1414, 16301), (1414, 10513), (1416, 10518), (1415, 16309), (1415, 10514), (1417, 16359), (1417, 16363), (1416, 10517), (1418, 16367), (1418, 16371), (1417, 10518), (1419, 10521), (1418, 16359), (1420, 10522), (1419, 16367), (1421, 10523), (1420, 10521), (1422, 10524), (1421, 10522)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5559, 5560]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [10425, 10426, 10427, 10428]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l16bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5559, 5560]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l16bt_sm_leaf_not_written tid h)

private theorem l16bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [10425, 10426, 10427, 10428]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l16bt_pm_leaf_not_written tid h)

private theorem l16bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5561 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5561 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5561 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8318)
        (denoteGraphDistributedFaithful sm initSM 5556)
        (denoteGraphDistributedFaithful sm initSM 5557)
        [denoteGraphDistributedFaithful sm initSM 5559]
        [denoteGraphDistributedFaithful sm initSM 5560]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l16bt_reduce5 sm initSM 667 l16btSmMoE5561
    8318 5556 5557 5559 5560 5561
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l16bt_sm_node_facts.1 ?_
    (l16bt_nonempty_sm 668) (l16bt_sm_not_written 668 5561 (by decide))
    (l16bt_nonempty_sm 667) (l16bt_sm_not_written 667 8318 (by decide))
    (l16bt_sm_not_written 667 5556 (by decide))
    (l16bt_sm_not_written 667 5557 (by decide))
    (l16bt_sm_not_written 667 5559 (by decide))
    (l16bt_sm_not_written 667 5560 (by decide))
  intro s
  have hb := l16bt_buddy_facts.1
  unfold l16btSmMoE5561 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8318 5556 5557 5559 5560 5561 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10429 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10429 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16320)
        (denoteGraphDistributedFaithful pm initPM 10419)
        (denoteGraphDistributedFaithful pm initPM 10421)
        [denoteGraphDistributedFaithful pm initPM 10425,
         denoteGraphDistributedFaithful pm initPM 10426]
        [denoteGraphDistributedFaithful pm initPM 10427,
         denoteGraphDistributedFaithful pm initPM 10428]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l16bt_reduce7 pm initPM 1396 l16btPmMoE10429
    16320 10419 10421 10425 10427 10426 10428 10429
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l16bt_pm_node_facts.1 ?_
    (l16bt_nonempty_pm 1397) (l16bt_pm_not_written 1397 10429 (by decide))
    (l16bt_nonempty_pm 1396) (l16bt_pm_not_written 1396 16320 (by decide))
    (l16bt_pm_not_written 1396 10419 (by decide))
    (l16bt_pm_not_written 1396 10421 (by decide))
    (l16bt_pm_not_written 1396 10425 (by decide))
    (l16bt_pm_not_written 1396 10427 (by decide))
    (l16bt_pm_not_written 1396 10426 (by decide))
    (l16bt_pm_not_written 1396 10428 (by decide))
  intro s
  have hb := l16bt_buddy_facts.2.1
  unfold l16btPmMoE10429 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16320 10419 10421 10425 10427 10429 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10430 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10430 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16343)
        (denoteGraphDistributedFaithful pm initPM 10420)
        (denoteGraphDistributedFaithful pm initPM 10422)
        [denoteGraphDistributedFaithful pm initPM 10425,
         denoteGraphDistributedFaithful pm initPM 10426]
        [denoteGraphDistributedFaithful pm initPM 10427,
         denoteGraphDistributedFaithful pm initPM 10428]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l16bt_reduce7 pm initPM 1399 l16btPmMoE10430
    16343 10420 10422 10425 10426 10427 10428 10430
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l16bt_pm_node_facts.2.1 ?_
    (l16bt_nonempty_pm 1400) (l16bt_pm_not_written 1400 10430 (by decide))
    (l16bt_nonempty_pm 1399) (l16bt_pm_not_written 1399 16343 (by decide))
    (l16bt_pm_not_written 1399 10420 (by decide))
    (l16bt_pm_not_written 1399 10422 (by decide))
    (l16bt_pm_not_written 1399 10425 (by decide))
    (l16bt_pm_not_written 1399 10426 (by decide))
    (l16bt_pm_not_written 1399 10427 (by decide))
    (l16bt_pm_not_written 1399 10428 (by decide))
  intro s
  have hb := l16bt_buddy_facts.2.2
  unfold l16btPmMoE10430 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16343 10420 10422 10426 10428 10430 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5576 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5576 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5576 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5575) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 670 l16btSmResh5576
    5575 5576 (fun x => fw_view [4096,512] x)
    (by native_decide) l16bt_sm_node_facts.2.1 ?_
    (l16bt_nonempty_sm 671) (l16bt_sm_not_written 671 5576 (by decide))
    (l16bt_nonempty_sm 670) (l16bt_sm_not_written 670 5575 (by decide))
  intro s
  unfold l16btSmResh5576
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5575 5576 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10483 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10483 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10481) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1402 l16btPmResh10483
    10481 10483 (fun x => fw_view [2048,512] x)
    (by native_decide) l16bt_pm_node_facts.2.2.1 ?_
    (l16bt_nonempty_pm 1403) (l16bt_pm_not_written 1403 10483 (by decide))
    (l16bt_nonempty_pm 1402) (l16bt_pm_not_written 1402 10481 (by decide))
  intro s
  unfold l16btPmResh10483
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10481 10483 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10484 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10484 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10482) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1403 l16btPmResh10484
    10482 10484 (fun x => fw_view [2048,512] x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.1 ?_
    (l16bt_nonempty_pm 1404) (l16bt_pm_not_written 1404 10484 (by decide))
    (l16bt_nonempty_pm 1403) (l16bt_pm_not_written 1403 10482 (by decide))
  intro s
  unfold l16btPmResh10484
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10482 10484 [2048,512]

/-! ### Node reductions: down-projection 5578 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5578 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5578 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5576)
        (denoteGraphDistributedFaithful sm initSM 5577) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 671 l16btSmMPL5578
    5576 5577 5578 fw_linear
    (by native_decide) l16bt_sm_node_facts.2.2.1 ?_
    (l16bt_nonempty_sm 672) (l16bt_sm_not_written 672 5578 (by decide))
    (l16bt_nonempty_sm 671) (l16bt_sm_not_written 671 5576 (by decide))
    (l16bt_w5577_sm_drop 671)
  intro s
  unfold l16btSmMPL5578
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5576 5577 5578

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10489 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10489 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10483)
        (denoteGraphDistributedFaithful pm initPM 5577) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1404 l16btPmMPL10489
    10483 5577 10489 fw_linear
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1405) (l16bt_pm_not_written 1405 10489 (by decide))
    (l16bt_nonempty_pm 1404) (l16bt_pm_not_written 1404 10483 (by decide))
    (l16bt_w5577_pm_drop 1404)
  intro s
  unfold l16btPmMPL10489
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10483 5577 10489

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10490 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10490 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10484)
        (denoteGraphDistributedFaithful pm initPM 5577) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1405 l16btPmMPL10490
    10484 5577 10490 fw_linear
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1406) (l16bt_pm_not_written 1406 10490 (by decide))
    (l16bt_nonempty_pm 1405) (l16bt_pm_not_written 1405 10484 (by decide))
    (l16bt_w5577_pm_drop 1405)
  intro s
  unfold l16btPmMPL10490
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10484 5577 10490

/-! ### Node reductions: view 5579 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5579 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5579 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5578) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 672 l16btSmView5579
    5578 5579 (fun x => fw_view [4096,1024] x)
    (by native_decide) l16bt_sm_node_facts.2.2.2.1 ?_
    (l16bt_nonempty_sm 673) (l16bt_sm_not_written 673 5579 (by decide))
    (l16bt_nonempty_sm 672) (l16bt_sm_not_written 672 5578 (by decide))
  intro s
  unfold l16btSmView5579
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5578 5579

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10499 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10499 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10489) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1406 l16btPmView10499
    10489 10499 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1407) (l16bt_pm_not_written 1407 10499 (by decide))
    (l16bt_nonempty_pm 1406) (l16bt_pm_not_written 1406 10489 (by decide))
  intro s
  unfold l16btPmView10499
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10489 10499

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10500 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10500 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10490) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1407 l16btPmView10500
    10490 10500 (fun x => fw_view [2048,1024] x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1408) (l16bt_pm_not_written 1408 10500 (by decide))
    (l16bt_nonempty_pm 1407) (l16bt_pm_not_written 1407 10490 (by decide))
  intro s
  unfold l16btPmView10500
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10490 10500

/-! ### Node reductions: gated multiply 5580 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5580 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5580 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5566)
        (denoteGraphDistributedFaithful sm initSM 5579) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 673 l16btSmMul5580
    5566 5579 5580 elemwiseMul
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.1 ?_
    (l16bt_nonempty_sm 674) (l16bt_sm_not_written 674 5580 (by decide))
    (l16bt_nonempty_sm 673) (l16bt_sm_not_written 673 5566 (by decide))
    (l16bt_sm_not_written 673 5579 (by decide))
  intro s
  unfold l16btSmMul5580
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5566 5579 5580

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10503 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10503 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10443)
        (denoteGraphDistributedFaithful pm initPM 10499) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1408 l16btPmMul10503
    10443 10499 10503 elemwiseMul
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1409) (l16bt_pm_not_written 1409 10503 (by decide))
    (l16bt_nonempty_pm 1408) (l16bt_pm_not_written 1408 10443 (by decide))
    (l16bt_pm_not_written 1408 10499 (by decide))
  intro s
  unfold l16btPmMul10503
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 10443 10499 10503

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10504 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10504 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10444)
        (denoteGraphDistributedFaithful pm initPM 10500) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1409 l16btPmMul10504
    10444 10500 10504 elemwiseMul
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1410) (l16bt_pm_not_written 1410 10504 (by decide))
    (l16bt_nonempty_pm 1409) (l16bt_pm_not_written 1409 10444 (by decide))
    (l16bt_pm_not_written 1409 10500 (by decide))
  intro s
  unfold l16btPmMul10504
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 10444 10500 10504

/-! ### Node reductions: MoE join 5581 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5581 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5581 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5561)
        (denoteGraphDistributedFaithful sm initSM 5580) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 674 l16btSmAdd5581
    5561 5580 5581 elemwiseAdd
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l16bt_nonempty_sm 675) (l16bt_sm_not_written 675 5581 (by decide))
    (l16bt_nonempty_sm 674) (l16bt_sm_not_written 674 5561 (by decide))
    (l16bt_sm_not_written 674 5580 (by decide))
  intro s
  unfold l16btSmAdd5581
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5561 5580 5581

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10507 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10507 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10429)
        (denoteGraphDistributedFaithful pm initPM 10503) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1410 l16btPmAdd10507
    10429 10503 10507 elemwiseAdd
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1411) (l16bt_pm_not_written 1411 10507 (by decide))
    (l16bt_nonempty_pm 1410) (l16bt_pm_not_written 1410 10429 (by decide))
    (l16bt_pm_not_written 1410 10503 (by decide))
  intro s
  unfold l16btPmAdd10507
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 10429 10503 10507

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10508 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10508 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10430)
        (denoteGraphDistributedFaithful pm initPM 10504) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1411 l16btPmAdd10508
    10430 10504 10508 elemwiseAdd
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1412) (l16bt_pm_not_written 1412 10508 (by decide))
    (l16bt_nonempty_pm 1411) (l16bt_pm_not_written 1411 10430 (by decide))
    (l16bt_pm_not_written 1411 10504 (by decide))
  intro s
  unfold l16btPmAdd10508
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 10430 10504 10508

/-! ### Node reductions: float 5582 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5582 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5582 =
      denoteGraphDistributedFaithful sm initSM 5581 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 675 l16btSmFloat5582
    5581 5582 (fun x => x)
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_sm 676) (l16bt_sm_not_written 676 5582 (by decide))
    (l16bt_nonempty_sm 675) (l16bt_sm_not_written 675 5581 (by decide))
  intro s
  unfold l16btSmFloat5582
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5581 5582 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10513 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10513 =
      denoteGraphDistributedFaithful pm initPM 10507 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1412 l16btPmFloat10513
    10507 10513 (fun x => x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1413) (l16bt_pm_not_written 1413 10513 (by decide))
    (l16bt_nonempty_pm 1412) (l16bt_pm_not_written 1412 10507 (by decide))
  intro s
  unfold l16btPmFloat10513
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 10507 10513 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10514 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10514 =
      denoteGraphDistributedFaithful pm initPM 10508 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1413 l16btPmFloat10514
    10508 10514 (fun x => x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1414) (l16bt_pm_not_written 1414 10514 (by decide))
    (l16bt_nonempty_pm 1413) (l16bt_pm_not_written 1413 10508 (by decide))
  intro s
  unfold l16btPmFloat10514
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 10508 10514 []

/-! ### Node reductions: residual join 5583 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5583 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5583 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8307)
        (denoteGraphDistributedFaithful sm initSM 5582) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 676 l16btSmAdd5583
    8307 5582 5583 elemwiseAdd
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_sm 677) (l16bt_sm_not_written 677 5583 (by decide))
    (l16bt_nonempty_sm 676) (l16bt_sm_not_written 676 8307 (by decide))
    (l16bt_sm_not_written 676 5582 (by decide))
  intro s
  unfold l16btSmAdd5583
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8307 5582 5583

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10517 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10517 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16301)
        (denoteGraphDistributedFaithful pm initPM 10513) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1414 l16btPmAdd10517
    16301 10513 10517 elemwiseAdd
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1415) (l16bt_pm_not_written 1415 10517 (by decide))
    (l16bt_nonempty_pm 1414) (l16bt_pm_not_written 1414 16301 (by decide))
    (l16bt_pm_not_written 1414 10513 (by decide))
  intro s
  unfold l16btPmAdd10517
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16301 10513 10517

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10518 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10518 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16309)
        (denoteGraphDistributedFaithful pm initPM 10514) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1415 l16btPmAdd10518
    16309 10514 10518 elemwiseAdd
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1416) (l16bt_pm_not_written 1416 10518 (by decide))
    (l16bt_nonempty_pm 1415) (l16bt_pm_not_written 1415 16309 (by decide))
    (l16bt_pm_not_written 1415 10514 (by decide))
  intro s
  unfold l16btPmAdd10518
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16309 10514 10518

/-! ### Node reductions: 2-way multiref off 5583 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm8334 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8334 =
      denoteGraphDistributedFaithful sm initSM 5583 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 677 l16btSmMref5583
    5583 8334 (fun x => x)
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_sm 678) (l16bt_sm_not_written 678 8334 (by decide))
    (l16bt_nonempty_sm 677) (l16bt_sm_not_written 677 5583 (by decide))
  intro s
  unfold l16btSmMref5583
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5583 8334 8338

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm8338 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8338 =
      denoteGraphDistributedFaithful sm initSM 5583 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 677 l16btSmMref5583
    5583 8338 (fun x => x)
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_sm 678) (l16bt_sm_not_written 678 8338 (by decide))
    (l16bt_nonempty_sm 677) (l16bt_sm_not_written 677 5583 (by decide))
  intro s
  unfold l16btSmMref5583
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5583 8334 8338 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm16359 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16359 =
      denoteGraphDistributedFaithful pm initPM 10517 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1416 l16btPmMref10517
    10517 16359 (fun x => x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1417) (l16bt_pm_not_written 1417 16359 (by decide))
    (l16bt_nonempty_pm 1416) (l16bt_pm_not_written 1416 10517 (by decide))
  intro s
  unfold l16btPmMref10517
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10517 16359 16363

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm16363 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16363 =
      denoteGraphDistributedFaithful pm initPM 10517 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1416 l16btPmMref10517
    10517 16363 (fun x => x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1417) (l16bt_pm_not_written 1417 16363 (by decide))
    (l16bt_nonempty_pm 1416) (l16bt_pm_not_written 1416 10517 (by decide))
  intro s
  unfold l16btPmMref10517
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10517 16359 16363 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm16367 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16367 =
      denoteGraphDistributedFaithful pm initPM 10518 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1417 l16btPmMref10518
    10518 16367 (fun x => x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1418) (l16bt_pm_not_written 1418 16367 (by decide))
    (l16bt_nonempty_pm 1417) (l16bt_pm_not_written 1417 10518 (by decide))
  intro s
  unfold l16btPmMref10518
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10518 16367 16371

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm16371 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16371 =
      denoteGraphDistributedFaithful pm initPM 10518 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1417 l16btPmMref10518
    10518 16371 (fun x => x)
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1418) (l16bt_pm_not_written 1418 16371 (by decide))
    (l16bt_nonempty_pm 1417) (l16bt_pm_not_written 1417 10518 (by decide))
  intro s
  unfold l16btPmMref10518
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10518 16367 16371 (by decide)

/-! ### Node reductions: RMSNorm 5585 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5585 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5585 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8334)
        (denoteGraphDistributedFaithful sm initSM 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 678 l16btSmRms5585
    8334 5584 5585 fw_rms_norm
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_sm 679) (l16bt_sm_not_written 679 5585 (by decide))
    (l16bt_nonempty_sm 678) (l16bt_sm_not_written 678 8334 (by decide))
    (l16bt_w5584_sm_drop 678)
  intro s
  unfold l16btSmRms5585
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8334 5584 5585

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10521 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10521 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16359)
        (denoteGraphDistributedFaithful pm initPM 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1418 l16btPmRms10521
    16359 5584 10521 fw_rms_norm
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1419) (l16bt_pm_not_written 1419 10521 (by decide))
    (l16bt_nonempty_pm 1418) (l16bt_pm_not_written 1418 16359 (by decide))
    (l16bt_w5584_pm_drop 1418)
  intro s
  unfold l16btPmRms10521
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16359 5584 10521

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10522 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10522 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16367)
        (denoteGraphDistributedFaithful pm initPM 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1419 l16btPmRms10522
    16367 5584 10522 fw_rms_norm
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1420) (l16bt_pm_not_written 1420 10522 (by decide))
    (l16bt_nonempty_pm 1419) (l16bt_pm_not_written 1419 16367 (by decide))
    (l16bt_w5584_pm_drop 1419)
  intro s
  unfold l16btPmRms10522
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16367 5584 10522

/-! ### Node reductions: per-head Q projection 5587 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_sm5587 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5587 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5585)
        (denoteGraphDistributedFaithful sm initSM 5586) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 679 l16btSmPhl5587
    5585 5586 5587 fw_per_head_linear
    (by native_decide) l16bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l16bt_nonempty_sm 680) (l16bt_sm_not_written 680 5587 (by decide))
    (l16bt_nonempty_sm 679) (l16bt_sm_not_written 679 5585 (by decide))
    (l16bt_w5586_sm_drop 679)
  intro s
  unfold l16btSmPhl5587
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5585 5586 5587 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10523 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10523 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10521)
        (denoteGraphDistributedFaithful pm initPM 5586) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1420 l16btPmPhl10523
    10521 5586 10523 fw_per_head_linear
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l16bt_nonempty_pm 1421) (l16bt_pm_not_written 1421 10523 (by decide))
    (l16bt_nonempty_pm 1420) (l16bt_pm_not_written 1420 10521 (by decide))
    (l16bt_w5586_pm_drop 1420)
  intro s
  unfold l16btPmPhl10523
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 10521 5586 10523 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_red_pm10524 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10524 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10522)
        (denoteGraphDistributedFaithful pm initPM 5586) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1421 l16btPmPhl10524
    10522 5586 10524 fw_per_head_linear
    (by native_decide) l16bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l16bt_nonempty_pm 1422) (l16bt_pm_not_written 1422 10524 (by decide))
    (l16bt_nonempty_pm 1421) (l16bt_pm_not_written 1421 10522 (by decide))
    (l16bt_w5586_pm_drop 1421)
  intro s
  unfold l16btPmPhl10524
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 10522 5586 10524 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l16bt_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W A B : Tid) (shard : Shape)
    (htp : gW.tps = [{rank := 0, tid := A}, {rank := 1, tid := B}])
    (hgd : gW.gatherDim = 0) (hrep : gW.replicated = false) (hts : gW.ts = W)
    (htpShapes : gW.tpShapes = [shard, shard]) (hshard : shard ≠ [1]) :
    initSM W = allGatherPrimDimN 0 2 0 [initPM A, initPM B] := by
  have h := hInit gW hgW
  unfold InitGoalHolds at h
  have hshapes := h.2.1
  rw [htp, htpShapes] at hshapes
  simp only [List.map, List.cons.injEq, and_true] at hshapes
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated gW pm.numRanks _ hrep, htp, hts, hgd] at hval
  simp only [List.map] at hval
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
        (by rw [hshapes.1]; exact hshard)] at hval
  rw [show pm.numRanks = 2 from rfl] at hval
  exact hval

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_weight_eq (initSM initPM : Store)
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
private theorem l16bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l16bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l16bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5541) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5541).shape = [2] := by
    rw [l16bt_pmFinal initPM 5541 l16bt_cu_not_written]
    exact hPM 5541 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5541)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5561 (block-3 MoE expert layer).
theorem recon_zigzagGoal_5561_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5561)
      (denoteGraphDistributedFaithful pm initPM 10429)
      (denoteGraphDistributedFaithful pm initPM 10430)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8318_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5556_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5557_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l16bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8318)
      (denoteGraphDistributedFaithful pm initPM 16320)
      (denoteGraphDistributedFaithful pm initPM 16343)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5556)
      (denoteGraphDistributedFaithful pm initPM 10419)
      (denoteGraphDistributedFaithful pm initPM 10420)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5557)
      (denoteGraphDistributedFaithful pm initPM 10421)
      (denoteGraphDistributedFaithful pm initPM 10422)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5559 = allGatherPrimDimN 0 2 0 [initPM 10425, initPM 10426] :=
    l16bt_weight_bridge initSM initPM hInit initGoal_5559 (by native_decide)
      5559 10425 10426 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5560 = allGatherPrimDimN 0 2 0 [initPM 10427, initPM 10428] :=
    l16bt_weight_bridge initSM initPM hInit initGoal_5560 (by native_decide)
      5560 10427 10428 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5559).shape = [64, 1024, 1024] :=
    hSM 5559 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5560).shape = [64, 1024, 512] :=
    hSM 5560 [64, 1024, 512] (by native_decide)
  rw [l16bt_red_sm5561 initSM, l16bt_red_pm10429 initPM, l16bt_red_pm10430 initPM]
  rw [l16bt_sm_leaf initSM 5559 (by decide), l16bt_sm_leaf initSM 5560 (by decide),
    l16bt_pm_leaf initPM 10425 (by decide), l16bt_pm_leaf initPM 10426 (by decide),
    l16bt_pm_leaf initPM 10427 (by decide), l16bt_pm_leaf initPM 10428 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5559) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5560) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 10425, initPM 10426])
    (allGatherPrimDimN 0 2 0 [initPM 10427, initPM 10428])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5576 (`FW_reshape`).
theorem recon_zigzagGoal_5576_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5576)
      (denoteGraphDistributedFaithful pm initPM 10483)
      (denoteGraphDistributedFaithful pm initPM 10484)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5575_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16bt_red_sm5576 initSM, l16bt_red_pm10483 initPM, l16bt_red_pm10484 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5578 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5578_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5578)
      (denoteGraphDistributedFaithful pm initPM 10489)
      (denoteGraphDistributedFaithful pm initPM 10490)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5576_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5577 =
      denoteGraphDistributedFaithful pm initPM 5577 :=
    l16bt_weight_eq initSM initPM hInit 5577 initGoal_5577 (by native_decide)
      rfl rfl rfl rfl
      l16bt_weights_not_written.1.1 l16bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5577).shape = [1024, 512] :=
    l16bt_pm_weight_shape initPM hPM 5577 [1024, 512] (by native_decide)
      l16bt_weights_not_written.2.1
  rw [l16bt_red_sm5578 initSM, l16bt_red_pm10489 initPM, l16bt_red_pm10490 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5579 (`FW_view`).
theorem recon_zigzagGoal_5579_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5579)
      (denoteGraphDistributedFaithful pm initPM 10499)
      (denoteGraphDistributedFaithful pm initPM 10500)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5578_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16bt_red_sm5579 initSM, l16bt_red_pm10499 initPM, l16bt_red_pm10500 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5580 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5580_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5580)
      (denoteGraphDistributedFaithful pm initPM 10503)
      (denoteGraphDistributedFaithful pm initPM 10504)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5566_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5579_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5566)
      (denoteGraphDistributedFaithful pm initPM 10443)
      (denoteGraphDistributedFaithful pm initPM 10444)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5579)
      (denoteGraphDistributedFaithful pm initPM 10499)
      (denoteGraphDistributedFaithful pm initPM 10500)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l16bt_red_sm5580 initSM, l16bt_red_pm10503 initPM, l16bt_red_pm10504 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5581 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5581_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5581)
      (denoteGraphDistributedFaithful pm initPM 10507)
      (denoteGraphDistributedFaithful pm initPM 10508)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5561_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5580_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5561)
      (denoteGraphDistributedFaithful pm initPM 10429)
      (denoteGraphDistributedFaithful pm initPM 10430)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5580)
      (denoteGraphDistributedFaithful pm initPM 10503)
      (denoteGraphDistributedFaithful pm initPM 10504)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l16bt_red_sm5581 initSM, l16bt_red_pm10507 initPM, l16bt_red_pm10508 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5582 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5582_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5582)
      (denoteGraphDistributedFaithful pm initPM 10513)
      (denoteGraphDistributedFaithful pm initPM 10514)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5581_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16bt_red_sm5582 initSM, l16bt_red_pm10513 initPM, l16bt_red_pm10514 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5583 (`FW_add`, residual join).
theorem recon_zigzagGoal_5583_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5583)
      (denoteGraphDistributedFaithful pm initPM 10517)
      (denoteGraphDistributedFaithful pm initPM 10518)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8307_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5582_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8307)
      (denoteGraphDistributedFaithful pm initPM 16301)
      (denoteGraphDistributedFaithful pm initPM 16309)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5582)
      (denoteGraphDistributedFaithful pm initPM 10513)
      (denoteGraphDistributedFaithful pm initPM 10514)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l16bt_red_sm5583 initSM, l16bt_red_pm10517 initPM, l16bt_red_pm10518 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8334 (multiref position 0 off 5583).
theorem recon_zigzagGoal_8334_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8334)
      (denoteGraphDistributedFaithful pm initPM 16359)
      (denoteGraphDistributedFaithful pm initPM 16367)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5583_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16bt_red_sm8334 initSM, l16bt_red_pm16359 initPM, l16bt_red_pm16367 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8338 (multiref position 1
-- off 5583): the cross-layer residual bypass consumed by block 4's `FW_add`.
theorem recon_zigzagGoal_8338_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8338)
      (denoteGraphDistributedFaithful pm initPM 16363)
      (denoteGraphDistributedFaithful pm initPM 16371)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5583_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l16bt_red_sm8338 initSM, l16bt_red_pm16363 initPM, l16bt_red_pm16371 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5585 (`FW_rms_norm`).
theorem recon_zigzagGoal_5585_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5585)
      (denoteGraphDistributedFaithful pm initPM 10521)
      (denoteGraphDistributedFaithful pm initPM 10522)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8334_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5584 =
      denoteGraphDistributedFaithful pm initPM 5584 :=
    l16bt_weight_eq initSM initPM hInit 5584 initGoal_5584 (by native_decide)
      rfl rfl rfl rfl
      l16bt_weights_not_written.1.2.1 l16bt_weights_not_written.2.2.1
  rw [l16bt_red_sm5585 initSM, l16bt_red_pm10521 initPM, l16bt_red_pm10522 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5587
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 4's
-- zigzag attention entry.
theorem recon_zigzagGoal_5587_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5587)
      (denoteGraphDistributedFaithful pm initPM 10523)
      (denoteGraphDistributedFaithful pm initPM 10524)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5585_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5586 =
      denoteGraphDistributedFaithful pm initPM 5586 :=
    l16bt_weight_eq initSM initPM hInit 5586 initGoal_5586 (by native_decide)
      rfl rfl rfl rfl
      l16bt_weights_not_written.1.2.2 l16bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5586).shape = [16, 64, 1024] :=
    l16bt_pm_weight_shape initPM hPM 5586 [16, 64, 1024] (by native_decide)
      l16bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5585)
      (denoteGraphDistributedFaithful pm initPM 10521)
      (denoteGraphDistributedFaithful pm initPM 10522)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l16bt_red_sm5587 initSM, l16bt_red_pm10523 initPM, l16bt_red_pm10524 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
