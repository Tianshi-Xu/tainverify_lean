/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L19FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L18FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-7 tail (MoE join -> block-7 Q)

Mechanical transport of the (green) block-6 tail `L13FaithfulBlockTail` to
block 7.  The block-7 cu tensor is **5688**.

* SM 772 `FW_all2all_moe_gmm [8435,5703,5704,5706,5707] -> [5708]` (PM 1606/1609 -> 10945/10946)
* SM 775 `FW_reshape [5722] -> [5723]`                             (PM 1612/1613 -> 10999/11000)
* SM 776 `FW_mix_precision_linear [5723,5724] -> [5725]`           (PM 1614/1615 -> 11005/11006)
* SM 777 `FW_view [5725] -> [5726]`                                (PM 1616/1617 -> 11015/11016)
* SM 778 `FW_mul [5713,5726] -> [5727]` (broadcast `[N,1]x[N,1024]`)(PM 1618/1619 -> 11019/11020)
* SM 779 `FW_add [5708,5727] -> [5728]`                            (PM 1620/1621 -> 11023/11024)
* SM 780 `FW_float [5728] -> [5729]`                               (PM 1622/1623 -> 11029/11030)
* SM 781 `FW_add [8424,5729] -> [5730]`                            (PM 1624/1625 -> 11033/11034)
* SM 782 `FW_multiref [5730] -> [8451,8455]`                       (PM 1626/1627)
* SM 783 `FW_rms_norm [8451,5731] -> [5732]`                       (PM 1628/1629 -> 11037/11038)
* SM 784 `FW_per_head_mix_precision_linear [5732,5733] -> [5734]`  (PM 1630/1631 -> 11039/11040)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8455_faithful` -- the cross-layer residual bypass consumed by
  block 7 (SM node 791 `FW_add`);
* `recon_zigzagGoal_5734_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 7's zigzag attention entry.

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

private theorem l19bt_reduce7
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

private theorem l19bt_reduce5
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
private def l19btSmMoE5708 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8435,5703,5704,5706,5707], outs := [5708],
    params := [64,0,64,8] }
private def l19btSmResh5723 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5722], outs := [5723],
    params := [4096,512] }
private def l19btSmMPL5725 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5723,5724], outs := [5725] }
private def l19btSmView5726 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5725], outs := [5726],
    params := [4096,1024] }
private def l19btSmMul5727 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5713,5726], outs := [5727] }
private def l19btSmAdd5728 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5708,5727], outs := [5728] }
private def l19btSmFloat5729 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5728], outs := [5729] }
private def l19btSmAdd5730 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8424,5729], outs := [5730] }
private def l19btSmMref5730 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5730], outs := [8451,8455],
    params := [2] }
private def l19btSmRms5732 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8451,5731], outs := [5732] }
private def l19btSmPhl5734 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5732,5733], outs := [5734] }

private def l19btPmMoE10945 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16554,10935,10937,10941,10943], outs := [10945],
    params := [64,0,32,8] }
private def l19btPmMoE10946 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16577,10936,10938,10942,10944], outs := [10946],
    params := [64,32,64,8] }
private def l19btPmResh10999 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10997], outs := [10999],
    params := [2048,512] }
private def l19btPmResh11000 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10998], outs := [11000],
    params := [2048,512] }
private def l19btPmMPL11005 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10999,5724], outs := [11005] }
private def l19btPmMPL11006 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11000,5724], outs := [11006] }
private def l19btPmView11015 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11005], outs := [11015],
    params := [2048,1024] }
private def l19btPmView11016 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11006], outs := [11016],
    params := [2048,1024] }
private def l19btPmMul11019 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10959,11015], outs := [11019] }
private def l19btPmMul11020 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10960,11016], outs := [11020] }
private def l19btPmAdd11023 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10945,11019], outs := [11023] }
private def l19btPmAdd11024 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10946,11020], outs := [11024] }
private def l19btPmFloat11029 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11023], outs := [11029] }
private def l19btPmFloat11030 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11024], outs := [11030] }
private def l19btPmAdd11033 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16535,11029], outs := [11033] }
private def l19btPmAdd11034 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16543,11030], outs := [11034] }
private def l19btPmMref11033 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11033], outs := [16593,16597],
    params := [2] }
private def l19btPmMref11034 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11034], outs := [16601,16605],
    params := [2] }
private def l19btPmRms11037 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16593,5731], outs := [11037] }
private def l19btPmRms11038 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16601,5731], outs := [11038] }
private def l19btPmPhl11039 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11037,5733], outs := [11039] }
private def l19btPmPhl11040 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11038,5733], outs := [11040] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l19bt_sm_node_facts :
    sm.nodes[772]'(by native_decide) = l19btSmMoE5708 ∧
    sm.nodes[775]'(by native_decide) = l19btSmResh5723 ∧
    sm.nodes[776]'(by native_decide) = l19btSmMPL5725 ∧
    sm.nodes[777]'(by native_decide) = l19btSmView5726 ∧
    sm.nodes[778]'(by native_decide) = l19btSmMul5727 ∧
    sm.nodes[779]'(by native_decide) = l19btSmAdd5728 ∧
    sm.nodes[780]'(by native_decide) = l19btSmFloat5729 ∧
    sm.nodes[781]'(by native_decide) = l19btSmAdd5730 ∧
    sm.nodes[782]'(by native_decide) = l19btSmMref5730 ∧
    sm.nodes[783]'(by native_decide) = l19btSmRms5732 ∧
    sm.nodes[784]'(by native_decide) = l19btSmPhl5734 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l19bt_pm_node_facts :
    pm.nodes[1606]'(by native_decide) = l19btPmMoE10945 ∧
    pm.nodes[1609]'(by native_decide) = l19btPmMoE10946 ∧
    pm.nodes[1612]'(by native_decide) = l19btPmResh10999 ∧
    pm.nodes[1613]'(by native_decide) = l19btPmResh11000 ∧
    pm.nodes[1614]'(by native_decide) = l19btPmMPL11005 ∧
    pm.nodes[1615]'(by native_decide) = l19btPmMPL11006 ∧
    pm.nodes[1616]'(by native_decide) = l19btPmView11015 ∧
    pm.nodes[1617]'(by native_decide) = l19btPmView11016 ∧
    pm.nodes[1618]'(by native_decide) = l19btPmMul11019 ∧
    pm.nodes[1619]'(by native_decide) = l19btPmMul11020 ∧
    pm.nodes[1620]'(by native_decide) = l19btPmAdd11023 ∧
    pm.nodes[1621]'(by native_decide) = l19btPmAdd11024 ∧
    pm.nodes[1622]'(by native_decide) = l19btPmFloat11029 ∧
    pm.nodes[1623]'(by native_decide) = l19btPmFloat11030 ∧
    pm.nodes[1624]'(by native_decide) = l19btPmAdd11033 ∧
    pm.nodes[1625]'(by native_decide) = l19btPmAdd11034 ∧
    pm.nodes[1626]'(by native_decide) = l19btPmMref11033 ∧
    pm.nodes[1627]'(by native_decide) = l19btPmMref11034 ∧
    pm.nodes[1628]'(by native_decide) = l19btPmRms11037 ∧
    pm.nodes[1629]'(by native_decide) = l19btPmRms11038 ∧
    pm.nodes[1630]'(by native_decide) = l19btPmPhl11039 ∧
    pm.nodes[1631]'(by native_decide) = l19btPmPhl11040 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l19bt_buddy_facts :
    sm.replicaBuddies l19btSmMoE5708 = [l19btSmMoE5708] ∧
    pm.replicaBuddies l19btPmMoE10945 = [l19btPmMoE10945, l19btPmMoE10946] ∧
    pm.replicaBuddies l19btPmMoE10946 = [l19btPmMoE10945, l19btPmMoE10946] := by
  native_decide

private theorem l19bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l19bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l19bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5724 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5731 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5733 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5724 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5731 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5733 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l19bt_cu_not_written : ∀ n ∈ pm.nodes, 5688 ∉ n.outs := by
  native_decide

private theorem l19bt_w5724_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5724 ∉ n.outs := by
  intro n hn
  exact l19bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l19bt_w5724_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5724 ∉ n.outs := by
  intro n hn
  exact l19bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l19bt_w5731_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5731 ∉ n.outs := by
  intro n hn
  exact l19bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l19bt_w5731_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5731 ∉ n.outs := by
  intro n hn
  exact l19bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l19bt_w5733_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5733 ∉ n.outs := by
  intro n hn
  exact l19bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l19bt_w5733_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5733 ∉ n.outs := by
  intro n hn
  exact l19bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l19bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(773, 5708), (772, 8435), (772, 5703), (772, 5704), (772, 5706), (772, 5707), (776, 5723), (775, 5722), (777, 5725), (776, 5723), (778, 5726), (777, 5725), (779, 5727), (778, 5713), (778, 5726), (780, 5728), (779, 5708), (779, 5727), (781, 5729), (780, 5728), (782, 5730), (781, 8424), (781, 5729), (783, 8451), (783, 8455), (782, 5730), (784, 5732), (783, 8451), (785, 5734), (784, 5732)]) :
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
private theorem l19bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1607, 10945), (1606, 16554), (1606, 10935), (1606, 10937), (1606, 10941), (1606, 10943), (1606, 10942), (1606, 10944), (1610, 10946), (1609, 16577), (1609, 10936), (1609, 10938), (1609, 10941), (1609, 10942), (1609, 10943), (1609, 10944), (1613, 10999), (1612, 10997), (1614, 11000), (1613, 10998), (1615, 11005), (1614, 10999), (1616, 11006), (1615, 11000), (1617, 11015), (1616, 11005), (1618, 11016), (1617, 11006), (1619, 11019), (1618, 10959), (1618, 11015), (1620, 11020), (1619, 10960), (1619, 11016), (1621, 11023), (1620, 10945), (1620, 11019), (1622, 11024), (1621, 10946), (1621, 11020), (1623, 11029), (1622, 11023), (1624, 11030), (1623, 11024), (1625, 11033), (1624, 16535), (1624, 11029), (1626, 11034), (1625, 16543), (1625, 11030), (1627, 16593), (1627, 16597), (1626, 11033), (1628, 16601), (1628, 16605), (1627, 11034), (1629, 11037), (1628, 16593), (1630, 11038), (1629, 16601), (1631, 11039), (1630, 11037), (1632, 11040), (1631, 11038)]) :
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
private theorem l19bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5706, 5707]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l19bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [10941, 10942, 10943, 10944]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l19bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5706, 5707]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l19bt_sm_leaf_not_written tid h)

private theorem l19bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [10941, 10942, 10943, 10944]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l19bt_pm_leaf_not_written tid h)

private theorem l19bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5708 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5708 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5708 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8435)
        (denoteGraphDistributedFaithful sm initSM 5703)
        (denoteGraphDistributedFaithful sm initSM 5704)
        [denoteGraphDistributedFaithful sm initSM 5706]
        [denoteGraphDistributedFaithful sm initSM 5707]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l19bt_reduce5 sm initSM 772 l19btSmMoE5708
    8435 5703 5704 5706 5707 5708
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l19bt_sm_node_facts.1 ?_
    (l19bt_nonempty_sm 773) (l19bt_sm_not_written 773 5708 (by decide))
    (l19bt_nonempty_sm 772) (l19bt_sm_not_written 772 8435 (by decide))
    (l19bt_sm_not_written 772 5703 (by decide))
    (l19bt_sm_not_written 772 5704 (by decide))
    (l19bt_sm_not_written 772 5706 (by decide))
    (l19bt_sm_not_written 772 5707 (by decide))
  intro s
  have hb := l19bt_buddy_facts.1
  unfold l19btSmMoE5708 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8435 5703 5704 5706 5707 5708 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm10945 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10945 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16554)
        (denoteGraphDistributedFaithful pm initPM 10935)
        (denoteGraphDistributedFaithful pm initPM 10937)
        [denoteGraphDistributedFaithful pm initPM 10941,
         denoteGraphDistributedFaithful pm initPM 10942]
        [denoteGraphDistributedFaithful pm initPM 10943,
         denoteGraphDistributedFaithful pm initPM 10944]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l19bt_reduce7 pm initPM 1606 l19btPmMoE10945
    16554 10935 10937 10941 10943 10942 10944 10945
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l19bt_pm_node_facts.1 ?_
    (l19bt_nonempty_pm 1607) (l19bt_pm_not_written 1607 10945 (by decide))
    (l19bt_nonempty_pm 1606) (l19bt_pm_not_written 1606 16554 (by decide))
    (l19bt_pm_not_written 1606 10935 (by decide))
    (l19bt_pm_not_written 1606 10937 (by decide))
    (l19bt_pm_not_written 1606 10941 (by decide))
    (l19bt_pm_not_written 1606 10943 (by decide))
    (l19bt_pm_not_written 1606 10942 (by decide))
    (l19bt_pm_not_written 1606 10944 (by decide))
  intro s
  have hb := l19bt_buddy_facts.2.1
  unfold l19btPmMoE10945 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16554 10935 10937 10941 10943 10945 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm10946 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10946 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16577)
        (denoteGraphDistributedFaithful pm initPM 10936)
        (denoteGraphDistributedFaithful pm initPM 10938)
        [denoteGraphDistributedFaithful pm initPM 10941,
         denoteGraphDistributedFaithful pm initPM 10942]
        [denoteGraphDistributedFaithful pm initPM 10943,
         denoteGraphDistributedFaithful pm initPM 10944]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l19bt_reduce7 pm initPM 1609 l19btPmMoE10946
    16577 10936 10938 10941 10942 10943 10944 10946
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l19bt_pm_node_facts.2.1 ?_
    (l19bt_nonempty_pm 1610) (l19bt_pm_not_written 1610 10946 (by decide))
    (l19bt_nonempty_pm 1609) (l19bt_pm_not_written 1609 16577 (by decide))
    (l19bt_pm_not_written 1609 10936 (by decide))
    (l19bt_pm_not_written 1609 10938 (by decide))
    (l19bt_pm_not_written 1609 10941 (by decide))
    (l19bt_pm_not_written 1609 10942 (by decide))
    (l19bt_pm_not_written 1609 10943 (by decide))
    (l19bt_pm_not_written 1609 10944 (by decide))
  intro s
  have hb := l19bt_buddy_facts.2.2
  unfold l19btPmMoE10946 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16577 10936 10938 10942 10944 10946 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5723 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5723 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5723 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5722) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 775 l19btSmResh5723
    5722 5723 (fun x => fw_view [4096,512] x)
    (by native_decide) l19bt_sm_node_facts.2.1 ?_
    (l19bt_nonempty_sm 776) (l19bt_sm_not_written 776 5723 (by decide))
    (l19bt_nonempty_sm 775) (l19bt_sm_not_written 775 5722 (by decide))
  intro s
  unfold l19btSmResh5723
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5722 5723 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm10999 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10999 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10997) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1612 l19btPmResh10999
    10997 10999 (fun x => fw_view [2048,512] x)
    (by native_decide) l19bt_pm_node_facts.2.2.1 ?_
    (l19bt_nonempty_pm 1613) (l19bt_pm_not_written 1613 10999 (by decide))
    (l19bt_nonempty_pm 1612) (l19bt_pm_not_written 1612 10997 (by decide))
  intro s
  unfold l19btPmResh10999
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10997 10999 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11000 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11000 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10998) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1613 l19btPmResh11000
    10998 11000 (fun x => fw_view [2048,512] x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.1 ?_
    (l19bt_nonempty_pm 1614) (l19bt_pm_not_written 1614 11000 (by decide))
    (l19bt_nonempty_pm 1613) (l19bt_pm_not_written 1613 10998 (by decide))
  intro s
  unfold l19btPmResh11000
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10998 11000 [2048,512]

/-! ### Node reductions: down-projection 5725 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5725 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5725 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5723)
        (denoteGraphDistributedFaithful sm initSM 5724) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 776 l19btSmMPL5725
    5723 5724 5725 fw_linear
    (by native_decide) l19bt_sm_node_facts.2.2.1 ?_
    (l19bt_nonempty_sm 777) (l19bt_sm_not_written 777 5725 (by decide))
    (l19bt_nonempty_sm 776) (l19bt_sm_not_written 776 5723 (by decide))
    (l19bt_w5724_sm_drop 776)
  intro s
  unfold l19btSmMPL5725
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5723 5724 5725

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11005 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11005 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10999)
        (denoteGraphDistributedFaithful pm initPM 5724) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1614 l19btPmMPL11005
    10999 5724 11005 fw_linear
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1615) (l19bt_pm_not_written 1615 11005 (by decide))
    (l19bt_nonempty_pm 1614) (l19bt_pm_not_written 1614 10999 (by decide))
    (l19bt_w5724_pm_drop 1614)
  intro s
  unfold l19btPmMPL11005
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10999 5724 11005

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11006 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11006 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11000)
        (denoteGraphDistributedFaithful pm initPM 5724) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1615 l19btPmMPL11006
    11000 5724 11006 fw_linear
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1616) (l19bt_pm_not_written 1616 11006 (by decide))
    (l19bt_nonempty_pm 1615) (l19bt_pm_not_written 1615 11000 (by decide))
    (l19bt_w5724_pm_drop 1615)
  intro s
  unfold l19btPmMPL11006
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11000 5724 11006

/-! ### Node reductions: view 5726 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5726 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5726 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5725) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 777 l19btSmView5726
    5725 5726 (fun x => fw_view [4096,1024] x)
    (by native_decide) l19bt_sm_node_facts.2.2.2.1 ?_
    (l19bt_nonempty_sm 778) (l19bt_sm_not_written 778 5726 (by decide))
    (l19bt_nonempty_sm 777) (l19bt_sm_not_written 777 5725 (by decide))
  intro s
  unfold l19btSmView5726
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5725 5726

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11015 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11015 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11005) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1616 l19btPmView11015
    11005 11015 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1617) (l19bt_pm_not_written 1617 11015 (by decide))
    (l19bt_nonempty_pm 1616) (l19bt_pm_not_written 1616 11005 (by decide))
  intro s
  unfold l19btPmView11015
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11005 11015

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11016 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11016 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11006) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1617 l19btPmView11016
    11006 11016 (fun x => fw_view [2048,1024] x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1618) (l19bt_pm_not_written 1618 11016 (by decide))
    (l19bt_nonempty_pm 1617) (l19bt_pm_not_written 1617 11006 (by decide))
  intro s
  unfold l19btPmView11016
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11006 11016

/-! ### Node reductions: gated multiply 5727 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5727 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5727 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5713)
        (denoteGraphDistributedFaithful sm initSM 5726) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 778 l19btSmMul5727
    5713 5726 5727 elemwiseMul
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.1 ?_
    (l19bt_nonempty_sm 779) (l19bt_sm_not_written 779 5727 (by decide))
    (l19bt_nonempty_sm 778) (l19bt_sm_not_written 778 5713 (by decide))
    (l19bt_sm_not_written 778 5726 (by decide))
  intro s
  unfold l19btSmMul5727
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5713 5726 5727

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11019 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11019 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10959)
        (denoteGraphDistributedFaithful pm initPM 11015) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1618 l19btPmMul11019
    10959 11015 11019 elemwiseMul
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1619) (l19bt_pm_not_written 1619 11019 (by decide))
    (l19bt_nonempty_pm 1618) (l19bt_pm_not_written 1618 10959 (by decide))
    (l19bt_pm_not_written 1618 11015 (by decide))
  intro s
  unfold l19btPmMul11019
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 10959 11015 11019

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11020 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11020 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10960)
        (denoteGraphDistributedFaithful pm initPM 11016) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1619 l19btPmMul11020
    10960 11016 11020 elemwiseMul
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1620) (l19bt_pm_not_written 1620 11020 (by decide))
    (l19bt_nonempty_pm 1619) (l19bt_pm_not_written 1619 10960 (by decide))
    (l19bt_pm_not_written 1619 11016 (by decide))
  intro s
  unfold l19btPmMul11020
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 10960 11016 11020

/-! ### Node reductions: MoE join 5728 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5728 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5728 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5708)
        (denoteGraphDistributedFaithful sm initSM 5727) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 779 l19btSmAdd5728
    5708 5727 5728 elemwiseAdd
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l19bt_nonempty_sm 780) (l19bt_sm_not_written 780 5728 (by decide))
    (l19bt_nonempty_sm 779) (l19bt_sm_not_written 779 5708 (by decide))
    (l19bt_sm_not_written 779 5727 (by decide))
  intro s
  unfold l19btSmAdd5728
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5708 5727 5728

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11023 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11023 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10945)
        (denoteGraphDistributedFaithful pm initPM 11019) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1620 l19btPmAdd11023
    10945 11019 11023 elemwiseAdd
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1621) (l19bt_pm_not_written 1621 11023 (by decide))
    (l19bt_nonempty_pm 1620) (l19bt_pm_not_written 1620 10945 (by decide))
    (l19bt_pm_not_written 1620 11019 (by decide))
  intro s
  unfold l19btPmAdd11023
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 10945 11019 11023

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11024 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11024 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10946)
        (denoteGraphDistributedFaithful pm initPM 11020) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1621 l19btPmAdd11024
    10946 11020 11024 elemwiseAdd
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1622) (l19bt_pm_not_written 1622 11024 (by decide))
    (l19bt_nonempty_pm 1621) (l19bt_pm_not_written 1621 10946 (by decide))
    (l19bt_pm_not_written 1621 11020 (by decide))
  intro s
  unfold l19btPmAdd11024
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 10946 11020 11024

/-! ### Node reductions: float 5729 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5729 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5729 =
      denoteGraphDistributedFaithful sm initSM 5728 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 780 l19btSmFloat5729
    5728 5729 (fun x => x)
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_sm 781) (l19bt_sm_not_written 781 5729 (by decide))
    (l19bt_nonempty_sm 780) (l19bt_sm_not_written 780 5728 (by decide))
  intro s
  unfold l19btSmFloat5729
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5728 5729 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11029 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11029 =
      denoteGraphDistributedFaithful pm initPM 11023 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1622 l19btPmFloat11029
    11023 11029 (fun x => x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1623) (l19bt_pm_not_written 1623 11029 (by decide))
    (l19bt_nonempty_pm 1622) (l19bt_pm_not_written 1622 11023 (by decide))
  intro s
  unfold l19btPmFloat11029
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 11023 11029 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11030 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11030 =
      denoteGraphDistributedFaithful pm initPM 11024 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1623 l19btPmFloat11030
    11024 11030 (fun x => x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1624) (l19bt_pm_not_written 1624 11030 (by decide))
    (l19bt_nonempty_pm 1623) (l19bt_pm_not_written 1623 11024 (by decide))
  intro s
  unfold l19btPmFloat11030
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 11024 11030 []

/-! ### Node reductions: residual join 5730 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5730 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5730 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8424)
        (denoteGraphDistributedFaithful sm initSM 5729) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 781 l19btSmAdd5730
    8424 5729 5730 elemwiseAdd
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_sm 782) (l19bt_sm_not_written 782 5730 (by decide))
    (l19bt_nonempty_sm 781) (l19bt_sm_not_written 781 8424 (by decide))
    (l19bt_sm_not_written 781 5729 (by decide))
  intro s
  unfold l19btSmAdd5730
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8424 5729 5730

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11033 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11033 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16535)
        (denoteGraphDistributedFaithful pm initPM 11029) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1624 l19btPmAdd11033
    16535 11029 11033 elemwiseAdd
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1625) (l19bt_pm_not_written 1625 11033 (by decide))
    (l19bt_nonempty_pm 1624) (l19bt_pm_not_written 1624 16535 (by decide))
    (l19bt_pm_not_written 1624 11029 (by decide))
  intro s
  unfold l19btPmAdd11033
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16535 11029 11033

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11034 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11034 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16543)
        (denoteGraphDistributedFaithful pm initPM 11030) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1625 l19btPmAdd11034
    16543 11030 11034 elemwiseAdd
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1626) (l19bt_pm_not_written 1626 11034 (by decide))
    (l19bt_nonempty_pm 1625) (l19bt_pm_not_written 1625 16543 (by decide))
    (l19bt_pm_not_written 1625 11030 (by decide))
  intro s
  unfold l19btPmAdd11034
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16543 11030 11034

/-! ### Node reductions: 2-way multiref off 5730 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm8451 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8451 =
      denoteGraphDistributedFaithful sm initSM 5730 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 782 l19btSmMref5730
    5730 8451 (fun x => x)
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_sm 783) (l19bt_sm_not_written 783 8451 (by decide))
    (l19bt_nonempty_sm 782) (l19bt_sm_not_written 782 5730 (by decide))
  intro s
  unfold l19btSmMref5730
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5730 8451 8455

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm8455 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8455 =
      denoteGraphDistributedFaithful sm initSM 5730 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 782 l19btSmMref5730
    5730 8455 (fun x => x)
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_sm 783) (l19bt_sm_not_written 783 8455 (by decide))
    (l19bt_nonempty_sm 782) (l19bt_sm_not_written 782 5730 (by decide))
  intro s
  unfold l19btSmMref5730
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5730 8451 8455 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm16593 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16593 =
      denoteGraphDistributedFaithful pm initPM 11033 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1626 l19btPmMref11033
    11033 16593 (fun x => x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1627) (l19bt_pm_not_written 1627 16593 (by decide))
    (l19bt_nonempty_pm 1626) (l19bt_pm_not_written 1626 11033 (by decide))
  intro s
  unfold l19btPmMref11033
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11033 16593 16597

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm16597 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16597 =
      denoteGraphDistributedFaithful pm initPM 11033 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1626 l19btPmMref11033
    11033 16597 (fun x => x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1627) (l19bt_pm_not_written 1627 16597 (by decide))
    (l19bt_nonempty_pm 1626) (l19bt_pm_not_written 1626 11033 (by decide))
  intro s
  unfold l19btPmMref11033
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11033 16593 16597 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm16601 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16601 =
      denoteGraphDistributedFaithful pm initPM 11034 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1627 l19btPmMref11034
    11034 16601 (fun x => x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1628) (l19bt_pm_not_written 1628 16601 (by decide))
    (l19bt_nonempty_pm 1627) (l19bt_pm_not_written 1627 11034 (by decide))
  intro s
  unfold l19btPmMref11034
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11034 16601 16605

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm16605 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16605 =
      denoteGraphDistributedFaithful pm initPM 11034 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1627 l19btPmMref11034
    11034 16605 (fun x => x)
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1628) (l19bt_pm_not_written 1628 16605 (by decide))
    (l19bt_nonempty_pm 1627) (l19bt_pm_not_written 1627 11034 (by decide))
  intro s
  unfold l19btPmMref11034
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11034 16601 16605 (by decide)

/-! ### Node reductions: RMSNorm 5732 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5732 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5732 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8451)
        (denoteGraphDistributedFaithful sm initSM 5731) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 783 l19btSmRms5732
    8451 5731 5732 fw_rms_norm
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_sm 784) (l19bt_sm_not_written 784 5732 (by decide))
    (l19bt_nonempty_sm 783) (l19bt_sm_not_written 783 8451 (by decide))
    (l19bt_w5731_sm_drop 783)
  intro s
  unfold l19btSmRms5732
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8451 5731 5732

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11037 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11037 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16593)
        (denoteGraphDistributedFaithful pm initPM 5731) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1628 l19btPmRms11037
    16593 5731 11037 fw_rms_norm
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1629) (l19bt_pm_not_written 1629 11037 (by decide))
    (l19bt_nonempty_pm 1628) (l19bt_pm_not_written 1628 16593 (by decide))
    (l19bt_w5731_pm_drop 1628)
  intro s
  unfold l19btPmRms11037
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16593 5731 11037

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11038 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11038 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16601)
        (denoteGraphDistributedFaithful pm initPM 5731) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1629 l19btPmRms11038
    16601 5731 11038 fw_rms_norm
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1630) (l19bt_pm_not_written 1630 11038 (by decide))
    (l19bt_nonempty_pm 1629) (l19bt_pm_not_written 1629 16601 (by decide))
    (l19bt_w5731_pm_drop 1629)
  intro s
  unfold l19btPmRms11038
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16601 5731 11038

/-! ### Node reductions: per-head Q projection 5734 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_sm5734 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5734 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5732)
        (denoteGraphDistributedFaithful sm initSM 5733) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 784 l19btSmPhl5734
    5732 5733 5734 fw_per_head_linear
    (by native_decide) l19bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l19bt_nonempty_sm 785) (l19bt_sm_not_written 785 5734 (by decide))
    (l19bt_nonempty_sm 784) (l19bt_sm_not_written 784 5732 (by decide))
    (l19bt_w5733_sm_drop 784)
  intro s
  unfold l19btSmPhl5734
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5732 5733 5734 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11039 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11039 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11037)
        (denoteGraphDistributedFaithful pm initPM 5733) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1630 l19btPmPhl11039
    11037 5733 11039 fw_per_head_linear
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l19bt_nonempty_pm 1631) (l19bt_pm_not_written 1631 11039 (by decide))
    (l19bt_nonempty_pm 1630) (l19bt_pm_not_written 1630 11037 (by decide))
    (l19bt_w5733_pm_drop 1630)
  intro s
  unfold l19btPmPhl11039
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 11037 5733 11039 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_red_pm11040 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11040 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11038)
        (denoteGraphDistributedFaithful pm initPM 5733) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1631 l19btPmPhl11040
    11038 5733 11040 fw_per_head_linear
    (by native_decide) l19bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l19bt_nonempty_pm 1632) (l19bt_pm_not_written 1632 11040 (by decide))
    (l19bt_nonempty_pm 1631) (l19bt_pm_not_written 1631 11038 (by decide))
    (l19bt_w5733_pm_drop 1631)
  intro s
  unfold l19btPmPhl11040
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 11038 5733 11040 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l19bt_weight_bridge (initSM initPM : Store)
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
private theorem l19bt_weight_eq (initSM initPM : Store)
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
private theorem l19bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l19bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l19bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5688) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5688).shape = [2] := by
    rw [l19bt_pmFinal initPM 5688 l19bt_cu_not_written]
    exact hPM 5688 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5688)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5708 (block-6 MoE expert layer).
theorem recon_zigzagGoal_5708_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5708)
      (denoteGraphDistributedFaithful pm initPM 10945)
      (denoteGraphDistributedFaithful pm initPM 10946)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8435_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5703_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5704_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l19bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8435)
      (denoteGraphDistributedFaithful pm initPM 16554)
      (denoteGraphDistributedFaithful pm initPM 16577)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5703)
      (denoteGraphDistributedFaithful pm initPM 10935)
      (denoteGraphDistributedFaithful pm initPM 10936)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5704)
      (denoteGraphDistributedFaithful pm initPM 10937)
      (denoteGraphDistributedFaithful pm initPM 10938)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5706 = allGatherPrimDimN 0 2 0 [initPM 10941, initPM 10942] :=
    l19bt_weight_bridge initSM initPM hInit initGoal_5706 (by native_decide)
      5706 10941 10942 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5707 = allGatherPrimDimN 0 2 0 [initPM 10943, initPM 10944] :=
    l19bt_weight_bridge initSM initPM hInit initGoal_5707 (by native_decide)
      5707 10943 10944 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5706).shape = [64, 1024, 1024] :=
    hSM 5706 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5707).shape = [64, 1024, 512] :=
    hSM 5707 [64, 1024, 512] (by native_decide)
  rw [l19bt_red_sm5708 initSM, l19bt_red_pm10945 initPM, l19bt_red_pm10946 initPM]
  rw [l19bt_sm_leaf initSM 5706 (by decide), l19bt_sm_leaf initSM 5707 (by decide),
    l19bt_pm_leaf initPM 10941 (by decide), l19bt_pm_leaf initPM 10942 (by decide),
    l19bt_pm_leaf initPM 10943 (by decide), l19bt_pm_leaf initPM 10944 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5706) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5707) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 10941, initPM 10942])
    (allGatherPrimDimN 0 2 0 [initPM 10943, initPM 10944])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5723 (`FW_reshape`).
theorem recon_zigzagGoal_5723_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5723)
      (denoteGraphDistributedFaithful pm initPM 10999)
      (denoteGraphDistributedFaithful pm initPM 11000)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5722_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19bt_red_sm5723 initSM, l19bt_red_pm10999 initPM, l19bt_red_pm11000 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5725 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5725_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5725)
      (denoteGraphDistributedFaithful pm initPM 11005)
      (denoteGraphDistributedFaithful pm initPM 11006)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5723_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5724 =
      denoteGraphDistributedFaithful pm initPM 5724 :=
    l19bt_weight_eq initSM initPM hInit 5724 initGoal_5724 (by native_decide)
      rfl rfl rfl rfl
      l19bt_weights_not_written.1.1 l19bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5724).shape = [1024, 512] :=
    l19bt_pm_weight_shape initPM hPM 5724 [1024, 512] (by native_decide)
      l19bt_weights_not_written.2.1
  rw [l19bt_red_sm5725 initSM, l19bt_red_pm11005 initPM, l19bt_red_pm11006 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5726 (`FW_view`).
theorem recon_zigzagGoal_5726_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5726)
      (denoteGraphDistributedFaithful pm initPM 11015)
      (denoteGraphDistributedFaithful pm initPM 11016)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5725_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19bt_red_sm5726 initSM, l19bt_red_pm11015 initPM, l19bt_red_pm11016 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5727 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5727_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5727)
      (denoteGraphDistributedFaithful pm initPM 11019)
      (denoteGraphDistributedFaithful pm initPM 11020)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5713_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5726_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5713)
      (denoteGraphDistributedFaithful pm initPM 10959)
      (denoteGraphDistributedFaithful pm initPM 10960)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5726)
      (denoteGraphDistributedFaithful pm initPM 11015)
      (denoteGraphDistributedFaithful pm initPM 11016)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l19bt_red_sm5727 initSM, l19bt_red_pm11019 initPM, l19bt_red_pm11020 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5728 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5728_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5728)
      (denoteGraphDistributedFaithful pm initPM 11023)
      (denoteGraphDistributedFaithful pm initPM 11024)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5708_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5727_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5708)
      (denoteGraphDistributedFaithful pm initPM 10945)
      (denoteGraphDistributedFaithful pm initPM 10946)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5727)
      (denoteGraphDistributedFaithful pm initPM 11019)
      (denoteGraphDistributedFaithful pm initPM 11020)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l19bt_red_sm5728 initSM, l19bt_red_pm11023 initPM, l19bt_red_pm11024 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5729 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5729_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5729)
      (denoteGraphDistributedFaithful pm initPM 11029)
      (denoteGraphDistributedFaithful pm initPM 11030)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5728_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19bt_red_sm5729 initSM, l19bt_red_pm11029 initPM, l19bt_red_pm11030 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5730 (`FW_add`, residual join).
theorem recon_zigzagGoal_5730_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5730)
      (denoteGraphDistributedFaithful pm initPM 11033)
      (denoteGraphDistributedFaithful pm initPM 11034)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8424_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5729_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8424)
      (denoteGraphDistributedFaithful pm initPM 16535)
      (denoteGraphDistributedFaithful pm initPM 16543)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5729)
      (denoteGraphDistributedFaithful pm initPM 11029)
      (denoteGraphDistributedFaithful pm initPM 11030)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l19bt_red_sm5730 initSM, l19bt_red_pm11033 initPM, l19bt_red_pm11034 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8451 (multiref position 0 off 5730).
theorem recon_zigzagGoal_8451_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8451)
      (denoteGraphDistributedFaithful pm initPM 16593)
      (denoteGraphDistributedFaithful pm initPM 16601)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5730_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19bt_red_sm8451 initSM, l19bt_red_pm16593 initPM, l19bt_red_pm16601 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8455 (multiref position 1
-- off 5730): the cross-layer residual bypass consumed by block 7's `FW_add`.
theorem recon_zigzagGoal_8455_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8455)
      (denoteGraphDistributedFaithful pm initPM 16597)
      (denoteGraphDistributedFaithful pm initPM 16605)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5730_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l19bt_red_sm8455 initSM, l19bt_red_pm16597 initPM, l19bt_red_pm16605 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5732 (`FW_rms_norm`).
theorem recon_zigzagGoal_5732_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5732)
      (denoteGraphDistributedFaithful pm initPM 11037)
      (denoteGraphDistributedFaithful pm initPM 11038)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8451_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5731 =
      denoteGraphDistributedFaithful pm initPM 5731 :=
    l19bt_weight_eq initSM initPM hInit 5731 initGoal_5731 (by native_decide)
      rfl rfl rfl rfl
      l19bt_weights_not_written.1.2.1 l19bt_weights_not_written.2.2.1
  rw [l19bt_red_sm5732 initSM, l19bt_red_pm11037 initPM, l19bt_red_pm11038 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5734
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 7's
-- zigzag attention entry.
theorem recon_zigzagGoal_5734_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5734)
      (denoteGraphDistributedFaithful pm initPM 11039)
      (denoteGraphDistributedFaithful pm initPM 11040)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5732_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5733 =
      denoteGraphDistributedFaithful pm initPM 5733 :=
    l19bt_weight_eq initSM initPM hInit 5733 initGoal_5733 (by native_decide)
      rfl rfl rfl rfl
      l19bt_weights_not_written.1.2.2 l19bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5733).shape = [16, 64, 1024] :=
    l19bt_pm_weight_shape initPM hPM 5733 [16, 64, 1024] (by native_decide)
      l19bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5732)
      (denoteGraphDistributedFaithful pm initPM 11037)
      (denoteGraphDistributedFaithful pm initPM 11038)
      (denoteGraphDistributedFaithful pm initPM 5688)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l19bt_red_sm5734 initSM, l19bt_red_pm11039 initPM, l19bt_red_pm11040 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
