/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L17FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L16FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-5 tail (MoE join -> block-5 Q)

Mechanical transport of the (green) block-4 tail `L13FaithfulBlockTail` to
block 5.  The block-5 cu tensor is **5590**.

* SM 702 `FW_all2all_moe_gmm [8357,5605,5606,5608,5609] -> [5610]` (PM 1466/1469 -> 10601/10602)
* SM 705 `FW_reshape [5624] -> [5625]`                             (PM 1472/1473 -> 10655/10656)
* SM 706 `FW_mix_precision_linear [5625,5626] -> [5627]`           (PM 1474/1475 -> 10661/10662)
* SM 707 `FW_view [5627] -> [5628]`                                (PM 1476/1477 -> 10671/10672)
* SM 708 `FW_mul [5615,5628] -> [5629]` (broadcast `[N,1]x[N,1024]`)(PM 1478/1479 -> 10675/10676)
* SM 709 `FW_add [5610,5629] -> [5630]`                            (PM 1480/1481 -> 10679/10680)
* SM 710 `FW_float [5630] -> [5631]`                               (PM 1482/1483 -> 10685/10686)
* SM 711 `FW_add [8346,5631] -> [5632]`                            (PM 1484/1485 -> 10689/10690)
* SM 712 `FW_multiref [5632] -> [8373,8377]`                       (PM 1486/1487)
* SM 713 `FW_rms_norm [8373,5633] -> [5634]`                       (PM 1488/1489 -> 10693/10694)
* SM 714 `FW_per_head_mix_precision_linear [5634,5635] -> [5636]`  (PM 1490/1491 -> 10695/10696)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8377_faithful` -- the cross-layer residual bypass consumed by
  block 5 (SM node 721 `FW_add`);
* `recon_zigzagGoal_5636_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 5's zigzag attention entry.

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

private theorem l17bt_reduce7
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

private theorem l17bt_reduce5
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
private def l17btSmMoE5610 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8357,5605,5606,5608,5609], outs := [5610],
    params := [64,0,64,8] }
private def l17btSmResh5625 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5624], outs := [5625],
    params := [4096,512] }
private def l17btSmMPL5627 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5625,5626], outs := [5627] }
private def l17btSmView5628 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5627], outs := [5628],
    params := [4096,1024] }
private def l17btSmMul5629 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5615,5628], outs := [5629] }
private def l17btSmAdd5630 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5610,5629], outs := [5630] }
private def l17btSmFloat5631 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5630], outs := [5631] }
private def l17btSmAdd5632 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8346,5631], outs := [5632] }
private def l17btSmMref5632 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5632], outs := [8373,8377],
    params := [2] }
private def l17btSmRms5634 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8373,5633], outs := [5634] }
private def l17btSmPhl5636 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5634,5635], outs := [5636] }

private def l17btPmMoE10601 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16398,10591,10593,10597,10599], outs := [10601],
    params := [64,0,32,8] }
private def l17btPmMoE10602 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16421,10592,10594,10598,10600], outs := [10602],
    params := [64,32,64,8] }
private def l17btPmResh10655 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10653], outs := [10655],
    params := [2048,512] }
private def l17btPmResh10656 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10654], outs := [10656],
    params := [2048,512] }
private def l17btPmMPL10661 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10655,5626], outs := [10661] }
private def l17btPmMPL10662 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10656,5626], outs := [10662] }
private def l17btPmView10671 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10661], outs := [10671],
    params := [2048,1024] }
private def l17btPmView10672 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10662], outs := [10672],
    params := [2048,1024] }
private def l17btPmMul10675 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10615,10671], outs := [10675] }
private def l17btPmMul10676 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10616,10672], outs := [10676] }
private def l17btPmAdd10679 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10601,10675], outs := [10679] }
private def l17btPmAdd10680 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10602,10676], outs := [10680] }
private def l17btPmFloat10685 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10679], outs := [10685] }
private def l17btPmFloat10686 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10680], outs := [10686] }
private def l17btPmAdd10689 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16379,10685], outs := [10689] }
private def l17btPmAdd10690 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16387,10686], outs := [10690] }
private def l17btPmMref10689 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10689], outs := [16437,16441],
    params := [2] }
private def l17btPmMref10690 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10690], outs := [16445,16449],
    params := [2] }
private def l17btPmRms10693 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16437,5633], outs := [10693] }
private def l17btPmRms10694 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16445,5633], outs := [10694] }
private def l17btPmPhl10695 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10693,5635], outs := [10695] }
private def l17btPmPhl10696 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10694,5635], outs := [10696] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l17bt_sm_node_facts :
    sm.nodes[702]'(by native_decide) = l17btSmMoE5610 ∧
    sm.nodes[705]'(by native_decide) = l17btSmResh5625 ∧
    sm.nodes[706]'(by native_decide) = l17btSmMPL5627 ∧
    sm.nodes[707]'(by native_decide) = l17btSmView5628 ∧
    sm.nodes[708]'(by native_decide) = l17btSmMul5629 ∧
    sm.nodes[709]'(by native_decide) = l17btSmAdd5630 ∧
    sm.nodes[710]'(by native_decide) = l17btSmFloat5631 ∧
    sm.nodes[711]'(by native_decide) = l17btSmAdd5632 ∧
    sm.nodes[712]'(by native_decide) = l17btSmMref5632 ∧
    sm.nodes[713]'(by native_decide) = l17btSmRms5634 ∧
    sm.nodes[714]'(by native_decide) = l17btSmPhl5636 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l17bt_pm_node_facts :
    pm.nodes[1466]'(by native_decide) = l17btPmMoE10601 ∧
    pm.nodes[1469]'(by native_decide) = l17btPmMoE10602 ∧
    pm.nodes[1472]'(by native_decide) = l17btPmResh10655 ∧
    pm.nodes[1473]'(by native_decide) = l17btPmResh10656 ∧
    pm.nodes[1474]'(by native_decide) = l17btPmMPL10661 ∧
    pm.nodes[1475]'(by native_decide) = l17btPmMPL10662 ∧
    pm.nodes[1476]'(by native_decide) = l17btPmView10671 ∧
    pm.nodes[1477]'(by native_decide) = l17btPmView10672 ∧
    pm.nodes[1478]'(by native_decide) = l17btPmMul10675 ∧
    pm.nodes[1479]'(by native_decide) = l17btPmMul10676 ∧
    pm.nodes[1480]'(by native_decide) = l17btPmAdd10679 ∧
    pm.nodes[1481]'(by native_decide) = l17btPmAdd10680 ∧
    pm.nodes[1482]'(by native_decide) = l17btPmFloat10685 ∧
    pm.nodes[1483]'(by native_decide) = l17btPmFloat10686 ∧
    pm.nodes[1484]'(by native_decide) = l17btPmAdd10689 ∧
    pm.nodes[1485]'(by native_decide) = l17btPmAdd10690 ∧
    pm.nodes[1486]'(by native_decide) = l17btPmMref10689 ∧
    pm.nodes[1487]'(by native_decide) = l17btPmMref10690 ∧
    pm.nodes[1488]'(by native_decide) = l17btPmRms10693 ∧
    pm.nodes[1489]'(by native_decide) = l17btPmRms10694 ∧
    pm.nodes[1490]'(by native_decide) = l17btPmPhl10695 ∧
    pm.nodes[1491]'(by native_decide) = l17btPmPhl10696 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l17bt_buddy_facts :
    sm.replicaBuddies l17btSmMoE5610 = [l17btSmMoE5610] ∧
    pm.replicaBuddies l17btPmMoE10601 = [l17btPmMoE10601, l17btPmMoE10602] ∧
    pm.replicaBuddies l17btPmMoE10602 = [l17btPmMoE10601, l17btPmMoE10602] := by
  native_decide

private theorem l17bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l17bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l17bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5626 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5633 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5635 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5626 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5633 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5635 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l17bt_cu_not_written : ∀ n ∈ pm.nodes, 5590 ∉ n.outs := by
  native_decide

private theorem l17bt_w5626_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5626 ∉ n.outs := by
  intro n hn
  exact l17bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l17bt_w5626_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5626 ∉ n.outs := by
  intro n hn
  exact l17bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l17bt_w5633_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5633 ∉ n.outs := by
  intro n hn
  exact l17bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l17bt_w5633_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5633 ∉ n.outs := by
  intro n hn
  exact l17bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l17bt_w5635_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5635 ∉ n.outs := by
  intro n hn
  exact l17bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l17bt_w5635_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5635 ∉ n.outs := by
  intro n hn
  exact l17bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l17bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(703, 5610), (702, 8357), (702, 5605), (702, 5606), (702, 5608), (702, 5609), (706, 5625), (705, 5624), (707, 5627), (706, 5625), (708, 5628), (707, 5627), (709, 5629), (708, 5615), (708, 5628), (710, 5630), (709, 5610), (709, 5629), (711, 5631), (710, 5630), (712, 5632), (711, 8346), (711, 5631), (713, 8373), (713, 8377), (712, 5632), (714, 5634), (713, 8373), (715, 5636), (714, 5634)]) :
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
private theorem l17bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1467, 10601), (1466, 16398), (1466, 10591), (1466, 10593), (1466, 10597), (1466, 10599), (1466, 10598), (1466, 10600), (1470, 10602), (1469, 16421), (1469, 10592), (1469, 10594), (1469, 10597), (1469, 10598), (1469, 10599), (1469, 10600), (1473, 10655), (1472, 10653), (1474, 10656), (1473, 10654), (1475, 10661), (1474, 10655), (1476, 10662), (1475, 10656), (1477, 10671), (1476, 10661), (1478, 10672), (1477, 10662), (1479, 10675), (1478, 10615), (1478, 10671), (1480, 10676), (1479, 10616), (1479, 10672), (1481, 10679), (1480, 10601), (1480, 10675), (1482, 10680), (1481, 10602), (1481, 10676), (1483, 10685), (1482, 10679), (1484, 10686), (1483, 10680), (1485, 10689), (1484, 16379), (1484, 10685), (1486, 10690), (1485, 16387), (1485, 10686), (1487, 16437), (1487, 16441), (1486, 10689), (1488, 16445), (1488, 16449), (1487, 10690), (1489, 10693), (1488, 16437), (1490, 10694), (1489, 16445), (1491, 10695), (1490, 10693), (1492, 10696), (1491, 10694)]) :
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
private theorem l17bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5608, 5609]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l17bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [10597, 10598, 10599, 10600]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l17bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5608, 5609]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l17bt_sm_leaf_not_written tid h)

private theorem l17bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [10597, 10598, 10599, 10600]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l17bt_pm_leaf_not_written tid h)

private theorem l17bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5610 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5610 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5610 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8357)
        (denoteGraphDistributedFaithful sm initSM 5605)
        (denoteGraphDistributedFaithful sm initSM 5606)
        [denoteGraphDistributedFaithful sm initSM 5608]
        [denoteGraphDistributedFaithful sm initSM 5609]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l17bt_reduce5 sm initSM 702 l17btSmMoE5610
    8357 5605 5606 5608 5609 5610
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l17bt_sm_node_facts.1 ?_
    (l17bt_nonempty_sm 703) (l17bt_sm_not_written 703 5610 (by decide))
    (l17bt_nonempty_sm 702) (l17bt_sm_not_written 702 8357 (by decide))
    (l17bt_sm_not_written 702 5605 (by decide))
    (l17bt_sm_not_written 702 5606 (by decide))
    (l17bt_sm_not_written 702 5608 (by decide))
    (l17bt_sm_not_written 702 5609 (by decide))
  intro s
  have hb := l17bt_buddy_facts.1
  unfold l17btSmMoE5610 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8357 5605 5606 5608 5609 5610 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10601 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10601 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16398)
        (denoteGraphDistributedFaithful pm initPM 10591)
        (denoteGraphDistributedFaithful pm initPM 10593)
        [denoteGraphDistributedFaithful pm initPM 10597,
         denoteGraphDistributedFaithful pm initPM 10598]
        [denoteGraphDistributedFaithful pm initPM 10599,
         denoteGraphDistributedFaithful pm initPM 10600]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l17bt_reduce7 pm initPM 1466 l17btPmMoE10601
    16398 10591 10593 10597 10599 10598 10600 10601
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l17bt_pm_node_facts.1 ?_
    (l17bt_nonempty_pm 1467) (l17bt_pm_not_written 1467 10601 (by decide))
    (l17bt_nonempty_pm 1466) (l17bt_pm_not_written 1466 16398 (by decide))
    (l17bt_pm_not_written 1466 10591 (by decide))
    (l17bt_pm_not_written 1466 10593 (by decide))
    (l17bt_pm_not_written 1466 10597 (by decide))
    (l17bt_pm_not_written 1466 10599 (by decide))
    (l17bt_pm_not_written 1466 10598 (by decide))
    (l17bt_pm_not_written 1466 10600 (by decide))
  intro s
  have hb := l17bt_buddy_facts.2.1
  unfold l17btPmMoE10601 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16398 10591 10593 10597 10599 10601 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10602 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10602 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16421)
        (denoteGraphDistributedFaithful pm initPM 10592)
        (denoteGraphDistributedFaithful pm initPM 10594)
        [denoteGraphDistributedFaithful pm initPM 10597,
         denoteGraphDistributedFaithful pm initPM 10598]
        [denoteGraphDistributedFaithful pm initPM 10599,
         denoteGraphDistributedFaithful pm initPM 10600]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l17bt_reduce7 pm initPM 1469 l17btPmMoE10602
    16421 10592 10594 10597 10598 10599 10600 10602
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l17bt_pm_node_facts.2.1 ?_
    (l17bt_nonempty_pm 1470) (l17bt_pm_not_written 1470 10602 (by decide))
    (l17bt_nonempty_pm 1469) (l17bt_pm_not_written 1469 16421 (by decide))
    (l17bt_pm_not_written 1469 10592 (by decide))
    (l17bt_pm_not_written 1469 10594 (by decide))
    (l17bt_pm_not_written 1469 10597 (by decide))
    (l17bt_pm_not_written 1469 10598 (by decide))
    (l17bt_pm_not_written 1469 10599 (by decide))
    (l17bt_pm_not_written 1469 10600 (by decide))
  intro s
  have hb := l17bt_buddy_facts.2.2
  unfold l17btPmMoE10602 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16421 10592 10594 10598 10600 10602 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5625 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5625 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5625 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5624) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 705 l17btSmResh5625
    5624 5625 (fun x => fw_view [4096,512] x)
    (by native_decide) l17bt_sm_node_facts.2.1 ?_
    (l17bt_nonempty_sm 706) (l17bt_sm_not_written 706 5625 (by decide))
    (l17bt_nonempty_sm 705) (l17bt_sm_not_written 705 5624 (by decide))
  intro s
  unfold l17btSmResh5625
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5624 5625 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10655 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10655 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10653) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1472 l17btPmResh10655
    10653 10655 (fun x => fw_view [2048,512] x)
    (by native_decide) l17bt_pm_node_facts.2.2.1 ?_
    (l17bt_nonempty_pm 1473) (l17bt_pm_not_written 1473 10655 (by decide))
    (l17bt_nonempty_pm 1472) (l17bt_pm_not_written 1472 10653 (by decide))
  intro s
  unfold l17btPmResh10655
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10653 10655 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10656 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10656 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10654) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1473 l17btPmResh10656
    10654 10656 (fun x => fw_view [2048,512] x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.1 ?_
    (l17bt_nonempty_pm 1474) (l17bt_pm_not_written 1474 10656 (by decide))
    (l17bt_nonempty_pm 1473) (l17bt_pm_not_written 1473 10654 (by decide))
  intro s
  unfold l17btPmResh10656
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10654 10656 [2048,512]

/-! ### Node reductions: down-projection 5627 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5627 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5627 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5625)
        (denoteGraphDistributedFaithful sm initSM 5626) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 706 l17btSmMPL5627
    5625 5626 5627 fw_linear
    (by native_decide) l17bt_sm_node_facts.2.2.1 ?_
    (l17bt_nonempty_sm 707) (l17bt_sm_not_written 707 5627 (by decide))
    (l17bt_nonempty_sm 706) (l17bt_sm_not_written 706 5625 (by decide))
    (l17bt_w5626_sm_drop 706)
  intro s
  unfold l17btSmMPL5627
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5625 5626 5627

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10661 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10661 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10655)
        (denoteGraphDistributedFaithful pm initPM 5626) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1474 l17btPmMPL10661
    10655 5626 10661 fw_linear
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1475) (l17bt_pm_not_written 1475 10661 (by decide))
    (l17bt_nonempty_pm 1474) (l17bt_pm_not_written 1474 10655 (by decide))
    (l17bt_w5626_pm_drop 1474)
  intro s
  unfold l17btPmMPL10661
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10655 5626 10661

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10662 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10662 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10656)
        (denoteGraphDistributedFaithful pm initPM 5626) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1475 l17btPmMPL10662
    10656 5626 10662 fw_linear
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1476) (l17bt_pm_not_written 1476 10662 (by decide))
    (l17bt_nonempty_pm 1475) (l17bt_pm_not_written 1475 10656 (by decide))
    (l17bt_w5626_pm_drop 1475)
  intro s
  unfold l17btPmMPL10662
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10656 5626 10662

/-! ### Node reductions: view 5628 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5628 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5628 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5627) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 707 l17btSmView5628
    5627 5628 (fun x => fw_view [4096,1024] x)
    (by native_decide) l17bt_sm_node_facts.2.2.2.1 ?_
    (l17bt_nonempty_sm 708) (l17bt_sm_not_written 708 5628 (by decide))
    (l17bt_nonempty_sm 707) (l17bt_sm_not_written 707 5627 (by decide))
  intro s
  unfold l17btSmView5628
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5627 5628

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10671 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10671 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10661) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1476 l17btPmView10671
    10661 10671 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1477) (l17bt_pm_not_written 1477 10671 (by decide))
    (l17bt_nonempty_pm 1476) (l17bt_pm_not_written 1476 10661 (by decide))
  intro s
  unfold l17btPmView10671
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10661 10671

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10672 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10672 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10662) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1477 l17btPmView10672
    10662 10672 (fun x => fw_view [2048,1024] x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1478) (l17bt_pm_not_written 1478 10672 (by decide))
    (l17bt_nonempty_pm 1477) (l17bt_pm_not_written 1477 10662 (by decide))
  intro s
  unfold l17btPmView10672
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10662 10672

/-! ### Node reductions: gated multiply 5629 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5629 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5629 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5615)
        (denoteGraphDistributedFaithful sm initSM 5628) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 708 l17btSmMul5629
    5615 5628 5629 elemwiseMul
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.1 ?_
    (l17bt_nonempty_sm 709) (l17bt_sm_not_written 709 5629 (by decide))
    (l17bt_nonempty_sm 708) (l17bt_sm_not_written 708 5615 (by decide))
    (l17bt_sm_not_written 708 5628 (by decide))
  intro s
  unfold l17btSmMul5629
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5615 5628 5629

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10675 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10675 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10615)
        (denoteGraphDistributedFaithful pm initPM 10671) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1478 l17btPmMul10675
    10615 10671 10675 elemwiseMul
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1479) (l17bt_pm_not_written 1479 10675 (by decide))
    (l17bt_nonempty_pm 1478) (l17bt_pm_not_written 1478 10615 (by decide))
    (l17bt_pm_not_written 1478 10671 (by decide))
  intro s
  unfold l17btPmMul10675
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 10615 10671 10675

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10676 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10676 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10616)
        (denoteGraphDistributedFaithful pm initPM 10672) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1479 l17btPmMul10676
    10616 10672 10676 elemwiseMul
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1480) (l17bt_pm_not_written 1480 10676 (by decide))
    (l17bt_nonempty_pm 1479) (l17bt_pm_not_written 1479 10616 (by decide))
    (l17bt_pm_not_written 1479 10672 (by decide))
  intro s
  unfold l17btPmMul10676
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 10616 10672 10676

/-! ### Node reductions: MoE join 5630 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5630 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5630 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5610)
        (denoteGraphDistributedFaithful sm initSM 5629) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 709 l17btSmAdd5630
    5610 5629 5630 elemwiseAdd
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l17bt_nonempty_sm 710) (l17bt_sm_not_written 710 5630 (by decide))
    (l17bt_nonempty_sm 709) (l17bt_sm_not_written 709 5610 (by decide))
    (l17bt_sm_not_written 709 5629 (by decide))
  intro s
  unfold l17btSmAdd5630
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5610 5629 5630

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10679 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10679 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10601)
        (denoteGraphDistributedFaithful pm initPM 10675) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1480 l17btPmAdd10679
    10601 10675 10679 elemwiseAdd
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1481) (l17bt_pm_not_written 1481 10679 (by decide))
    (l17bt_nonempty_pm 1480) (l17bt_pm_not_written 1480 10601 (by decide))
    (l17bt_pm_not_written 1480 10675 (by decide))
  intro s
  unfold l17btPmAdd10679
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 10601 10675 10679

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10680 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10680 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10602)
        (denoteGraphDistributedFaithful pm initPM 10676) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1481 l17btPmAdd10680
    10602 10676 10680 elemwiseAdd
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1482) (l17bt_pm_not_written 1482 10680 (by decide))
    (l17bt_nonempty_pm 1481) (l17bt_pm_not_written 1481 10602 (by decide))
    (l17bt_pm_not_written 1481 10676 (by decide))
  intro s
  unfold l17btPmAdd10680
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 10602 10676 10680

/-! ### Node reductions: float 5631 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5631 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5631 =
      denoteGraphDistributedFaithful sm initSM 5630 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 710 l17btSmFloat5631
    5630 5631 (fun x => x)
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_sm 711) (l17bt_sm_not_written 711 5631 (by decide))
    (l17bt_nonempty_sm 710) (l17bt_sm_not_written 710 5630 (by decide))
  intro s
  unfold l17btSmFloat5631
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5630 5631 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10685 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10685 =
      denoteGraphDistributedFaithful pm initPM 10679 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1482 l17btPmFloat10685
    10679 10685 (fun x => x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1483) (l17bt_pm_not_written 1483 10685 (by decide))
    (l17bt_nonempty_pm 1482) (l17bt_pm_not_written 1482 10679 (by decide))
  intro s
  unfold l17btPmFloat10685
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 10679 10685 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10686 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10686 =
      denoteGraphDistributedFaithful pm initPM 10680 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1483 l17btPmFloat10686
    10680 10686 (fun x => x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1484) (l17bt_pm_not_written 1484 10686 (by decide))
    (l17bt_nonempty_pm 1483) (l17bt_pm_not_written 1483 10680 (by decide))
  intro s
  unfold l17btPmFloat10686
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 10680 10686 []

/-! ### Node reductions: residual join 5632 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5632 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5632 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8346)
        (denoteGraphDistributedFaithful sm initSM 5631) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 711 l17btSmAdd5632
    8346 5631 5632 elemwiseAdd
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_sm 712) (l17bt_sm_not_written 712 5632 (by decide))
    (l17bt_nonempty_sm 711) (l17bt_sm_not_written 711 8346 (by decide))
    (l17bt_sm_not_written 711 5631 (by decide))
  intro s
  unfold l17btSmAdd5632
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8346 5631 5632

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10689 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10689 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16379)
        (denoteGraphDistributedFaithful pm initPM 10685) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1484 l17btPmAdd10689
    16379 10685 10689 elemwiseAdd
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1485) (l17bt_pm_not_written 1485 10689 (by decide))
    (l17bt_nonempty_pm 1484) (l17bt_pm_not_written 1484 16379 (by decide))
    (l17bt_pm_not_written 1484 10685 (by decide))
  intro s
  unfold l17btPmAdd10689
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16379 10685 10689

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10690 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10690 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16387)
        (denoteGraphDistributedFaithful pm initPM 10686) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1485 l17btPmAdd10690
    16387 10686 10690 elemwiseAdd
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1486) (l17bt_pm_not_written 1486 10690 (by decide))
    (l17bt_nonempty_pm 1485) (l17bt_pm_not_written 1485 16387 (by decide))
    (l17bt_pm_not_written 1485 10686 (by decide))
  intro s
  unfold l17btPmAdd10690
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16387 10686 10690

/-! ### Node reductions: 2-way multiref off 5632 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm8373 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8373 =
      denoteGraphDistributedFaithful sm initSM 5632 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 712 l17btSmMref5632
    5632 8373 (fun x => x)
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_sm 713) (l17bt_sm_not_written 713 8373 (by decide))
    (l17bt_nonempty_sm 712) (l17bt_sm_not_written 712 5632 (by decide))
  intro s
  unfold l17btSmMref5632
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5632 8373 8377

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm8377 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8377 =
      denoteGraphDistributedFaithful sm initSM 5632 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 712 l17btSmMref5632
    5632 8377 (fun x => x)
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_sm 713) (l17bt_sm_not_written 713 8377 (by decide))
    (l17bt_nonempty_sm 712) (l17bt_sm_not_written 712 5632 (by decide))
  intro s
  unfold l17btSmMref5632
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5632 8373 8377 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm16437 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16437 =
      denoteGraphDistributedFaithful pm initPM 10689 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1486 l17btPmMref10689
    10689 16437 (fun x => x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1487) (l17bt_pm_not_written 1487 16437 (by decide))
    (l17bt_nonempty_pm 1486) (l17bt_pm_not_written 1486 10689 (by decide))
  intro s
  unfold l17btPmMref10689
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10689 16437 16441

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm16441 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16441 =
      denoteGraphDistributedFaithful pm initPM 10689 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1486 l17btPmMref10689
    10689 16441 (fun x => x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1487) (l17bt_pm_not_written 1487 16441 (by decide))
    (l17bt_nonempty_pm 1486) (l17bt_pm_not_written 1486 10689 (by decide))
  intro s
  unfold l17btPmMref10689
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10689 16437 16441 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm16445 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16445 =
      denoteGraphDistributedFaithful pm initPM 10690 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1487 l17btPmMref10690
    10690 16445 (fun x => x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1488) (l17bt_pm_not_written 1488 16445 (by decide))
    (l17bt_nonempty_pm 1487) (l17bt_pm_not_written 1487 10690 (by decide))
  intro s
  unfold l17btPmMref10690
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10690 16445 16449

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm16449 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16449 =
      denoteGraphDistributedFaithful pm initPM 10690 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1487 l17btPmMref10690
    10690 16449 (fun x => x)
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1488) (l17bt_pm_not_written 1488 16449 (by decide))
    (l17bt_nonempty_pm 1487) (l17bt_pm_not_written 1487 10690 (by decide))
  intro s
  unfold l17btPmMref10690
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10690 16445 16449 (by decide)

/-! ### Node reductions: RMSNorm 5634 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5634 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5634 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8373)
        (denoteGraphDistributedFaithful sm initSM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 713 l17btSmRms5634
    8373 5633 5634 fw_rms_norm
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_sm 714) (l17bt_sm_not_written 714 5634 (by decide))
    (l17bt_nonempty_sm 713) (l17bt_sm_not_written 713 8373 (by decide))
    (l17bt_w5633_sm_drop 713)
  intro s
  unfold l17btSmRms5634
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8373 5633 5634

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10693 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10693 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16437)
        (denoteGraphDistributedFaithful pm initPM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1488 l17btPmRms10693
    16437 5633 10693 fw_rms_norm
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1489) (l17bt_pm_not_written 1489 10693 (by decide))
    (l17bt_nonempty_pm 1488) (l17bt_pm_not_written 1488 16437 (by decide))
    (l17bt_w5633_pm_drop 1488)
  intro s
  unfold l17btPmRms10693
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16437 5633 10693

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10694 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10694 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16445)
        (denoteGraphDistributedFaithful pm initPM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1489 l17btPmRms10694
    16445 5633 10694 fw_rms_norm
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1490) (l17bt_pm_not_written 1490 10694 (by decide))
    (l17bt_nonempty_pm 1489) (l17bt_pm_not_written 1489 16445 (by decide))
    (l17bt_w5633_pm_drop 1489)
  intro s
  unfold l17btPmRms10694
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16445 5633 10694

/-! ### Node reductions: per-head Q projection 5636 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_sm5636 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5636 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5634)
        (denoteGraphDistributedFaithful sm initSM 5635) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 714 l17btSmPhl5636
    5634 5635 5636 fw_per_head_linear
    (by native_decide) l17bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l17bt_nonempty_sm 715) (l17bt_sm_not_written 715 5636 (by decide))
    (l17bt_nonempty_sm 714) (l17bt_sm_not_written 714 5634 (by decide))
    (l17bt_w5635_sm_drop 714)
  intro s
  unfold l17btSmPhl5636
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5634 5635 5636 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10695 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10695 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10693)
        (denoteGraphDistributedFaithful pm initPM 5635) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1490 l17btPmPhl10695
    10693 5635 10695 fw_per_head_linear
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l17bt_nonempty_pm 1491) (l17bt_pm_not_written 1491 10695 (by decide))
    (l17bt_nonempty_pm 1490) (l17bt_pm_not_written 1490 10693 (by decide))
    (l17bt_w5635_pm_drop 1490)
  intro s
  unfold l17btPmPhl10695
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 10693 5635 10695 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_red_pm10696 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10696 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10694)
        (denoteGraphDistributedFaithful pm initPM 5635) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1491 l17btPmPhl10696
    10694 5635 10696 fw_per_head_linear
    (by native_decide) l17bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l17bt_nonempty_pm 1492) (l17bt_pm_not_written 1492 10696 (by decide))
    (l17bt_nonempty_pm 1491) (l17bt_pm_not_written 1491 10694 (by decide))
    (l17bt_w5635_pm_drop 1491)
  intro s
  unfold l17btPmPhl10696
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 10694 5635 10696 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l17bt_weight_bridge (initSM initPM : Store)
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
private theorem l17bt_weight_eq (initSM initPM : Store)
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
private theorem l17bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l17bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l17bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5590) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5590).shape = [2] := by
    rw [l17bt_pmFinal initPM 5590 l17bt_cu_not_written]
    exact hPM 5590 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5590)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5610 (block-4 MoE expert layer).
theorem recon_zigzagGoal_5610_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5610)
      (denoteGraphDistributedFaithful pm initPM 10601)
      (denoteGraphDistributedFaithful pm initPM 10602)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8357_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5605_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5606_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l17bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8357)
      (denoteGraphDistributedFaithful pm initPM 16398)
      (denoteGraphDistributedFaithful pm initPM 16421)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5605)
      (denoteGraphDistributedFaithful pm initPM 10591)
      (denoteGraphDistributedFaithful pm initPM 10592)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5606)
      (denoteGraphDistributedFaithful pm initPM 10593)
      (denoteGraphDistributedFaithful pm initPM 10594)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5608 = allGatherPrimDimN 0 2 0 [initPM 10597, initPM 10598] :=
    l17bt_weight_bridge initSM initPM hInit initGoal_5608 (by native_decide)
      5608 10597 10598 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5609 = allGatherPrimDimN 0 2 0 [initPM 10599, initPM 10600] :=
    l17bt_weight_bridge initSM initPM hInit initGoal_5609 (by native_decide)
      5609 10599 10600 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5608).shape = [64, 1024, 1024] :=
    hSM 5608 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5609).shape = [64, 1024, 512] :=
    hSM 5609 [64, 1024, 512] (by native_decide)
  rw [l17bt_red_sm5610 initSM, l17bt_red_pm10601 initPM, l17bt_red_pm10602 initPM]
  rw [l17bt_sm_leaf initSM 5608 (by decide), l17bt_sm_leaf initSM 5609 (by decide),
    l17bt_pm_leaf initPM 10597 (by decide), l17bt_pm_leaf initPM 10598 (by decide),
    l17bt_pm_leaf initPM 10599 (by decide), l17bt_pm_leaf initPM 10600 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5608) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5609) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 10597, initPM 10598])
    (allGatherPrimDimN 0 2 0 [initPM 10599, initPM 10600])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5625 (`FW_reshape`).
theorem recon_zigzagGoal_5625_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5625)
      (denoteGraphDistributedFaithful pm initPM 10655)
      (denoteGraphDistributedFaithful pm initPM 10656)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5624_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17bt_red_sm5625 initSM, l17bt_red_pm10655 initPM, l17bt_red_pm10656 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5627 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5627_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5627)
      (denoteGraphDistributedFaithful pm initPM 10661)
      (denoteGraphDistributedFaithful pm initPM 10662)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5625_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5626 =
      denoteGraphDistributedFaithful pm initPM 5626 :=
    l17bt_weight_eq initSM initPM hInit 5626 initGoal_5626 (by native_decide)
      rfl rfl rfl rfl
      l17bt_weights_not_written.1.1 l17bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5626).shape = [1024, 512] :=
    l17bt_pm_weight_shape initPM hPM 5626 [1024, 512] (by native_decide)
      l17bt_weights_not_written.2.1
  rw [l17bt_red_sm5627 initSM, l17bt_red_pm10661 initPM, l17bt_red_pm10662 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5628 (`FW_view`).
theorem recon_zigzagGoal_5628_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5628)
      (denoteGraphDistributedFaithful pm initPM 10671)
      (denoteGraphDistributedFaithful pm initPM 10672)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5627_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17bt_red_sm5628 initSM, l17bt_red_pm10671 initPM, l17bt_red_pm10672 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5629 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5629_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5629)
      (denoteGraphDistributedFaithful pm initPM 10675)
      (denoteGraphDistributedFaithful pm initPM 10676)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5615_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5628_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5615)
      (denoteGraphDistributedFaithful pm initPM 10615)
      (denoteGraphDistributedFaithful pm initPM 10616)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5628)
      (denoteGraphDistributedFaithful pm initPM 10671)
      (denoteGraphDistributedFaithful pm initPM 10672)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l17bt_red_sm5629 initSM, l17bt_red_pm10675 initPM, l17bt_red_pm10676 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5630 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5630_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5630)
      (denoteGraphDistributedFaithful pm initPM 10679)
      (denoteGraphDistributedFaithful pm initPM 10680)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5610_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5629_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5610)
      (denoteGraphDistributedFaithful pm initPM 10601)
      (denoteGraphDistributedFaithful pm initPM 10602)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5629)
      (denoteGraphDistributedFaithful pm initPM 10675)
      (denoteGraphDistributedFaithful pm initPM 10676)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l17bt_red_sm5630 initSM, l17bt_red_pm10679 initPM, l17bt_red_pm10680 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5631 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5631_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5631)
      (denoteGraphDistributedFaithful pm initPM 10685)
      (denoteGraphDistributedFaithful pm initPM 10686)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5630_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17bt_red_sm5631 initSM, l17bt_red_pm10685 initPM, l17bt_red_pm10686 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5632 (`FW_add`, residual join).
theorem recon_zigzagGoal_5632_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5632)
      (denoteGraphDistributedFaithful pm initPM 10689)
      (denoteGraphDistributedFaithful pm initPM 10690)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8346_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5631_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8346)
      (denoteGraphDistributedFaithful pm initPM 16379)
      (denoteGraphDistributedFaithful pm initPM 16387)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5631)
      (denoteGraphDistributedFaithful pm initPM 10685)
      (denoteGraphDistributedFaithful pm initPM 10686)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l17bt_red_sm5632 initSM, l17bt_red_pm10689 initPM, l17bt_red_pm10690 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8373 (multiref position 0 off 5632).
theorem recon_zigzagGoal_8373_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8373)
      (denoteGraphDistributedFaithful pm initPM 16437)
      (denoteGraphDistributedFaithful pm initPM 16445)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5632_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17bt_red_sm8373 initSM, l17bt_red_pm16437 initPM, l17bt_red_pm16445 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8377 (multiref position 1
-- off 5632): the cross-layer residual bypass consumed by block 5's `FW_add`.
theorem recon_zigzagGoal_8377_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8377)
      (denoteGraphDistributedFaithful pm initPM 16441)
      (denoteGraphDistributedFaithful pm initPM 16449)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5632_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l17bt_red_sm8377 initSM, l17bt_red_pm16441 initPM, l17bt_red_pm16449 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5634 (`FW_rms_norm`).
theorem recon_zigzagGoal_5634_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5634)
      (denoteGraphDistributedFaithful pm initPM 10693)
      (denoteGraphDistributedFaithful pm initPM 10694)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8373_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5633 =
      denoteGraphDistributedFaithful pm initPM 5633 :=
    l17bt_weight_eq initSM initPM hInit 5633 initGoal_5633 (by native_decide)
      rfl rfl rfl rfl
      l17bt_weights_not_written.1.2.1 l17bt_weights_not_written.2.2.1
  rw [l17bt_red_sm5634 initSM, l17bt_red_pm10693 initPM, l17bt_red_pm10694 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5636
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 5's
-- zigzag attention entry.
theorem recon_zigzagGoal_5636_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5636)
      (denoteGraphDistributedFaithful pm initPM 10695)
      (denoteGraphDistributedFaithful pm initPM 10696)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5634_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5635 =
      denoteGraphDistributedFaithful pm initPM 5635 :=
    l17bt_weight_eq initSM initPM hInit 5635 initGoal_5635 (by native_decide)
      rfl rfl rfl rfl
      l17bt_weights_not_written.1.2.2 l17bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5635).shape = [16, 64, 1024] :=
    l17bt_pm_weight_shape initPM hPM 5635 [16, 64, 1024] (by native_decide)
      l17bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5634)
      (denoteGraphDistributedFaithful pm initPM 10693)
      (denoteGraphDistributedFaithful pm initPM 10694)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l17bt_red_sm5636 initSM, l17bt_red_pm10695 initPM, l17bt_red_pm10696 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
