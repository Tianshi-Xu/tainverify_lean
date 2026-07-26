/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L18FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L17FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-6 tail (MoE join -> block-6 Q)

Mechanical transport of the (green) block-5 tail `L13FaithfulBlockTail` to
block 6.  The block-6 cu tensor is **5639**.

* SM 737 `FW_all2all_moe_gmm [8396,5654,5655,5657,5658] -> [5659]` (PM 1536/1539 -> 10773/10774)
* SM 740 `FW_reshape [5673] -> [5674]`                             (PM 1542/1543 -> 10827/10828)
* SM 741 `FW_mix_precision_linear [5674,5675] -> [5676]`           (PM 1544/1545 -> 10833/10834)
* SM 742 `FW_view [5676] -> [5677]`                                (PM 1546/1547 -> 10843/10844)
* SM 743 `FW_mul [5664,5677] -> [5678]` (broadcast `[N,1]x[N,1024]`)(PM 1548/1549 -> 10847/10848)
* SM 744 `FW_add [5659,5678] -> [5679]`                            (PM 1550/1551 -> 10851/10852)
* SM 745 `FW_float [5679] -> [5680]`                               (PM 1552/1553 -> 10857/10858)
* SM 746 `FW_add [8385,5680] -> [5681]`                            (PM 1554/1555 -> 10861/10862)
* SM 747 `FW_multiref [5681] -> [8412,8416]`                       (PM 1556/1557)
* SM 748 `FW_rms_norm [8412,5682] -> [5683]`                       (PM 1558/1559 -> 10865/10866)
* SM 749 `FW_per_head_mix_precision_linear [5683,5684] -> [5685]`  (PM 1560/1561 -> 10867/10868)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8416_faithful` -- the cross-layer residual bypass consumed by
  block 6 (SM node 756 `FW_add`);
* `recon_zigzagGoal_5685_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 6's zigzag attention entry.

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

private theorem l18bt_reduce7
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

private theorem l18bt_reduce5
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
private def l18btSmMoE5659 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8396,5654,5655,5657,5658], outs := [5659],
    params := [64,0,64,8] }
private def l18btSmResh5674 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5673], outs := [5674],
    params := [4096,512] }
private def l18btSmMPL5676 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5674,5675], outs := [5676] }
private def l18btSmView5677 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5676], outs := [5677],
    params := [4096,1024] }
private def l18btSmMul5678 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5664,5677], outs := [5678] }
private def l18btSmAdd5679 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5659,5678], outs := [5679] }
private def l18btSmFloat5680 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5679], outs := [5680] }
private def l18btSmAdd5681 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8385,5680], outs := [5681] }
private def l18btSmMref5681 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5681], outs := [8412,8416],
    params := [2] }
private def l18btSmRms5683 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8412,5682], outs := [5683] }
private def l18btSmPhl5685 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5683,5684], outs := [5685] }

private def l18btPmMoE10773 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16476,10763,10765,10769,10771], outs := [10773],
    params := [64,0,32,8] }
private def l18btPmMoE10774 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16499,10764,10766,10770,10772], outs := [10774],
    params := [64,32,64,8] }
private def l18btPmResh10827 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10825], outs := [10827],
    params := [2048,512] }
private def l18btPmResh10828 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10826], outs := [10828],
    params := [2048,512] }
private def l18btPmMPL10833 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10827,5675], outs := [10833] }
private def l18btPmMPL10834 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10828,5675], outs := [10834] }
private def l18btPmView10843 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10833], outs := [10843],
    params := [2048,1024] }
private def l18btPmView10844 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10834], outs := [10844],
    params := [2048,1024] }
private def l18btPmMul10847 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [10787,10843], outs := [10847] }
private def l18btPmMul10848 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [10788,10844], outs := [10848] }
private def l18btPmAdd10851 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [10773,10847], outs := [10851] }
private def l18btPmAdd10852 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [10774,10848], outs := [10852] }
private def l18btPmFloat10857 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [10851], outs := [10857] }
private def l18btPmFloat10858 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [10852], outs := [10858] }
private def l18btPmAdd10861 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16457,10857], outs := [10861] }
private def l18btPmAdd10862 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16465,10858], outs := [10862] }
private def l18btPmMref10861 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10861], outs := [16515,16519],
    params := [2] }
private def l18btPmMref10862 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10862], outs := [16523,16527],
    params := [2] }
private def l18btPmRms10865 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16515,5682], outs := [10865] }
private def l18btPmRms10866 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16523,5682], outs := [10866] }
private def l18btPmPhl10867 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10865,5684], outs := [10867] }
private def l18btPmPhl10868 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10866,5684], outs := [10868] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l18bt_sm_node_facts :
    sm.nodes[737]'(by native_decide) = l18btSmMoE5659 ∧
    sm.nodes[740]'(by native_decide) = l18btSmResh5674 ∧
    sm.nodes[741]'(by native_decide) = l18btSmMPL5676 ∧
    sm.nodes[742]'(by native_decide) = l18btSmView5677 ∧
    sm.nodes[743]'(by native_decide) = l18btSmMul5678 ∧
    sm.nodes[744]'(by native_decide) = l18btSmAdd5679 ∧
    sm.nodes[745]'(by native_decide) = l18btSmFloat5680 ∧
    sm.nodes[746]'(by native_decide) = l18btSmAdd5681 ∧
    sm.nodes[747]'(by native_decide) = l18btSmMref5681 ∧
    sm.nodes[748]'(by native_decide) = l18btSmRms5683 ∧
    sm.nodes[749]'(by native_decide) = l18btSmPhl5685 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l18bt_pm_node_facts :
    pm.nodes[1536]'(by native_decide) = l18btPmMoE10773 ∧
    pm.nodes[1539]'(by native_decide) = l18btPmMoE10774 ∧
    pm.nodes[1542]'(by native_decide) = l18btPmResh10827 ∧
    pm.nodes[1543]'(by native_decide) = l18btPmResh10828 ∧
    pm.nodes[1544]'(by native_decide) = l18btPmMPL10833 ∧
    pm.nodes[1545]'(by native_decide) = l18btPmMPL10834 ∧
    pm.nodes[1546]'(by native_decide) = l18btPmView10843 ∧
    pm.nodes[1547]'(by native_decide) = l18btPmView10844 ∧
    pm.nodes[1548]'(by native_decide) = l18btPmMul10847 ∧
    pm.nodes[1549]'(by native_decide) = l18btPmMul10848 ∧
    pm.nodes[1550]'(by native_decide) = l18btPmAdd10851 ∧
    pm.nodes[1551]'(by native_decide) = l18btPmAdd10852 ∧
    pm.nodes[1552]'(by native_decide) = l18btPmFloat10857 ∧
    pm.nodes[1553]'(by native_decide) = l18btPmFloat10858 ∧
    pm.nodes[1554]'(by native_decide) = l18btPmAdd10861 ∧
    pm.nodes[1555]'(by native_decide) = l18btPmAdd10862 ∧
    pm.nodes[1556]'(by native_decide) = l18btPmMref10861 ∧
    pm.nodes[1557]'(by native_decide) = l18btPmMref10862 ∧
    pm.nodes[1558]'(by native_decide) = l18btPmRms10865 ∧
    pm.nodes[1559]'(by native_decide) = l18btPmRms10866 ∧
    pm.nodes[1560]'(by native_decide) = l18btPmPhl10867 ∧
    pm.nodes[1561]'(by native_decide) = l18btPmPhl10868 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l18bt_buddy_facts :
    sm.replicaBuddies l18btSmMoE5659 = [l18btSmMoE5659] ∧
    pm.replicaBuddies l18btPmMoE10773 = [l18btPmMoE10773, l18btPmMoE10774] ∧
    pm.replicaBuddies l18btPmMoE10774 = [l18btPmMoE10773, l18btPmMoE10774] := by
  native_decide

private theorem l18bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l18bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l18bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5675 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5682 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5684 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5675 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5682 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5684 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l18bt_cu_not_written : ∀ n ∈ pm.nodes, 5639 ∉ n.outs := by
  native_decide

private theorem l18bt_w5675_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5675 ∉ n.outs := by
  intro n hn
  exact l18bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l18bt_w5675_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5675 ∉ n.outs := by
  intro n hn
  exact l18bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l18bt_w5682_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5682 ∉ n.outs := by
  intro n hn
  exact l18bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l18bt_w5682_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5682 ∉ n.outs := by
  intro n hn
  exact l18bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l18bt_w5684_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5684 ∉ n.outs := by
  intro n hn
  exact l18bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l18bt_w5684_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5684 ∉ n.outs := by
  intro n hn
  exact l18bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l18bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(738, 5659), (737, 8396), (737, 5654), (737, 5655), (737, 5657), (737, 5658), (741, 5674), (740, 5673), (742, 5676), (741, 5674), (743, 5677), (742, 5676), (744, 5678), (743, 5664), (743, 5677), (745, 5679), (744, 5659), (744, 5678), (746, 5680), (745, 5679), (747, 5681), (746, 8385), (746, 5680), (748, 8412), (748, 8416), (747, 5681), (749, 5683), (748, 8412), (750, 5685), (749, 5683)]) :
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
private theorem l18bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1537, 10773), (1536, 16476), (1536, 10763), (1536, 10765), (1536, 10769), (1536, 10771), (1536, 10770), (1536, 10772), (1540, 10774), (1539, 16499), (1539, 10764), (1539, 10766), (1539, 10769), (1539, 10770), (1539, 10771), (1539, 10772), (1543, 10827), (1542, 10825), (1544, 10828), (1543, 10826), (1545, 10833), (1544, 10827), (1546, 10834), (1545, 10828), (1547, 10843), (1546, 10833), (1548, 10844), (1547, 10834), (1549, 10847), (1548, 10787), (1548, 10843), (1550, 10848), (1549, 10788), (1549, 10844), (1551, 10851), (1550, 10773), (1550, 10847), (1552, 10852), (1551, 10774), (1551, 10848), (1553, 10857), (1552, 10851), (1554, 10858), (1553, 10852), (1555, 10861), (1554, 16457), (1554, 10857), (1556, 10862), (1555, 16465), (1555, 10858), (1557, 16515), (1557, 16519), (1556, 10861), (1558, 16523), (1558, 16527), (1557, 10862), (1559, 10865), (1558, 16515), (1560, 10866), (1559, 16523), (1561, 10867), (1560, 10865), (1562, 10868), (1561, 10866)]) :
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
private theorem l18bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5657, 5658]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l18bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [10769, 10770, 10771, 10772]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l18bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5657, 5658]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l18bt_sm_leaf_not_written tid h)

private theorem l18bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [10769, 10770, 10771, 10772]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l18bt_pm_leaf_not_written tid h)

private theorem l18bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5659 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5659 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5659 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8396)
        (denoteGraphDistributedFaithful sm initSM 5654)
        (denoteGraphDistributedFaithful sm initSM 5655)
        [denoteGraphDistributedFaithful sm initSM 5657]
        [denoteGraphDistributedFaithful sm initSM 5658]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l18bt_reduce5 sm initSM 737 l18btSmMoE5659
    8396 5654 5655 5657 5658 5659
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l18bt_sm_node_facts.1 ?_
    (l18bt_nonempty_sm 738) (l18bt_sm_not_written 738 5659 (by decide))
    (l18bt_nonempty_sm 737) (l18bt_sm_not_written 737 8396 (by decide))
    (l18bt_sm_not_written 737 5654 (by decide))
    (l18bt_sm_not_written 737 5655 (by decide))
    (l18bt_sm_not_written 737 5657 (by decide))
    (l18bt_sm_not_written 737 5658 (by decide))
  intro s
  have hb := l18bt_buddy_facts.1
  unfold l18btSmMoE5659 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8396 5654 5655 5657 5658 5659 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10773 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10773 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16476)
        (denoteGraphDistributedFaithful pm initPM 10763)
        (denoteGraphDistributedFaithful pm initPM 10765)
        [denoteGraphDistributedFaithful pm initPM 10769,
         denoteGraphDistributedFaithful pm initPM 10770]
        [denoteGraphDistributedFaithful pm initPM 10771,
         denoteGraphDistributedFaithful pm initPM 10772]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l18bt_reduce7 pm initPM 1536 l18btPmMoE10773
    16476 10763 10765 10769 10771 10770 10772 10773
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l18bt_pm_node_facts.1 ?_
    (l18bt_nonempty_pm 1537) (l18bt_pm_not_written 1537 10773 (by decide))
    (l18bt_nonempty_pm 1536) (l18bt_pm_not_written 1536 16476 (by decide))
    (l18bt_pm_not_written 1536 10763 (by decide))
    (l18bt_pm_not_written 1536 10765 (by decide))
    (l18bt_pm_not_written 1536 10769 (by decide))
    (l18bt_pm_not_written 1536 10771 (by decide))
    (l18bt_pm_not_written 1536 10770 (by decide))
    (l18bt_pm_not_written 1536 10772 (by decide))
  intro s
  have hb := l18bt_buddy_facts.2.1
  unfold l18btPmMoE10773 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16476 10763 10765 10769 10771 10773 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10774 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10774 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16499)
        (denoteGraphDistributedFaithful pm initPM 10764)
        (denoteGraphDistributedFaithful pm initPM 10766)
        [denoteGraphDistributedFaithful pm initPM 10769,
         denoteGraphDistributedFaithful pm initPM 10770]
        [denoteGraphDistributedFaithful pm initPM 10771,
         denoteGraphDistributedFaithful pm initPM 10772]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l18bt_reduce7 pm initPM 1539 l18btPmMoE10774
    16499 10764 10766 10769 10770 10771 10772 10774
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l18bt_pm_node_facts.2.1 ?_
    (l18bt_nonempty_pm 1540) (l18bt_pm_not_written 1540 10774 (by decide))
    (l18bt_nonempty_pm 1539) (l18bt_pm_not_written 1539 16499 (by decide))
    (l18bt_pm_not_written 1539 10764 (by decide))
    (l18bt_pm_not_written 1539 10766 (by decide))
    (l18bt_pm_not_written 1539 10769 (by decide))
    (l18bt_pm_not_written 1539 10770 (by decide))
    (l18bt_pm_not_written 1539 10771 (by decide))
    (l18bt_pm_not_written 1539 10772 (by decide))
  intro s
  have hb := l18bt_buddy_facts.2.2
  unfold l18btPmMoE10774 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16499 10764 10766 10770 10772 10774 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5674 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5674 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5674 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5673) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 740 l18btSmResh5674
    5673 5674 (fun x => fw_view [4096,512] x)
    (by native_decide) l18bt_sm_node_facts.2.1 ?_
    (l18bt_nonempty_sm 741) (l18bt_sm_not_written 741 5674 (by decide))
    (l18bt_nonempty_sm 740) (l18bt_sm_not_written 740 5673 (by decide))
  intro s
  unfold l18btSmResh5674
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5673 5674 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10827 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10827 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10825) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1542 l18btPmResh10827
    10825 10827 (fun x => fw_view [2048,512] x)
    (by native_decide) l18bt_pm_node_facts.2.2.1 ?_
    (l18bt_nonempty_pm 1543) (l18bt_pm_not_written 1543 10827 (by decide))
    (l18bt_nonempty_pm 1542) (l18bt_pm_not_written 1542 10825 (by decide))
  intro s
  unfold l18btPmResh10827
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 10825 10827 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10828 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10828 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 10826) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1543 l18btPmResh10828
    10826 10828 (fun x => fw_view [2048,512] x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.1 ?_
    (l18bt_nonempty_pm 1544) (l18bt_pm_not_written 1544 10828 (by decide))
    (l18bt_nonempty_pm 1543) (l18bt_pm_not_written 1543 10826 (by decide))
  intro s
  unfold l18btPmResh10828
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 10826 10828 [2048,512]

/-! ### Node reductions: down-projection 5676 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5676 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5676 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5674)
        (denoteGraphDistributedFaithful sm initSM 5675) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 741 l18btSmMPL5676
    5674 5675 5676 fw_linear
    (by native_decide) l18bt_sm_node_facts.2.2.1 ?_
    (l18bt_nonempty_sm 742) (l18bt_sm_not_written 742 5676 (by decide))
    (l18bt_nonempty_sm 741) (l18bt_sm_not_written 741 5674 (by decide))
    (l18bt_w5675_sm_drop 741)
  intro s
  unfold l18btSmMPL5676
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5674 5675 5676

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10833 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10833 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10827)
        (denoteGraphDistributedFaithful pm initPM 5675) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1544 l18btPmMPL10833
    10827 5675 10833 fw_linear
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1545) (l18bt_pm_not_written 1545 10833 (by decide))
    (l18bt_nonempty_pm 1544) (l18bt_pm_not_written 1544 10827 (by decide))
    (l18bt_w5675_pm_drop 1544)
  intro s
  unfold l18btPmMPL10833
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 10827 5675 10833

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10834 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10834 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 10828)
        (denoteGraphDistributedFaithful pm initPM 5675) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1545 l18btPmMPL10834
    10828 5675 10834 fw_linear
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1546) (l18bt_pm_not_written 1546 10834 (by decide))
    (l18bt_nonempty_pm 1545) (l18bt_pm_not_written 1545 10828 (by decide))
    (l18bt_w5675_pm_drop 1545)
  intro s
  unfold l18btPmMPL10834
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 10828 5675 10834

/-! ### Node reductions: view 5677 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5677 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5677 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5676) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 742 l18btSmView5677
    5676 5677 (fun x => fw_view [4096,1024] x)
    (by native_decide) l18bt_sm_node_facts.2.2.2.1 ?_
    (l18bt_nonempty_sm 743) (l18bt_sm_not_written 743 5677 (by decide))
    (l18bt_nonempty_sm 742) (l18bt_sm_not_written 742 5676 (by decide))
  intro s
  unfold l18btSmView5677
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5676 5677

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10843 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10843 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10833) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1546 l18btPmView10843
    10833 10843 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1547) (l18bt_pm_not_written 1547 10843 (by decide))
    (l18bt_nonempty_pm 1546) (l18bt_pm_not_written 1546 10833 (by decide))
  intro s
  unfold l18btPmView10843
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 10833 10843

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10844 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10844 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 10834) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1547 l18btPmView10844
    10834 10844 (fun x => fw_view [2048,1024] x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1548) (l18bt_pm_not_written 1548 10844 (by decide))
    (l18bt_nonempty_pm 1547) (l18bt_pm_not_written 1547 10834 (by decide))
  intro s
  unfold l18btPmView10844
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 10834 10844

/-! ### Node reductions: gated multiply 5678 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5678 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5678 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5664)
        (denoteGraphDistributedFaithful sm initSM 5677) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 743 l18btSmMul5678
    5664 5677 5678 elemwiseMul
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.1 ?_
    (l18bt_nonempty_sm 744) (l18bt_sm_not_written 744 5678 (by decide))
    (l18bt_nonempty_sm 743) (l18bt_sm_not_written 743 5664 (by decide))
    (l18bt_sm_not_written 743 5677 (by decide))
  intro s
  unfold l18btSmMul5678
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5664 5677 5678

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10847 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10847 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10787)
        (denoteGraphDistributedFaithful pm initPM 10843) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1548 l18btPmMul10847
    10787 10843 10847 elemwiseMul
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1549) (l18bt_pm_not_written 1549 10847 (by decide))
    (l18bt_nonempty_pm 1548) (l18bt_pm_not_written 1548 10787 (by decide))
    (l18bt_pm_not_written 1548 10843 (by decide))
  intro s
  unfold l18btPmMul10847
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 10787 10843 10847

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10848 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10848 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 10788)
        (denoteGraphDistributedFaithful pm initPM 10844) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1549 l18btPmMul10848
    10788 10844 10848 elemwiseMul
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1550) (l18bt_pm_not_written 1550 10848 (by decide))
    (l18bt_nonempty_pm 1549) (l18bt_pm_not_written 1549 10788 (by decide))
    (l18bt_pm_not_written 1549 10844 (by decide))
  intro s
  unfold l18btPmMul10848
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 10788 10844 10848

/-! ### Node reductions: MoE join 5679 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5679 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5679 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5659)
        (denoteGraphDistributedFaithful sm initSM 5678) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 744 l18btSmAdd5679
    5659 5678 5679 elemwiseAdd
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l18bt_nonempty_sm 745) (l18bt_sm_not_written 745 5679 (by decide))
    (l18bt_nonempty_sm 744) (l18bt_sm_not_written 744 5659 (by decide))
    (l18bt_sm_not_written 744 5678 (by decide))
  intro s
  unfold l18btSmAdd5679
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5659 5678 5679

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10851 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10851 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10773)
        (denoteGraphDistributedFaithful pm initPM 10847) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1550 l18btPmAdd10851
    10773 10847 10851 elemwiseAdd
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1551) (l18bt_pm_not_written 1551 10851 (by decide))
    (l18bt_nonempty_pm 1550) (l18bt_pm_not_written 1550 10773 (by decide))
    (l18bt_pm_not_written 1550 10847 (by decide))
  intro s
  unfold l18btPmAdd10851
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 10773 10847 10851

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10852 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10852 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 10774)
        (denoteGraphDistributedFaithful pm initPM 10848) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1551 l18btPmAdd10852
    10774 10848 10852 elemwiseAdd
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1552) (l18bt_pm_not_written 1552 10852 (by decide))
    (l18bt_nonempty_pm 1551) (l18bt_pm_not_written 1551 10774 (by decide))
    (l18bt_pm_not_written 1551 10848 (by decide))
  intro s
  unfold l18btPmAdd10852
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 10774 10848 10852

/-! ### Node reductions: float 5680 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5680 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5680 =
      denoteGraphDistributedFaithful sm initSM 5679 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 745 l18btSmFloat5680
    5679 5680 (fun x => x)
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_sm 746) (l18bt_sm_not_written 746 5680 (by decide))
    (l18bt_nonempty_sm 745) (l18bt_sm_not_written 745 5679 (by decide))
  intro s
  unfold l18btSmFloat5680
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5679 5680 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10857 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10857 =
      denoteGraphDistributedFaithful pm initPM 10851 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1552 l18btPmFloat10857
    10851 10857 (fun x => x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1553) (l18bt_pm_not_written 1553 10857 (by decide))
    (l18bt_nonempty_pm 1552) (l18bt_pm_not_written 1552 10851 (by decide))
  intro s
  unfold l18btPmFloat10857
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 10851 10857 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10858 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10858 =
      denoteGraphDistributedFaithful pm initPM 10852 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1553 l18btPmFloat10858
    10852 10858 (fun x => x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1554) (l18bt_pm_not_written 1554 10858 (by decide))
    (l18bt_nonempty_pm 1553) (l18bt_pm_not_written 1553 10852 (by decide))
  intro s
  unfold l18btPmFloat10858
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 10852 10858 []

/-! ### Node reductions: residual join 5681 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5681 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5681 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8385)
        (denoteGraphDistributedFaithful sm initSM 5680) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 746 l18btSmAdd5681
    8385 5680 5681 elemwiseAdd
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_sm 747) (l18bt_sm_not_written 747 5681 (by decide))
    (l18bt_nonempty_sm 746) (l18bt_sm_not_written 746 8385 (by decide))
    (l18bt_sm_not_written 746 5680 (by decide))
  intro s
  unfold l18btSmAdd5681
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8385 5680 5681

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10861 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10861 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16457)
        (denoteGraphDistributedFaithful pm initPM 10857) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1554 l18btPmAdd10861
    16457 10857 10861 elemwiseAdd
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1555) (l18bt_pm_not_written 1555 10861 (by decide))
    (l18bt_nonempty_pm 1554) (l18bt_pm_not_written 1554 16457 (by decide))
    (l18bt_pm_not_written 1554 10857 (by decide))
  intro s
  unfold l18btPmAdd10861
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16457 10857 10861

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10862 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10862 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16465)
        (denoteGraphDistributedFaithful pm initPM 10858) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1555 l18btPmAdd10862
    16465 10858 10862 elemwiseAdd
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1556) (l18bt_pm_not_written 1556 10862 (by decide))
    (l18bt_nonempty_pm 1555) (l18bt_pm_not_written 1555 16465 (by decide))
    (l18bt_pm_not_written 1555 10858 (by decide))
  intro s
  unfold l18btPmAdd10862
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16465 10858 10862

/-! ### Node reductions: 2-way multiref off 5681 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm8412 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8412 =
      denoteGraphDistributedFaithful sm initSM 5681 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 747 l18btSmMref5681
    5681 8412 (fun x => x)
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_sm 748) (l18bt_sm_not_written 748 8412 (by decide))
    (l18bt_nonempty_sm 747) (l18bt_sm_not_written 747 5681 (by decide))
  intro s
  unfold l18btSmMref5681
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5681 8412 8416

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm8416 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8416 =
      denoteGraphDistributedFaithful sm initSM 5681 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 747 l18btSmMref5681
    5681 8416 (fun x => x)
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_sm 748) (l18bt_sm_not_written 748 8416 (by decide))
    (l18bt_nonempty_sm 747) (l18bt_sm_not_written 747 5681 (by decide))
  intro s
  unfold l18btSmMref5681
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5681 8412 8416 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm16515 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16515 =
      denoteGraphDistributedFaithful pm initPM 10861 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1556 l18btPmMref10861
    10861 16515 (fun x => x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1557) (l18bt_pm_not_written 1557 16515 (by decide))
    (l18bt_nonempty_pm 1556) (l18bt_pm_not_written 1556 10861 (by decide))
  intro s
  unfold l18btPmMref10861
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 10861 16515 16519

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm16519 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16519 =
      denoteGraphDistributedFaithful pm initPM 10861 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1556 l18btPmMref10861
    10861 16519 (fun x => x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1557) (l18bt_pm_not_written 1557 16519 (by decide))
    (l18bt_nonempty_pm 1556) (l18bt_pm_not_written 1556 10861 (by decide))
  intro s
  unfold l18btPmMref10861
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 10861 16515 16519 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm16523 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16523 =
      denoteGraphDistributedFaithful pm initPM 10862 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1557 l18btPmMref10862
    10862 16523 (fun x => x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1558) (l18bt_pm_not_written 1558 16523 (by decide))
    (l18bt_nonempty_pm 1557) (l18bt_pm_not_written 1557 10862 (by decide))
  intro s
  unfold l18btPmMref10862
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 10862 16523 16527

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm16527 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16527 =
      denoteGraphDistributedFaithful pm initPM 10862 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1557 l18btPmMref10862
    10862 16527 (fun x => x)
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1558) (l18bt_pm_not_written 1558 16527 (by decide))
    (l18bt_nonempty_pm 1557) (l18bt_pm_not_written 1557 10862 (by decide))
  intro s
  unfold l18btPmMref10862
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 10862 16523 16527 (by decide)

/-! ### Node reductions: RMSNorm 5683 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5683 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5683 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8412)
        (denoteGraphDistributedFaithful sm initSM 5682) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 748 l18btSmRms5683
    8412 5682 5683 fw_rms_norm
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_sm 749) (l18bt_sm_not_written 749 5683 (by decide))
    (l18bt_nonempty_sm 748) (l18bt_sm_not_written 748 8412 (by decide))
    (l18bt_w5682_sm_drop 748)
  intro s
  unfold l18btSmRms5683
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8412 5682 5683

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10865 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10865 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16515)
        (denoteGraphDistributedFaithful pm initPM 5682) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1558 l18btPmRms10865
    16515 5682 10865 fw_rms_norm
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1559) (l18bt_pm_not_written 1559 10865 (by decide))
    (l18bt_nonempty_pm 1558) (l18bt_pm_not_written 1558 16515 (by decide))
    (l18bt_w5682_pm_drop 1558)
  intro s
  unfold l18btPmRms10865
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16515 5682 10865

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10866 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10866 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16523)
        (denoteGraphDistributedFaithful pm initPM 5682) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1559 l18btPmRms10866
    16523 5682 10866 fw_rms_norm
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1560) (l18bt_pm_not_written 1560 10866 (by decide))
    (l18bt_nonempty_pm 1559) (l18bt_pm_not_written 1559 16523 (by decide))
    (l18bt_w5682_pm_drop 1559)
  intro s
  unfold l18btPmRms10866
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16523 5682 10866

/-! ### Node reductions: per-head Q projection 5685 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_sm5685 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5685 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5683)
        (denoteGraphDistributedFaithful sm initSM 5684) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 749 l18btSmPhl5685
    5683 5684 5685 fw_per_head_linear
    (by native_decide) l18bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l18bt_nonempty_sm 750) (l18bt_sm_not_written 750 5685 (by decide))
    (l18bt_nonempty_sm 749) (l18bt_sm_not_written 749 5683 (by decide))
    (l18bt_w5684_sm_drop 749)
  intro s
  unfold l18btSmPhl5685
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5683 5684 5685 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10867 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10867 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10865)
        (denoteGraphDistributedFaithful pm initPM 5684) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1560 l18btPmPhl10867
    10865 5684 10867 fw_per_head_linear
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l18bt_nonempty_pm 1561) (l18bt_pm_not_written 1561 10867 (by decide))
    (l18bt_nonempty_pm 1560) (l18bt_pm_not_written 1560 10865 (by decide))
    (l18bt_w5684_pm_drop 1560)
  intro s
  unfold l18btPmPhl10867
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 10865 5684 10867 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_red_pm10868 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10868 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 10866)
        (denoteGraphDistributedFaithful pm initPM 5684) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1561 l18btPmPhl10868
    10866 5684 10868 fw_per_head_linear
    (by native_decide) l18bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l18bt_nonempty_pm 1562) (l18bt_pm_not_written 1562 10868 (by decide))
    (l18bt_nonempty_pm 1561) (l18bt_pm_not_written 1561 10866 (by decide))
    (l18bt_w5684_pm_drop 1561)
  intro s
  unfold l18btPmPhl10868
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 10866 5684 10868 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l18bt_weight_bridge (initSM initPM : Store)
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
private theorem l18bt_weight_eq (initSM initPM : Store)
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
private theorem l18bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l18bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l18bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5639) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5639).shape = [2] := by
    rw [l18bt_pmFinal initPM 5639 l18bt_cu_not_written]
    exact hPM 5639 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5639)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5659 (block-5 MoE expert layer).
theorem recon_zigzagGoal_5659_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5659)
      (denoteGraphDistributedFaithful pm initPM 10773)
      (denoteGraphDistributedFaithful pm initPM 10774)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8396_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5654_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5655_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l18bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8396)
      (denoteGraphDistributedFaithful pm initPM 16476)
      (denoteGraphDistributedFaithful pm initPM 16499)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5654)
      (denoteGraphDistributedFaithful pm initPM 10763)
      (denoteGraphDistributedFaithful pm initPM 10764)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5655)
      (denoteGraphDistributedFaithful pm initPM 10765)
      (denoteGraphDistributedFaithful pm initPM 10766)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5657 = allGatherPrimDimN 0 2 0 [initPM 10769, initPM 10770] :=
    l18bt_weight_bridge initSM initPM hInit initGoal_5657 (by native_decide)
      5657 10769 10770 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5658 = allGatherPrimDimN 0 2 0 [initPM 10771, initPM 10772] :=
    l18bt_weight_bridge initSM initPM hInit initGoal_5658 (by native_decide)
      5658 10771 10772 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5657).shape = [64, 1024, 1024] :=
    hSM 5657 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5658).shape = [64, 1024, 512] :=
    hSM 5658 [64, 1024, 512] (by native_decide)
  rw [l18bt_red_sm5659 initSM, l18bt_red_pm10773 initPM, l18bt_red_pm10774 initPM]
  rw [l18bt_sm_leaf initSM 5657 (by decide), l18bt_sm_leaf initSM 5658 (by decide),
    l18bt_pm_leaf initPM 10769 (by decide), l18bt_pm_leaf initPM 10770 (by decide),
    l18bt_pm_leaf initPM 10771 (by decide), l18bt_pm_leaf initPM 10772 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5657) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5658) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 10769, initPM 10770])
    (allGatherPrimDimN 0 2 0 [initPM 10771, initPM 10772])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5674 (`FW_reshape`).
theorem recon_zigzagGoal_5674_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5674)
      (denoteGraphDistributedFaithful pm initPM 10827)
      (denoteGraphDistributedFaithful pm initPM 10828)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5673_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18bt_red_sm5674 initSM, l18bt_red_pm10827 initPM, l18bt_red_pm10828 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5676 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5676_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5676)
      (denoteGraphDistributedFaithful pm initPM 10833)
      (denoteGraphDistributedFaithful pm initPM 10834)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5674_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5675 =
      denoteGraphDistributedFaithful pm initPM 5675 :=
    l18bt_weight_eq initSM initPM hInit 5675 initGoal_5675 (by native_decide)
      rfl rfl rfl rfl
      l18bt_weights_not_written.1.1 l18bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5675).shape = [1024, 512] :=
    l18bt_pm_weight_shape initPM hPM 5675 [1024, 512] (by native_decide)
      l18bt_weights_not_written.2.1
  rw [l18bt_red_sm5676 initSM, l18bt_red_pm10833 initPM, l18bt_red_pm10834 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5677 (`FW_view`).
theorem recon_zigzagGoal_5677_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5677)
      (denoteGraphDistributedFaithful pm initPM 10843)
      (denoteGraphDistributedFaithful pm initPM 10844)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5676_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18bt_red_sm5677 initSM, l18bt_red_pm10843 initPM, l18bt_red_pm10844 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5678 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5678_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5678)
      (denoteGraphDistributedFaithful pm initPM 10847)
      (denoteGraphDistributedFaithful pm initPM 10848)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5664_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5677_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5664)
      (denoteGraphDistributedFaithful pm initPM 10787)
      (denoteGraphDistributedFaithful pm initPM 10788)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5677)
      (denoteGraphDistributedFaithful pm initPM 10843)
      (denoteGraphDistributedFaithful pm initPM 10844)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l18bt_red_sm5678 initSM, l18bt_red_pm10847 initPM, l18bt_red_pm10848 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5679 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5679_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5679)
      (denoteGraphDistributedFaithful pm initPM 10851)
      (denoteGraphDistributedFaithful pm initPM 10852)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5659_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5678_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5659)
      (denoteGraphDistributedFaithful pm initPM 10773)
      (denoteGraphDistributedFaithful pm initPM 10774)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5678)
      (denoteGraphDistributedFaithful pm initPM 10847)
      (denoteGraphDistributedFaithful pm initPM 10848)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l18bt_red_sm5679 initSM, l18bt_red_pm10851 initPM, l18bt_red_pm10852 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5680 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5680_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5680)
      (denoteGraphDistributedFaithful pm initPM 10857)
      (denoteGraphDistributedFaithful pm initPM 10858)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5679_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18bt_red_sm5680 initSM, l18bt_red_pm10857 initPM, l18bt_red_pm10858 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5681 (`FW_add`, residual join).
theorem recon_zigzagGoal_5681_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5681)
      (denoteGraphDistributedFaithful pm initPM 10861)
      (denoteGraphDistributedFaithful pm initPM 10862)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8385_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5680_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8385)
      (denoteGraphDistributedFaithful pm initPM 16457)
      (denoteGraphDistributedFaithful pm initPM 16465)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5680)
      (denoteGraphDistributedFaithful pm initPM 10857)
      (denoteGraphDistributedFaithful pm initPM 10858)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l18bt_red_sm5681 initSM, l18bt_red_pm10861 initPM, l18bt_red_pm10862 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8412 (multiref position 0 off 5681).
theorem recon_zigzagGoal_8412_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8412)
      (denoteGraphDistributedFaithful pm initPM 16515)
      (denoteGraphDistributedFaithful pm initPM 16523)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5681_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18bt_red_sm8412 initSM, l18bt_red_pm16515 initPM, l18bt_red_pm16523 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8416 (multiref position 1
-- off 5681): the cross-layer residual bypass consumed by block 6's `FW_add`.
theorem recon_zigzagGoal_8416_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8416)
      (denoteGraphDistributedFaithful pm initPM 16519)
      (denoteGraphDistributedFaithful pm initPM 16527)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5681_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l18bt_red_sm8416 initSM, l18bt_red_pm16519 initPM, l18bt_red_pm16527 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5683 (`FW_rms_norm`).
theorem recon_zigzagGoal_5683_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5683)
      (denoteGraphDistributedFaithful pm initPM 10865)
      (denoteGraphDistributedFaithful pm initPM 10866)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8412_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5682 =
      denoteGraphDistributedFaithful pm initPM 5682 :=
    l18bt_weight_eq initSM initPM hInit 5682 initGoal_5682 (by native_decide)
      rfl rfl rfl rfl
      l18bt_weights_not_written.1.2.1 l18bt_weights_not_written.2.2.1
  rw [l18bt_red_sm5683 initSM, l18bt_red_pm10865 initPM, l18bt_red_pm10866 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5685
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 6's
-- zigzag attention entry.
theorem recon_zigzagGoal_5685_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5685)
      (denoteGraphDistributedFaithful pm initPM 10867)
      (denoteGraphDistributedFaithful pm initPM 10868)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5683_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5684 =
      denoteGraphDistributedFaithful pm initPM 5684 :=
    l18bt_weight_eq initSM initPM hInit 5684 initGoal_5684 (by native_decide)
      rfl rfl rfl rfl
      l18bt_weights_not_written.1.2.2 l18bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5684).shape = [16, 64, 1024] :=
    l18bt_pm_weight_shape initPM hPM 5684 [16, 64, 1024] (by native_decide)
      l18bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5683)
      (denoteGraphDistributedFaithful pm initPM 10865)
      (denoteGraphDistributedFaithful pm initPM 10866)
      (denoteGraphDistributedFaithful pm initPM 5639)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l18bt_red_sm5685 initSM, l18bt_red_pm10867 initPM, l18bt_red_pm10868 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
