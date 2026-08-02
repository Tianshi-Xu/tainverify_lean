/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L22FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L21FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-10 tail (MoE join -> block-10 Q)

Mechanical transport of the (green) block-9 tail `L13FaithfulBlockTail` to
block 10.  The block-10 cu tensor is **5835**.

* SM 877 `FW_all2all_moe_gmm [8552,5850,5851,5853,5854] -> [5855]` (PM 1816/1819 -> 11461/11462)
* SM 880 `FW_reshape [5869] -> [5870]`                             (PM 1822/1823 -> 11515/11516)
* SM 881 `FW_mix_precision_linear [5870,5871] -> [5872]`           (PM 1824/1825 -> 11521/11522)
* SM 882 `FW_view [5872] -> [5873]`                                (PM 1826/1827 -> 11531/11532)
* SM 883 `FW_mul [5860,5873] -> [5874]` (broadcast `[N,1]x[N,1024]`)(PM 1828/1829 -> 11535/11536)
* SM 884 `FW_add [5855,5874] -> [5875]`                            (PM 1830/1831 -> 11539/11540)
* SM 885 `FW_float [5875] -> [5876]`                               (PM 1832/1833 -> 11545/11546)
* SM 886 `FW_add [8541,5876] -> [5877]`                            (PM 1834/1835 -> 11549/11550)
* SM 887 `FW_multiref [5877] -> [8568,8572]`                       (PM 1836/1837)
* SM 888 `FW_rms_norm [8568,5878] -> [5879]`                       (PM 1838/1839 -> 11553/11554)
* SM 889 `FW_per_head_mix_precision_linear [5879,5880] -> [5881]`  (PM 1840/1841 -> 11555/11556)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8572_faithful` -- the cross-layer residual bypass consumed by
  block 10 (SM node 896 `FW_add`);
* `recon_zigzagGoal_5881_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 10's zigzag attention entry.

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

private theorem l22bt_reduce7
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

private theorem l22bt_reduce5
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
private def l22btSmMoE5855 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8552,5850,5851,5853,5854], outs := [5855],
    params := [64,0,64,8] }
private def l22btSmResh5870 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5869], outs := [5870],
    params := [4096,512] }
private def l22btSmMPL5872 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5870,5871], outs := [5872] }
private def l22btSmView5873 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5872], outs := [5873],
    params := [4096,1024] }
private def l22btSmMul5874 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5860,5873], outs := [5874] }
private def l22btSmAdd5875 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5855,5874], outs := [5875] }
private def l22btSmFloat5876 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5875], outs := [5876] }
private def l22btSmAdd5877 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8541,5876], outs := [5877] }
private def l22btSmMref5877 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5877], outs := [8568,8572],
    params := [2] }
private def l22btSmRms5879 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8568,5878], outs := [5879] }
private def l22btSmPhl5881 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5879,5880], outs := [5881] }

private def l22btPmMoE11461 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16788,11451,11453,11457,11459], outs := [11461],
    params := [64,0,32,8] }
private def l22btPmMoE11462 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16811,11452,11454,11458,11460], outs := [11462],
    params := [64,32,64,8] }
private def l22btPmResh11515 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11513], outs := [11515],
    params := [2048,512] }
private def l22btPmResh11516 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11514], outs := [11516],
    params := [2048,512] }
private def l22btPmMPL11521 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11515,5871], outs := [11521] }
private def l22btPmMPL11522 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11516,5871], outs := [11522] }
private def l22btPmView11531 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11521], outs := [11531],
    params := [2048,1024] }
private def l22btPmView11532 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11522], outs := [11532],
    params := [2048,1024] }
private def l22btPmMul11535 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11475,11531], outs := [11535] }
private def l22btPmMul11536 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11476,11532], outs := [11536] }
private def l22btPmAdd11539 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11461,11535], outs := [11539] }
private def l22btPmAdd11540 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11462,11536], outs := [11540] }
private def l22btPmFloat11545 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11539], outs := [11545] }
private def l22btPmFloat11546 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11540], outs := [11546] }
private def l22btPmAdd11549 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16769,11545], outs := [11549] }
private def l22btPmAdd11550 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16777,11546], outs := [11550] }
private def l22btPmMref11549 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11549], outs := [16827,16831],
    params := [2] }
private def l22btPmMref11550 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11550], outs := [16835,16839],
    params := [2] }
private def l22btPmRms11553 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16827,5878], outs := [11553] }
private def l22btPmRms11554 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16835,5878], outs := [11554] }
private def l22btPmPhl11555 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11553,5880], outs := [11555] }
private def l22btPmPhl11556 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11554,5880], outs := [11556] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l22bt_sm_node_facts :
    sm.nodes[877]'(by native_decide) = l22btSmMoE5855 ∧
    sm.nodes[880]'(by native_decide) = l22btSmResh5870 ∧
    sm.nodes[881]'(by native_decide) = l22btSmMPL5872 ∧
    sm.nodes[882]'(by native_decide) = l22btSmView5873 ∧
    sm.nodes[883]'(by native_decide) = l22btSmMul5874 ∧
    sm.nodes[884]'(by native_decide) = l22btSmAdd5875 ∧
    sm.nodes[885]'(by native_decide) = l22btSmFloat5876 ∧
    sm.nodes[886]'(by native_decide) = l22btSmAdd5877 ∧
    sm.nodes[887]'(by native_decide) = l22btSmMref5877 ∧
    sm.nodes[888]'(by native_decide) = l22btSmRms5879 ∧
    sm.nodes[889]'(by native_decide) = l22btSmPhl5881 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l22bt_pm_node_facts :
    pm.nodes[1816]'(by native_decide) = l22btPmMoE11461 ∧
    pm.nodes[1819]'(by native_decide) = l22btPmMoE11462 ∧
    pm.nodes[1822]'(by native_decide) = l22btPmResh11515 ∧
    pm.nodes[1823]'(by native_decide) = l22btPmResh11516 ∧
    pm.nodes[1824]'(by native_decide) = l22btPmMPL11521 ∧
    pm.nodes[1825]'(by native_decide) = l22btPmMPL11522 ∧
    pm.nodes[1826]'(by native_decide) = l22btPmView11531 ∧
    pm.nodes[1827]'(by native_decide) = l22btPmView11532 ∧
    pm.nodes[1828]'(by native_decide) = l22btPmMul11535 ∧
    pm.nodes[1829]'(by native_decide) = l22btPmMul11536 ∧
    pm.nodes[1830]'(by native_decide) = l22btPmAdd11539 ∧
    pm.nodes[1831]'(by native_decide) = l22btPmAdd11540 ∧
    pm.nodes[1832]'(by native_decide) = l22btPmFloat11545 ∧
    pm.nodes[1833]'(by native_decide) = l22btPmFloat11546 ∧
    pm.nodes[1834]'(by native_decide) = l22btPmAdd11549 ∧
    pm.nodes[1835]'(by native_decide) = l22btPmAdd11550 ∧
    pm.nodes[1836]'(by native_decide) = l22btPmMref11549 ∧
    pm.nodes[1837]'(by native_decide) = l22btPmMref11550 ∧
    pm.nodes[1838]'(by native_decide) = l22btPmRms11553 ∧
    pm.nodes[1839]'(by native_decide) = l22btPmRms11554 ∧
    pm.nodes[1840]'(by native_decide) = l22btPmPhl11555 ∧
    pm.nodes[1841]'(by native_decide) = l22btPmPhl11556 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l22bt_buddy_facts :
    sm.replicaBuddies l22btSmMoE5855 = [l22btSmMoE5855] ∧
    pm.replicaBuddies l22btPmMoE11461 = [l22btPmMoE11461, l22btPmMoE11462] ∧
    pm.replicaBuddies l22btPmMoE11462 = [l22btPmMoE11461, l22btPmMoE11462] := by
  native_decide

private theorem l22bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l22bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l22bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5871 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5878 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5880 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5871 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5878 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5880 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l22bt_cu_not_written : ∀ n ∈ pm.nodes, 5835 ∉ n.outs := by
  native_decide

private theorem l22bt_w5871_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5871 ∉ n.outs := by
  intro n hn
  exact l22bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l22bt_w5871_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5871 ∉ n.outs := by
  intro n hn
  exact l22bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l22bt_w5878_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5878 ∉ n.outs := by
  intro n hn
  exact l22bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l22bt_w5878_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5878 ∉ n.outs := by
  intro n hn
  exact l22bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l22bt_w5880_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5880 ∉ n.outs := by
  intro n hn
  exact l22bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l22bt_w5880_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5880 ∉ n.outs := by
  intro n hn
  exact l22bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l22bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(878, 5855), (877, 8552), (877, 5850), (877, 5851), (877, 5853), (877, 5854), (881, 5870), (880, 5869), (882, 5872), (881, 5870), (883, 5873), (882, 5872), (884, 5874), (883, 5860), (883, 5873), (885, 5875), (884, 5855), (884, 5874), (886, 5876), (885, 5875), (887, 5877), (886, 8541), (886, 5876), (888, 8568), (888, 8572), (887, 5877), (889, 5879), (888, 8568), (890, 5881), (889, 5879)]) :
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
private theorem l22bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1817, 11461), (1816, 16788), (1816, 11451), (1816, 11453), (1816, 11457), (1816, 11459), (1816, 11458), (1816, 11460), (1820, 11462), (1819, 16811), (1819, 11452), (1819, 11454), (1819, 11457), (1819, 11458), (1819, 11459), (1819, 11460), (1823, 11515), (1822, 11513), (1824, 11516), (1823, 11514), (1825, 11521), (1824, 11515), (1826, 11522), (1825, 11516), (1827, 11531), (1826, 11521), (1828, 11532), (1827, 11522), (1829, 11535), (1828, 11475), (1828, 11531), (1830, 11536), (1829, 11476), (1829, 11532), (1831, 11539), (1830, 11461), (1830, 11535), (1832, 11540), (1831, 11462), (1831, 11536), (1833, 11545), (1832, 11539), (1834, 11546), (1833, 11540), (1835, 11549), (1834, 16769), (1834, 11545), (1836, 11550), (1835, 16777), (1835, 11546), (1837, 16827), (1837, 16831), (1836, 11549), (1838, 16835), (1838, 16839), (1837, 11550), (1839, 11553), (1838, 16827), (1840, 11554), (1839, 16835), (1841, 11555), (1840, 11553), (1842, 11556), (1841, 11554)]) :
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
private theorem l22bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5853, 5854]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l22bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [11457, 11458, 11459, 11460]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l22bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5853, 5854]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l22bt_sm_leaf_not_written tid h)

private theorem l22bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [11457, 11458, 11459, 11460]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l22bt_pm_leaf_not_written tid h)

private theorem l22bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5855 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5855 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5855 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8552)
        (denoteGraphDistributedFaithful sm initSM 5850)
        (denoteGraphDistributedFaithful sm initSM 5851)
        [denoteGraphDistributedFaithful sm initSM 5853]
        [denoteGraphDistributedFaithful sm initSM 5854]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l22bt_reduce5 sm initSM 877 l22btSmMoE5855
    8552 5850 5851 5853 5854 5855
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l22bt_sm_node_facts.1 ?_
    (l22bt_nonempty_sm 878) (l22bt_sm_not_written 878 5855 (by decide))
    (l22bt_nonempty_sm 877) (l22bt_sm_not_written 877 8552 (by decide))
    (l22bt_sm_not_written 877 5850 (by decide))
    (l22bt_sm_not_written 877 5851 (by decide))
    (l22bt_sm_not_written 877 5853 (by decide))
    (l22bt_sm_not_written 877 5854 (by decide))
  intro s
  have hb := l22bt_buddy_facts.1
  unfold l22btSmMoE5855 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8552 5850 5851 5853 5854 5855 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11461 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11461 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16788)
        (denoteGraphDistributedFaithful pm initPM 11451)
        (denoteGraphDistributedFaithful pm initPM 11453)
        [denoteGraphDistributedFaithful pm initPM 11457,
         denoteGraphDistributedFaithful pm initPM 11458]
        [denoteGraphDistributedFaithful pm initPM 11459,
         denoteGraphDistributedFaithful pm initPM 11460]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l22bt_reduce7 pm initPM 1816 l22btPmMoE11461
    16788 11451 11453 11457 11459 11458 11460 11461
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l22bt_pm_node_facts.1 ?_
    (l22bt_nonempty_pm 1817) (l22bt_pm_not_written 1817 11461 (by decide))
    (l22bt_nonempty_pm 1816) (l22bt_pm_not_written 1816 16788 (by decide))
    (l22bt_pm_not_written 1816 11451 (by decide))
    (l22bt_pm_not_written 1816 11453 (by decide))
    (l22bt_pm_not_written 1816 11457 (by decide))
    (l22bt_pm_not_written 1816 11459 (by decide))
    (l22bt_pm_not_written 1816 11458 (by decide))
    (l22bt_pm_not_written 1816 11460 (by decide))
  intro s
  have hb := l22bt_buddy_facts.2.1
  unfold l22btPmMoE11461 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16788 11451 11453 11457 11459 11461 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11462 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11462 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16811)
        (denoteGraphDistributedFaithful pm initPM 11452)
        (denoteGraphDistributedFaithful pm initPM 11454)
        [denoteGraphDistributedFaithful pm initPM 11457,
         denoteGraphDistributedFaithful pm initPM 11458]
        [denoteGraphDistributedFaithful pm initPM 11459,
         denoteGraphDistributedFaithful pm initPM 11460]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l22bt_reduce7 pm initPM 1819 l22btPmMoE11462
    16811 11452 11454 11457 11458 11459 11460 11462
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l22bt_pm_node_facts.2.1 ?_
    (l22bt_nonempty_pm 1820) (l22bt_pm_not_written 1820 11462 (by decide))
    (l22bt_nonempty_pm 1819) (l22bt_pm_not_written 1819 16811 (by decide))
    (l22bt_pm_not_written 1819 11452 (by decide))
    (l22bt_pm_not_written 1819 11454 (by decide))
    (l22bt_pm_not_written 1819 11457 (by decide))
    (l22bt_pm_not_written 1819 11458 (by decide))
    (l22bt_pm_not_written 1819 11459 (by decide))
    (l22bt_pm_not_written 1819 11460 (by decide))
  intro s
  have hb := l22bt_buddy_facts.2.2
  unfold l22btPmMoE11462 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16811 11452 11454 11458 11460 11462 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5870 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5870 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5870 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5869) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 880 l22btSmResh5870
    5869 5870 (fun x => fw_view [4096,512] x)
    (by native_decide) l22bt_sm_node_facts.2.1 ?_
    (l22bt_nonempty_sm 881) (l22bt_sm_not_written 881 5870 (by decide))
    (l22bt_nonempty_sm 880) (l22bt_sm_not_written 880 5869 (by decide))
  intro s
  unfold l22btSmResh5870
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5869 5870 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11515 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11515 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11513) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1822 l22btPmResh11515
    11513 11515 (fun x => fw_view [2048,512] x)
    (by native_decide) l22bt_pm_node_facts.2.2.1 ?_
    (l22bt_nonempty_pm 1823) (l22bt_pm_not_written 1823 11515 (by decide))
    (l22bt_nonempty_pm 1822) (l22bt_pm_not_written 1822 11513 (by decide))
  intro s
  unfold l22btPmResh11515
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11513 11515 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11516 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11516 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11514) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1823 l22btPmResh11516
    11514 11516 (fun x => fw_view [2048,512] x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.1 ?_
    (l22bt_nonempty_pm 1824) (l22bt_pm_not_written 1824 11516 (by decide))
    (l22bt_nonempty_pm 1823) (l22bt_pm_not_written 1823 11514 (by decide))
  intro s
  unfold l22btPmResh11516
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11514 11516 [2048,512]

/-! ### Node reductions: down-projection 5872 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5872 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5872 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5870)
        (denoteGraphDistributedFaithful sm initSM 5871) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 881 l22btSmMPL5872
    5870 5871 5872 fw_linear
    (by native_decide) l22bt_sm_node_facts.2.2.1 ?_
    (l22bt_nonempty_sm 882) (l22bt_sm_not_written 882 5872 (by decide))
    (l22bt_nonempty_sm 881) (l22bt_sm_not_written 881 5870 (by decide))
    (l22bt_w5871_sm_drop 881)
  intro s
  unfold l22btSmMPL5872
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5870 5871 5872

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11521 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11521 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11515)
        (denoteGraphDistributedFaithful pm initPM 5871) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1824 l22btPmMPL11521
    11515 5871 11521 fw_linear
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1825) (l22bt_pm_not_written 1825 11521 (by decide))
    (l22bt_nonempty_pm 1824) (l22bt_pm_not_written 1824 11515 (by decide))
    (l22bt_w5871_pm_drop 1824)
  intro s
  unfold l22btPmMPL11521
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11515 5871 11521

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11522 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11522 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11516)
        (denoteGraphDistributedFaithful pm initPM 5871) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1825 l22btPmMPL11522
    11516 5871 11522 fw_linear
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1826) (l22bt_pm_not_written 1826 11522 (by decide))
    (l22bt_nonempty_pm 1825) (l22bt_pm_not_written 1825 11516 (by decide))
    (l22bt_w5871_pm_drop 1825)
  intro s
  unfold l22btPmMPL11522
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11516 5871 11522

/-! ### Node reductions: view 5873 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5873 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5873 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5872) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 882 l22btSmView5873
    5872 5873 (fun x => fw_view [4096,1024] x)
    (by native_decide) l22bt_sm_node_facts.2.2.2.1 ?_
    (l22bt_nonempty_sm 883) (l22bt_sm_not_written 883 5873 (by decide))
    (l22bt_nonempty_sm 882) (l22bt_sm_not_written 882 5872 (by decide))
  intro s
  unfold l22btSmView5873
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5872 5873

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11531 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11531 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11521) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1826 l22btPmView11531
    11521 11531 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1827) (l22bt_pm_not_written 1827 11531 (by decide))
    (l22bt_nonempty_pm 1826) (l22bt_pm_not_written 1826 11521 (by decide))
  intro s
  unfold l22btPmView11531
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11521 11531

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11532 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11532 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11522) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1827 l22btPmView11532
    11522 11532 (fun x => fw_view [2048,1024] x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1828) (l22bt_pm_not_written 1828 11532 (by decide))
    (l22bt_nonempty_pm 1827) (l22bt_pm_not_written 1827 11522 (by decide))
  intro s
  unfold l22btPmView11532
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11522 11532

/-! ### Node reductions: gated multiply 5874 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5874 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5874 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5860)
        (denoteGraphDistributedFaithful sm initSM 5873) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 883 l22btSmMul5874
    5860 5873 5874 elemwiseMul
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.1 ?_
    (l22bt_nonempty_sm 884) (l22bt_sm_not_written 884 5874 (by decide))
    (l22bt_nonempty_sm 883) (l22bt_sm_not_written 883 5860 (by decide))
    (l22bt_sm_not_written 883 5873 (by decide))
  intro s
  unfold l22btSmMul5874
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5860 5873 5874

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11535 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11535 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11475)
        (denoteGraphDistributedFaithful pm initPM 11531) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1828 l22btPmMul11535
    11475 11531 11535 elemwiseMul
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1829) (l22bt_pm_not_written 1829 11535 (by decide))
    (l22bt_nonempty_pm 1828) (l22bt_pm_not_written 1828 11475 (by decide))
    (l22bt_pm_not_written 1828 11531 (by decide))
  intro s
  unfold l22btPmMul11535
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 11475 11531 11535

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11536 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11536 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11476)
        (denoteGraphDistributedFaithful pm initPM 11532) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1829 l22btPmMul11536
    11476 11532 11536 elemwiseMul
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1830) (l22bt_pm_not_written 1830 11536 (by decide))
    (l22bt_nonempty_pm 1829) (l22bt_pm_not_written 1829 11476 (by decide))
    (l22bt_pm_not_written 1829 11532 (by decide))
  intro s
  unfold l22btPmMul11536
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 11476 11532 11536

/-! ### Node reductions: MoE join 5875 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5875 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5875 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5855)
        (denoteGraphDistributedFaithful sm initSM 5874) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 884 l22btSmAdd5875
    5855 5874 5875 elemwiseAdd
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l22bt_nonempty_sm 885) (l22bt_sm_not_written 885 5875 (by decide))
    (l22bt_nonempty_sm 884) (l22bt_sm_not_written 884 5855 (by decide))
    (l22bt_sm_not_written 884 5874 (by decide))
  intro s
  unfold l22btSmAdd5875
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5855 5874 5875

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11539 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11539 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11461)
        (denoteGraphDistributedFaithful pm initPM 11535) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1830 l22btPmAdd11539
    11461 11535 11539 elemwiseAdd
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1831) (l22bt_pm_not_written 1831 11539 (by decide))
    (l22bt_nonempty_pm 1830) (l22bt_pm_not_written 1830 11461 (by decide))
    (l22bt_pm_not_written 1830 11535 (by decide))
  intro s
  unfold l22btPmAdd11539
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 11461 11535 11539

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11540 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11540 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11462)
        (denoteGraphDistributedFaithful pm initPM 11536) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1831 l22btPmAdd11540
    11462 11536 11540 elemwiseAdd
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1832) (l22bt_pm_not_written 1832 11540 (by decide))
    (l22bt_nonempty_pm 1831) (l22bt_pm_not_written 1831 11462 (by decide))
    (l22bt_pm_not_written 1831 11536 (by decide))
  intro s
  unfold l22btPmAdd11540
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 11462 11536 11540

/-! ### Node reductions: float 5876 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5876 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5876 =
      denoteGraphDistributedFaithful sm initSM 5875 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 885 l22btSmFloat5876
    5875 5876 (fun x => x)
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_sm 886) (l22bt_sm_not_written 886 5876 (by decide))
    (l22bt_nonempty_sm 885) (l22bt_sm_not_written 885 5875 (by decide))
  intro s
  unfold l22btSmFloat5876
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5875 5876 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11545 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11545 =
      denoteGraphDistributedFaithful pm initPM 11539 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1832 l22btPmFloat11545
    11539 11545 (fun x => x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1833) (l22bt_pm_not_written 1833 11545 (by decide))
    (l22bt_nonempty_pm 1832) (l22bt_pm_not_written 1832 11539 (by decide))
  intro s
  unfold l22btPmFloat11545
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 11539 11545 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11546 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11546 =
      denoteGraphDistributedFaithful pm initPM 11540 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1833 l22btPmFloat11546
    11540 11546 (fun x => x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1834) (l22bt_pm_not_written 1834 11546 (by decide))
    (l22bt_nonempty_pm 1833) (l22bt_pm_not_written 1833 11540 (by decide))
  intro s
  unfold l22btPmFloat11546
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 11540 11546 []

/-! ### Node reductions: residual join 5877 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5877 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5877 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8541)
        (denoteGraphDistributedFaithful sm initSM 5876) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 886 l22btSmAdd5877
    8541 5876 5877 elemwiseAdd
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_sm 887) (l22bt_sm_not_written 887 5877 (by decide))
    (l22bt_nonempty_sm 886) (l22bt_sm_not_written 886 8541 (by decide))
    (l22bt_sm_not_written 886 5876 (by decide))
  intro s
  unfold l22btSmAdd5877
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8541 5876 5877

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11549 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11549 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16769)
        (denoteGraphDistributedFaithful pm initPM 11545) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1834 l22btPmAdd11549
    16769 11545 11549 elemwiseAdd
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1835) (l22bt_pm_not_written 1835 11549 (by decide))
    (l22bt_nonempty_pm 1834) (l22bt_pm_not_written 1834 16769 (by decide))
    (l22bt_pm_not_written 1834 11545 (by decide))
  intro s
  unfold l22btPmAdd11549
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16769 11545 11549

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11550 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11550 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16777)
        (denoteGraphDistributedFaithful pm initPM 11546) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1835 l22btPmAdd11550
    16777 11546 11550 elemwiseAdd
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1836) (l22bt_pm_not_written 1836 11550 (by decide))
    (l22bt_nonempty_pm 1835) (l22bt_pm_not_written 1835 16777 (by decide))
    (l22bt_pm_not_written 1835 11546 (by decide))
  intro s
  unfold l22btPmAdd11550
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16777 11546 11550

/-! ### Node reductions: 2-way multiref off 5877 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm8568 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8568 =
      denoteGraphDistributedFaithful sm initSM 5877 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 887 l22btSmMref5877
    5877 8568 (fun x => x)
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_sm 888) (l22bt_sm_not_written 888 8568 (by decide))
    (l22bt_nonempty_sm 887) (l22bt_sm_not_written 887 5877 (by decide))
  intro s
  unfold l22btSmMref5877
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5877 8568 8572

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm8572 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8572 =
      denoteGraphDistributedFaithful sm initSM 5877 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 887 l22btSmMref5877
    5877 8572 (fun x => x)
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_sm 888) (l22bt_sm_not_written 888 8572 (by decide))
    (l22bt_nonempty_sm 887) (l22bt_sm_not_written 887 5877 (by decide))
  intro s
  unfold l22btSmMref5877
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5877 8568 8572 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm16827 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16827 =
      denoteGraphDistributedFaithful pm initPM 11549 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1836 l22btPmMref11549
    11549 16827 (fun x => x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1837) (l22bt_pm_not_written 1837 16827 (by decide))
    (l22bt_nonempty_pm 1836) (l22bt_pm_not_written 1836 11549 (by decide))
  intro s
  unfold l22btPmMref11549
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11549 16827 16831

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm16831 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16831 =
      denoteGraphDistributedFaithful pm initPM 11549 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1836 l22btPmMref11549
    11549 16831 (fun x => x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1837) (l22bt_pm_not_written 1837 16831 (by decide))
    (l22bt_nonempty_pm 1836) (l22bt_pm_not_written 1836 11549 (by decide))
  intro s
  unfold l22btPmMref11549
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11549 16827 16831 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm16835 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16835 =
      denoteGraphDistributedFaithful pm initPM 11550 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1837 l22btPmMref11550
    11550 16835 (fun x => x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1838) (l22bt_pm_not_written 1838 16835 (by decide))
    (l22bt_nonempty_pm 1837) (l22bt_pm_not_written 1837 11550 (by decide))
  intro s
  unfold l22btPmMref11550
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11550 16835 16839

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm16839 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16839 =
      denoteGraphDistributedFaithful pm initPM 11550 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1837 l22btPmMref11550
    11550 16839 (fun x => x)
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1838) (l22bt_pm_not_written 1838 16839 (by decide))
    (l22bt_nonempty_pm 1837) (l22bt_pm_not_written 1837 11550 (by decide))
  intro s
  unfold l22btPmMref11550
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11550 16835 16839 (by decide)

/-! ### Node reductions: RMSNorm 5879 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5879 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5879 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8568)
        (denoteGraphDistributedFaithful sm initSM 5878) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 888 l22btSmRms5879
    8568 5878 5879 fw_rms_norm
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_sm 889) (l22bt_sm_not_written 889 5879 (by decide))
    (l22bt_nonempty_sm 888) (l22bt_sm_not_written 888 8568 (by decide))
    (l22bt_w5878_sm_drop 888)
  intro s
  unfold l22btSmRms5879
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8568 5878 5879

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11553 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11553 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16827)
        (denoteGraphDistributedFaithful pm initPM 5878) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1838 l22btPmRms11553
    16827 5878 11553 fw_rms_norm
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1839) (l22bt_pm_not_written 1839 11553 (by decide))
    (l22bt_nonempty_pm 1838) (l22bt_pm_not_written 1838 16827 (by decide))
    (l22bt_w5878_pm_drop 1838)
  intro s
  unfold l22btPmRms11553
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16827 5878 11553

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11554 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11554 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16835)
        (denoteGraphDistributedFaithful pm initPM 5878) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1839 l22btPmRms11554
    16835 5878 11554 fw_rms_norm
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1840) (l22bt_pm_not_written 1840 11554 (by decide))
    (l22bt_nonempty_pm 1839) (l22bt_pm_not_written 1839 16835 (by decide))
    (l22bt_w5878_pm_drop 1839)
  intro s
  unfold l22btPmRms11554
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16835 5878 11554

/-! ### Node reductions: per-head Q projection 5881 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_sm5881 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5881 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5879)
        (denoteGraphDistributedFaithful sm initSM 5880) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 889 l22btSmPhl5881
    5879 5880 5881 fw_per_head_linear
    (by native_decide) l22bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l22bt_nonempty_sm 890) (l22bt_sm_not_written 890 5881 (by decide))
    (l22bt_nonempty_sm 889) (l22bt_sm_not_written 889 5879 (by decide))
    (l22bt_w5880_sm_drop 889)
  intro s
  unfold l22btSmPhl5881
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5879 5880 5881 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11555 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11555 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11553)
        (denoteGraphDistributedFaithful pm initPM 5880) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1840 l22btPmPhl11555
    11553 5880 11555 fw_per_head_linear
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l22bt_nonempty_pm 1841) (l22bt_pm_not_written 1841 11555 (by decide))
    (l22bt_nonempty_pm 1840) (l22bt_pm_not_written 1840 11553 (by decide))
    (l22bt_w5880_pm_drop 1840)
  intro s
  unfold l22btPmPhl11555
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 11553 5880 11555 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_red_pm11556 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11556 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11554)
        (denoteGraphDistributedFaithful pm initPM 5880) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1841 l22btPmPhl11556
    11554 5880 11556 fw_per_head_linear
    (by native_decide) l22bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l22bt_nonempty_pm 1842) (l22bt_pm_not_written 1842 11556 (by decide))
    (l22bt_nonempty_pm 1841) (l22bt_pm_not_written 1841 11554 (by decide))
    (l22bt_w5880_pm_drop 1841)
  intro s
  unfold l22btPmPhl11556
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 11554 5880 11556 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l22bt_weight_bridge (initSM initPM : Store)
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
private theorem l22bt_weight_eq (initSM initPM : Store)
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
private theorem l22bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l22bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l22bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5835) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5835).shape = [2] := by
    rw [l22bt_pmFinal initPM 5835 l22bt_cu_not_written]
    exact hPM 5835 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5835)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5855 (block-9 MoE expert layer).
theorem recon_zigzagGoal_5855_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5855)
      (denoteGraphDistributedFaithful pm initPM 11461)
      (denoteGraphDistributedFaithful pm initPM 11462)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8552_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5850_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5851_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l22bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8552)
      (denoteGraphDistributedFaithful pm initPM 16788)
      (denoteGraphDistributedFaithful pm initPM 16811)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5850)
      (denoteGraphDistributedFaithful pm initPM 11451)
      (denoteGraphDistributedFaithful pm initPM 11452)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5851)
      (denoteGraphDistributedFaithful pm initPM 11453)
      (denoteGraphDistributedFaithful pm initPM 11454)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5853 = allGatherPrimDimN 0 2 0 [initPM 11457, initPM 11458] :=
    l22bt_weight_bridge initSM initPM hInit initGoal_5853 (by native_decide)
      5853 11457 11458 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5854 = allGatherPrimDimN 0 2 0 [initPM 11459, initPM 11460] :=
    l22bt_weight_bridge initSM initPM hInit initGoal_5854 (by native_decide)
      5854 11459 11460 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5853).shape = [64, 1024, 1024] :=
    hSM 5853 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5854).shape = [64, 1024, 512] :=
    hSM 5854 [64, 1024, 512] (by native_decide)
  rw [l22bt_red_sm5855 initSM, l22bt_red_pm11461 initPM, l22bt_red_pm11462 initPM]
  rw [l22bt_sm_leaf initSM 5853 (by decide), l22bt_sm_leaf initSM 5854 (by decide),
    l22bt_pm_leaf initPM 11457 (by decide), l22bt_pm_leaf initPM 11458 (by decide),
    l22bt_pm_leaf initPM 11459 (by decide), l22bt_pm_leaf initPM 11460 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5853) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5854) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 11457, initPM 11458])
    (allGatherPrimDimN 0 2 0 [initPM 11459, initPM 11460])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5870 (`FW_reshape`).
theorem recon_zigzagGoal_5870_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5870)
      (denoteGraphDistributedFaithful pm initPM 11515)
      (denoteGraphDistributedFaithful pm initPM 11516)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5869_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22bt_red_sm5870 initSM, l22bt_red_pm11515 initPM, l22bt_red_pm11516 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5872 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5872_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5872)
      (denoteGraphDistributedFaithful pm initPM 11521)
      (denoteGraphDistributedFaithful pm initPM 11522)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5870_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5871 =
      denoteGraphDistributedFaithful pm initPM 5871 :=
    l22bt_weight_eq initSM initPM hInit 5871 initGoal_5871 (by native_decide)
      rfl rfl rfl rfl
      l22bt_weights_not_written.1.1 l22bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5871).shape = [1024, 512] :=
    l22bt_pm_weight_shape initPM hPM 5871 [1024, 512] (by native_decide)
      l22bt_weights_not_written.2.1
  rw [l22bt_red_sm5872 initSM, l22bt_red_pm11521 initPM, l22bt_red_pm11522 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5873 (`FW_view`).
theorem recon_zigzagGoal_5873_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5873)
      (denoteGraphDistributedFaithful pm initPM 11531)
      (denoteGraphDistributedFaithful pm initPM 11532)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5872_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22bt_red_sm5873 initSM, l22bt_red_pm11531 initPM, l22bt_red_pm11532 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5874 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5874_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5874)
      (denoteGraphDistributedFaithful pm initPM 11535)
      (denoteGraphDistributedFaithful pm initPM 11536)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5860_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5873_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5860)
      (denoteGraphDistributedFaithful pm initPM 11475)
      (denoteGraphDistributedFaithful pm initPM 11476)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5873)
      (denoteGraphDistributedFaithful pm initPM 11531)
      (denoteGraphDistributedFaithful pm initPM 11532)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l22bt_red_sm5874 initSM, l22bt_red_pm11535 initPM, l22bt_red_pm11536 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5875 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5875_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5875)
      (denoteGraphDistributedFaithful pm initPM 11539)
      (denoteGraphDistributedFaithful pm initPM 11540)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5855_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5874_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5855)
      (denoteGraphDistributedFaithful pm initPM 11461)
      (denoteGraphDistributedFaithful pm initPM 11462)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5874)
      (denoteGraphDistributedFaithful pm initPM 11535)
      (denoteGraphDistributedFaithful pm initPM 11536)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l22bt_red_sm5875 initSM, l22bt_red_pm11539 initPM, l22bt_red_pm11540 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5876 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5876_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5876)
      (denoteGraphDistributedFaithful pm initPM 11545)
      (denoteGraphDistributedFaithful pm initPM 11546)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5875_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22bt_red_sm5876 initSM, l22bt_red_pm11545 initPM, l22bt_red_pm11546 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5877 (`FW_add`, residual join).
theorem recon_zigzagGoal_5877_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5877)
      (denoteGraphDistributedFaithful pm initPM 11549)
      (denoteGraphDistributedFaithful pm initPM 11550)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8541_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5876_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8541)
      (denoteGraphDistributedFaithful pm initPM 16769)
      (denoteGraphDistributedFaithful pm initPM 16777)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5876)
      (denoteGraphDistributedFaithful pm initPM 11545)
      (denoteGraphDistributedFaithful pm initPM 11546)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l22bt_red_sm5877 initSM, l22bt_red_pm11549 initPM, l22bt_red_pm11550 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8568 (multiref position 0 off 5877).
theorem recon_zigzagGoal_8568_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8568)
      (denoteGraphDistributedFaithful pm initPM 16827)
      (denoteGraphDistributedFaithful pm initPM 16835)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5877_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22bt_red_sm8568 initSM, l22bt_red_pm16827 initPM, l22bt_red_pm16835 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8572 (multiref position 1
-- off 5877): the cross-layer residual bypass consumed by block 10's `FW_add`.
theorem recon_zigzagGoal_8572_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8572)
      (denoteGraphDistributedFaithful pm initPM 16831)
      (denoteGraphDistributedFaithful pm initPM 16839)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5877_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l22bt_red_sm8572 initSM, l22bt_red_pm16831 initPM, l22bt_red_pm16839 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5879 (`FW_rms_norm`).
theorem recon_zigzagGoal_5879_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5879)
      (denoteGraphDistributedFaithful pm initPM 11553)
      (denoteGraphDistributedFaithful pm initPM 11554)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8568_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5878 =
      denoteGraphDistributedFaithful pm initPM 5878 :=
    l22bt_weight_eq initSM initPM hInit 5878 initGoal_5878 (by native_decide)
      rfl rfl rfl rfl
      l22bt_weights_not_written.1.2.1 l22bt_weights_not_written.2.2.1
  rw [l22bt_red_sm5879 initSM, l22bt_red_pm11553 initPM, l22bt_red_pm11554 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5881
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 10's
-- zigzag attention entry.
theorem recon_zigzagGoal_5881_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5881)
      (denoteGraphDistributedFaithful pm initPM 11555)
      (denoteGraphDistributedFaithful pm initPM 11556)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5879_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5880 =
      denoteGraphDistributedFaithful pm initPM 5880 :=
    l22bt_weight_eq initSM initPM hInit 5880 initGoal_5880 (by native_decide)
      rfl rfl rfl rfl
      l22bt_weights_not_written.1.2.2 l22bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5880).shape = [16, 64, 1024] :=
    l22bt_pm_weight_shape initPM hPM 5880 [16, 64, 1024] (by native_decide)
      l22bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5879)
      (denoteGraphDistributedFaithful pm initPM 11553)
      (denoteGraphDistributedFaithful pm initPM 11554)
      (denoteGraphDistributedFaithful pm initPM 5835)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l22bt_red_sm5881 initSM, l22bt_red_pm11555 initPM, l22bt_red_pm11556 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
