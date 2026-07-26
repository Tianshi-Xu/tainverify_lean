/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L21FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L20FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-9 tail (MoE join -> block-9 Q)

Mechanical transport of the (green) block-8 tail `L13FaithfulBlockTail` to
block 9.  The block-9 cu tensor is **5786**.

* SM 842 `FW_all2all_moe_gmm [8513,5801,5802,5804,5805] -> [5806]` (PM 1746/1749 -> 11289/11290)
* SM 845 `FW_reshape [5820] -> [5821]`                             (PM 1752/1753 -> 11343/11344)
* SM 846 `FW_mix_precision_linear [5821,5822] -> [5823]`           (PM 1754/1755 -> 11349/11350)
* SM 847 `FW_view [5823] -> [5824]`                                (PM 1756/1757 -> 11359/11360)
* SM 848 `FW_mul [5811,5824] -> [5825]` (broadcast `[N,1]x[N,1024]`)(PM 1758/1759 -> 11363/11364)
* SM 849 `FW_add [5806,5825] -> [5826]`                            (PM 1760/1761 -> 11367/11368)
* SM 850 `FW_float [5826] -> [5827]`                               (PM 1762/1763 -> 11373/11374)
* SM 851 `FW_add [8502,5827] -> [5828]`                            (PM 1764/1765 -> 11377/11378)
* SM 852 `FW_multiref [5828] -> [8529,8533]`                       (PM 1766/1767)
* SM 853 `FW_rms_norm [8529,5829] -> [5830]`                       (PM 1768/1769 -> 11381/11382)
* SM 854 `FW_per_head_mix_precision_linear [5830,5831] -> [5832]`  (PM 1770/1771 -> 11383/11384)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8533_faithful` -- the cross-layer residual bypass consumed by
  block 9 (SM node 861 `FW_add`);
* `recon_zigzagGoal_5832_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 9's zigzag attention entry.

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

private theorem l21bt_reduce7
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

private theorem l21bt_reduce5
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
private def l21btSmMoE5806 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8513,5801,5802,5804,5805], outs := [5806],
    params := [64,0,64,8] }
private def l21btSmResh5821 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5820], outs := [5821],
    params := [4096,512] }
private def l21btSmMPL5823 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5821,5822], outs := [5823] }
private def l21btSmView5824 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5823], outs := [5824],
    params := [4096,1024] }
private def l21btSmMul5825 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5811,5824], outs := [5825] }
private def l21btSmAdd5826 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5806,5825], outs := [5826] }
private def l21btSmFloat5827 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5826], outs := [5827] }
private def l21btSmAdd5828 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8502,5827], outs := [5828] }
private def l21btSmMref5828 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5828], outs := [8529,8533],
    params := [2] }
private def l21btSmRms5830 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8529,5829], outs := [5830] }
private def l21btSmPhl5832 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5830,5831], outs := [5832] }

private def l21btPmMoE11289 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16710,11279,11281,11285,11287], outs := [11289],
    params := [64,0,32,8] }
private def l21btPmMoE11290 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16733,11280,11282,11286,11288], outs := [11290],
    params := [64,32,64,8] }
private def l21btPmResh11343 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11341], outs := [11343],
    params := [2048,512] }
private def l21btPmResh11344 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11342], outs := [11344],
    params := [2048,512] }
private def l21btPmMPL11349 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11343,5822], outs := [11349] }
private def l21btPmMPL11350 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11344,5822], outs := [11350] }
private def l21btPmView11359 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11349], outs := [11359],
    params := [2048,1024] }
private def l21btPmView11360 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11350], outs := [11360],
    params := [2048,1024] }
private def l21btPmMul11363 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11303,11359], outs := [11363] }
private def l21btPmMul11364 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11304,11360], outs := [11364] }
private def l21btPmAdd11367 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11289,11363], outs := [11367] }
private def l21btPmAdd11368 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11290,11364], outs := [11368] }
private def l21btPmFloat11373 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11367], outs := [11373] }
private def l21btPmFloat11374 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11368], outs := [11374] }
private def l21btPmAdd11377 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16691,11373], outs := [11377] }
private def l21btPmAdd11378 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16699,11374], outs := [11378] }
private def l21btPmMref11377 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11377], outs := [16749,16753],
    params := [2] }
private def l21btPmMref11378 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11378], outs := [16757,16761],
    params := [2] }
private def l21btPmRms11381 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16749,5829], outs := [11381] }
private def l21btPmRms11382 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16757,5829], outs := [11382] }
private def l21btPmPhl11383 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11381,5831], outs := [11383] }
private def l21btPmPhl11384 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11382,5831], outs := [11384] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l21bt_sm_node_facts :
    sm.nodes[842]'(by native_decide) = l21btSmMoE5806 ∧
    sm.nodes[845]'(by native_decide) = l21btSmResh5821 ∧
    sm.nodes[846]'(by native_decide) = l21btSmMPL5823 ∧
    sm.nodes[847]'(by native_decide) = l21btSmView5824 ∧
    sm.nodes[848]'(by native_decide) = l21btSmMul5825 ∧
    sm.nodes[849]'(by native_decide) = l21btSmAdd5826 ∧
    sm.nodes[850]'(by native_decide) = l21btSmFloat5827 ∧
    sm.nodes[851]'(by native_decide) = l21btSmAdd5828 ∧
    sm.nodes[852]'(by native_decide) = l21btSmMref5828 ∧
    sm.nodes[853]'(by native_decide) = l21btSmRms5830 ∧
    sm.nodes[854]'(by native_decide) = l21btSmPhl5832 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l21bt_pm_node_facts :
    pm.nodes[1746]'(by native_decide) = l21btPmMoE11289 ∧
    pm.nodes[1749]'(by native_decide) = l21btPmMoE11290 ∧
    pm.nodes[1752]'(by native_decide) = l21btPmResh11343 ∧
    pm.nodes[1753]'(by native_decide) = l21btPmResh11344 ∧
    pm.nodes[1754]'(by native_decide) = l21btPmMPL11349 ∧
    pm.nodes[1755]'(by native_decide) = l21btPmMPL11350 ∧
    pm.nodes[1756]'(by native_decide) = l21btPmView11359 ∧
    pm.nodes[1757]'(by native_decide) = l21btPmView11360 ∧
    pm.nodes[1758]'(by native_decide) = l21btPmMul11363 ∧
    pm.nodes[1759]'(by native_decide) = l21btPmMul11364 ∧
    pm.nodes[1760]'(by native_decide) = l21btPmAdd11367 ∧
    pm.nodes[1761]'(by native_decide) = l21btPmAdd11368 ∧
    pm.nodes[1762]'(by native_decide) = l21btPmFloat11373 ∧
    pm.nodes[1763]'(by native_decide) = l21btPmFloat11374 ∧
    pm.nodes[1764]'(by native_decide) = l21btPmAdd11377 ∧
    pm.nodes[1765]'(by native_decide) = l21btPmAdd11378 ∧
    pm.nodes[1766]'(by native_decide) = l21btPmMref11377 ∧
    pm.nodes[1767]'(by native_decide) = l21btPmMref11378 ∧
    pm.nodes[1768]'(by native_decide) = l21btPmRms11381 ∧
    pm.nodes[1769]'(by native_decide) = l21btPmRms11382 ∧
    pm.nodes[1770]'(by native_decide) = l21btPmPhl11383 ∧
    pm.nodes[1771]'(by native_decide) = l21btPmPhl11384 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l21bt_buddy_facts :
    sm.replicaBuddies l21btSmMoE5806 = [l21btSmMoE5806] ∧
    pm.replicaBuddies l21btPmMoE11289 = [l21btPmMoE11289, l21btPmMoE11290] ∧
    pm.replicaBuddies l21btPmMoE11290 = [l21btPmMoE11289, l21btPmMoE11290] := by
  native_decide

private theorem l21bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l21bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l21bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5822 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5829 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5831 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5822 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5829 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5831 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l21bt_cu_not_written : ∀ n ∈ pm.nodes, 5786 ∉ n.outs := by
  native_decide

private theorem l21bt_w5822_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5822 ∉ n.outs := by
  intro n hn
  exact l21bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l21bt_w5822_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5822 ∉ n.outs := by
  intro n hn
  exact l21bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l21bt_w5829_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5829 ∉ n.outs := by
  intro n hn
  exact l21bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l21bt_w5829_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5829 ∉ n.outs := by
  intro n hn
  exact l21bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l21bt_w5831_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5831 ∉ n.outs := by
  intro n hn
  exact l21bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l21bt_w5831_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5831 ∉ n.outs := by
  intro n hn
  exact l21bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l21bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(843, 5806), (842, 8513), (842, 5801), (842, 5802), (842, 5804), (842, 5805), (846, 5821), (845, 5820), (847, 5823), (846, 5821), (848, 5824), (847, 5823), (849, 5825), (848, 5811), (848, 5824), (850, 5826), (849, 5806), (849, 5825), (851, 5827), (850, 5826), (852, 5828), (851, 8502), (851, 5827), (853, 8529), (853, 8533), (852, 5828), (854, 5830), (853, 8529), (855, 5832), (854, 5830)]) :
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
private theorem l21bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1747, 11289), (1746, 16710), (1746, 11279), (1746, 11281), (1746, 11285), (1746, 11287), (1746, 11286), (1746, 11288), (1750, 11290), (1749, 16733), (1749, 11280), (1749, 11282), (1749, 11285), (1749, 11286), (1749, 11287), (1749, 11288), (1753, 11343), (1752, 11341), (1754, 11344), (1753, 11342), (1755, 11349), (1754, 11343), (1756, 11350), (1755, 11344), (1757, 11359), (1756, 11349), (1758, 11360), (1757, 11350), (1759, 11363), (1758, 11303), (1758, 11359), (1760, 11364), (1759, 11304), (1759, 11360), (1761, 11367), (1760, 11289), (1760, 11363), (1762, 11368), (1761, 11290), (1761, 11364), (1763, 11373), (1762, 11367), (1764, 11374), (1763, 11368), (1765, 11377), (1764, 16691), (1764, 11373), (1766, 11378), (1765, 16699), (1765, 11374), (1767, 16749), (1767, 16753), (1766, 11377), (1768, 16757), (1768, 16761), (1767, 11378), (1769, 11381), (1768, 16749), (1770, 11382), (1769, 16757), (1771, 11383), (1770, 11381), (1772, 11384), (1771, 11382)]) :
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
private theorem l21bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5804, 5805]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l21bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [11285, 11286, 11287, 11288]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l21bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5804, 5805]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l21bt_sm_leaf_not_written tid h)

private theorem l21bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [11285, 11286, 11287, 11288]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l21bt_pm_leaf_not_written tid h)

private theorem l21bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5806 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5806 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5806 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8513)
        (denoteGraphDistributedFaithful sm initSM 5801)
        (denoteGraphDistributedFaithful sm initSM 5802)
        [denoteGraphDistributedFaithful sm initSM 5804]
        [denoteGraphDistributedFaithful sm initSM 5805]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l21bt_reduce5 sm initSM 842 l21btSmMoE5806
    8513 5801 5802 5804 5805 5806
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l21bt_sm_node_facts.1 ?_
    (l21bt_nonempty_sm 843) (l21bt_sm_not_written 843 5806 (by decide))
    (l21bt_nonempty_sm 842) (l21bt_sm_not_written 842 8513 (by decide))
    (l21bt_sm_not_written 842 5801 (by decide))
    (l21bt_sm_not_written 842 5802 (by decide))
    (l21bt_sm_not_written 842 5804 (by decide))
    (l21bt_sm_not_written 842 5805 (by decide))
  intro s
  have hb := l21bt_buddy_facts.1
  unfold l21btSmMoE5806 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8513 5801 5802 5804 5805 5806 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11289 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11289 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16710)
        (denoteGraphDistributedFaithful pm initPM 11279)
        (denoteGraphDistributedFaithful pm initPM 11281)
        [denoteGraphDistributedFaithful pm initPM 11285,
         denoteGraphDistributedFaithful pm initPM 11286]
        [denoteGraphDistributedFaithful pm initPM 11287,
         denoteGraphDistributedFaithful pm initPM 11288]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l21bt_reduce7 pm initPM 1746 l21btPmMoE11289
    16710 11279 11281 11285 11287 11286 11288 11289
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l21bt_pm_node_facts.1 ?_
    (l21bt_nonempty_pm 1747) (l21bt_pm_not_written 1747 11289 (by decide))
    (l21bt_nonempty_pm 1746) (l21bt_pm_not_written 1746 16710 (by decide))
    (l21bt_pm_not_written 1746 11279 (by decide))
    (l21bt_pm_not_written 1746 11281 (by decide))
    (l21bt_pm_not_written 1746 11285 (by decide))
    (l21bt_pm_not_written 1746 11287 (by decide))
    (l21bt_pm_not_written 1746 11286 (by decide))
    (l21bt_pm_not_written 1746 11288 (by decide))
  intro s
  have hb := l21bt_buddy_facts.2.1
  unfold l21btPmMoE11289 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16710 11279 11281 11285 11287 11289 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11290 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11290 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16733)
        (denoteGraphDistributedFaithful pm initPM 11280)
        (denoteGraphDistributedFaithful pm initPM 11282)
        [denoteGraphDistributedFaithful pm initPM 11285,
         denoteGraphDistributedFaithful pm initPM 11286]
        [denoteGraphDistributedFaithful pm initPM 11287,
         denoteGraphDistributedFaithful pm initPM 11288]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l21bt_reduce7 pm initPM 1749 l21btPmMoE11290
    16733 11280 11282 11285 11286 11287 11288 11290
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l21bt_pm_node_facts.2.1 ?_
    (l21bt_nonempty_pm 1750) (l21bt_pm_not_written 1750 11290 (by decide))
    (l21bt_nonempty_pm 1749) (l21bt_pm_not_written 1749 16733 (by decide))
    (l21bt_pm_not_written 1749 11280 (by decide))
    (l21bt_pm_not_written 1749 11282 (by decide))
    (l21bt_pm_not_written 1749 11285 (by decide))
    (l21bt_pm_not_written 1749 11286 (by decide))
    (l21bt_pm_not_written 1749 11287 (by decide))
    (l21bt_pm_not_written 1749 11288 (by decide))
  intro s
  have hb := l21bt_buddy_facts.2.2
  unfold l21btPmMoE11290 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16733 11280 11282 11286 11288 11290 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5821 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5821 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5821 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5820) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 845 l21btSmResh5821
    5820 5821 (fun x => fw_view [4096,512] x)
    (by native_decide) l21bt_sm_node_facts.2.1 ?_
    (l21bt_nonempty_sm 846) (l21bt_sm_not_written 846 5821 (by decide))
    (l21bt_nonempty_sm 845) (l21bt_sm_not_written 845 5820 (by decide))
  intro s
  unfold l21btSmResh5821
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5820 5821 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11343 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11343 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11341) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1752 l21btPmResh11343
    11341 11343 (fun x => fw_view [2048,512] x)
    (by native_decide) l21bt_pm_node_facts.2.2.1 ?_
    (l21bt_nonempty_pm 1753) (l21bt_pm_not_written 1753 11343 (by decide))
    (l21bt_nonempty_pm 1752) (l21bt_pm_not_written 1752 11341 (by decide))
  intro s
  unfold l21btPmResh11343
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11341 11343 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11344 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11344 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11342) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1753 l21btPmResh11344
    11342 11344 (fun x => fw_view [2048,512] x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.1 ?_
    (l21bt_nonempty_pm 1754) (l21bt_pm_not_written 1754 11344 (by decide))
    (l21bt_nonempty_pm 1753) (l21bt_pm_not_written 1753 11342 (by decide))
  intro s
  unfold l21btPmResh11344
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11342 11344 [2048,512]

/-! ### Node reductions: down-projection 5823 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5823 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5823 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5821)
        (denoteGraphDistributedFaithful sm initSM 5822) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 846 l21btSmMPL5823
    5821 5822 5823 fw_linear
    (by native_decide) l21bt_sm_node_facts.2.2.1 ?_
    (l21bt_nonempty_sm 847) (l21bt_sm_not_written 847 5823 (by decide))
    (l21bt_nonempty_sm 846) (l21bt_sm_not_written 846 5821 (by decide))
    (l21bt_w5822_sm_drop 846)
  intro s
  unfold l21btSmMPL5823
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5821 5822 5823

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11349 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11349 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11343)
        (denoteGraphDistributedFaithful pm initPM 5822) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1754 l21btPmMPL11349
    11343 5822 11349 fw_linear
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1755) (l21bt_pm_not_written 1755 11349 (by decide))
    (l21bt_nonempty_pm 1754) (l21bt_pm_not_written 1754 11343 (by decide))
    (l21bt_w5822_pm_drop 1754)
  intro s
  unfold l21btPmMPL11349
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11343 5822 11349

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11350 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11350 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11344)
        (denoteGraphDistributedFaithful pm initPM 5822) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1755 l21btPmMPL11350
    11344 5822 11350 fw_linear
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1756) (l21bt_pm_not_written 1756 11350 (by decide))
    (l21bt_nonempty_pm 1755) (l21bt_pm_not_written 1755 11344 (by decide))
    (l21bt_w5822_pm_drop 1755)
  intro s
  unfold l21btPmMPL11350
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11344 5822 11350

/-! ### Node reductions: view 5824 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5824 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5824 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5823) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 847 l21btSmView5824
    5823 5824 (fun x => fw_view [4096,1024] x)
    (by native_decide) l21bt_sm_node_facts.2.2.2.1 ?_
    (l21bt_nonempty_sm 848) (l21bt_sm_not_written 848 5824 (by decide))
    (l21bt_nonempty_sm 847) (l21bt_sm_not_written 847 5823 (by decide))
  intro s
  unfold l21btSmView5824
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5823 5824

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11359 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11359 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11349) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1756 l21btPmView11359
    11349 11359 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1757) (l21bt_pm_not_written 1757 11359 (by decide))
    (l21bt_nonempty_pm 1756) (l21bt_pm_not_written 1756 11349 (by decide))
  intro s
  unfold l21btPmView11359
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11349 11359

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11360 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11360 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11350) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1757 l21btPmView11360
    11350 11360 (fun x => fw_view [2048,1024] x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1758) (l21bt_pm_not_written 1758 11360 (by decide))
    (l21bt_nonempty_pm 1757) (l21bt_pm_not_written 1757 11350 (by decide))
  intro s
  unfold l21btPmView11360
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11350 11360

/-! ### Node reductions: gated multiply 5825 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5825 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5825 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5811)
        (denoteGraphDistributedFaithful sm initSM 5824) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 848 l21btSmMul5825
    5811 5824 5825 elemwiseMul
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.1 ?_
    (l21bt_nonempty_sm 849) (l21bt_sm_not_written 849 5825 (by decide))
    (l21bt_nonempty_sm 848) (l21bt_sm_not_written 848 5811 (by decide))
    (l21bt_sm_not_written 848 5824 (by decide))
  intro s
  unfold l21btSmMul5825
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5811 5824 5825

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11363 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11363 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11303)
        (denoteGraphDistributedFaithful pm initPM 11359) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1758 l21btPmMul11363
    11303 11359 11363 elemwiseMul
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1759) (l21bt_pm_not_written 1759 11363 (by decide))
    (l21bt_nonempty_pm 1758) (l21bt_pm_not_written 1758 11303 (by decide))
    (l21bt_pm_not_written 1758 11359 (by decide))
  intro s
  unfold l21btPmMul11363
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 11303 11359 11363

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11364 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11364 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11304)
        (denoteGraphDistributedFaithful pm initPM 11360) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1759 l21btPmMul11364
    11304 11360 11364 elemwiseMul
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1760) (l21bt_pm_not_written 1760 11364 (by decide))
    (l21bt_nonempty_pm 1759) (l21bt_pm_not_written 1759 11304 (by decide))
    (l21bt_pm_not_written 1759 11360 (by decide))
  intro s
  unfold l21btPmMul11364
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 11304 11360 11364

/-! ### Node reductions: MoE join 5826 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5826 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5826 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5806)
        (denoteGraphDistributedFaithful sm initSM 5825) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 849 l21btSmAdd5826
    5806 5825 5826 elemwiseAdd
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l21bt_nonempty_sm 850) (l21bt_sm_not_written 850 5826 (by decide))
    (l21bt_nonempty_sm 849) (l21bt_sm_not_written 849 5806 (by decide))
    (l21bt_sm_not_written 849 5825 (by decide))
  intro s
  unfold l21btSmAdd5826
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5806 5825 5826

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11367 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11367 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11289)
        (denoteGraphDistributedFaithful pm initPM 11363) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1760 l21btPmAdd11367
    11289 11363 11367 elemwiseAdd
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1761) (l21bt_pm_not_written 1761 11367 (by decide))
    (l21bt_nonempty_pm 1760) (l21bt_pm_not_written 1760 11289 (by decide))
    (l21bt_pm_not_written 1760 11363 (by decide))
  intro s
  unfold l21btPmAdd11367
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 11289 11363 11367

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11368 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11368 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11290)
        (denoteGraphDistributedFaithful pm initPM 11364) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1761 l21btPmAdd11368
    11290 11364 11368 elemwiseAdd
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1762) (l21bt_pm_not_written 1762 11368 (by decide))
    (l21bt_nonempty_pm 1761) (l21bt_pm_not_written 1761 11290 (by decide))
    (l21bt_pm_not_written 1761 11364 (by decide))
  intro s
  unfold l21btPmAdd11368
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 11290 11364 11368

/-! ### Node reductions: float 5827 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5827 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5827 =
      denoteGraphDistributedFaithful sm initSM 5826 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 850 l21btSmFloat5827
    5826 5827 (fun x => x)
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_sm 851) (l21bt_sm_not_written 851 5827 (by decide))
    (l21bt_nonempty_sm 850) (l21bt_sm_not_written 850 5826 (by decide))
  intro s
  unfold l21btSmFloat5827
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5826 5827 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11373 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11373 =
      denoteGraphDistributedFaithful pm initPM 11367 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1762 l21btPmFloat11373
    11367 11373 (fun x => x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1763) (l21bt_pm_not_written 1763 11373 (by decide))
    (l21bt_nonempty_pm 1762) (l21bt_pm_not_written 1762 11367 (by decide))
  intro s
  unfold l21btPmFloat11373
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 11367 11373 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11374 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11374 =
      denoteGraphDistributedFaithful pm initPM 11368 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1763 l21btPmFloat11374
    11368 11374 (fun x => x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1764) (l21bt_pm_not_written 1764 11374 (by decide))
    (l21bt_nonempty_pm 1763) (l21bt_pm_not_written 1763 11368 (by decide))
  intro s
  unfold l21btPmFloat11374
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 11368 11374 []

/-! ### Node reductions: residual join 5828 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5828 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5828 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8502)
        (denoteGraphDistributedFaithful sm initSM 5827) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 851 l21btSmAdd5828
    8502 5827 5828 elemwiseAdd
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_sm 852) (l21bt_sm_not_written 852 5828 (by decide))
    (l21bt_nonempty_sm 851) (l21bt_sm_not_written 851 8502 (by decide))
    (l21bt_sm_not_written 851 5827 (by decide))
  intro s
  unfold l21btSmAdd5828
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8502 5827 5828

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11377 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11377 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16691)
        (denoteGraphDistributedFaithful pm initPM 11373) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1764 l21btPmAdd11377
    16691 11373 11377 elemwiseAdd
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1765) (l21bt_pm_not_written 1765 11377 (by decide))
    (l21bt_nonempty_pm 1764) (l21bt_pm_not_written 1764 16691 (by decide))
    (l21bt_pm_not_written 1764 11373 (by decide))
  intro s
  unfold l21btPmAdd11377
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16691 11373 11377

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11378 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11378 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16699)
        (denoteGraphDistributedFaithful pm initPM 11374) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1765 l21btPmAdd11378
    16699 11374 11378 elemwiseAdd
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1766) (l21bt_pm_not_written 1766 11378 (by decide))
    (l21bt_nonempty_pm 1765) (l21bt_pm_not_written 1765 16699 (by decide))
    (l21bt_pm_not_written 1765 11374 (by decide))
  intro s
  unfold l21btPmAdd11378
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16699 11374 11378

/-! ### Node reductions: 2-way multiref off 5828 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm8529 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8529 =
      denoteGraphDistributedFaithful sm initSM 5828 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 852 l21btSmMref5828
    5828 8529 (fun x => x)
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_sm 853) (l21bt_sm_not_written 853 8529 (by decide))
    (l21bt_nonempty_sm 852) (l21bt_sm_not_written 852 5828 (by decide))
  intro s
  unfold l21btSmMref5828
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5828 8529 8533

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm8533 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8533 =
      denoteGraphDistributedFaithful sm initSM 5828 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 852 l21btSmMref5828
    5828 8533 (fun x => x)
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_sm 853) (l21bt_sm_not_written 853 8533 (by decide))
    (l21bt_nonempty_sm 852) (l21bt_sm_not_written 852 5828 (by decide))
  intro s
  unfold l21btSmMref5828
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5828 8529 8533 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm16749 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16749 =
      denoteGraphDistributedFaithful pm initPM 11377 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1766 l21btPmMref11377
    11377 16749 (fun x => x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1767) (l21bt_pm_not_written 1767 16749 (by decide))
    (l21bt_nonempty_pm 1766) (l21bt_pm_not_written 1766 11377 (by decide))
  intro s
  unfold l21btPmMref11377
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11377 16749 16753

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm16753 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16753 =
      denoteGraphDistributedFaithful pm initPM 11377 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1766 l21btPmMref11377
    11377 16753 (fun x => x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1767) (l21bt_pm_not_written 1767 16753 (by decide))
    (l21bt_nonempty_pm 1766) (l21bt_pm_not_written 1766 11377 (by decide))
  intro s
  unfold l21btPmMref11377
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11377 16749 16753 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm16757 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16757 =
      denoteGraphDistributedFaithful pm initPM 11378 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1767 l21btPmMref11378
    11378 16757 (fun x => x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1768) (l21bt_pm_not_written 1768 16757 (by decide))
    (l21bt_nonempty_pm 1767) (l21bt_pm_not_written 1767 11378 (by decide))
  intro s
  unfold l21btPmMref11378
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11378 16757 16761

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm16761 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16761 =
      denoteGraphDistributedFaithful pm initPM 11378 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1767 l21btPmMref11378
    11378 16761 (fun x => x)
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1768) (l21bt_pm_not_written 1768 16761 (by decide))
    (l21bt_nonempty_pm 1767) (l21bt_pm_not_written 1767 11378 (by decide))
  intro s
  unfold l21btPmMref11378
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11378 16757 16761 (by decide)

/-! ### Node reductions: RMSNorm 5830 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5830 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5830 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8529)
        (denoteGraphDistributedFaithful sm initSM 5829) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 853 l21btSmRms5830
    8529 5829 5830 fw_rms_norm
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_sm 854) (l21bt_sm_not_written 854 5830 (by decide))
    (l21bt_nonempty_sm 853) (l21bt_sm_not_written 853 8529 (by decide))
    (l21bt_w5829_sm_drop 853)
  intro s
  unfold l21btSmRms5830
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8529 5829 5830

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11381 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11381 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16749)
        (denoteGraphDistributedFaithful pm initPM 5829) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1768 l21btPmRms11381
    16749 5829 11381 fw_rms_norm
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1769) (l21bt_pm_not_written 1769 11381 (by decide))
    (l21bt_nonempty_pm 1768) (l21bt_pm_not_written 1768 16749 (by decide))
    (l21bt_w5829_pm_drop 1768)
  intro s
  unfold l21btPmRms11381
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16749 5829 11381

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11382 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11382 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16757)
        (denoteGraphDistributedFaithful pm initPM 5829) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1769 l21btPmRms11382
    16757 5829 11382 fw_rms_norm
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1770) (l21bt_pm_not_written 1770 11382 (by decide))
    (l21bt_nonempty_pm 1769) (l21bt_pm_not_written 1769 16757 (by decide))
    (l21bt_w5829_pm_drop 1769)
  intro s
  unfold l21btPmRms11382
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16757 5829 11382

/-! ### Node reductions: per-head Q projection 5832 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_sm5832 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5832 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5830)
        (denoteGraphDistributedFaithful sm initSM 5831) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 854 l21btSmPhl5832
    5830 5831 5832 fw_per_head_linear
    (by native_decide) l21bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l21bt_nonempty_sm 855) (l21bt_sm_not_written 855 5832 (by decide))
    (l21bt_nonempty_sm 854) (l21bt_sm_not_written 854 5830 (by decide))
    (l21bt_w5831_sm_drop 854)
  intro s
  unfold l21btSmPhl5832
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5830 5831 5832 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11383 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11383 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11381)
        (denoteGraphDistributedFaithful pm initPM 5831) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1770 l21btPmPhl11383
    11381 5831 11383 fw_per_head_linear
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l21bt_nonempty_pm 1771) (l21bt_pm_not_written 1771 11383 (by decide))
    (l21bt_nonempty_pm 1770) (l21bt_pm_not_written 1770 11381 (by decide))
    (l21bt_w5831_pm_drop 1770)
  intro s
  unfold l21btPmPhl11383
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 11381 5831 11383 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_red_pm11384 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11384 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11382)
        (denoteGraphDistributedFaithful pm initPM 5831) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1771 l21btPmPhl11384
    11382 5831 11384 fw_per_head_linear
    (by native_decide) l21bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l21bt_nonempty_pm 1772) (l21bt_pm_not_written 1772 11384 (by decide))
    (l21bt_nonempty_pm 1771) (l21bt_pm_not_written 1771 11382 (by decide))
    (l21bt_w5831_pm_drop 1771)
  intro s
  unfold l21btPmPhl11384
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 11382 5831 11384 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l21bt_weight_bridge (initSM initPM : Store)
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
private theorem l21bt_weight_eq (initSM initPM : Store)
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
private theorem l21bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l21bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l21bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5786) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5786).shape = [2] := by
    rw [l21bt_pmFinal initPM 5786 l21bt_cu_not_written]
    exact hPM 5786 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5786)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5806 (block-8 MoE expert layer).
theorem recon_zigzagGoal_5806_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5806)
      (denoteGraphDistributedFaithful pm initPM 11289)
      (denoteGraphDistributedFaithful pm initPM 11290)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8513_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5801_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5802_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l21bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8513)
      (denoteGraphDistributedFaithful pm initPM 16710)
      (denoteGraphDistributedFaithful pm initPM 16733)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5801)
      (denoteGraphDistributedFaithful pm initPM 11279)
      (denoteGraphDistributedFaithful pm initPM 11280)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5802)
      (denoteGraphDistributedFaithful pm initPM 11281)
      (denoteGraphDistributedFaithful pm initPM 11282)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5804 = allGatherPrimDimN 0 2 0 [initPM 11285, initPM 11286] :=
    l21bt_weight_bridge initSM initPM hInit initGoal_5804 (by native_decide)
      5804 11285 11286 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5805 = allGatherPrimDimN 0 2 0 [initPM 11287, initPM 11288] :=
    l21bt_weight_bridge initSM initPM hInit initGoal_5805 (by native_decide)
      5805 11287 11288 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5804).shape = [64, 1024, 1024] :=
    hSM 5804 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5805).shape = [64, 1024, 512] :=
    hSM 5805 [64, 1024, 512] (by native_decide)
  rw [l21bt_red_sm5806 initSM, l21bt_red_pm11289 initPM, l21bt_red_pm11290 initPM]
  rw [l21bt_sm_leaf initSM 5804 (by decide), l21bt_sm_leaf initSM 5805 (by decide),
    l21bt_pm_leaf initPM 11285 (by decide), l21bt_pm_leaf initPM 11286 (by decide),
    l21bt_pm_leaf initPM 11287 (by decide), l21bt_pm_leaf initPM 11288 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5804) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5805) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 11285, initPM 11286])
    (allGatherPrimDimN 0 2 0 [initPM 11287, initPM 11288])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5821 (`FW_reshape`).
theorem recon_zigzagGoal_5821_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5821)
      (denoteGraphDistributedFaithful pm initPM 11343)
      (denoteGraphDistributedFaithful pm initPM 11344)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5820_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21bt_red_sm5821 initSM, l21bt_red_pm11343 initPM, l21bt_red_pm11344 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5823 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5823_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5823)
      (denoteGraphDistributedFaithful pm initPM 11349)
      (denoteGraphDistributedFaithful pm initPM 11350)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5821_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5822 =
      denoteGraphDistributedFaithful pm initPM 5822 :=
    l21bt_weight_eq initSM initPM hInit 5822 initGoal_5822 (by native_decide)
      rfl rfl rfl rfl
      l21bt_weights_not_written.1.1 l21bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5822).shape = [1024, 512] :=
    l21bt_pm_weight_shape initPM hPM 5822 [1024, 512] (by native_decide)
      l21bt_weights_not_written.2.1
  rw [l21bt_red_sm5823 initSM, l21bt_red_pm11349 initPM, l21bt_red_pm11350 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5824 (`FW_view`).
theorem recon_zigzagGoal_5824_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5824)
      (denoteGraphDistributedFaithful pm initPM 11359)
      (denoteGraphDistributedFaithful pm initPM 11360)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5823_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21bt_red_sm5824 initSM, l21bt_red_pm11359 initPM, l21bt_red_pm11360 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5825 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5825_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5825)
      (denoteGraphDistributedFaithful pm initPM 11363)
      (denoteGraphDistributedFaithful pm initPM 11364)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5811_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5824_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5811)
      (denoteGraphDistributedFaithful pm initPM 11303)
      (denoteGraphDistributedFaithful pm initPM 11304)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5824)
      (denoteGraphDistributedFaithful pm initPM 11359)
      (denoteGraphDistributedFaithful pm initPM 11360)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l21bt_red_sm5825 initSM, l21bt_red_pm11363 initPM, l21bt_red_pm11364 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5826 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5826_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5826)
      (denoteGraphDistributedFaithful pm initPM 11367)
      (denoteGraphDistributedFaithful pm initPM 11368)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5806_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5825_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5806)
      (denoteGraphDistributedFaithful pm initPM 11289)
      (denoteGraphDistributedFaithful pm initPM 11290)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5825)
      (denoteGraphDistributedFaithful pm initPM 11363)
      (denoteGraphDistributedFaithful pm initPM 11364)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l21bt_red_sm5826 initSM, l21bt_red_pm11367 initPM, l21bt_red_pm11368 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5827 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5827_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5827)
      (denoteGraphDistributedFaithful pm initPM 11373)
      (denoteGraphDistributedFaithful pm initPM 11374)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5826_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21bt_red_sm5827 initSM, l21bt_red_pm11373 initPM, l21bt_red_pm11374 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5828 (`FW_add`, residual join).
theorem recon_zigzagGoal_5828_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5828)
      (denoteGraphDistributedFaithful pm initPM 11377)
      (denoteGraphDistributedFaithful pm initPM 11378)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8502_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5827_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8502)
      (denoteGraphDistributedFaithful pm initPM 16691)
      (denoteGraphDistributedFaithful pm initPM 16699)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5827)
      (denoteGraphDistributedFaithful pm initPM 11373)
      (denoteGraphDistributedFaithful pm initPM 11374)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l21bt_red_sm5828 initSM, l21bt_red_pm11377 initPM, l21bt_red_pm11378 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8529 (multiref position 0 off 5828).
theorem recon_zigzagGoal_8529_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8529)
      (denoteGraphDistributedFaithful pm initPM 16749)
      (denoteGraphDistributedFaithful pm initPM 16757)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5828_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21bt_red_sm8529 initSM, l21bt_red_pm16749 initPM, l21bt_red_pm16757 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8533 (multiref position 1
-- off 5828): the cross-layer residual bypass consumed by block 9's `FW_add`.
theorem recon_zigzagGoal_8533_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8533)
      (denoteGraphDistributedFaithful pm initPM 16753)
      (denoteGraphDistributedFaithful pm initPM 16761)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5828_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l21bt_red_sm8533 initSM, l21bt_red_pm16753 initPM, l21bt_red_pm16761 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5830 (`FW_rms_norm`).
theorem recon_zigzagGoal_5830_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5830)
      (denoteGraphDistributedFaithful pm initPM 11381)
      (denoteGraphDistributedFaithful pm initPM 11382)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8529_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5829 =
      denoteGraphDistributedFaithful pm initPM 5829 :=
    l21bt_weight_eq initSM initPM hInit 5829 initGoal_5829 (by native_decide)
      rfl rfl rfl rfl
      l21bt_weights_not_written.1.2.1 l21bt_weights_not_written.2.2.1
  rw [l21bt_red_sm5830 initSM, l21bt_red_pm11381 initPM, l21bt_red_pm11382 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5832
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 9's
-- zigzag attention entry.
theorem recon_zigzagGoal_5832_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5832)
      (denoteGraphDistributedFaithful pm initPM 11383)
      (denoteGraphDistributedFaithful pm initPM 11384)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5830_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5831 =
      denoteGraphDistributedFaithful pm initPM 5831 :=
    l21bt_weight_eq initSM initPM hInit 5831 initGoal_5831 (by native_decide)
      rfl rfl rfl rfl
      l21bt_weights_not_written.1.2.2 l21bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5831).shape = [16, 64, 1024] :=
    l21bt_pm_weight_shape initPM hPM 5831 [16, 64, 1024] (by native_decide)
      l21bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5830)
      (denoteGraphDistributedFaithful pm initPM 11381)
      (denoteGraphDistributedFaithful pm initPM 11382)
      (denoteGraphDistributedFaithful pm initPM 5786)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l21bt_red_sm5832 initSM, l21bt_red_pm11383 initPM, l21bt_red_pm11384 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
