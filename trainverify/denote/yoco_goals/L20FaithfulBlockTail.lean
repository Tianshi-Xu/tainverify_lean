/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L20FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L19FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-8 tail (MoE join -> block-8 Q)

Mechanical transport of the (green) block-7 tail `L13FaithfulBlockTail` to
block 8.  The block-8 cu tensor is **5737**.

* SM 807 `FW_all2all_moe_gmm [8474,5752,5753,5755,5756] -> [5757]` (PM 1676/1679 -> 11117/11118)
* SM 810 `FW_reshape [5771] -> [5772]`                             (PM 1682/1683 -> 11171/11172)
* SM 811 `FW_mix_precision_linear [5772,5773] -> [5774]`           (PM 1684/1685 -> 11177/11178)
* SM 812 `FW_view [5774] -> [5775]`                                (PM 1686/1687 -> 11187/11188)
* SM 813 `FW_mul [5762,5775] -> [5776]` (broadcast `[N,1]x[N,1024]`)(PM 1688/1689 -> 11191/11192)
* SM 814 `FW_add [5757,5776] -> [5777]`                            (PM 1690/1691 -> 11195/11196)
* SM 815 `FW_float [5777] -> [5778]`                               (PM 1692/1693 -> 11201/11202)
* SM 816 `FW_add [8463,5778] -> [5779]`                            (PM 1694/1695 -> 11205/11206)
* SM 817 `FW_multiref [5779] -> [8490,8494]`                       (PM 1696/1697)
* SM 818 `FW_rms_norm [8490,5780] -> [5781]`                       (PM 1698/1699 -> 11209/11210)
* SM 819 `FW_per_head_mix_precision_linear [5781,5782] -> [5783]`  (PM 1700/1701 -> 11211/11212)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8494_faithful` -- the cross-layer residual bypass consumed by
  block 8 (SM node 826 `FW_add`);
* `recon_zigzagGoal_5783_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 8's zigzag attention entry.

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

private theorem l20bt_reduce7
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

private theorem l20bt_reduce5
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
private def l20btSmMoE5757 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8474,5752,5753,5755,5756], outs := [5757],
    params := [64,0,64,8] }
private def l20btSmResh5772 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5771], outs := [5772],
    params := [4096,512] }
private def l20btSmMPL5774 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5772,5773], outs := [5774] }
private def l20btSmView5775 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5774], outs := [5775],
    params := [4096,1024] }
private def l20btSmMul5776 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5762,5775], outs := [5776] }
private def l20btSmAdd5777 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5757,5776], outs := [5777] }
private def l20btSmFloat5778 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5777], outs := [5778] }
private def l20btSmAdd5779 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8463,5778], outs := [5779] }
private def l20btSmMref5779 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5779], outs := [8490,8494],
    params := [2] }
private def l20btSmRms5781 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8490,5780], outs := [5781] }
private def l20btSmPhl5783 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5781,5782], outs := [5783] }

private def l20btPmMoE11117 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16632,11107,11109,11113,11115], outs := [11117],
    params := [64,0,32,8] }
private def l20btPmMoE11118 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16655,11108,11110,11114,11116], outs := [11118],
    params := [64,32,64,8] }
private def l20btPmResh11171 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11169], outs := [11171],
    params := [2048,512] }
private def l20btPmResh11172 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11170], outs := [11172],
    params := [2048,512] }
private def l20btPmMPL11177 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11171,5773], outs := [11177] }
private def l20btPmMPL11178 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11172,5773], outs := [11178] }
private def l20btPmView11187 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11177], outs := [11187],
    params := [2048,1024] }
private def l20btPmView11188 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11178], outs := [11188],
    params := [2048,1024] }
private def l20btPmMul11191 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11131,11187], outs := [11191] }
private def l20btPmMul11192 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11132,11188], outs := [11192] }
private def l20btPmAdd11195 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11117,11191], outs := [11195] }
private def l20btPmAdd11196 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11118,11192], outs := [11196] }
private def l20btPmFloat11201 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11195], outs := [11201] }
private def l20btPmFloat11202 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11196], outs := [11202] }
private def l20btPmAdd11205 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16613,11201], outs := [11205] }
private def l20btPmAdd11206 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16621,11202], outs := [11206] }
private def l20btPmMref11205 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11205], outs := [16671,16675],
    params := [2] }
private def l20btPmMref11206 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11206], outs := [16679,16683],
    params := [2] }
private def l20btPmRms11209 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16671,5780], outs := [11209] }
private def l20btPmRms11210 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16679,5780], outs := [11210] }
private def l20btPmPhl11211 : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11209,5782], outs := [11211] }
private def l20btPmPhl11212 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11210,5782], outs := [11212] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l20bt_sm_node_facts :
    sm.nodes[807]'(by native_decide) = l20btSmMoE5757 ∧
    sm.nodes[810]'(by native_decide) = l20btSmResh5772 ∧
    sm.nodes[811]'(by native_decide) = l20btSmMPL5774 ∧
    sm.nodes[812]'(by native_decide) = l20btSmView5775 ∧
    sm.nodes[813]'(by native_decide) = l20btSmMul5776 ∧
    sm.nodes[814]'(by native_decide) = l20btSmAdd5777 ∧
    sm.nodes[815]'(by native_decide) = l20btSmFloat5778 ∧
    sm.nodes[816]'(by native_decide) = l20btSmAdd5779 ∧
    sm.nodes[817]'(by native_decide) = l20btSmMref5779 ∧
    sm.nodes[818]'(by native_decide) = l20btSmRms5781 ∧
    sm.nodes[819]'(by native_decide) = l20btSmPhl5783 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l20bt_pm_node_facts :
    pm.nodes[1676]'(by native_decide) = l20btPmMoE11117 ∧
    pm.nodes[1679]'(by native_decide) = l20btPmMoE11118 ∧
    pm.nodes[1682]'(by native_decide) = l20btPmResh11171 ∧
    pm.nodes[1683]'(by native_decide) = l20btPmResh11172 ∧
    pm.nodes[1684]'(by native_decide) = l20btPmMPL11177 ∧
    pm.nodes[1685]'(by native_decide) = l20btPmMPL11178 ∧
    pm.nodes[1686]'(by native_decide) = l20btPmView11187 ∧
    pm.nodes[1687]'(by native_decide) = l20btPmView11188 ∧
    pm.nodes[1688]'(by native_decide) = l20btPmMul11191 ∧
    pm.nodes[1689]'(by native_decide) = l20btPmMul11192 ∧
    pm.nodes[1690]'(by native_decide) = l20btPmAdd11195 ∧
    pm.nodes[1691]'(by native_decide) = l20btPmAdd11196 ∧
    pm.nodes[1692]'(by native_decide) = l20btPmFloat11201 ∧
    pm.nodes[1693]'(by native_decide) = l20btPmFloat11202 ∧
    pm.nodes[1694]'(by native_decide) = l20btPmAdd11205 ∧
    pm.nodes[1695]'(by native_decide) = l20btPmAdd11206 ∧
    pm.nodes[1696]'(by native_decide) = l20btPmMref11205 ∧
    pm.nodes[1697]'(by native_decide) = l20btPmMref11206 ∧
    pm.nodes[1698]'(by native_decide) = l20btPmRms11209 ∧
    pm.nodes[1699]'(by native_decide) = l20btPmRms11210 ∧
    pm.nodes[1700]'(by native_decide) = l20btPmPhl11211 ∧
    pm.nodes[1701]'(by native_decide) = l20btPmPhl11212 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l20bt_buddy_facts :
    sm.replicaBuddies l20btSmMoE5757 = [l20btSmMoE5757] ∧
    pm.replicaBuddies l20btPmMoE11117 = [l20btPmMoE11117, l20btPmMoE11118] ∧
    pm.replicaBuddies l20btPmMoE11118 = [l20btPmMoE11117, l20btPmMoE11118] := by
  native_decide

private theorem l20bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l20bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l20bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5773 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5780 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5782 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5773 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5780 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5782 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l20bt_cu_not_written : ∀ n ∈ pm.nodes, 5737 ∉ n.outs := by
  native_decide

private theorem l20bt_w5773_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5773 ∉ n.outs := by
  intro n hn
  exact l20bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l20bt_w5773_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5773 ∉ n.outs := by
  intro n hn
  exact l20bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l20bt_w5780_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5780 ∉ n.outs := by
  intro n hn
  exact l20bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l20bt_w5780_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5780 ∉ n.outs := by
  intro n hn
  exact l20bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l20bt_w5782_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5782 ∉ n.outs := by
  intro n hn
  exact l20bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l20bt_w5782_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5782 ∉ n.outs := by
  intro n hn
  exact l20bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l20bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(808, 5757), (807, 8474), (807, 5752), (807, 5753), (807, 5755), (807, 5756), (811, 5772), (810, 5771), (812, 5774), (811, 5772), (813, 5775), (812, 5774), (814, 5776), (813, 5762), (813, 5775), (815, 5777), (814, 5757), (814, 5776), (816, 5778), (815, 5777), (817, 5779), (816, 8463), (816, 5778), (818, 8490), (818, 8494), (817, 5779), (819, 5781), (818, 8490), (820, 5783), (819, 5781)]) :
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
private theorem l20bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1677, 11117), (1676, 16632), (1676, 11107), (1676, 11109), (1676, 11113), (1676, 11115), (1676, 11114), (1676, 11116), (1680, 11118), (1679, 16655), (1679, 11108), (1679, 11110), (1679, 11113), (1679, 11114), (1679, 11115), (1679, 11116), (1683, 11171), (1682, 11169), (1684, 11172), (1683, 11170), (1685, 11177), (1684, 11171), (1686, 11178), (1685, 11172), (1687, 11187), (1686, 11177), (1688, 11188), (1687, 11178), (1689, 11191), (1688, 11131), (1688, 11187), (1690, 11192), (1689, 11132), (1689, 11188), (1691, 11195), (1690, 11117), (1690, 11191), (1692, 11196), (1691, 11118), (1691, 11192), (1693, 11201), (1692, 11195), (1694, 11202), (1693, 11196), (1695, 11205), (1694, 16613), (1694, 11201), (1696, 11206), (1695, 16621), (1695, 11202), (1697, 16671), (1697, 16675), (1696, 11205), (1698, 16679), (1698, 16683), (1697, 11206), (1699, 11209), (1698, 16671), (1700, 11210), (1699, 16679), (1701, 11211), (1700, 11209), (1702, 11212), (1701, 11210)]) :
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
private theorem l20bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5755, 5756]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l20bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [11113, 11114, 11115, 11116]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l20bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5755, 5756]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l20bt_sm_leaf_not_written tid h)

private theorem l20bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [11113, 11114, 11115, 11116]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l20bt_pm_leaf_not_written tid h)

private theorem l20bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5757 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5757 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5757 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8474)
        (denoteGraphDistributedFaithful sm initSM 5752)
        (denoteGraphDistributedFaithful sm initSM 5753)
        [denoteGraphDistributedFaithful sm initSM 5755]
        [denoteGraphDistributedFaithful sm initSM 5756]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l20bt_reduce5 sm initSM 807 l20btSmMoE5757
    8474 5752 5753 5755 5756 5757
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l20bt_sm_node_facts.1 ?_
    (l20bt_nonempty_sm 808) (l20bt_sm_not_written 808 5757 (by decide))
    (l20bt_nonempty_sm 807) (l20bt_sm_not_written 807 8474 (by decide))
    (l20bt_sm_not_written 807 5752 (by decide))
    (l20bt_sm_not_written 807 5753 (by decide))
    (l20bt_sm_not_written 807 5755 (by decide))
    (l20bt_sm_not_written 807 5756 (by decide))
  intro s
  have hb := l20bt_buddy_facts.1
  unfold l20btSmMoE5757 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8474 5752 5753 5755 5756 5757 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11117 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11117 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16632)
        (denoteGraphDistributedFaithful pm initPM 11107)
        (denoteGraphDistributedFaithful pm initPM 11109)
        [denoteGraphDistributedFaithful pm initPM 11113,
         denoteGraphDistributedFaithful pm initPM 11114]
        [denoteGraphDistributedFaithful pm initPM 11115,
         denoteGraphDistributedFaithful pm initPM 11116]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l20bt_reduce7 pm initPM 1676 l20btPmMoE11117
    16632 11107 11109 11113 11115 11114 11116 11117
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l20bt_pm_node_facts.1 ?_
    (l20bt_nonempty_pm 1677) (l20bt_pm_not_written 1677 11117 (by decide))
    (l20bt_nonempty_pm 1676) (l20bt_pm_not_written 1676 16632 (by decide))
    (l20bt_pm_not_written 1676 11107 (by decide))
    (l20bt_pm_not_written 1676 11109 (by decide))
    (l20bt_pm_not_written 1676 11113 (by decide))
    (l20bt_pm_not_written 1676 11115 (by decide))
    (l20bt_pm_not_written 1676 11114 (by decide))
    (l20bt_pm_not_written 1676 11116 (by decide))
  intro s
  have hb := l20bt_buddy_facts.2.1
  unfold l20btPmMoE11117 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16632 11107 11109 11113 11115 11117 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11118 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11118 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16655)
        (denoteGraphDistributedFaithful pm initPM 11108)
        (denoteGraphDistributedFaithful pm initPM 11110)
        [denoteGraphDistributedFaithful pm initPM 11113,
         denoteGraphDistributedFaithful pm initPM 11114]
        [denoteGraphDistributedFaithful pm initPM 11115,
         denoteGraphDistributedFaithful pm initPM 11116]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l20bt_reduce7 pm initPM 1679 l20btPmMoE11118
    16655 11108 11110 11113 11114 11115 11116 11118
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l20bt_pm_node_facts.2.1 ?_
    (l20bt_nonempty_pm 1680) (l20bt_pm_not_written 1680 11118 (by decide))
    (l20bt_nonempty_pm 1679) (l20bt_pm_not_written 1679 16655 (by decide))
    (l20bt_pm_not_written 1679 11108 (by decide))
    (l20bt_pm_not_written 1679 11110 (by decide))
    (l20bt_pm_not_written 1679 11113 (by decide))
    (l20bt_pm_not_written 1679 11114 (by decide))
    (l20bt_pm_not_written 1679 11115 (by decide))
    (l20bt_pm_not_written 1679 11116 (by decide))
  intro s
  have hb := l20bt_buddy_facts.2.2
  unfold l20btPmMoE11118 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16655 11108 11110 11114 11116 11118 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5772 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5772 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5772 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5771) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 810 l20btSmResh5772
    5771 5772 (fun x => fw_view [4096,512] x)
    (by native_decide) l20bt_sm_node_facts.2.1 ?_
    (l20bt_nonempty_sm 811) (l20bt_sm_not_written 811 5772 (by decide))
    (l20bt_nonempty_sm 810) (l20bt_sm_not_written 810 5771 (by decide))
  intro s
  unfold l20btSmResh5772
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5771 5772 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11171 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11171 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11169) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1682 l20btPmResh11171
    11169 11171 (fun x => fw_view [2048,512] x)
    (by native_decide) l20bt_pm_node_facts.2.2.1 ?_
    (l20bt_nonempty_pm 1683) (l20bt_pm_not_written 1683 11171 (by decide))
    (l20bt_nonempty_pm 1682) (l20bt_pm_not_written 1682 11169 (by decide))
  intro s
  unfold l20btPmResh11171
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11169 11171 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11172 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11172 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11170) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1683 l20btPmResh11172
    11170 11172 (fun x => fw_view [2048,512] x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.1 ?_
    (l20bt_nonempty_pm 1684) (l20bt_pm_not_written 1684 11172 (by decide))
    (l20bt_nonempty_pm 1683) (l20bt_pm_not_written 1683 11170 (by decide))
  intro s
  unfold l20btPmResh11172
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11170 11172 [2048,512]

/-! ### Node reductions: down-projection 5774 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5774 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5774 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5772)
        (denoteGraphDistributedFaithful sm initSM 5773) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 811 l20btSmMPL5774
    5772 5773 5774 fw_linear
    (by native_decide) l20bt_sm_node_facts.2.2.1 ?_
    (l20bt_nonempty_sm 812) (l20bt_sm_not_written 812 5774 (by decide))
    (l20bt_nonempty_sm 811) (l20bt_sm_not_written 811 5772 (by decide))
    (l20bt_w5773_sm_drop 811)
  intro s
  unfold l20btSmMPL5774
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5772 5773 5774

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11177 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11177 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11171)
        (denoteGraphDistributedFaithful pm initPM 5773) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1684 l20btPmMPL11177
    11171 5773 11177 fw_linear
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1685) (l20bt_pm_not_written 1685 11177 (by decide))
    (l20bt_nonempty_pm 1684) (l20bt_pm_not_written 1684 11171 (by decide))
    (l20bt_w5773_pm_drop 1684)
  intro s
  unfold l20btPmMPL11177
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11171 5773 11177

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11178 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11178 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11172)
        (denoteGraphDistributedFaithful pm initPM 5773) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1685 l20btPmMPL11178
    11172 5773 11178 fw_linear
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1686) (l20bt_pm_not_written 1686 11178 (by decide))
    (l20bt_nonempty_pm 1685) (l20bt_pm_not_written 1685 11172 (by decide))
    (l20bt_w5773_pm_drop 1685)
  intro s
  unfold l20btPmMPL11178
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11172 5773 11178

/-! ### Node reductions: view 5775 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5775 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5775 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5774) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 812 l20btSmView5775
    5774 5775 (fun x => fw_view [4096,1024] x)
    (by native_decide) l20bt_sm_node_facts.2.2.2.1 ?_
    (l20bt_nonempty_sm 813) (l20bt_sm_not_written 813 5775 (by decide))
    (l20bt_nonempty_sm 812) (l20bt_sm_not_written 812 5774 (by decide))
  intro s
  unfold l20btSmView5775
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5774 5775

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11187 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11187 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11177) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1686 l20btPmView11187
    11177 11187 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1687) (l20bt_pm_not_written 1687 11187 (by decide))
    (l20bt_nonempty_pm 1686) (l20bt_pm_not_written 1686 11177 (by decide))
  intro s
  unfold l20btPmView11187
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11177 11187

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11188 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11188 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11178) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1687 l20btPmView11188
    11178 11188 (fun x => fw_view [2048,1024] x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1688) (l20bt_pm_not_written 1688 11188 (by decide))
    (l20bt_nonempty_pm 1687) (l20bt_pm_not_written 1687 11178 (by decide))
  intro s
  unfold l20btPmView11188
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11178 11188

/-! ### Node reductions: gated multiply 5776 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5776 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5776 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5762)
        (denoteGraphDistributedFaithful sm initSM 5775) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 813 l20btSmMul5776
    5762 5775 5776 elemwiseMul
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.1 ?_
    (l20bt_nonempty_sm 814) (l20bt_sm_not_written 814 5776 (by decide))
    (l20bt_nonempty_sm 813) (l20bt_sm_not_written 813 5762 (by decide))
    (l20bt_sm_not_written 813 5775 (by decide))
  intro s
  unfold l20btSmMul5776
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5762 5775 5776

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11191 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11191 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11131)
        (denoteGraphDistributedFaithful pm initPM 11187) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1688 l20btPmMul11191
    11131 11187 11191 elemwiseMul
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1689) (l20bt_pm_not_written 1689 11191 (by decide))
    (l20bt_nonempty_pm 1688) (l20bt_pm_not_written 1688 11131 (by decide))
    (l20bt_pm_not_written 1688 11187 (by decide))
  intro s
  unfold l20btPmMul11191
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 11131 11187 11191

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11192 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11192 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11132)
        (denoteGraphDistributedFaithful pm initPM 11188) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1689 l20btPmMul11192
    11132 11188 11192 elemwiseMul
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1690) (l20bt_pm_not_written 1690 11192 (by decide))
    (l20bt_nonempty_pm 1689) (l20bt_pm_not_written 1689 11132 (by decide))
    (l20bt_pm_not_written 1689 11188 (by decide))
  intro s
  unfold l20btPmMul11192
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 11132 11188 11192

/-! ### Node reductions: MoE join 5777 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5777 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5777 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5757)
        (denoteGraphDistributedFaithful sm initSM 5776) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 814 l20btSmAdd5777
    5757 5776 5777 elemwiseAdd
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l20bt_nonempty_sm 815) (l20bt_sm_not_written 815 5777 (by decide))
    (l20bt_nonempty_sm 814) (l20bt_sm_not_written 814 5757 (by decide))
    (l20bt_sm_not_written 814 5776 (by decide))
  intro s
  unfold l20btSmAdd5777
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5757 5776 5777

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11195 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11195 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11117)
        (denoteGraphDistributedFaithful pm initPM 11191) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1690 l20btPmAdd11195
    11117 11191 11195 elemwiseAdd
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1691) (l20bt_pm_not_written 1691 11195 (by decide))
    (l20bt_nonempty_pm 1690) (l20bt_pm_not_written 1690 11117 (by decide))
    (l20bt_pm_not_written 1690 11191 (by decide))
  intro s
  unfold l20btPmAdd11195
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 11117 11191 11195

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11196 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11196 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11118)
        (denoteGraphDistributedFaithful pm initPM 11192) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1691 l20btPmAdd11196
    11118 11192 11196 elemwiseAdd
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1692) (l20bt_pm_not_written 1692 11196 (by decide))
    (l20bt_nonempty_pm 1691) (l20bt_pm_not_written 1691 11118 (by decide))
    (l20bt_pm_not_written 1691 11192 (by decide))
  intro s
  unfold l20btPmAdd11196
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 11118 11192 11196

/-! ### Node reductions: float 5778 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5778 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5778 =
      denoteGraphDistributedFaithful sm initSM 5777 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 815 l20btSmFloat5778
    5777 5778 (fun x => x)
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_sm 816) (l20bt_sm_not_written 816 5778 (by decide))
    (l20bt_nonempty_sm 815) (l20bt_sm_not_written 815 5777 (by decide))
  intro s
  unfold l20btSmFloat5778
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5777 5778 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11201 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11201 =
      denoteGraphDistributedFaithful pm initPM 11195 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1692 l20btPmFloat11201
    11195 11201 (fun x => x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1693) (l20bt_pm_not_written 1693 11201 (by decide))
    (l20bt_nonempty_pm 1692) (l20bt_pm_not_written 1692 11195 (by decide))
  intro s
  unfold l20btPmFloat11201
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 11195 11201 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11202 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11202 =
      denoteGraphDistributedFaithful pm initPM 11196 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1693 l20btPmFloat11202
    11196 11202 (fun x => x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1694) (l20bt_pm_not_written 1694 11202 (by decide))
    (l20bt_nonempty_pm 1693) (l20bt_pm_not_written 1693 11196 (by decide))
  intro s
  unfold l20btPmFloat11202
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 11196 11202 []

/-! ### Node reductions: residual join 5779 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5779 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5779 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8463)
        (denoteGraphDistributedFaithful sm initSM 5778) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 816 l20btSmAdd5779
    8463 5778 5779 elemwiseAdd
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_sm 817) (l20bt_sm_not_written 817 5779 (by decide))
    (l20bt_nonempty_sm 816) (l20bt_sm_not_written 816 8463 (by decide))
    (l20bt_sm_not_written 816 5778 (by decide))
  intro s
  unfold l20btSmAdd5779
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8463 5778 5779

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11205 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11205 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16613)
        (denoteGraphDistributedFaithful pm initPM 11201) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1694 l20btPmAdd11205
    16613 11201 11205 elemwiseAdd
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1695) (l20bt_pm_not_written 1695 11205 (by decide))
    (l20bt_nonempty_pm 1694) (l20bt_pm_not_written 1694 16613 (by decide))
    (l20bt_pm_not_written 1694 11201 (by decide))
  intro s
  unfold l20btPmAdd11205
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16613 11201 11205

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11206 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11206 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16621)
        (denoteGraphDistributedFaithful pm initPM 11202) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1695 l20btPmAdd11206
    16621 11202 11206 elemwiseAdd
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1696) (l20bt_pm_not_written 1696 11206 (by decide))
    (l20bt_nonempty_pm 1695) (l20bt_pm_not_written 1695 16621 (by decide))
    (l20bt_pm_not_written 1695 11202 (by decide))
  intro s
  unfold l20btPmAdd11206
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16621 11202 11206

/-! ### Node reductions: 2-way multiref off 5779 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm8490 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8490 =
      denoteGraphDistributedFaithful sm initSM 5779 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 817 l20btSmMref5779
    5779 8490 (fun x => x)
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_sm 818) (l20bt_sm_not_written 818 8490 (by decide))
    (l20bt_nonempty_sm 817) (l20bt_sm_not_written 817 5779 (by decide))
  intro s
  unfold l20btSmMref5779
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out sm s 0 5779 8490 8494

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm8494 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 8494 =
      denoteGraphDistributedFaithful sm initSM 5779 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 817 l20btSmMref5779
    5779 8494 (fun x => x)
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_sm 818) (l20bt_sm_not_written 818 8494 (by decide))
    (l20bt_nonempty_sm 817) (l20bt_sm_not_written 817 5779 (by decide))
  intro s
  unfold l20btSmMref5779
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' sm s 0 5779 8490 8494 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm16671 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16671 =
      denoteGraphDistributedFaithful pm initPM 11205 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1696 l20btPmMref11205
    11205 16671 (fun x => x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1697) (l20bt_pm_not_written 1697 16671 (by decide))
    (l20bt_nonempty_pm 1696) (l20bt_pm_not_written 1696 11205 (by decide))
  intro s
  unfold l20btPmMref11205
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 0 11205 16671 16675

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm16675 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16675 =
      denoteGraphDistributedFaithful pm initPM 11205 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1696 l20btPmMref11205
    11205 16675 (fun x => x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1697) (l20bt_pm_not_written 1697 16675 (by decide))
    (l20bt_nonempty_pm 1696) (l20bt_pm_not_written 1696 11205 (by decide))
  intro s
  unfold l20btPmMref11205
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 0 11205 16671 16675 (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm16679 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16679 =
      denoteGraphDistributedFaithful pm initPM 11206 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1697 l20btPmMref11206
    11206 16679 (fun x => x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1698) (l20bt_pm_not_written 1698 16679 (by decide))
    (l20bt_nonempty_pm 1697) (l20bt_pm_not_written 1697 11206 (by decide))
  intro s
  unfold l20btPmMref11206
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_first_out pm s 1 11206 16679 16683

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm16683 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 16683 =
      denoteGraphDistributedFaithful pm initPM 11206 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1697 l20btPmMref11206
    11206 16683 (fun x => x)
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1698) (l20bt_pm_not_written 1698 16683 (by decide))
    (l20bt_nonempty_pm 1697) (l20bt_pm_not_written 1697 11206 (by decide))
  intro s
  unfold l20btPmMref11206
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out' pm s 1 11206 16679 16683 (by decide)

/-! ### Node reductions: RMSNorm 5781 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5781 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5781 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8490)
        (denoteGraphDistributedFaithful sm initSM 5780) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 818 l20btSmRms5781
    8490 5780 5781 fw_rms_norm
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_sm 819) (l20bt_sm_not_written 819 5781 (by decide))
    (l20bt_nonempty_sm 818) (l20bt_sm_not_written 818 8490 (by decide))
    (l20bt_w5780_sm_drop 818)
  intro s
  unfold l20btSmRms5781
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm s 0 8490 5780 5781

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11209 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11209 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16671)
        (denoteGraphDistributedFaithful pm initPM 5780) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1698 l20btPmRms11209
    16671 5780 11209 fw_rms_norm
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1699) (l20bt_pm_not_written 1699 11209 (by decide))
    (l20bt_nonempty_pm 1698) (l20bt_pm_not_written 1698 16671 (by decide))
    (l20bt_w5780_pm_drop 1698)
  intro s
  unfold l20btPmRms11209
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 0 16671 5780 11209

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11210 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11210 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 16679)
        (denoteGraphDistributedFaithful pm initPM 5780) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1699 l20btPmRms11210
    16679 5780 11210 fw_rms_norm
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1700) (l20bt_pm_not_written 1700 11210 (by decide))
    (l20bt_nonempty_pm 1699) (l20bt_pm_not_written 1699 16679 (by decide))
    (l20bt_w5780_pm_drop 1699)
  intro s
  unfold l20btPmRms11210
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm s 1 16679 5780 11210

/-! ### Node reductions: per-head Q projection 5783 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_sm5783 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5783 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5781)
        (denoteGraphDistributedFaithful sm initSM 5782) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 819 l20btSmPhl5783
    5781 5782 5783 fw_per_head_linear
    (by native_decide) l20bt_sm_node_facts.2.2.2.2.2.2.2.2.2.2 ?_
    (l20bt_nonempty_sm 820) (l20bt_sm_not_written 820 5783 (by decide))
    (l20bt_nonempty_sm 819) (l20bt_sm_not_written 819 5781 (by decide))
    (l20bt_w5782_sm_drop 819)
  intro s
  unfold l20btSmPhl5783
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5781 5782 5783 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11211 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11211 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11209)
        (denoteGraphDistributedFaithful pm initPM 5782) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1700 l20btPmPhl11211
    11209 5782 11211 fw_per_head_linear
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l20bt_nonempty_pm 1701) (l20bt_pm_not_written 1701 11211 (by decide))
    (l20bt_nonempty_pm 1700) (l20bt_pm_not_written 1700 11209 (by decide))
    (l20bt_w5782_pm_drop 1700)
  intro s
  unfold l20btPmPhl11211
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 11209 5782 11211 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_red_pm11212 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11212 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 11210)
        (denoteGraphDistributedFaithful pm initPM 5782) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1701 l20btPmPhl11212
    11210 5782 11212 fw_per_head_linear
    (by native_decide) l20bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l20bt_nonempty_pm 1702) (l20bt_pm_not_written 1702 11212 (by decide))
    (l20bt_nonempty_pm 1701) (l20bt_pm_not_written 1701 11210 (by decide))
    (l20bt_w5782_pm_drop 1701)
  intro s
  unfold l20btPmPhl11212
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 11210 5782 11212 []

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l20bt_weight_bridge (initSM initPM : Store)
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
private theorem l20bt_weight_eq (initSM initPM : Store)
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
private theorem l20bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l20bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l20bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5737) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5737).shape = [2] := by
    rw [l20bt_pmFinal initPM 5737 l20bt_cu_not_written]
    exact hPM 5737 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5737)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5757 (block-7 MoE expert layer).
theorem recon_zigzagGoal_5757_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5757)
      (denoteGraphDistributedFaithful pm initPM 11117)
      (denoteGraphDistributedFaithful pm initPM 11118)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8474_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5752_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5753_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l20bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8474)
      (denoteGraphDistributedFaithful pm initPM 16632)
      (denoteGraphDistributedFaithful pm initPM 16655)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5752)
      (denoteGraphDistributedFaithful pm initPM 11107)
      (denoteGraphDistributedFaithful pm initPM 11108)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5753)
      (denoteGraphDistributedFaithful pm initPM 11109)
      (denoteGraphDistributedFaithful pm initPM 11110)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5755 = allGatherPrimDimN 0 2 0 [initPM 11113, initPM 11114] :=
    l20bt_weight_bridge initSM initPM hInit initGoal_5755 (by native_decide)
      5755 11113 11114 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5756 = allGatherPrimDimN 0 2 0 [initPM 11115, initPM 11116] :=
    l20bt_weight_bridge initSM initPM hInit initGoal_5756 (by native_decide)
      5756 11115 11116 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5755).shape = [64, 1024, 1024] :=
    hSM 5755 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5756).shape = [64, 1024, 512] :=
    hSM 5756 [64, 1024, 512] (by native_decide)
  rw [l20bt_red_sm5757 initSM, l20bt_red_pm11117 initPM, l20bt_red_pm11118 initPM]
  rw [l20bt_sm_leaf initSM 5755 (by decide), l20bt_sm_leaf initSM 5756 (by decide),
    l20bt_pm_leaf initPM 11113 (by decide), l20bt_pm_leaf initPM 11114 (by decide),
    l20bt_pm_leaf initPM 11115 (by decide), l20bt_pm_leaf initPM 11116 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5755) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5756) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 11113, initPM 11114])
    (allGatherPrimDimN 0 2 0 [initPM 11115, initPM 11116])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5772 (`FW_reshape`).
theorem recon_zigzagGoal_5772_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5772)
      (denoteGraphDistributedFaithful pm initPM 11171)
      (denoteGraphDistributedFaithful pm initPM 11172)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5771_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20bt_red_sm5772 initSM, l20bt_red_pm11171 initPM, l20bt_red_pm11172 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5774 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5774_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5774)
      (denoteGraphDistributedFaithful pm initPM 11177)
      (denoteGraphDistributedFaithful pm initPM 11178)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5772_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5773 =
      denoteGraphDistributedFaithful pm initPM 5773 :=
    l20bt_weight_eq initSM initPM hInit 5773 initGoal_5773 (by native_decide)
      rfl rfl rfl rfl
      l20bt_weights_not_written.1.1 l20bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5773).shape = [1024, 512] :=
    l20bt_pm_weight_shape initPM hPM 5773 [1024, 512] (by native_decide)
      l20bt_weights_not_written.2.1
  rw [l20bt_red_sm5774 initSM, l20bt_red_pm11177 initPM, l20bt_red_pm11178 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5775 (`FW_view`).
theorem recon_zigzagGoal_5775_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5775)
      (denoteGraphDistributedFaithful pm initPM 11187)
      (denoteGraphDistributedFaithful pm initPM 11188)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5774_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20bt_red_sm5775 initSM, l20bt_red_pm11187 initPM, l20bt_red_pm11188 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5776 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5776_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5776)
      (denoteGraphDistributedFaithful pm initPM 11191)
      (denoteGraphDistributedFaithful pm initPM 11192)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5762_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5775_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5762)
      (denoteGraphDistributedFaithful pm initPM 11131)
      (denoteGraphDistributedFaithful pm initPM 11132)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5775)
      (denoteGraphDistributedFaithful pm initPM 11187)
      (denoteGraphDistributedFaithful pm initPM 11188)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l20bt_red_sm5776 initSM, l20bt_red_pm11191 initPM, l20bt_red_pm11192 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5777 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5777_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5777)
      (denoteGraphDistributedFaithful pm initPM 11195)
      (denoteGraphDistributedFaithful pm initPM 11196)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5757_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5776_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5757)
      (denoteGraphDistributedFaithful pm initPM 11117)
      (denoteGraphDistributedFaithful pm initPM 11118)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5776)
      (denoteGraphDistributedFaithful pm initPM 11191)
      (denoteGraphDistributedFaithful pm initPM 11192)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l20bt_red_sm5777 initSM, l20bt_red_pm11195 initPM, l20bt_red_pm11196 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5778 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5778_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5778)
      (denoteGraphDistributedFaithful pm initPM 11201)
      (denoteGraphDistributedFaithful pm initPM 11202)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5777_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20bt_red_sm5778 initSM, l20bt_red_pm11201 initPM, l20bt_red_pm11202 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5779 (`FW_add`, residual join).
theorem recon_zigzagGoal_5779_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5779)
      (denoteGraphDistributedFaithful pm initPM 11205)
      (denoteGraphDistributedFaithful pm initPM 11206)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8463_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5778_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8463)
      (denoteGraphDistributedFaithful pm initPM 16613)
      (denoteGraphDistributedFaithful pm initPM 16621)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5778)
      (denoteGraphDistributedFaithful pm initPM 11201)
      (denoteGraphDistributedFaithful pm initPM 11202)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l20bt_red_sm5779 initSM, l20bt_red_pm11205 initPM, l20bt_red_pm11206 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 8490 (multiref position 0 off 5779).
theorem recon_zigzagGoal_8490_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8490)
      (denoteGraphDistributedFaithful pm initPM 16671)
      (denoteGraphDistributedFaithful pm initPM 16679)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5779_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20bt_red_sm8490 initSM, l20bt_red_pm16671 initPM, l20bt_red_pm16679 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 8494 (multiref position 1
-- off 5779): the cross-layer residual bypass consumed by block 8's `FW_add`.
theorem recon_zigzagGoal_8494_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8494)
      (denoteGraphDistributedFaithful pm initPM 16675)
      (denoteGraphDistributedFaithful pm initPM 16683)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5779_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l20bt_red_sm8494 initSM, l20bt_red_pm16675 initPM, l20bt_red_pm16683 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5781 (`FW_rms_norm`).
theorem recon_zigzagGoal_5781_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5781)
      (denoteGraphDistributedFaithful pm initPM 11209)
      (denoteGraphDistributedFaithful pm initPM 11210)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_8490_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5780 =
      denoteGraphDistributedFaithful pm initPM 5780 :=
    l20bt_weight_eq initSM initPM hInit 5780 initGoal_5780 (by native_decide)
      rfl rfl rfl rfl
      l20bt_weights_not_written.1.2.1 l20bt_weights_not_written.2.2.1
  rw [l20bt_red_sm5781 initSM, l20bt_red_pm11209 initPM, l20bt_red_pm11210 initPM, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 hparent (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- **Cross-layer boundary contract.**  Generated goal 5783
-- (`FW_per_head_mix_precision_linear`): the per-head Q projection feeding block 8's
-- zigzag attention entry.
theorem recon_zigzagGoal_5783_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5783)
      (denoteGraphDistributedFaithful pm initPM 11211)
      (denoteGraphDistributedFaithful pm initPM 11212)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 16, 64] [2048, 16, 64] := by
  have hparent := recon_zigzagGoal_5781_faithful initSM initPM hSM hPM hInit hValues hCu
  have hw : denoteGraphDistributedFaithful sm initSM 5782 =
      denoteGraphDistributedFaithful pm initPM 5782 :=
    l20bt_weight_eq initSM initPM hInit 5782 initGoal_5782 (by native_decide)
      rfl rfl rfl rfl
      l20bt_weights_not_written.1.2.2 l20bt_weights_not_written.2.2.2
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5782).shape = [16, 64, 1024] :=
    l20bt_pm_weight_shape initPM hPM 5782 [16, 64, 1024] (by native_decide)
      l20bt_weights_not_written.2.2.2
  obtain ⟨source0, source1, hs⟩ := hparent
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5781)
      (denoteGraphDistributedFaithful pm initPM 11209)
      (denoteGraphDistributedFaithful pm initPM 11210)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l20bt_red_sm5783 initSM, l20bt_red_pm11211 initPM, l20bt_red_pm11212 initPM, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
