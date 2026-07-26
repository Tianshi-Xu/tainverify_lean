/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L23FaithfulMoEBranch
import denote.yoco_goals.L12FaithfulMoEExpert
import denote.yoco_goals.L12FaithfulMoEGate
import denote.yoco_goals.L22FaithfulBlockTail

/-!
# Faithful zigzag relations for the block-11 tail (MoE join -> block-11 Q)

Mechanical transport of the (green) block-10 tail `L13FaithfulBlockTail` to
block 11.  The block-11 cu tensor is **5884**.

* SM 912 `FW_all2all_moe_gmm [8591,5899,5900,5902,5903] -> [5904]` (PM 1886/1889 -> 11633/11634)
* SM 915 `FW_reshape [5918] -> [5919]`                             (PM 1892/1893 -> 11687/11688)
* SM 916 `FW_mix_precision_linear [5919,5920] -> [5921]`           (PM 1894/1895 -> 11693/11694)
* SM 917 `FW_view [5921] -> [5922]`                                (PM 1896/1897 -> 11703/11704)
* SM 918 `FW_mul [5909,5922] -> [5923]` (broadcast `[N,1]x[N,1024]`)(PM 1898/1899 -> 11707/11708)
* SM 919 `FW_add [5904,5923] -> [5924]`                            (PM 1900/1901 -> 11711/11712)
* SM 920 `FW_float [5924] -> [5925]`                               (PM 1902/1903 -> 11717/11718)
* SM 921 `FW_add [8580,5925] -> [5926]`                            (PM 1904/1905 -> 11721/11722)
* SM 922 `FW_multiref [5926] -> [8607,8611]`                       (PM 1906/1907)
* SM 923 `FW_rms_norm [8607,5927] -> [5928]`                       (PM 1908/1909 -> 11725/11726)
* SM 924 `FW_per_head_mix_precision_linear [5928,5929] -> [5930]`  (PM 1910/1911 -> 11727/11728)

Two of the exported relations are **cross-layer boundary contracts**:

* `recon_zigzagGoal_8611_faithful` -- the cross-layer residual bypass consumed by
  block 11 (SM node 931 `FW_add`);
* `recon_zigzagGoal_5930_faithful` -- the per-head Q projection `[4096,16,64]` /
  `[2048,16,64]` feeding block 11's zigzag attention entry.

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

private theorem l23bt_reduce7
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

private theorem l23bt_reduce5
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
private def l23btSmMoE5904 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8591,5899,5900,5902,5903], outs := [5904],
    params := [64,0,64,8] }
private def l23btSmResh5919 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5918], outs := [5919],
    params := [4096,512] }
private def l23btSmMPL5921 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919,5920], outs := [5921] }
private def l23btSmView5922 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5921], outs := [5922],
    params := [4096,1024] }
private def l23btSmMul5923 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [5909,5922], outs := [5923] }
private def l23btSmAdd5924 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [5904,5923], outs := [5924] }
private def l23btSmFloat5925 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [5924], outs := [5925] }
private def l23btSmAdd5926 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8580,5925], outs := [5926] }
private def l23btPmMoE11633 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16866,11623,11625,11629,11631], outs := [11633],
    params := [64,0,32,8] }
private def l23btPmMoE11634 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16889,11624,11626,11630,11632], outs := [11634],
    params := [64,32,64,8] }
private def l23btPmResh11687 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11685], outs := [11687],
    params := [2048,512] }
private def l23btPmResh11688 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11686], outs := [11688],
    params := [2048,512] }
private def l23btPmMPL11693 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11687,5920], outs := [11693] }
private def l23btPmMPL11694 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11688,5920], outs := [11694] }
private def l23btPmView11703 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11693], outs := [11703],
    params := [2048,1024] }
private def l23btPmView11704 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11694], outs := [11704],
    params := [2048,1024] }
private def l23btPmMul11707 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mul", ins := [11647,11703], outs := [11707] }
private def l23btPmMul11708 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mul", ins := [11648,11704], outs := [11708] }
private def l23btPmAdd11711 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [11633,11707], outs := [11711] }
private def l23btPmAdd11712 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [11634,11708], outs := [11712] }
private def l23btPmFloat11717 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11711], outs := [11717] }
private def l23btPmFloat11718 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11712], outs := [11718] }
private def l23btPmAdd11721 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16847,11717], outs := [11721] }
private def l23btPmAdd11722 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16855,11718], outs := [11722] }
/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l23bt_sm_node_facts :
    sm.nodes[912]'(by native_decide) = l23btSmMoE5904 ∧
    sm.nodes[917]'(by native_decide) = l23btSmResh5919 ∧
    sm.nodes[918]'(by native_decide) = l23btSmMPL5921 ∧
    sm.nodes[919]'(by native_decide) = l23btSmView5922 ∧
    sm.nodes[920]'(by native_decide) = l23btSmMul5923 ∧
    sm.nodes[921]'(by native_decide) = l23btSmAdd5924 ∧
    sm.nodes[922]'(by native_decide) = l23btSmFloat5925 ∧
    sm.nodes[923]'(by native_decide) = l23btSmAdd5926
 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23bt_pm_node_facts :
    pm.nodes[1886]'(by native_decide) = l23btPmMoE11633 ∧
    pm.nodes[1891]'(by native_decide) = l23btPmMoE11634 ∧
    pm.nodes[1896]'(by native_decide) = l23btPmResh11687 ∧
    pm.nodes[1899]'(by native_decide) = l23btPmResh11688 ∧
    pm.nodes[1900]'(by native_decide) = l23btPmMPL11693 ∧
    pm.nodes[1901]'(by native_decide) = l23btPmMPL11694 ∧
    pm.nodes[1902]'(by native_decide) = l23btPmView11703 ∧
    pm.nodes[1903]'(by native_decide) = l23btPmView11704 ∧
    pm.nodes[1904]'(by native_decide) = l23btPmMul11707 ∧
    pm.nodes[1905]'(by native_decide) = l23btPmMul11708 ∧
    pm.nodes[1906]'(by native_decide) = l23btPmAdd11711 ∧
    pm.nodes[1907]'(by native_decide) = l23btPmAdd11712 ∧
    pm.nodes[1908]'(by native_decide) = l23btPmFloat11717 ∧
    pm.nodes[1909]'(by native_decide) = l23btPmFloat11718 ∧
    pm.nodes[1910]'(by native_decide) = l23btPmAdd11721 ∧
    pm.nodes[1911]'(by native_decide) = l23btPmAdd11722
 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23bt_buddy_facts :
    sm.replicaBuddies l23btSmMoE5904 = [l23btSmMoE5904] ∧
    pm.replicaBuddies l23btPmMoE11633 = [l23btPmMoE11633, l23btPmMoE11634] ∧
    pm.replicaBuddies l23btPmMoE11634 = [l23btPmMoE11633, l23btPmMoE11634]
 := by
  native_decide

private theorem l23bt_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l23bt_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23bt_weights_not_written :
    ((∀ n ∈ sm.nodes, 5920 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5927 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5929 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5920 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5927 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5929 ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23bt_cu_not_written : ∀ n ∈ pm.nodes, 5884 ∉ n.outs := by
  native_decide

private theorem l23bt_w5920_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5920 ∉ n.outs := by
  intro n hn
  exact l23bt_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l23bt_w5920_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5920 ∉ n.outs := by
  intro n hn
  exact l23bt_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l23bt_w5927_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5927 ∉ n.outs := by
  intro n hn
  exact l23bt_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l23bt_w5927_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5927 ∉ n.outs := by
  intro n hn
  exact l23bt_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l23bt_w5929_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5929 ∉ n.outs := by
  intro n hn
  exact l23bt_weights_not_written.1.2.2 n (List.mem_of_mem_drop hn)

private theorem l23bt_w5929_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5929 ∉ n.outs := by
  intro n hn
  exact l23bt_weights_not_written.2.2.2 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23bt_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(912, 5899), (912, 5900), (912, 5902), (912, 5903), (912, 8591), (913, 5904), (917, 5918), (918, 5909), (918, 5919), (919, 5904), (919, 5921), (920, 5909), (920, 5922), (921, 5904), (921, 5923), (921, 8580), (922, 5924), (923, 5925), (923, 8580), (923, 8607), (923, 8611), (924, 5926)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23bt_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1886, 11623), (1886, 11625), (1886, 11629), (1886, 11630), (1886, 11631), (1886, 11632), (1886, 16866), (1887, 11633), (1889, 11624), (1889, 11626), (1889, 11629), (1889, 11630), (1889, 11631), (1889, 11632), (1889, 16889), (1891, 11624), (1891, 11626), (1891, 11629), (1891, 11630), (1891, 11631), (1891, 11632), (1891, 16889), (1892, 11634), (1892, 11685), (1896, 11685), (1897, 11687), (1898, 11647), (1899, 11648), (1899, 11686), (1900, 11633), (1900, 11687), (1900, 11688), (1901, 11634), (1901, 11688), (1901, 11693), (1902, 11693), (1902, 11694), (1903, 11694), (1903, 11703), (1904, 11647), (1904, 11703), (1904, 11704), (1904, 16847), (1905, 11648), (1905, 11704), (1905, 11707), (1905, 16855), (1906, 11633), (1906, 11707), (1906, 11708), (1907, 11634), (1907, 11708), (1907, 11711), (1907, 16905), (1907, 16909), (1908, 11711), (1908, 11712), (1908, 16905), (1908, 16913), (1908, 16917), (1909, 11712), (1909, 11717), (1909, 11725), (1909, 16913), (1910, 11717), (1910, 11718), (1910, 11725), (1910, 11726), (1910, 16847), (1911, 11718), (1911, 11721), (1911, 11726), (1911, 16855), (1912, 11722)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23bt_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5902, 5903]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23bt_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [11629, 11630, 11631, 11632]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> native_decide +revert

private theorem l23bt_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5902, 5903]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l23bt_sm_leaf_not_written tid h)

private theorem l23bt_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [11629, 11630, 11631, 11632]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l23bt_pm_leaf_not_written tid h)

private theorem l23bt_pmFinal (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty hw

/-! ### Node reductions: MoE expert 5904 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5904 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5904 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8591)
        (denoteGraphDistributedFaithful sm initSM 5899)
        (denoteGraphDistributedFaithful sm initSM 5900)
        [denoteGraphDistributedFaithful sm initSM 5902]
        [denoteGraphDistributedFaithful sm initSM 5903]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l23bt_reduce5 sm initSM 912 l23btSmMoE5904
    8591 5899 5900 5902 5903 5904
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l23bt_sm_node_facts.1 ?_
    (l23bt_nonempty_sm 913) (l23bt_sm_not_written 913 5904 (by decide))
    (l23bt_nonempty_sm 912) (l23bt_sm_not_written 912 8591 (by decide))
    (l23bt_sm_not_written 912 5899 (by decide))
    (l23bt_sm_not_written 912 5900 (by decide))
    (l23bt_sm_not_written 912 5902 (by decide))
    (l23bt_sm_not_written 912 5903 (by decide))
  intro s
  have hb := l23bt_buddy_facts.1
  unfold l23btSmMoE5904 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8591 5899 5900 5902 5903 5904 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11633 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11633 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16866)
        (denoteGraphDistributedFaithful pm initPM 11623)
        (denoteGraphDistributedFaithful pm initPM 11625)
        [denoteGraphDistributedFaithful pm initPM 11629,
         denoteGraphDistributedFaithful pm initPM 11630]
        [denoteGraphDistributedFaithful pm initPM 11631,
         denoteGraphDistributedFaithful pm initPM 11632]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l23bt_reduce7 pm initPM 1886 l23btPmMoE11633
    16866 11623 11625 11629 11631 11630 11632 11633
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l23bt_pm_node_facts.1 ?_
    (l23bt_nonempty_pm 1887) (l23bt_pm_not_written 1887 11633 (by decide))
    (l23bt_nonempty_pm 1886) (l23bt_pm_not_written 1886 16866 (by decide))
    (l23bt_pm_not_written 1886 11623 (by decide))
    (l23bt_pm_not_written 1886 11625 (by decide))
    (l23bt_pm_not_written 1886 11629 (by decide))
    (l23bt_pm_not_written 1886 11631 (by decide))
    (l23bt_pm_not_written 1886 11630 (by decide))
    (l23bt_pm_not_written 1886 11632 (by decide))
  intro s
  have hb := l23bt_buddy_facts.2.1
  unfold l23btPmMoE11633 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16866 11623 11625 11629 11631 11633 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11634 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11634 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16889)
        (denoteGraphDistributedFaithful pm initPM 11624)
        (denoteGraphDistributedFaithful pm initPM 11626)
        [denoteGraphDistributedFaithful pm initPM 11629,
         denoteGraphDistributedFaithful pm initPM 11630]
        [denoteGraphDistributedFaithful pm initPM 11631,
         denoteGraphDistributedFaithful pm initPM 11632]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l23bt_reduce7 pm initPM 1891 l23btPmMoE11634
    16889 11624 11626 11629 11630 11631 11632 11634
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l23bt_pm_node_facts.2.1 ?_
    (l23bt_nonempty_pm 1892) (l23bt_pm_not_written 1892 11634 (by decide))
    (l23bt_nonempty_pm 1891) (l23bt_pm_not_written 1891 16889 (by decide))
    (l23bt_pm_not_written 1891 11624 (by decide))
    (l23bt_pm_not_written 1891 11626 (by decide))
    (l23bt_pm_not_written 1891 11629 (by decide))
    (l23bt_pm_not_written 1891 11630 (by decide))
    (l23bt_pm_not_written 1891 11631 (by decide))
    (l23bt_pm_not_written 1891 11632 (by decide))
  intro s
  have hb := l23bt_buddy_facts.2.2
  unfold l23btPmMoE11634 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16889 11624 11626 11630 11632 11634 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Node reductions: reshape 5919 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5919 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5919 =
      fw_view [4096,512] (denoteGraphDistributedFaithful sm initSM 5918) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 917 l23btSmResh5919
    5918 5919 (fun x => fw_view [4096,512] x)
    (by native_decide) l23bt_sm_node_facts.2.1 ?_
    (l23bt_nonempty_sm 918) (l23bt_sm_not_written 918 5919 (by decide))
    (l23bt_nonempty_sm 917) (l23bt_sm_not_written 917 5918 (by decide))
  intro s
  unfold l23btSmResh5919
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 5918 5919 [4096,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11687 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11687 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11685) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1896 l23btPmResh11687
    11685 11687 (fun x => fw_view [2048,512] x)
    (by native_decide) l23bt_pm_node_facts.2.2.1 ?_
    (l23bt_nonempty_pm 1897) (l23bt_pm_not_written 1897 11687 (by decide))
    (l23bt_nonempty_pm 1896) (l23bt_pm_not_written 1896 11685 (by decide))
  intro s
  unfold l23btPmResh11687
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 11685 11687 [2048,512]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11688 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11688 =
      fw_view [2048,512] (denoteGraphDistributedFaithful pm initPM 11686) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1899 l23btPmResh11688
    11686 11688 (fun x => fw_view [2048,512] x)
    (by native_decide) l23bt_pm_node_facts.2.2.2.1 ?_
    (l23bt_nonempty_pm 1900) (l23bt_pm_not_written 1900 11688 (by decide))
    (l23bt_nonempty_pm 1899) (l23bt_pm_not_written 1899 11686 (by decide))
  intro s
  unfold l23btPmResh11688
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 11686 11688 [2048,512]

/-! ### Node reductions: down-projection 5921 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5921 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5921 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5919)
        (denoteGraphDistributedFaithful sm initSM 5920) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 918 l23btSmMPL5921
    5919 5920 5921 fw_linear
    (by native_decide) l23bt_sm_node_facts.2.2.1 ?_
    (l23bt_nonempty_sm 919) (l23bt_sm_not_written 919 5921 (by decide))
    (l23bt_nonempty_sm 918) (l23bt_sm_not_written 918 5919 (by decide))
    (l23bt_w5920_sm_drop 918)
  intro s
  unfold l23btSmMPL5921
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5919 5920 5921

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11693 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11693 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11687)
        (denoteGraphDistributedFaithful pm initPM 5920) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1900 l23btPmMPL11693
    11687 5920 11693 fw_linear
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1901) (l23bt_pm_not_written 1901 11693 (by decide))
    (l23bt_nonempty_pm 1900) (l23bt_pm_not_written 1900 11687 (by decide))
    (l23bt_w5920_pm_drop 1900)
  intro s
  unfold l23btPmMPL11693
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11687 5920 11693

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11694 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11694 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11688)
        (denoteGraphDistributedFaithful pm initPM 5920) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1901 l23btPmMPL11694
    11688 5920 11694 fw_linear
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1902) (l23bt_pm_not_written 1902 11694 (by decide))
    (l23bt_nonempty_pm 1901) (l23bt_pm_not_written 1901 11688 (by decide))
    (l23bt_w5920_pm_drop 1901)
  intro s
  unfold l23btPmMPL11694
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11688 5920 11694

/-! ### Node reductions: view 5922 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5922 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5922 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 5921) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 919 l23btSmView5922
    5921 5922 (fun x => fw_view [4096,1024] x)
    (by native_decide) l23bt_sm_node_facts.2.2.2.1 ?_
    (l23bt_nonempty_sm 920) (l23bt_sm_not_written 920 5922 (by decide))
    (l23bt_nonempty_sm 919) (l23bt_sm_not_written 919 5921 (by decide))
  intro s
  unfold l23btSmView5922
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm s 0 4096 [1024] 5921 5922

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11703 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11703 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11693) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1902 l23btPmView11703
    11693 11703 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1903) (l23bt_pm_not_written 1903 11703 (by decide))
    (l23bt_nonempty_pm 1902) (l23bt_pm_not_written 1902 11693 (by decide))
  intro s
  unfold l23btPmView11703
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 0 2048 [1024] 11693 11703

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11704 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11704 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 11694) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1903 l23btPmView11704
    11694 11704 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1904) (l23bt_pm_not_written 1904 11704 (by decide))
    (l23bt_nonempty_pm 1903) (l23bt_pm_not_written 1903 11694 (by decide))
  intro s
  unfold l23btPmView11704
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm s 1 2048 [1024] 11694 11704

/-! ### Node reductions: gated multiply 5923 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5923 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5923 =
      elemwiseMul (denoteGraphDistributedFaithful sm initSM 5909)
        (denoteGraphDistributedFaithful sm initSM 5922) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 920 l23btSmMul5923
    5909 5922 5923 elemwiseMul
    (by native_decide) l23bt_sm_node_facts.2.2.2.2.1 ?_
    (l23bt_nonempty_sm 921) (l23bt_sm_not_written 921 5923 (by decide))
    (l23bt_nonempty_sm 920) (l23bt_sm_not_written 920 5909 (by decide))
    (l23bt_sm_not_written 920 5922 (by decide))
  intro s
  unfold l23btSmMul5923
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out sm s 0 5909 5922 5923

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11707 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11707 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11647)
        (denoteGraphDistributedFaithful pm initPM 11703) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1904 l23btPmMul11707
    11647 11703 11707 elemwiseMul
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1905) (l23bt_pm_not_written 1905 11707 (by decide))
    (l23bt_nonempty_pm 1904) (l23bt_pm_not_written 1904 11647 (by decide))
    (l23bt_pm_not_written 1904 11703 (by decide))
  intro s
  unfold l23btPmMul11707
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 0 11647 11703 11707

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11708 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11708 =
      elemwiseMul (denoteGraphDistributedFaithful pm initPM 11648)
        (denoteGraphDistributedFaithful pm initPM 11704) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1905 l23btPmMul11708
    11648 11704 11708 elemwiseMul
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1906) (l23bt_pm_not_written 1906 11708 (by decide))
    (l23bt_nonempty_pm 1905) (l23bt_pm_not_written 1905 11648 (by decide))
    (l23bt_pm_not_written 1905 11704 (by decide))
  intro s
  unfold l23btPmMul11708
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mul_out pm s 1 11648 11704 11708

/-! ### Node reductions: MoE join 5924 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5924 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5924 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 5904)
        (denoteGraphDistributedFaithful sm initSM 5923) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 921 l23btSmAdd5924
    5904 5923 5924 elemwiseAdd
    (by native_decide) l23bt_sm_node_facts.2.2.2.2.2.1 ?_
    (l23bt_nonempty_sm 922) (l23bt_sm_not_written 922 5924 (by decide))
    (l23bt_nonempty_sm 921) (l23bt_sm_not_written 921 5904 (by decide))
    (l23bt_sm_not_written 921 5923 (by decide))
  intro s
  unfold l23btSmAdd5924
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 5904 5923 5924

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11711 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11711 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11633)
        (denoteGraphDistributedFaithful pm initPM 11707) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1906 l23btPmAdd11711
    11633 11707 11711 elemwiseAdd
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1907) (l23bt_pm_not_written 1907 11711 (by decide))
    (l23bt_nonempty_pm 1906) (l23bt_pm_not_written 1906 11633 (by decide))
    (l23bt_pm_not_written 1906 11707 (by decide))
  intro s
  unfold l23btPmAdd11711
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 11633 11707 11711

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11712 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11712 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 11634)
        (denoteGraphDistributedFaithful pm initPM 11708) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1907 l23btPmAdd11712
    11634 11708 11712 elemwiseAdd
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1908) (l23bt_pm_not_written 1908 11712 (by decide))
    (l23bt_nonempty_pm 1907) (l23bt_pm_not_written 1907 11634 (by decide))
    (l23bt_pm_not_written 1907 11708 (by decide))
  intro s
  unfold l23btPmAdd11712
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 11634 11708 11712

/-! ### Node reductions: float 5925 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5925 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5925 =
      denoteGraphDistributedFaithful sm initSM 5924 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 922 l23btSmFloat5925
    5924 5925 (fun x => x)
    (by native_decide) l23bt_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_sm 923) (l23bt_sm_not_written 923 5925 (by decide))
    (l23bt_nonempty_sm 922) (l23bt_sm_not_written 922 5924 (by decide))
  intro s
  unfold l23btSmFloat5925
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 5924 5925 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11717 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11717 =
      denoteGraphDistributedFaithful pm initPM 11711 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1908 l23btPmFloat11717
    11711 11717 (fun x => x)
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1909) (l23bt_pm_not_written 1909 11717 (by decide))
    (l23bt_nonempty_pm 1908) (l23bt_pm_not_written 1908 11711 (by decide))
  intro s
  unfold l23btPmFloat11717
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 11711 11717 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11718 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11718 =
      denoteGraphDistributedFaithful pm initPM 11712 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1909 l23btPmFloat11718
    11712 11718 (fun x => x)
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1910) (l23bt_pm_not_written 1910 11718 (by decide))
    (l23bt_nonempty_pm 1909) (l23bt_pm_not_written 1909 11712 (by decide))
  intro s
  unfold l23btPmFloat11718
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 11712 11718 []

/-! ### Node reductions: residual join 5926 -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_sm5926 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5926 =
      elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8580)
        (denoteGraphDistributedFaithful sm initSM 5925) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 923 l23btSmAdd5926
    8580 5925 5926 elemwiseAdd
    (by native_decide) l23bt_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l23bt_nonempty_sm 924) (l23bt_sm_not_written 924 5926 (by decide))
    (l23bt_nonempty_sm 923) (l23bt_sm_not_written 923 8580 (by decide))
    (l23bt_sm_not_written 923 5925 (by decide))
  intro s
  unfold l23btSmAdd5926
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm s 0 8580 5925 5926

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11721 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11721 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16847)
        (denoteGraphDistributedFaithful pm initPM 11717) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1910 l23btPmAdd11721
    16847 11717 11721 elemwiseAdd
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23bt_nonempty_pm 1911) (l23bt_pm_not_written 1911 11721 (by decide))
    (l23bt_nonempty_pm 1910) (l23bt_pm_not_written 1910 16847 (by decide))
    (l23bt_pm_not_written 1910 11717 (by decide))
  intro s
  unfold l23btPmAdd11721
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 0 16847 11717 11721

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_red_pm11722 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11722 =
      elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16855)
        (denoteGraphDistributedFaithful pm initPM 11718) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1911 l23btPmAdd11722
    16855 11718 11722 elemwiseAdd
    (by native_decide) l23bt_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23bt_nonempty_pm 1912) (l23bt_pm_not_written 1912 11722 (by decide))
    (l23bt_nonempty_pm 1911) (l23bt_pm_not_written 1911 16855 (by decide))
    (l23bt_pm_not_written 1911 11718 (by decide))
  intro s
  unfold l23btPmAdd11722
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm s 1 16855 11718 11722

/-! ### Node reductions: 2-way multiref off 5926 -/

/-! ### Node reductions: RMSNorm 5928 -/

/-! ### Node reductions: per-head Q projection 5930 -/

/-! ### Shared helpers: weight transport and cu identification -/

set_option maxRecDepth 1000000 in
private theorem l23bt_weight_bridge (initSM initPM : Store)
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
private theorem l23bt_weight_eq (initSM initPM : Store)
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
private theorem l23bt_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  rw [l23bt_pmFinal initPM W hpw]
  exact hPM W sh hmem

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23bt_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5884) = [0, 2 * 2048] := by
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5884).shape = [2] := by
    rw [l23bt_pmFinal initPM 5884 l23bt_cu_not_written]
    exact hPM 5884 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5884)).length = 2 := by
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
-- Faithful zigzag relation for generated goal 5904 (block-10 MoE expert layer).
theorem recon_zigzagGoal_5904_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5904)
      (denoteGraphDistributedFaithful pm initPM 11633)
      (denoteGraphDistributedFaithful pm initPM 11634)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hX := recon_zigzagGoal_8591_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5899_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5900_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l23bt_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8591)
      (denoteGraphDistributedFaithful pm initPM 16866)
      (denoteGraphDistributedFaithful pm initPM 16889)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5899)
      (denoteGraphDistributedFaithful pm initPM 11623)
      (denoteGraphDistributedFaithful pm initPM 11624)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5900)
      (denoteGraphDistributedFaithful pm initPM 11625)
      (denoteGraphDistributedFaithful pm initPM 11626)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5902 = allGatherPrimDimN 0 2 0 [initPM 11629, initPM 11630] :=
    l23bt_weight_bridge initSM initPM hInit initGoal_5902 (by native_decide)
      5902 11629 11630 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5903 = allGatherPrimDimN 0 2 0 [initPM 11631, initPM 11632] :=
    l23bt_weight_bridge initSM initPM hInit initGoal_5903 (by native_decide)
      5903 11631 11632 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5902).shape = [64, 1024, 1024] :=
    hSM 5902 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5903).shape = [64, 1024, 512] :=
    hSM 5903 [64, 1024, 512] (by native_decide)
  rw [l23bt_red_sm5904 initSM, l23bt_red_pm11633 initPM, l23bt_red_pm11634 initPM]
  rw [l23bt_sm_leaf initSM 5902 (by decide), l23bt_sm_leaf initSM 5903 (by decide),
    l23bt_pm_leaf initPM 11629 (by decide), l23bt_pm_leaf initPM 11630 (by decide),
    l23bt_pm_leaf initPM 11631 (by decide), l23bt_pm_leaf initPM 11632 (by decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5902) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5903) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 11629, initPM 11630])
    (allGatherPrimDimN 0 2 0 [initPM 11631, initPM 11632])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5919 (`FW_reshape`).
theorem recon_zigzagGoal_5919_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5919)
      (denoteGraphDistributedFaithful pm initPM 11687)
      (denoteGraphDistributedFaithful pm initPM 11688)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 512] [2048, 512] := by
  have hparent := recon_zigzagGoal_5918_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23bt_red_sm5919 initSM, l23bt_red_pm11687 initPM, l23bt_red_pm11688 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5921 (`FW_mix_precision_linear`).
theorem recon_zigzagGoal_5921_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5921)
      (denoteGraphDistributedFaithful pm initPM 11693)
      (denoteGraphDistributedFaithful pm initPM 11694)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5919_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5920 =
      denoteGraphDistributedFaithful pm initPM 5920 :=
    l23bt_weight_eq initSM initPM hInit 5920 initGoal_5920 (by native_decide)
      rfl rfl rfl rfl
      l23bt_weights_not_written.1.1 l23bt_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5920).shape = [1024, 512] :=
    l23bt_pm_weight_shape initPM hPM 5920 [1024, 512] (by native_decide)
      l23bt_weights_not_written.2.1
  rw [l23bt_red_sm5921 initSM, l23bt_red_pm11693 initPM, l23bt_red_pm11694 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5922 (`FW_view`).
theorem recon_zigzagGoal_5922_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5922)
      (denoteGraphDistributedFaithful pm initPM 11703)
      (denoteGraphDistributedFaithful pm initPM 11704)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5921_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23bt_red_sm5922 initSM, l23bt_red_pm11703 initPM, l23bt_red_pm11704 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5923 (broadcast `FW_mul`).
theorem recon_zigzagGoal_5923_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5923)
      (denoteGraphDistributedFaithful pm initPM 11707)
      (denoteGraphDistributedFaithful pm initPM 11708)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5909_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5922_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5909)
      (denoteGraphDistributedFaithful pm initPM 11647)
      (denoteGraphDistributedFaithful pm initPM 11648)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1] [2048, 1] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5922)
      (denoteGraphDistributedFaithful pm initPM 11703)
      (denoteGraphDistributedFaithful pm initPM 11704)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l23bt_red_sm5923 initSM, l23bt_red_pm11707 initPM, l23bt_red_pm11708 initPM]
  exact Zigzag2Rel.mul_broadcast_col1 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5924 (`FW_add`, MoE join).
theorem recon_zigzagGoal_5924_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5924)
      (denoteGraphDistributedFaithful pm initPM 11711)
      (denoteGraphDistributedFaithful pm initPM 11712)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_5904_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5923_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5904)
      (denoteGraphDistributedFaithful pm initPM 11633)
      (denoteGraphDistributedFaithful pm initPM 11634)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5923)
      (denoteGraphDistributedFaithful pm initPM 11707)
      (denoteGraphDistributedFaithful pm initPM 11708)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l23bt_red_sm5924 initSM, l23bt_red_pm11711 initPM, l23bt_red_pm11712 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5925 (`FW_float`, identity cast).
theorem recon_zigzagGoal_5925_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5925)
      (denoteGraphDistributedFaithful pm initPM 11717)
      (denoteGraphDistributedFaithful pm initPM 11718)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5924_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23bt_red_sm5925 initSM, l23bt_red_pm11717 initPM, l23bt_red_pm11718 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for generated goal 5926 (`FW_add`, residual join).
theorem recon_zigzagGoal_5926_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5926)
      (denoteGraphDistributedFaithful pm initPM 11721)
      (denoteGraphDistributedFaithful pm initPM 11722)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hA := recon_zigzagGoal_8580_faithful initSM initPM hSM hPM hInit hValues hCu
  have hB := recon_zigzagGoal_5925_faithful initSM initPM hSM hPM hInit hValues hCu
  obtain ⟨a0, a1, has⟩ := hA
  obtain ⟨b0, b1, hbs⟩ := hB
  have hA' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8580)
      (denoteGraphDistributedFaithful pm initPM 16847)
      (denoteGraphDistributedFaithful pm initPM 16855)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1024] [2048, 1024] := ⟨a0, a1, has⟩
  have hB' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5925)
      (denoteGraphDistributedFaithful pm initPM 11717)
      (denoteGraphDistributedFaithful pm initPM 11718)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1024] [2048, 1024] := ⟨b0, b1, hbs⟩
  rw [l23bt_red_sm5926 initSM, l23bt_red_pm11721 initPM, l23bt_red_pm11722 initPM]
  exact Zigzag2Rel.add 2048 1024 hA' hB' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
